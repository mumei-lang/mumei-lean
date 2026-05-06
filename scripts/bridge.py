"""Orchestrate the mumei → mumei-lean → mumei certificate pipeline.

Given a mumei ``.proof-cert.json`` (or a ``std-proof-bundle.json``),
this script:

1. Calls :mod:`scripts.ingest_cert` to translate every ``unknown`` atom
   into a Lean theorem under ``generated/``.
2. Runs ``lake build`` to type-check and prove those theorems.
3. Calls :mod:`scripts.export_cert` to emit a mumei-compatible
   ``.lean-cert.json`` recording which atoms the Lean side proved.

The script is also useful as a *dry run* (``--no-build``) when you
just want to see which atoms would be lifted into Lean.

It can also scan a mumei repository's ``std/certs/`` directory in bulk
(``--scan-unknown``) and aggregate every per-module certificate that
contains an ``unknown`` atom.

This is the only script meant to be invoked by humans during normal
use; ``ingest_cert.py`` and ``export_cert.py`` are usable on their own
but exist primarily to keep the orchestration steps testable in
isolation.
"""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path
from typing import List, Optional, Tuple

try:
    from .ingest_cert import (
        IngestedAtom,
        collect_unknown_atoms,
        module_to_path,
        write_modules,
    )
    from .export_cert import (
        _failed_theorem_attributions,
        _has_unattributable_failures,
        upgrade_certificate,
    )
except ImportError:  # pragma: no cover - direct ``python scripts/bridge.py``
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from ingest_cert import (  # type: ignore
        IngestedAtom,
        collect_unknown_atoms,
        module_to_path,
        write_modules,
    )
    from export_cert import (  # type: ignore
        _failed_theorem_attributions,
        _has_unattributable_failures,
        upgrade_certificate,
    )


def _load_cert(path: Path) -> dict:
    return json.loads(path.read_text())


def _scan_unknown_certs(std_certs_dir: Path) -> List[Tuple[Path, dict]]:
    """Return a list of ``(path, certificate_dict)`` for each per-module
    cert under ``std_certs_dir`` that contains at least one ``unknown``
    atom.
    """
    found: List[Tuple[Path, dict]] = []
    if not std_certs_dir.exists():
        return found
    for path in sorted(std_certs_dir.rglob("*.json")):
        try:
            payload = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        atoms = payload.get("atoms")
        if not isinstance(atoms, list):
            continue
        if any(
            isinstance(a, dict) and a.get("z3_check_result") == "unknown"
            for a in atoms
        ):
            found.append((path, payload))
    return found


def _run_lake_build(repo_dir: Path, log_path: Path) -> int:
    """Run ``lake build`` and capture its combined output to ``log_path``.

    Returns the process exit code. Returns ``127`` when ``lake`` is not
    on ``$PATH`` so callers can distinguish "Lean toolchain missing"
    from "build failed".
    """
    if shutil.which("lake") is None:
        log_path.write_text("error: `lake` not found on PATH\n")
        return 127
    proc = subprocess.run(  # noqa: S603 - explicit lake invocation
        ["lake", "build"],
        cwd=repo_dir,
        capture_output=True,
        text=True,
    )
    log_path.write_text(proc.stdout + proc.stderr)
    return proc.returncode


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "End-to-end orchestrator for the mumei ↔ mumei-lean bridge."
        ),
    )
    src = parser.add_mutually_exclusive_group(required=True)
    src.add_argument(
        "--cert",
        type=Path,
        help="Path to a single mumei .proof-cert.json.",
    )
    src.add_argument(
        "--bundle",
        type=Path,
        help="Path to a mumei std-proof-bundle.json.",
    )
    src.add_argument(
        "--scan-unknown",
        type=Path,
        metavar="MUMEI_REPO",
        help="Scan <MUMEI_REPO>/std/certs for per-module certificates "
        "containing unknown atoms.",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("generated"),
        help="Directory to emit generated Lean sources into "
        "(default: generated/).",
    )
    parser.add_argument(
        "--module-prefix",
        default="Generated",
        help="Top-level Lean module prefix (default: Generated).",
    )
    parser.add_argument(
        "--lean-cert-out",
        type=Path,
        default=None,
        help="Where to write the resulting .lean-cert.json. "
        "Required unless --no-export is set.",
    )
    parser.add_argument(
        "--summary-json",
        type=Path,
        default=None,
        help="Optional path to write a JSON summary of unknown atoms "
        "discovered (per module + names). Useful as a CI artifact when "
        "running with --scan-unknown.",
    )
    parser.add_argument(
        "--lean-version",
        default="unknown",
        help="Lean toolchain version to record in the output certificate.",
    )
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="Skip the `lake build` step (useful for dry runs).",
    )
    parser.add_argument(
        "--ci-mode",
        action="store_true",
        help="CI mode: on lake build failure, fall back to --no-build and "
        "preserve generated .lean files as artifacts.",
    )
    parser.add_argument(
        "--no-export",
        action="store_true",
        help="Skip writing the final .lean-cert.json (implies dry run).",
    )
    parser.add_argument(
        "--repo-dir",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="mumei-lean repo root used as the lake working directory "
        "(default: this repo).",
    )
    args = parser.parse_args(argv)

    # 1. Build the input payload + remember the originating cert(s).
    if args.cert is not None:
        payloads: List[Tuple[Path, dict]] = [(args.cert, _load_cert(args.cert))]
    elif args.bundle is not None:
        payloads = [(args.bundle, _load_cert(args.bundle))]
    else:
        payloads = _scan_unknown_certs(args.scan_unknown / "std" / "certs")
        if not payloads:
            print(
                f"info: no certificates with unknown atoms found under "
                f"{args.scan_unknown / 'std' / 'certs'}"
            )
            if args.summary_json is not None:
                # Still emit a summary so downstream CI artifacts have
                # a deterministic file to upload even when the scan is
                # empty.
                args.summary_json.parent.mkdir(parents=True, exist_ok=True)
                args.summary_json.write_text(
                    json.dumps(
                        {
                            "total_unknown": 0,
                            "modules": [],
                            "ci_mode_fallback": False,
                        },
                        indent=2,
                        ensure_ascii=False,
                    )
                    + "\n"
                )
                print(f"wrote {args.summary_json} (0 unknown atoms)")
            return 0

    # Track proved atom names *per payload* so that, in multi-cert
    # mode, an ``unknown`` atom in one cert cannot accidentally
    # overwrite a same-named ``unsat`` atom in another cert. We also
    # remember each payload's full ``IngestedAtom`` list so we can
    # reproduce the originating ``Generated/<...>.lean`` path for
    # per-file failure attribution further down.
    proved_per_payload: List[List[str]] = []
    atoms_per_payload: List[List[IngestedAtom]] = []
    # Collect all atoms across payloads first, then call ``write_modules``
    # once. ``write_modules`` writes one Lean file per module key and
    # would silently overwrite earlier payloads if two payloads
    # produced atoms whose module keys collide after sanitisation
    # (e.g. ``math.mm`` vs ``Math.mm`` → ``Generated.Math``).
    all_atoms: List[IngestedAtom] = []
    for src_path, payload in payloads:
        atoms = collect_unknown_atoms(payload)
        all_atoms.extend(atoms)
        proved_per_payload.append([a.name for a in atoms])
        atoms_per_payload.append(atoms)
        print(
            f"ingested {len(atoms):3d} unknown atom(s) from {src_path}"
        )
    write_modules(all_atoms, args.out_dir, args.module_prefix)

    # Aggregate per-module unknown atom counts so CI / humans can
    # see which mumei modules still rely on Lean to close their
    # obligations. The summary is grouped by ``module_key`` rather
    # than by source certificate so that bundle inputs collapse
    # naturally into per-namespace stats.
    modules_summary: dict[str, List[str]] = {}
    for atom in all_atoms:
        modules_summary.setdefault(atom.module_key, []).append(atom.name)
    modules_list = [
        {
            "module": key,
            "unknown_count": len(names),
            "atoms": sorted(names),
        }
        for key, names in sorted(modules_summary.items())
    ]
    summary_payload = {
        "total_unknown": len(all_atoms),
        "modules": modules_list,
        "ci_mode_fallback": False,
    }
    if args.summary_json is not None:
        args.summary_json.parent.mkdir(parents=True, exist_ok=True)
        args.summary_json.write_text(
            json.dumps(summary_payload, indent=2, ensure_ascii=False) + "\n"
        )
        print(
            f"wrote {args.summary_json} "
            f"({summary_payload['total_unknown']} unknown atom(s) across "
            f"{len(modules_list)} module(s))"
        )

    if args.no_build:
        print("dry run: skipping `lake build`")
        return 0

    # 2. Build.
    log_path = args.out_dir / "lake_build.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    rc = _run_lake_build(args.repo_dir, log_path)
    lake_missing = rc == 127
    if lake_missing:
        print(
            "warning: `lake` is not installed; skipping build. "
            "Install Lean 4 / Lake to enable end-to-end verification.",
            file=sys.stderr,
        )
    if args.ci_mode and rc != 0:
        print(
            "warning: `lake build` failed in --ci-mode; preserving generated "
            "Lean files and skipping export.",
            file=sys.stderr,
        )
        if args.summary_json is not None:
            summary_payload["ci_mode_fallback"] = True
            args.summary_json.write_text(
                json.dumps(summary_payload, indent=2, ensure_ascii=False) + "\n"
            )
        return 0

    build_log = log_path.read_text()
    print(f"`lake build` exited with status {rc}; log: {log_path}")

    if args.no_export:
        return rc

    # 3. Export per-input certificate.
    if args.lean_cert_out is None:
        parser.error("--lean-cert-out is required unless --no-export is set")

    attributions = _failed_theorem_attributions(build_log)
    # If the build log has a failure we couldn't attribute to a
    # specific theorem (e.g. a file-level ``import`` error), we cannot
    # safely tell which atoms succeeded — fall back to the same
    # conservative behaviour as ``lake_missing``.
    unattributable = (not lake_missing) and _has_unattributable_failures(build_log)
    # ``lake build`` returned non-zero but neither sorry nor compile
    # errors matched (e.g. infrastructure errors like ``error: cannot
    # resolve dependency 'mathlib'`` whose ``error:`` is not preceded
    # by a ``file:line:col`` location, lake itself crashing without a
    # diagnostic, or an empty log). In those cases we have no way to
    # attribute the failure but a non-zero ``rc`` *is* a hard signal
    # that nothing was verified — be conservative.
    unrecognised_failure = (
        (not lake_missing)
        and rc != 0
        and not attributions
        and not unattributable
    )
    if lake_missing or unattributable or unrecognised_failure:
        if unattributable:
            print(
                "warning: build log contains failures that could not be "
                "attributed to a specific theorem; treating all lifted "
                "atoms as failed.",
                file=sys.stderr,
            )
        elif unrecognised_failure:
            print(
                f"warning: `lake build` exited with status {rc} but no "
                f"theorem-level failures could be parsed from the log; "
                f"treating all lifted atoms as failed.",
                file=sys.stderr,
            )
        # Treat every atom we would have lifted into Lean as failed
        # in *every* payload so the resulting certificate is
        # conservative (no false ``lean_verified``).
        per_payload_failed: List[List[str]] = [
            list(set(proved)) for proved in proved_per_payload
        ]
    else:
        # Map each payload to the set of generated source files it
        # owns. Failures whose Lake-reported file path matches one of
        # those files are attributed to that payload only, which
        # avoids cross-payload contamination when two certs contain
        # atoms with the same name. Failures without a recoverable
        # file path, or whose file path does not match any known
        # payload, are applied to *every* payload that owns an atom
        # by that name so we never silently drop a real failure.
        payload_files: List[set] = []
        for atoms in atoms_per_payload:
            files: set = set()
            for atom in atoms:
                rel = module_to_path(atom.module_key, args.module_prefix)
                files.add(str((args.out_dir / rel).as_posix()))
                files.add(str(rel.as_posix()))
            payload_files.append(files)

        all_known_files: set = set().union(*payload_files) if payload_files else set()

        per_payload_failed = []
        for proved, files in zip(proved_per_payload, payload_files):
            local: set = set()
            proved_set = set(proved)
            for file_path, name in attributions:
                if name not in proved_set:
                    continue
                if file_path is None:
                    # No file context — apply to every payload that
                    # owns the name to stay conservative.
                    local.add(name)
                    continue
                file_norm = str(Path(file_path).as_posix())
                matched_known = any(
                    file_norm == f or file_norm.endswith(f)
                    for f in all_known_files
                )
                matched_local = any(
                    file_norm == f or file_norm.endswith(f) for f in files
                )
                if matched_local:
                    local.add(name)
                elif not matched_known:
                    # File path doesn't correspond to any payload we
                    # generated; fall back to applying the failure
                    # globally rather than silently ignoring it.
                    local.add(name)
            per_payload_failed.append(sorted(local))

    if len(payloads) == 1:
        upgraded = upgrade_certificate(
            cert=payloads[0][1],
            proved_atoms=proved_per_payload[0],
            failed_atoms=per_payload_failed[0],
            lean_version=args.lean_version,
        )
        args.lean_cert_out.parent.mkdir(parents=True, exist_ok=True)
        args.lean_cert_out.write_text(
            json.dumps(upgraded, indent=2, ensure_ascii=False) + "\n"
        )
        print(f"wrote {args.lean_cert_out}")
        return 0 if rc == 0 else rc

    # Multi-input mode: write one .lean-cert.json per input alongside
    # ``args.lean_cert_out`` interpreted as a directory.
    out_dir = args.lean_cert_out
    out_dir.mkdir(parents=True, exist_ok=True)
    for (src_path, payload), proved, failed in zip(
        payloads, proved_per_payload, per_payload_failed
    ):
        upgraded = upgrade_certificate(
            cert=payload,
            proved_atoms=proved,
            failed_atoms=failed,
            lean_version=args.lean_version,
        )
        target = out_dir / src_path.name
        target.write_text(json.dumps(upgraded, indent=2, ensure_ascii=False) + "\n")
        print(f"wrote {target}")
    return 0 if rc == 0 else rc


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
