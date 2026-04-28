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
    from .ingest_cert import collect_unknown_atoms, write_modules
    from .export_cert import upgrade_certificate
except ImportError:  # pragma: no cover - direct ``python scripts/bridge.py``
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from ingest_cert import collect_unknown_atoms, write_modules  # type: ignore
    from export_cert import upgrade_certificate  # type: ignore


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
            return 0

    proved_atom_names: List[str] = []
    for src_path, payload in payloads:
        atoms = collect_unknown_atoms(payload)
        write_modules(atoms, args.out_dir, args.module_prefix)
        proved_atom_names.extend(a.name for a in atoms)
        print(
            f"ingested {len(atoms):3d} unknown atom(s) from {src_path}"
        )

    if args.no_build:
        print("dry run: skipping `lake build`")
        return 0

    # 2. Build.
    log_path = args.out_dir / "lake_build.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    rc = _run_lake_build(args.repo_dir, log_path)
    if rc == 127:
        print(
            "warning: `lake` is not installed; skipping build. "
            "Install Lean 4 / Lake to enable end-to-end verification.",
            file=sys.stderr,
        )
        if args.no_export:
            return 0
        # Without `lake` we cannot prove anything; treat all atoms as
        # failed so the resulting certificate is conservative.
        build_log = ""
    else:
        build_log = log_path.read_text()
        print(f"`lake build` exited with status {rc}; log: {log_path}")

    if args.no_export:
        return rc

    # 3. Export per-input certificate.
    if args.lean_cert_out is None:
        parser.error("--lean-cert-out is required unless --no-export is set")

    if len(payloads) == 1:
        from export_cert import _failed_theorem_names  # type: ignore
        failed = _failed_theorem_names(build_log)
        upgraded = upgrade_certificate(
            cert=payloads[0][1],
            proved_atoms=proved_atom_names,
            failed_atoms=failed,
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
    from export_cert import _failed_theorem_names  # type: ignore
    failed = _failed_theorem_names(build_log)
    for src_path, payload in payloads:
        upgraded = upgrade_certificate(
            cert=payload,
            proved_atoms=proved_atom_names,
            failed_atoms=failed,
            lean_version=args.lean_version,
        )
        target = out_dir / src_path.name
        target.write_text(json.dumps(upgraded, indent=2, ensure_ascii=False) + "\n")
        print(f"wrote {target}")
    return 0 if rc == 0 else rc


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
