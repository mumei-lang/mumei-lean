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
from typing import Dict, List, Optional, Tuple

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
        BRIDGE_LEMMA_HASH,
        LEAN_VERIFIED,
        MANUAL_LEMMA_REQUIRED,
        TRANSLATOR_VERSION,
        upgrade_certificate,
    )
    from .bridge_harness import (
        bridge_failure_taxonomy,
        bridge_harness_contract,
        bridge_stage_metadata,
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
        BRIDGE_LEMMA_HASH,
        LEAN_VERIFIED,
        MANUAL_LEMMA_REQUIRED,
        TRANSLATOR_VERSION,
        upgrade_certificate,
    )
    from bridge_harness import (  # type: ignore
        bridge_failure_taxonomy,
        bridge_harness_contract,
        bridge_stage_metadata,
    )


KNOWN_LEAN_WITNESSES: Dict[str, Dict[str, str]] = {
    "abs_saturating": {
        "module_key": "std/math/abs",
        "module": "MumeiLean.StdMathAbs",
        "theorem": "abs_saturating_correct",
    },
    "fixed_point_abs": {
        "module_key": "std/math/fixed_point",
        "module": "MumeiLean.StdMathAbs",
        "theorem": "fixed_point_abs_correct",
    },
    "fixed_point_from_int": {
        "module_key": "std/math/fixed_point",
        "module": "MumeiLean.StdMathAbs",
        "theorem": "fixed_point_from_int_correct",
    },
    "list_length": {
        "module_key": "std/list",
        "module": "MumeiLean.StdMathAbs",
        "theorem": "list_length_correct",
    },
}

AtomKey = Tuple[str, str]


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


def _candidate_metadata(
    atom: IngestedAtom,
    out_dir: Path,
    module_prefix: str,
    status: str,
    harness_stage: Optional[dict] = None,
) -> dict:
    rel = module_to_path(atom.module_key, module_prefix)
    diagnostics: List[str] = []
    if atom.escalation_reason:
        diagnostics.append(f"escalation_reason={atom.escalation_reason}")
    if atom.logic_fragment_tags:
        diagnostics.append(
            "logic_fragments=" + ",".join(sorted(atom.logic_fragment_tags))
        )
    if atom.is_partial_translation:
        diagnostics.append("partial_translation")
    if atom.manual_lemma_reason:
        diagnostics.append(f"manual_lemma_reason={atom.manual_lemma_reason}")
    heatmap_data = _load_solver_heatmap(atom, out_dir)
    if heatmap_data is not None:
        diagnostics.append("solver_heatmap_available=true")
        diagnostics.append(
            "top_constraints="
            + _format_top_constraints(heatmap_data.get("constraints", []), 3)
        )
    proof_strategy = select_proof_strategy(atom)
    mathlib_imports = resolve_mathlib_imports(atom)
    metadata = {
        "status": status,
        "theorem_name": f"{atom.name}_correct",
        "translator_version": TRANSLATOR_VERSION,
        "bridge_lemma_hash": BRIDGE_LEMMA_HASH,
        "proof_path": str((out_dir / rel).as_posix()),
        "diagnostics": diagnostics,
        "escalation_reason": atom.escalation_reason,
        "logic_fragment_tags": atom.logic_fragment_tags,
        "z3_result_class": atom.z3_result_class,
        "translator_ir": atom.translator_ir,
        "manual_lemma_reason": atom.manual_lemma_reason,
        "proof_strategy": proof_strategy,
        "mathlib_imports": mathlib_imports,
    }
    if heatmap_data is not None:
        metadata["solver_heatmap"] = heatmap_data
    if harness_stage is not None:
        metadata["harness"] = {
            **harness_stage,
            "failure_taxonomy": bridge_failure_taxonomy(status, diagnostics),
        }
    return metadata


def _load_solver_heatmap(atom: IngestedAtom, out_dir: Path) -> Optional[dict]:
    for path in (
        out_dir / f"{atom.name}_heatmap.json",
        out_dir.parent / f"{atom.name}_heatmap.json",
    ):
        if not path.exists():
            continue
        try:
            payload = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        if isinstance(payload, dict):
            return payload
    return None


def _format_top_constraints(constraints: List[dict], top_n: int) -> str:
    sorted_constraints = sorted(
        constraints,
        key=lambda constraint: constraint.get("rlimit_consumed", 0),
        reverse=True,
    )
    return ",".join(
        f"{constraint.get('constraint_id', 'unknown')}({constraint.get('rlimit_consumed', 0)})"
        for constraint in sorted_constraints[:top_n]
    )


def _has_structural_partial_translation(atom: IngestedAtom) -> bool:
    body_partial = (
        atom.body_translation is not None and atom.body_translation.is_partial
    )
    return (
        atom.requires_translation.is_partial
        or atom.ensures_translation.is_partial
        or body_partial
    )


def select_proof_strategy(atom: IngestedAtom) -> dict:
    """Select an automated proof strategy based on TranslatorIR metadata.

    Examines the atom's ``lowering_rules`` and ``requires_bridge_lemmas``
    to choose which Lean tactic or proof pattern to attempt first. This
    enables the bridge to emit targeted ``by`` blocks rather than falling
    back to the generic ``mumei_arith`` cascade for every obligation.

    Returns a dict with:
    - ``strategy``: name of the proof strategy
    - ``tactics``: ordered list of Lean tactics to try
    - ``imports``: additional Lean imports required
    - ``hints``: human-readable explanation
    """
    ir = atom.translator_ir
    if not isinstance(ir, dict):
        return {
            "strategy": "default",
            "tactics": ["mumei_arith"],
            "imports": [],
            "hints": "no TranslatorIR metadata; using default cascade",
        }
    rules = ir.get("lowering_rules", [])
    hints_list = ir.get("proof_trace_hints", [])

    tactics: List[str] = []
    imports: List[str] = []
    strategy = "default"

    if "finite_field_lowering" in rules:
        strategy = "finite_field"
        tactics.extend(["unfold MumeiLean.Algebra.mumei_ff_in_field",
                         "constructor", "exact Int.emod_nonneg _ _",
                         "exact Int.emod_lt_of_pos _ _"])
        imports.append("MumeiLean.Algebra")

    if "group_theory_lowering" in rules:
        strategy = "group_theory" if strategy == "default" else f"{strategy}+group"
        tactics.extend(["simp [mul_assoc]", "ring"])
        imports.append("MumeiLean.Algebra")

    if "crypto_primitive_lowering" in rules:
        strategy = "crypto" if strategy == "default" else f"{strategy}+crypto"
        tactics.extend(["unfold MumeiLean.Crypto.hash",
                         "unfold MumeiLean.Crypto.encrypt",
                         "unfold MumeiLean.Crypto.decrypt",
                         "ring"])
        imports.append("MumeiLean.Crypto")

    if "quantifier_skolemize_lowering" in rules:
        strategy = "skolemize" if strategy == "default" else f"{strategy}+skolemize"
        tactics.extend(["rcases", "exact"])
        imports.append("MumeiLean.Quantifiers")

    if "implication_lowering" in rules:
        strategy = "implication" if strategy == "default" else f"{strategy}+implication"
        tactics.extend(["intro", "exact"])
        imports.append("MumeiLean.Quantifiers")

    if "higher_order_predicate_lowering" in rules:
        strategy = "higher_order" if strategy == "default" else f"{strategy}+higher_order"
        tactics.extend(["intro", "apply", "exact"])
        imports.append("MumeiLean.AdvancedPatterns")

    if not tactics:
        tactics = ["mumei_arith"]

    return {
        "strategy": strategy,
        "tactics": tactics,
        "imports": sorted(set(imports)),
        "hints": "; ".join(hints_list) if hints_list else "using default cascade",
    }


def resolve_mathlib_imports(atom: IngestedAtom) -> List[str]:
    """Determine which mathlib4 modules should be imported based on the atom's
    TranslatorIR lowering rules.

    Returns a list of Lean ``import`` strings. This allows ``ingest_cert.py``
    to emit the correct imports at the top of generated Lean files without
    requiring manual specification.
    """
    ir = atom.translator_ir
    if not isinstance(ir, dict):
        return []
    rules = ir.get("lowering_rules", [])
    imports: List[str] = []
    if "finite_field_lowering" in rules:
        imports.extend([
            "import Mathlib.Data.ZMod.Basic",
            "import Mathlib.Data.Int.ModEq",
        ])
    if "group_theory_lowering" in rules:
        imports.append("import Mathlib.Algebra.Group.Basic")
    if "crypto_primitive_lowering" in rules:
        imports.extend([
            "import Mathlib.Data.Int.ModEq",
            "import Mathlib.Data.Nat.Totient",
        ])
    if "integer_overflow_bridge" in rules:
        imports.append("import Mathlib.Tactic")
    return sorted(set(imports))


def _atom_key(atom: IngestedAtom) -> AtomKey:
    return (atom.module_key, atom.name)


def _known_witness_names(
    atoms: List[IngestedAtom],
    known_witness_proved: set[AtomKey],
) -> List[str]:
    return sorted(
        {
            atom.name
            for atom in atoms
            if _atom_key(atom) in known_witness_proved
        }
    )


def _candidate_status(
    atom: IngestedAtom,
    proved: List[str],
    failed: List[str],
    known_witness_proved: Optional[set[AtomKey]] = None,
) -> str:
    if (
        known_witness_proved is not None
        and _atom_key(atom) in known_witness_proved
        and atom.name in proved
        and atom.name not in failed
    ):
        return LEAN_VERIFIED
    if _has_structural_partial_translation(atom):
        return "partial_translation"
    if atom.manual_lemma_reason:
        return MANUAL_LEMMA_REQUIRED
    if (
        atom.translator_version != TRANSLATOR_VERSION
        or atom.bridge_lemma_hash != BRIDGE_LEMMA_HASH
    ):
        return "stale_translator"
    if atom.name in proved and atom.name not in failed:
        return LEAN_VERIFIED
    return MANUAL_LEMMA_REQUIRED


def _metadata_for_atoms(
    atoms: List[IngestedAtom],
    out_dir: Path,
    module_prefix: str,
    proved: List[str],
    failed: List[str],
    harness_stage: Optional[dict] = None,
    known_witness_proved: Optional[set[AtomKey]] = None,
) -> Dict[str, dict]:
    return {
        atom.name: _candidate_metadata(
            atom,
            out_dir,
            module_prefix,
            _candidate_status(atom, proved, failed, known_witness_proved),
            harness_stage,
        )
        for atom in atoms
    }


def _empty_metric_bucket() -> dict:
    return {
        "attempts": 0,
        "lean_successes": 0,
        "partial_translation": 0,
        MANUAL_LEMMA_REQUIRED: 0,
        "stale_translator": 0,
        "success_rate": 0.0,
    }


def _metric_bucket_success_rate(bucket: dict) -> None:
    attempts = bucket["attempts"]
    bucket["success_rate"] = (
        round(bucket["lean_successes"] / attempts, 4) if attempts else 0.0
    )


def _aggregate_metrics(
    metadata_by_payload: List[Dict[str, dict]],
    atoms_per_payload: List[List[IngestedAtom]],
) -> dict:
    metrics = {
        "escalation_attempts": 0,
        "lean_successes": 0,
        "partial_translation": 0,
        MANUAL_LEMMA_REQUIRED: 0,
        "stale_translator": 0,
        "by_atom": {},
        "by_logic_fragment": {},
        "by_failure_reason": {},
        "by_z3_result_class": {},
        "low_success_categories": [],
    }
    for metadata, atoms in zip(metadata_by_payload, atoms_per_payload):
        for atom in atoms:
            status = metadata.get(atom.name, {}).get("status", MANUAL_LEMMA_REQUIRED)
            if status == "manual_required":
                status = MANUAL_LEMMA_REQUIRED
            metrics["escalation_attempts"] += 1
            if status == LEAN_VERIFIED:
                metrics["lean_successes"] += 1
            elif status == "partial_translation":
                metrics["partial_translation"] += 1
                if atom.manual_lemma_reason:
                    metrics[MANUAL_LEMMA_REQUIRED] += 1
            elif status == "stale_translator":
                metrics["stale_translator"] += 1
            else:
                metrics[MANUAL_LEMMA_REQUIRED] += 1
            metrics["by_atom"][atom.name] = {
                "status": status,
                "failure_reason": atom.escalation_reason,
                "logic_fragment_tags": atom.logic_fragment_tags,
                "z3_result_class": atom.z3_result_class,
                "translator_version": atom.translator_version,
                "bridge_lemma_hash": atom.bridge_lemma_hash,
                "manual_lemma_reason": atom.manual_lemma_reason,
            }
            reason = atom.escalation_reason or "unknown"
            reason_bucket = metrics["by_failure_reason"].setdefault(
                reason,
                _empty_metric_bucket(),
            )
            reason_bucket["attempts"] += 1
            reason_bucket_key = (
                "lean_successes" if status == LEAN_VERIFIED else status
            )
            reason_bucket[reason_bucket_key] += 1
            for tag in atom.logic_fragment_tags or ["untagged"]:
                tag_bucket = metrics["by_logic_fragment"].setdefault(
                    tag,
                    _empty_metric_bucket(),
                )
                tag_bucket["attempts"] += 1
                tag_bucket_key = (
                    "lean_successes" if status == LEAN_VERIFIED else status
                )
                tag_bucket[tag_bucket_key] += 1
            class_bucket = metrics["by_z3_result_class"].setdefault(
                atom.z3_result_class or atom.z3_check_result,
                _empty_metric_bucket(),
            )
            class_bucket["attempts"] += 1
            class_bucket_key = (
                "lean_successes" if status == LEAN_VERIFIED else status
            )
            class_bucket[class_bucket_key] += 1
    for grouping_name in (
        "by_failure_reason",
        "by_logic_fragment",
        "by_z3_result_class",
    ):
        for key, bucket in metrics[grouping_name].items():
            _metric_bucket_success_rate(bucket)
            if bucket["attempts"] >= 1 and bucket["success_rate"] < 0.7:
                metrics["low_success_categories"].append(
                    {"group": grouping_name, "category": key, **bucket}
                )
    return metrics


def _run_lake_build(repo_dir: Path, log_path: Path) -> int:
    """Run ``lake build`` and capture its combined output to ``log_path``.

    Returns the process exit code. Returns ``127`` when ``lake`` is not
    on ``$PATH`` so callers can distinguish "Lean toolchain missing"
    from "build failed".
    """
    lake = shutil.which("lake")
    elan = shutil.which("elan")
    toolchain_path = repo_dir / "lean-toolchain"
    cmd = ["lake", "build"]
    if elan is not None and toolchain_path.exists():
        toolchain = toolchain_path.read_text().strip()
        if toolchain:
            cmd = [elan, "run", toolchain, "lake", "build"]
    elif lake is None:
        log_path.write_text("error: `lake` not found on PATH\n")
        return 127
    proc = subprocess.run(  # noqa: S603 - explicit lake invocation
        cmd,
        cwd=repo_dir,
        capture_output=True,
        text=True,
    )
    log_path.write_text(proc.stdout + proc.stderr)
    return proc.returncode


def _module_source_path(repo_dir: Path, module: str) -> Path:
    return repo_dir / (module.replace(".", "/") + ".lean")


def _lake_build_command(repo_dir: Path, target: str) -> Optional[List[str]]:
    lake = shutil.which("lake")
    elan = shutil.which("elan")
    toolchain_path = repo_dir / "lean-toolchain"
    if elan is not None and toolchain_path.exists():
        toolchain = toolchain_path.read_text().strip()
        if toolchain:
            return [elan, "run", toolchain, "lake", "build", target]
    if lake is not None:
        return ["lake", "build", target]
    return None


def _verify_known_witnesses(
    atoms: List[IngestedAtom],
    repo_dir: Path,
    log_dir: Path,
) -> List[AtomKey]:
    modules: Dict[str, List[AtomKey]] = {}
    for atom in atoms:
        witness = KNOWN_LEAN_WITNESSES.get(atom.name)
        if witness is None or atom.module_key != witness["module_key"]:
            continue
        src = _module_source_path(repo_dir, witness["module"])
        try:
            source_text = src.read_text()
        except OSError:
            continue
        if f"theorem {witness['theorem']}" not in source_text:
            continue
        modules.setdefault(witness["module"], []).append(_atom_key(atom))

    proved: List[AtomKey] = []
    log_dir.mkdir(parents=True, exist_ok=True)
    for module, atom_keys in sorted(modules.items()):
        cmd = _lake_build_command(repo_dir, module)
        log_path = log_dir / f"known_witness_{module.replace('.', '_')}.log"
        if cmd is None:
            log_path.write_text("error: `lake` not found on PATH\n")
            continue
        proc = subprocess.run(  # noqa: S603 - explicit lake invocation
            cmd,
            cwd=repo_dir,
            capture_output=True,
            text=True,
        )
        log_path.write_text(proc.stdout + proc.stderr)
        if proc.returncode == 0:
            proved.extend(atom_keys)
    return sorted(set(proved))


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
        "--escalation-bundle",
        "--ingest-bundle",
        dest="escalation_bundle",
        type=Path,
        help="Path to a mumei escalation-bundle.json.",
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
        "Required unless --no-export is set. For --escalation-bundle, "
        "defaults to out/<bundle-stem>.lean-cert.json.",
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

    if (
        args.lean_cert_out is None
        and args.escalation_bundle is not None
        and not args.no_export
    ):
        bundle_name = args.escalation_bundle.name
        suffix = ".escalation-bundle.json"
        if bundle_name.endswith(suffix):
            stem = bundle_name[: -len(suffix)]
        elif bundle_name.endswith(".json"):
            stem = bundle_name[: -len(".json")]
        else:
            stem = args.escalation_bundle.stem
        args.lean_cert_out = Path("out") / f"{stem}.lean-cert.json"

    if args.cert is not None:
        input_kind = "cert"
    elif args.bundle is not None:
        input_kind = "bundle"
    elif args.escalation_bundle is not None:
        input_kind = "escalation_bundle"
    else:
        input_kind = "scan_unknown"
    build_mode = (
        "no_build"
        if args.no_build
        else "ci_mode"
        if args.ci_mode
        else "lake_build"
    )
    harness_contract = bridge_harness_contract(
        input_kind=input_kind,
        build_mode=build_mode,
        module_prefix=args.module_prefix,
        out_dir=str(args.out_dir),
        lean_cert_out=(
            str(args.lean_cert_out)
            if args.lean_cert_out is not None
            else None
        ),
    )
    harness_stage = bridge_stage_metadata(
        input_kind=input_kind,
        build_mode=build_mode,
        module_prefix=args.module_prefix,
        out_dir=str(args.out_dir),
        lean_cert_out=(
            str(args.lean_cert_out)
            if args.lean_cert_out is not None
            else None
        ),
    )

    # 1. Build the input payload + remember the originating cert(s).
    if args.cert is not None:
        payloads: List[Tuple[Path, dict]] = [(args.cert, _load_cert(args.cert))]
    elif args.bundle is not None:
        payloads = [(args.bundle, _load_cert(args.bundle))]
    elif args.escalation_bundle is not None:
        payloads = [(args.escalation_bundle, _load_cert(args.escalation_bundle))]
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
                            "harness_contract": harness_contract,
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
    all_candidate_atoms: List[IngestedAtom] = []
    all_atoms: List[IngestedAtom] = []
    for src_path, payload in payloads:
        atoms = collect_unknown_atoms(payload)
        proof_atoms = [atom for atom in atoms if not atom.is_partial_translation]
        all_candidate_atoms.extend(atoms)
        all_atoms.extend(proof_atoms)
        proved_per_payload.append([a.name for a in proof_atoms])
        atoms_per_payload.append(atoms)
        partial_count = len(atoms) - len(proof_atoms)
        print(
            f"ingested {len(atoms):3d} Lean candidate(s) from {src_path} "
            f"({partial_count} partial translation)"
        )
    write_modules(all_atoms, args.out_dir, args.module_prefix)

    # Aggregate per-module unknown atom counts so CI / humans can
    # see which mumei modules still rely on Lean to close their
    # obligations. The summary is grouped by ``module_key`` rather
    # than by source certificate so that bundle inputs collapse
    # naturally into per-namespace stats.
    modules_summary: dict[str, List[str]] = {}
    for atom in all_candidate_atoms:
        modules_summary.setdefault(atom.module_key, []).append(atom.name)
    modules_list = [
        {
            "module": key,
            "candidate_count": len(names),
            "unknown_count": len(names),
            "atoms": sorted(names),
        }
        for key, names in sorted(modules_summary.items())
    ]
    summary_payload = {
        "total_candidates": len(all_candidate_atoms),
        "total_unknown": len(all_candidate_atoms),
        "total_generated": len(all_atoms),
        "modules": modules_list,
        "ci_mode_fallback": False,
        "harness_contract": harness_contract,
    }
    if args.summary_json is not None:
        args.summary_json.parent.mkdir(parents=True, exist_ok=True)
        args.summary_json.write_text(
            json.dumps(summary_payload, indent=2, ensure_ascii=False) + "\n"
        )
        print(
            f"wrote {args.summary_json} "
            f"({summary_payload['total_candidates']} Lean candidate(s) across "
            f"{len(modules_list)} module(s))"
        )

    if args.no_build:
        metadata_per_payload = [
            _metadata_for_atoms(
                atoms,
                args.out_dir,
                args.module_prefix,
                proved,
                proved,
                harness_stage,
            )
            for atoms, proved in zip(atoms_per_payload, proved_per_payload)
        ]
        summary_payload["metrics"] = _aggregate_metrics(
            metadata_per_payload,
            atoms_per_payload,
        )
        if args.summary_json is not None:
            args.summary_json.write_text(
                json.dumps(summary_payload, indent=2, ensure_ascii=False) + "\n"
            )
        if not args.no_export and args.lean_cert_out is not None:
            if len(payloads) == 1:
                upgraded = upgrade_certificate(
                    cert=payloads[0][1],
                    proved_atoms=proved_per_payload[0],
                    failed_atoms=proved_per_payload[0],
                    lean_version=args.lean_version,
                    atom_metadata=metadata_per_payload[0],
                    harness_contract=harness_contract,
                )
                args.lean_cert_out.parent.mkdir(parents=True, exist_ok=True)
                args.lean_cert_out.write_text(
                    json.dumps(upgraded, indent=2, ensure_ascii=False) + "\n"
                )
                print(f"wrote {args.lean_cert_out}")
            else:
                out_dir = args.lean_cert_out
                out_dir.mkdir(parents=True, exist_ok=True)
                for (src_path, payload), proved, metadata in zip(
                    payloads,
                    proved_per_payload,
                    metadata_per_payload,
                ):
                    upgraded = upgrade_certificate(
                        cert=payload,
                        proved_atoms=proved,
                        failed_atoms=proved,
                        lean_version=args.lean_version,
                        atom_metadata=metadata,
                        harness_contract=harness_contract,
                    )
                    target = out_dir / src_path.name
                    target.write_text(
                        json.dumps(upgraded, indent=2, ensure_ascii=False) + "\n"
                    )
                    print(f"wrote {target}")
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
        if args.no_export:
            return 0
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
    if rc != 0:
        print("--- lake build log tail ---", file=sys.stderr)
        print("\n".join(build_log.splitlines()[-80:]), file=sys.stderr)
        print("--- end lake build log tail ---", file=sys.stderr)
    known_witness_proved: set[AtomKey] = set(
        _verify_known_witnesses(
            all_candidate_atoms,
            args.repo_dir,
            args.out_dir,
        )
        if rc != 0 and not lake_missing
        else []
    )
    if known_witness_proved:
        for index, atoms in enumerate(atoms_per_payload):
            existing = set(proved_per_payload[index])
            for name in _known_witness_names(atoms, known_witness_proved):
                if name not in existing:
                    proved_per_payload[index].append(name)
                    existing.add(name)

    # 3. Export per-input certificate.
    if not args.no_export and args.lean_cert_out is None:
        parser.error("--lean-cert-out is required unless --no-export is set")

    attributions = _failed_theorem_attributions(build_log, source_root=args.repo_dir)
    # If the build log has a failure we couldn't attribute to a
    # specific theorem (e.g. a file-level ``import`` error), we cannot
    # safely tell which atoms succeeded — fall back to the same
    # conservative behaviour as ``lake_missing``.
    unattributable = (not lake_missing) and _has_unattributable_failures(
        build_log,
        source_root=args.repo_dir,
    )
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
        per_payload_failed: List[List[str]] = []
        for atoms, proved in zip(atoms_per_payload, proved_per_payload):
            local_known = set(_known_witness_names(atoms, known_witness_proved))
            per_payload_failed.append(sorted(set(proved) - local_known))
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
        for atoms, proved, files in zip(
            atoms_per_payload,
            proved_per_payload,
            payload_files,
        ):
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
            local_known = set(_known_witness_names(atoms, known_witness_proved))
            local -= local_known
            per_payload_failed.append(sorted(local))

    metadata_per_payload = [
        _metadata_for_atoms(
            atoms,
            args.out_dir,
            args.module_prefix,
            proved,
            failed,
            harness_stage,
            known_witness_proved,
        )
        for atoms, proved, failed in zip(
            atoms_per_payload,
            proved_per_payload,
            per_payload_failed,
        )
    ]
    summary_payload["metrics"] = _aggregate_metrics(
        metadata_per_payload,
        atoms_per_payload,
    )
    if args.summary_json is not None:
        args.summary_json.write_text(
            json.dumps(summary_payload, indent=2, ensure_ascii=False) + "\n"
        )

    if args.no_export:
        return rc

    if len(payloads) == 1:
        upgraded = upgrade_certificate(
            cert=payloads[0][1],
            proved_atoms=proved_per_payload[0],
            failed_atoms=per_payload_failed[0],
            lean_version=args.lean_version,
            atom_metadata=metadata_per_payload[0],
            harness_contract=harness_contract,
        )
        args.lean_cert_out.parent.mkdir(parents=True, exist_ok=True)
        args.lean_cert_out.write_text(
            json.dumps(upgraded, indent=2, ensure_ascii=False) + "\n"
        )
        print(f"wrote {args.lean_cert_out}")
        return 0 if rc == 0 or not any(per_payload_failed) else rc

    # Multi-input mode: write one .lean-cert.json per input alongside
    # ``args.lean_cert_out`` interpreted as a directory.
    out_dir = args.lean_cert_out
    out_dir.mkdir(parents=True, exist_ok=True)
    for (src_path, payload), proved, failed, metadata in zip(
        payloads,
        proved_per_payload,
        per_payload_failed,
        metadata_per_payload,
    ):
        upgraded = upgrade_certificate(
            cert=payload,
            proved_atoms=proved,
            failed_atoms=failed,
            lean_version=args.lean_version,
            atom_metadata=metadata,
            harness_contract=harness_contract,
        )
        target = out_dir / src_path.name
        target.write_text(json.dumps(upgraded, indent=2, ensure_ascii=False) + "\n")
        print(f"wrote {target}")
    return 0 if rc == 0 or not any(per_payload_failed) else rc


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
