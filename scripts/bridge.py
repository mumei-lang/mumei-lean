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
import time
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

try:
    from .proofcert import Z3CheckResult
    from .ingest_cert import (
        IngestedAtom,
        collect_unknown_atoms,
        module_to_path,
        write_modules,
    )
    from .export_cert import (
        build_failure_report,
        _failed_theorem_attributions,
        _has_unattributable_failures,
        _normalise_atom_names,
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
    from .external_proof import (
        AI_GENERATED_PROOF,
        apply_external_proofs,
        load_external_proofs,
    )
    from .known_witnesses import KNOWN_LEAN_WITNESSES
    from .bridge_scan import (
        _is_unknown_lean_candidate,
        _load_cert,
        _scan_unknown_certs,
    )
    from .bridge_strategy import resolve_mathlib_imports, select_proof_strategy
    from .tactic_search import (
        DEFAULT_TACTIC_SEARCH_TIMEOUT_S,
        STAGE_BUILD_FAILURE,
        STAGE_RESIDUAL,
        TacticSearchResult,
        apply_search_result,
        is_search_eligible,
        obligation_class_of,
        search_tactic,
    )
    from .tactic_history import (
        HISTORY_PATH,
        TacticSearchHistory,
        load_history,
        save_history,
    )
    from .bridge_metrics import (
        _aggregate_metrics,
        _empty_metric_bucket,
        _metric_bucket_success_rate,
        _summary_details,
    )
except ImportError:  # pragma: no cover - direct ``python scripts/bridge.py``
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from proofcert import Z3CheckResult  # type: ignore
    from ingest_cert import (  # type: ignore
        IngestedAtom,
        collect_unknown_atoms,
        module_to_path,
        write_modules,
    )
    from export_cert import (  # type: ignore
        build_failure_report,
        _failed_theorem_attributions,
        _has_unattributable_failures,
        _normalise_atom_names,
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
    from external_proof import (  # type: ignore
        AI_GENERATED_PROOF,
        apply_external_proofs,
        load_external_proofs,
    )
    from known_witnesses import KNOWN_LEAN_WITNESSES  # type: ignore
    from bridge_scan import (  # type: ignore
        _is_unknown_lean_candidate,
        _load_cert,
        _scan_unknown_certs,
    )
    from bridge_strategy import (  # type: ignore
        resolve_mathlib_imports,
        select_proof_strategy,
    )
    from tactic_search import (  # type: ignore
        DEFAULT_TACTIC_SEARCH_TIMEOUT_S,
        STAGE_BUILD_FAILURE,
        STAGE_RESIDUAL,
        TacticSearchResult,
        apply_search_result,
        is_search_eligible,
        obligation_class_of,
        search_tactic,
    )
    from tactic_history import (  # type: ignore
        HISTORY_PATH,
        TacticSearchHistory,
        load_history,
        save_history,
    )
    from bridge_metrics import (  # type: ignore
        _aggregate_metrics,
        _empty_metric_bucket,
        _metric_bucket_success_rate,
        _summary_details,
    )

AtomKey = Tuple[str, str]


def _candidate_metadata(
    atom: IngestedAtom,
    out_dir: Path,
    module_prefix: str,
    status: str,
    harness_stage: Optional[dict] = None,
    known_witness_used: bool = False,
    lean_solver_time_s: Optional[float] = None,
    tactic_search: Optional[dict] = None,
    build_failures: Optional[List[dict]] = None,
) -> dict:
    rel = module_to_path(atom.module_key, module_prefix)
    lean_module = ".".join(rel.with_suffix("").parts)
    lean_theorem_name = f"{lean_module}.{atom.name}_correct"
    diagnostics: List[str] = []
    if atom.escalation_reason:
        diagnostics.append(f"escalation_reason={atom.escalation_reason}")
    if atom.logic_fragment_tags:
        diagnostics.append(
            "logic_fragments=" + ",".join(sorted(atom.logic_fragment_tags))
        )
    if atom.logic_fragment_tag:
        diagnostics.append(f"logic_fragment_tag={atom.logic_fragment_tag}")
    if atom.is_partial_translation:
        diagnostics.append("partial_translation")
    if atom.manual_lemma_reason:
        diagnostics.append(f"manual_lemma_reason={atom.manual_lemma_reason}")
    if tactic_search is not None:
        adopted = tactic_search.get("adopted_tactic")
        diagnostics.append(
            f"tactic_search_adopted={adopted}"
            if adopted
            else "tactic_search_exhausted"
        )
    if atom.external_proof is not None:
        diagnostics.append(f"external_proof_source={atom.external_proof.source}")
    if atom.external_proof_rejection is not None:
        diagnostics.append(
            f"external_proof_rejected={atom.external_proof_rejection}"
        )
    heatmap_data = _load_solver_heatmap(atom, out_dir)
    if heatmap_data is not None:
        diagnostics.append("solver_heatmap_available=true")
        diagnostics.append(
            "top_constraints="
            + _format_top_constraints(heatmap_data.get("constraints", []), 3)
        )
    proof_strategy = select_proof_strategy(atom)
    mathlib_imports = resolve_mathlib_imports(atom)
    manual_reason = atom.manual_lemma_reason if not getattr(atom, "has_custom_bridge_proof", False) else None
    external_proof_meta: Optional[dict] = None
    if atom.external_proof is not None:
        external_proof_meta = atom.external_proof.provenance()
    elif atom.external_proof_rejection is not None:
        external_proof_meta = {"rejected": atom.external_proof_rejection}
    if (
        atom.proof_body_override is not None
        and manual_reason is not None
        and status == LEAN_VERIFIED
    ):
        # The automatic tactic search (spec §12.4) or an external proof
        # (spec §13) discharged the obligation the template catalog could
        # not: keep the reason as provenance instead of a promotion-blocking
        # field.
        if atom.external_proof is not None and external_proof_meta is not None:
            external_proof_meta["supersedes_manual_lemma_reason"] = manual_reason
        elif tactic_search is not None:
            tactic_search = {
                **tactic_search,
                "supersedes_manual_lemma_reason": manual_reason,
            }
        manual_reason = None
    metadata = {
        "status": status,
        "theorem_name": f"{atom.name}_correct",
        "lean_module": lean_module,
        "lean_theorem_name": lean_theorem_name,
        "translator_version": TRANSLATOR_VERSION,
        "bridge_lemma_hash": BRIDGE_LEMMA_HASH,
        "proof_path": str((out_dir / rel).as_posix()),
        "diagnostics": diagnostics,
        "escalation_reason": atom.escalation_reason,
        "logic_fragment_tag": atom.logic_fragment_tag,
        "logic_fragment_tags": atom.logic_fragment_tags,
        "z3_result_class": atom.z3_result_class,
        "translator_ir": atom.translator_ir,
        "manual_lemma_reason": manual_reason,
        "proof_strategy": proof_strategy,
        "mathlib_imports": mathlib_imports,
        "known_witness_used": known_witness_used,
        "lean_solver_time_s": lean_solver_time_s,
    }
    if tactic_search is not None:
        metadata["tactic_search"] = tactic_search
    if build_failures:
        metadata["build_failures"] = [dict(entry) for entry in build_failures]
        for kind in sorted({entry["kind"] for entry in build_failures}):
            diagnostics.append(f"build_failure={kind}")
    if external_proof_meta is not None:
        # ``ai_proof_used`` is the provenance key mumei-agent already writes;
        # it is only true once the real build promoted the atom.
        metadata["external_proof"] = external_proof_meta
        metadata["ai_proof_used"] = bool(
            atom.external_proof is not None
            and atom.external_proof.source == AI_GENERATED_PROOF
            and status == LEAN_VERIFIED
        )
        if (
            atom.external_proof is not None
            and atom.external_proof.attempts is not None
        ):
            metadata["ai_proof_attempts"] = atom.external_proof.attempts
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
    if getattr(atom, "has_custom_bridge_proof", False):
        return False
    body_partial = (
        atom.body_translation is not None and atom.body_translation.is_partial
    )
    return (
        atom.requires_translation.is_partial
        or atom.ensures_translation.is_partial
        or body_partial
    )


def _atom_key(atom: IngestedAtom) -> AtomKey:
    return (atom.module_key, atom.name)


def _known_witness_names(
    atoms: List[IngestedAtom],
    known_witness_proved: Set[AtomKey],
) -> Set[str]:
    return {
        atom.name
        for atom in atoms
        if _atom_key(atom) in known_witness_proved
    }


def _candidate_status(
    atom: IngestedAtom,
    proved: List[str],
    failed: List[str],
    *,
    known_witness_proved: Optional[Set[AtomKey]] = None,
) -> str:
    proved_set = _normalise_atom_names(proved)
    failed_set = _normalise_atom_names(failed)
    if (
        known_witness_proved is not None
        and _atom_key(atom) in known_witness_proved
        and atom.name in proved_set
        and atom.name not in failed_set
    ):
        return LEAN_VERIFIED
    if _has_structural_partial_translation(atom):
        return "partial_translation"
    if (
        atom.manual_lemma_reason
        and not getattr(atom, "has_custom_bridge_proof", False)
        and atom.proof_body_override is None
    ):
        return MANUAL_LEMMA_REQUIRED
    if (
        atom.translator_version != TRANSLATOR_VERSION
        or atom.bridge_lemma_hash != BRIDGE_LEMMA_HASH
    ):
        return "stale_translator"
    if atom.name in proved_set and atom.name not in failed_set:
        return LEAN_VERIFIED
    return MANUAL_LEMMA_REQUIRED


def _metadata_for_atoms(
    atoms: List[IngestedAtom],
    out_dir: Path,
    module_prefix: str,
    proved: List[str],
    failed: List[str],
    harness_stage: Optional[dict] = None,
    known_witness_proved: Optional[Set[AtomKey]] = None,
    lean_solver_time_s: Optional[float] = None,
    tactic_search_results: Optional[Dict[AtomKey, TacticSearchResult]] = None,
    build_failures: Optional[List[dict]] = None,
) -> Dict[str, dict]:
    metadata_by_atom: Dict[str, dict] = {}
    known_witness_proved = known_witness_proved or set()
    tactic_search_results = tactic_search_results or {}
    failed_names = set(failed)
    for atom in atoms:
        atom_failures = [
            entry
            for entry in (build_failures or [])
            if entry["atom"] == atom.name and atom.name in failed_names
        ]
        search_result = tactic_search_results.get(_atom_key(atom))
        atom_solver_time = lean_solver_time_s
        if search_result is not None and atom_solver_time is not None:
            atom_solver_time = round(
                atom_solver_time + search_result.search_time_s, 3
            )
        metadata = _candidate_metadata(
            atom,
            out_dir,
            module_prefix,
            _candidate_status(atom, proved, failed, known_witness_proved=known_witness_proved),
            harness_stage,
            _atom_key(atom) in known_witness_proved,
            atom_solver_time,
            search_result.as_metadata() if search_result is not None else None,
            atom_failures,
        )
        if _atom_key(atom) in known_witness_proved:
            metadata = _known_witness_metadata(atom, metadata, harness_stage)
        metadata_by_atom[atom.name] = metadata
    return metadata_by_atom


def _known_witness_metadata(
    atom: IngestedAtom,
    metadata: dict,
    harness_stage: Optional[dict],
) -> dict:
    witness = KNOWN_LEAN_WITNESSES.get(atom.name)
    if witness is None:
        return metadata
    metadata = dict(metadata)
    diagnostics = list(metadata.get("diagnostics", []))
    diagnostics.append("known_witness_module")
    metadata["diagnostics"] = diagnostics
    metadata["theorem_name"] = witness["theorem"]
    metadata["lean_theorem_name"] = witness["theorem"]
    metadata["lean_module"] = witness["module"]
    metadata["known_witness_used"] = True
    metadata["proof_path"] = _module_source_path(
        Path("."),
        witness["module"],
    ).as_posix()
    metadata["proof_strategy"] = {
        "strategy": "known_witness_module",
        "module": witness["module"],
        "theorem": witness["theorem"],
    }
    if harness_stage is not None:
        metadata["harness"] = {
            **harness_stage,
            "verifier_gate": (
                "known hand-written Lean witness module builds successfully."
            ),
            "failure_taxonomy": bridge_failure_taxonomy(LEAN_VERIFIED, diagnostics),
        }
    return metadata


def _remove_stale_generated_modules(
    *,
    out_dir: Path,
    module_prefix: str,
    generated_atoms: List[IngestedAtom],
) -> None:
    """Prune stale files only inside the bridge-generated module tree."""
    generated_module_paths = {
        module_to_path(atom.module_key, module_prefix) for atom in generated_atoms
    }
    target_root = out_dir / module_prefix
    if not target_root.exists():
        return
    for source in target_root.rglob("*.lean"):
        rel = source.relative_to(out_dir)
        if rel not in generated_module_paths:
            source.unlink()


def _mirror_generated_modules(out_dir: Path, repo_dir: Path, module_prefix: str) -> None:
    source_root = out_dir / module_prefix
    target_root = repo_dir / "generated" / module_prefix
    if not source_root.exists():
        return
    for source in source_root.rglob("*.lean"):
        rel = source.relative_to(source_root)
        target = target_root / rel
        if source.resolve() == target.resolve():
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)


def _run_lake_build(repo_dir: Path, log_path: Path) -> Tuple[int, Optional[float]]:
    """Run ``lake build`` and capture its combined output to ``log_path``.

    Returns the process exit code plus the wall-clock seconds the build
    took (``None`` when no build ran). The exit code is ``127`` when
    ``lake`` is not on ``$PATH`` so callers can distinguish "Lean
    toolchain missing" from "build failed".
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
        return 127, None
    started = time.monotonic()
    proc = subprocess.run(  # noqa: S603 - explicit lake invocation
        cmd,
        cwd=repo_dir,
        capture_output=True,
        text=True,
    )
    elapsed = time.monotonic() - started
    log_path.write_text(proc.stdout + proc.stderr)
    return proc.returncode, round(elapsed, 3)


def _module_source_path(repo_dir: Path, module: str) -> Path:
    return repo_dir / (module.replace(".", "/") + ".lean")


def _lake_command_prefix(repo_dir: Path) -> Optional[List[str]]:
    """Command prefix that runs ``lake`` under the pinned toolchain."""
    lake = shutil.which("lake")
    elan = shutil.which("elan")
    toolchain_path = repo_dir / "lean-toolchain"
    if elan is not None and toolchain_path.exists():
        toolchain = toolchain_path.read_text().strip()
        if toolchain:
            return [elan, "run", toolchain, "lake"]
    if lake is not None:
        return ["lake"]
    return None


def _run_tactic_search_stage(
    atoms: List[IngestedAtom],
    stage: str,
    *,
    lake_cmd: List[str],
    timeout_s: float,
    results: Dict[AtomKey, TacticSearchResult],
    repo_dir: Path,
    history: Optional[TacticSearchHistory] = None,
    history_path: Optional[Path] = None,
) -> int:
    """Search the tactic ladder for every eligible atom in ``atoms``.

    Adopted tactics are written onto the atoms in place; the number of
    adoptions is returned so callers know whether a rebuild is worthwhile.
    """
    adopted = 0
    for atom in atoms:
        if not is_search_eligible(atom, stage):
            continue
        result = search_tactic(
            atom,
            stage=stage,
            lake_cmd=lake_cmd,
            timeout_s=timeout_s,
            probe_dir=repo_dir / ".tactic_search",
            history=history,
        )
        if result.skipped_reason is not None:
            continue
        # Announced from the first obligation the artifact actually reordered,
        # so the log never claims a ranking that did not happen (spec §12.4).
        if result.history_ranked and not any(
            other.history_ranked for other in results.values()
        ):
            print(
                f"tactic search ladder ranked by {history_path or HISTORY_PATH} "
                f"(fingerprint {result.history_fingerprint})"
            )
        results[_atom_key(atom)] = result
        apply_search_result(atom, result)
        if result.adopted_tactic is not None:
            adopted += 1
            print(
                f"tactic search ({stage}) adopted `{result.adopted_tactic}` for "
                f"atom {atom.name} in {result.search_time_s:.3f}s"
            )
        else:
            print(
                f"tactic search ({stage}) exhausted "
                f"{len(result.candidates_tried)} candidate(s) for atom "
                f"{atom.name}"
                + (" (timed out)" if result.timed_out else "")
            )
    return adopted


def _record_tactic_search_history(
    *,
    history_path: Path,
    atoms_per_payload: List[List[IngestedAtom]],
    failed_per_payload: List[List[str]],
    results: Dict[AtomKey, TacticSearchResult],
) -> None:
    """Persist the adopted tactics that actually built (spec §12.5).

    Only adoptions whose regenerated theorem passed ``lake build`` are learned,
    so the artifact never biases the ladder towards a tactic that merely
    type-checked in the probe. The artifact is re-read here and this run's
    successes are merged into it, so recording never drops earlier entries --
    including when the run probed the declared order via
    ``--no-tactic-search-history``.
    """
    history = load_history(history_path)
    recorded = 0
    for atoms, failed in zip(atoms_per_payload, failed_per_payload):
        failed_names = set(failed)
        for atom in atoms:
            result = results.get(_atom_key(atom))
            if result is None or result.adopted_tactic is None:
                continue
            if atom.name in failed_names:
                continue
            history.record_success(
                obligation_class=obligation_class_of(atom),
                stage=result.stage,
                candidate=result.adopted_tactic,
            )
            recorded += 1
    if recorded:
        save_history(history, history_path)
        print(
            f"recorded {recorded} tactic search success(es) in {history_path} "
            f"(fingerprint {history.fingerprint})"
        )


def _attribute_failures(
    *,
    build_log: str,
    rc: int,
    lake_missing: bool,
    atoms_per_payload: List[List[IngestedAtom]],
    proved_per_payload: List[List[str]],
    known_witness_proved: Set[AtomKey],
    out_dir: Path,
    module_prefix: str,
    repo_dir: Path,
    verbose: bool = True,
) -> List[List[str]]:
    """Map a ``lake build`` log onto per-payload failed atom names."""
    attributions = _failed_theorem_attributions(build_log, source_root=repo_dir)
    # If the build log has a failure we couldn't attribute to a
    # specific theorem (e.g. a file-level ``import`` error), we cannot
    # safely tell which atoms succeeded — fall back to the same
    # conservative behaviour as ``lake_missing``.
    unattributable = (not lake_missing) and _has_unattributable_failures(
        build_log,
        source_root=repo_dir,
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
        if unattributable and verbose:
            print(
                "warning: build log contains failures that could not be "
                "attributed to a specific theorem; treating all lifted "
                "atoms as failed.",
                file=sys.stderr,
            )
        elif unrecognised_failure and verbose:
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
            local_known = _known_witness_names(atoms, known_witness_proved)
            per_payload_failed.append(sorted(set(proved) - local_known))
        return per_payload_failed

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
            rel = module_to_path(atom.module_key, module_prefix)
            files.add(str((out_dir / rel).as_posix()))
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
        local_known = _known_witness_names(atoms, known_witness_proved)
        local -= local_known
        per_payload_failed.append(sorted(local))
    return per_payload_failed


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
        "--no-tactic-search",
        action="store_true",
        help="Disable the automatic tactic search for residual obligations "
        "(docs/LEAN_TRANSLATOR_SPEC.md §12).",
    )
    parser.add_argument(
        "--tactic-search-history",
        type=Path,
        default=HISTORY_PATH,
        metavar="PATH",
        help="Pinned artifact whose recorded successes deterministically "
        "re-rank the tactic search ladder (docs/LEAN_TRANSLATOR_SPEC.md §12.5).",
    )
    parser.add_argument(
        "--no-tactic-search-history",
        action="store_true",
        help="Probe the declared ladder order, ignoring the learned ranking.",
    )
    parser.add_argument(
        "--record-tactic-search-history",
        action="store_true",
        help="Write this run's adopted tactics back into the pinned history "
        "artifact so the next run probes them first.",
    )
    parser.add_argument(
        "--tactic-search-timeout",
        type=float,
        default=DEFAULT_TACTIC_SEARCH_TIMEOUT_S,
        metavar="SECONDS",
        help="Per-obligation wall-clock budget for the automatic tactic "
        f"search (default: {DEFAULT_TACTIC_SEARCH_TIMEOUT_S:.0f}s).",
    )
    parser.add_argument(
        "--failure-report",
        type=Path,
        default=None,
        metavar="PATH",
        help="Where to write the structured per-atom build failure JSON "
        "(default: <out-dir>/lake_build_failures.json).",
    )
    parser.add_argument(
        "--external-proofs",
        type=Path,
        default=None,
        metavar="PATH",
        help="JSON file of caller-supplied tactic scripts / witness lemmas "
        "(e.g. mumei-agent AI proofs) injected as proof bodies of the "
        "regenerated statements (docs/LEAN_TRANSLATOR_SPEC.md §13). "
        "Promotion still requires `lake build` and the export gates.",
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
                            "details": [],
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
    proof_atoms_per_payload: List[List[IngestedAtom]] = []
    # Collect all atoms across payloads first, then call ``write_modules``
    # once. ``write_modules`` writes one Lean file per module key and
    # would silently overwrite earlier payloads if two payloads
    # produced atoms whose module keys collide after sanitisation
    # (e.g. ``math.mm`` vs ``Math.mm`` → ``Generated.Math``).
    all_candidate_atoms: List[IngestedAtom] = []
    tactic_search_results: Dict[AtomKey, TacticSearchResult] = {}
    lake_cmd = _lake_command_prefix(args.repo_dir)
    tactic_search_enabled = (
        not args.no_tactic_search and not args.no_build and lake_cmd is not None
    )
    # Learned candidate order (spec §12.5): a pinned artifact, so the ranking
    # is reproducible from the checkout alone.
    tactic_search_history = (
        TacticSearchHistory()
        if args.no_tactic_search_history
        else load_history(args.tactic_search_history)
    )
    external_proofs = (
        load_external_proofs(args.external_proofs)
        if args.external_proofs is not None
        else []
    )
    for src_path, payload in payloads:
        atoms = collect_unknown_atoms(payload)
        if external_proofs:
            rejections = apply_external_proofs(atoms, external_proofs)
            for name, reason in sorted(rejections.items()):
                print(
                    f"warning: external proof for atom {name} rejected: {reason}",
                    file=sys.stderr,
                )
            for atom in atoms:
                if atom.external_proof is not None:
                    print(
                        f"external proof ({atom.external_proof.source}) injected "
                        f"for atom {atom.name}"
                    )
        if tactic_search_enabled:
            # Stage ``residual``: obligations the template catalog left with a
            # ``manual_lemma_reason`` are probed before they are emitted, so an
            # adopted tactic makes them ordinary generated theorems.
            _run_tactic_search_stage(
                atoms,
                STAGE_RESIDUAL,
                lake_cmd=lake_cmd,
                timeout_s=args.tactic_search_timeout,
                results=tactic_search_results,
                repo_dir=args.repo_dir,
                history=tactic_search_history,
                history_path=args.tactic_search_history,
            )
        proof_atoms = [atom for atom in atoms if not atom.is_partial_translation]
        all_candidate_atoms.extend(atoms)
        proof_atoms_per_payload.append(proof_atoms)
        atoms_per_payload.append(atoms)
        partial_count = len(atoms) - len(proof_atoms)
        print(
            f"ingested {len(atoms):3d} Lean candidate(s) from {src_path} "
            f"({partial_count} partial translation)"
        )

    known_witness_proved: Set[AtomKey] = set()

    all_atoms: List[IngestedAtom] = []
    for atoms, proof_atoms in zip(atoms_per_payload, proof_atoms_per_payload):
        local_proved: List[str] = []
        for atom in proof_atoms:
            all_atoms.append(atom)
            local_proved.append(atom.name)
        for name in _known_witness_names(atoms, known_witness_proved):
            if name not in local_proved:
                local_proved.append(name)
        proved_per_payload.append(local_proved)

    _remove_stale_generated_modules(
        out_dir=args.out_dir,
        module_prefix=args.module_prefix,
        generated_atoms=all_atoms,
    )
    write_modules(all_atoms, args.out_dir, args.module_prefix)
    _mirror_generated_modules(args.out_dir, args.repo_dir, args.module_prefix)
    _remove_stale_generated_modules(
        out_dir=args.repo_dir / "generated",
        module_prefix=args.module_prefix,
        generated_atoms=all_atoms,
    )

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
        "lean_fallback": {
            "attempted": len(all_candidate_atoms),
            "proved": 0,
            "known_witness_used": len(known_witness_proved),
            "lean_solver_time_s": None,
        },
        "details": [],
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
                known_witness_proved=set(),
            )
            for atoms, proved in zip(atoms_per_payload, proved_per_payload)
        ]
        summary_payload["metrics"] = _aggregate_metrics(
            metadata_per_payload,
            atoms_per_payload,
        )
        summary_payload["lean_fallback"]["proved"] = summary_payload["metrics"]["lean_successes"]
        summary_payload["details"] = _summary_details(
            payloads,
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
                    known_witness_override=_known_witness_names(
                        atoms_per_payload[0],
                        known_witness_proved,
                    ),
                )
                args.lean_cert_out.parent.mkdir(parents=True, exist_ok=True)
                args.lean_cert_out.write_text(
                    json.dumps(upgraded, indent=2, ensure_ascii=False) + "\n"
                )
                print(f"wrote {args.lean_cert_out}")
            else:
                out_dir = args.lean_cert_out
                out_dir.mkdir(parents=True, exist_ok=True)
                for (src_path, payload), proved, metadata, atoms in zip(
                    payloads,
                    proved_per_payload,
                    metadata_per_payload,
                    atoms_per_payload,
                ):
                    upgraded = upgrade_certificate(
                        cert=payload,
                        proved_atoms=proved,
                        failed_atoms=proved,
                        lean_version=args.lean_version,
                        atom_metadata=metadata,
                        harness_contract=harness_contract,
                        known_witness_override=_known_witness_names(
                            atoms,
                            known_witness_proved,
                        ),
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
    lean_solver_time_s: Optional[float] = None
    if not all_atoms and known_witness_proved:
        rc = 0
        log_path.write_text(
            "skipped generated lake build: all lifted atoms were discharged "
            "by known hand-written Lean witnesses\n"
        )
        print(
            "known hand-written Lean witnesses discharged all generated "
            f"candidate(s); log: {log_path}"
        )
    else:
        rc, lean_solver_time_s = _run_lake_build(args.repo_dir, log_path)
    summary_payload["lean_fallback"]["lean_solver_time_s"] = lean_solver_time_s
    lake_missing = rc == 127
    if lake_missing:
        print(
            "warning: `lake` is not installed; skipping build. "
            "Install Lean 4 / Lake to enable end-to-end verification.",
            file=sys.stderr,
        )
        if args.no_export:
            return 0

    # Stage ``build_failure``: obligations whose generic-fallback proof did not
    # build are probed for a tactic that closes them, then rebuilt once.
    if tactic_search_enabled and rc != 0 and not lake_missing:
        preliminary_failed = _attribute_failures(
            build_log=log_path.read_text(),
            rc=rc,
            lake_missing=lake_missing,
            atoms_per_payload=atoms_per_payload,
            proved_per_payload=proved_per_payload,
            known_witness_proved=known_witness_proved,
            out_dir=args.out_dir,
            module_prefix=args.module_prefix,
            repo_dir=args.repo_dir,
            verbose=False,
        )
        retry_atoms: List[IngestedAtom] = []
        for atoms, failed in zip(atoms_per_payload, preliminary_failed):
            failed_names = set(failed)
            retry_atoms.extend(
                atom for atom in atoms if atom.name in failed_names
            )
        adopted = _run_tactic_search_stage(
            retry_atoms,
            STAGE_BUILD_FAILURE,
            lake_cmd=lake_cmd,
            timeout_s=args.tactic_search_timeout,
            results=tactic_search_results,
            repo_dir=args.repo_dir,
            history=tactic_search_history,
            history_path=args.tactic_search_history,
        )
        if adopted:
            write_modules(all_atoms, args.out_dir, args.module_prefix)
            _mirror_generated_modules(
                args.out_dir,
                args.repo_dir,
                args.module_prefix,
            )
            rc, retry_time = _run_lake_build(args.repo_dir, log_path)
            if retry_time is not None:
                lean_solver_time_s = round(
                    (lean_solver_time_s or 0.0) + retry_time,
                    3,
                )
                summary_payload["lean_fallback"][
                    "lean_solver_time_s"
                ] = lean_solver_time_s
            lake_missing = rc == 127
            print(
                f"`lake build` after tactic search exited with status {rc}; "
                f"log: {log_path}"
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
    if rc != 0:
        print("--- lake build log tail ---", file=sys.stderr)
        print("\n".join(build_log.splitlines()[-80:]), file=sys.stderr)
        print("--- end lake build log tail ---", file=sys.stderr)
    if rc != 0 and not lake_missing:
        known_witness_proved.update(
            _verify_known_witnesses(
                all_candidate_atoms,
                args.repo_dir,
                args.out_dir,
            )
        )
    # Inject canonical known-witness names into ``proved_per_payload`` so
    # that downstream ``upgrade_certificate()`` and ``_candidate_status()``
    # see them as proved atoms (the meaning of ``proved_per_payload`` is
    # now "atoms emitted to Generated/*.lean + canonical known witnesses").
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

    per_payload_failed = _attribute_failures(
        build_log=build_log,
        rc=rc,
        lake_missing=lake_missing,
        atoms_per_payload=atoms_per_payload,
        proved_per_payload=proved_per_payload,
        known_witness_proved=known_witness_proved,
        out_dir=args.out_dir,
        module_prefix=args.module_prefix,
        repo_dir=args.repo_dir,
    )

    failure_report = build_failure_report(build_log, source_root=args.repo_dir)
    failure_report_path = args.failure_report or (args.out_dir / "lake_build_failures.json")
    failure_report_path.parent.mkdir(parents=True, exist_ok=True)
    failure_report_path.write_text(
        json.dumps(failure_report, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    )
    if failure_report["failures"] or failure_report["unattributed"]:
        print(f"wrote structured build failures to {failure_report_path}")

    if args.record_tactic_search_history:
        _record_tactic_search_history(
            history_path=args.tactic_search_history,
            atoms_per_payload=atoms_per_payload,
            failed_per_payload=per_payload_failed,
            results=tactic_search_results,
        )

    metadata_per_payload = [
        _metadata_for_atoms(
            atoms,
            args.out_dir,
            args.module_prefix,
            proved,
            failed,
            harness_stage,
            known_witness_proved,
            lean_solver_time_s,
            tactic_search_results,
            failure_report["failures"],
        )
        for atoms, proved, failed in zip(
            atoms_per_payload,
            proved_per_payload,
            per_payload_failed,
        )
    ]
    if lean_solver_time_s is not None:
        print(f"lean escalation took {lean_solver_time_s:.3f}s")
    summary_payload["metrics"] = _aggregate_metrics(
        metadata_per_payload,
        atoms_per_payload,
    )
    summary_payload["lean_fallback"]["proved"] = summary_payload["metrics"]["lean_successes"]
    summary_payload["lean_fallback"]["known_witness_used"] = len(known_witness_proved)
    summary_payload["details"] = _summary_details(
        payloads,
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
            known_witness_override=_known_witness_names(
                atoms_per_payload[0],
                known_witness_proved,
            ),
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
    for (src_path, payload), proved, failed, metadata, atoms in zip(
        payloads,
        proved_per_payload,
        per_payload_failed,
        metadata_per_payload,
        atoms_per_payload,
    ):
        upgraded = upgrade_certificate(
            cert=payload,
            proved_atoms=proved,
            failed_atoms=failed,
            lean_version=args.lean_version,
            atom_metadata=metadata,
            harness_contract=harness_contract,
            known_witness_override=_known_witness_names(
                atoms,
                known_witness_proved,
            ),
        )
        target = out_dir / src_path.name
        target.write_text(json.dumps(upgraded, indent=2, ensure_ascii=False) + "\n")
        print(f"wrote {target}")
    return 0 if rc == 0 or not any(per_payload_failed) else rc


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
