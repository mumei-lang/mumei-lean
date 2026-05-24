"""Bridge harness contract metadata shared by bridge and exporter."""
from __future__ import annotations

from typing import Any

BRIDGE_HARNESS_POLICY = "mumei-lean-bridge-harness/v1"


def bridge_harness_contract(
    *,
    input_kind: str,
    build_mode: str,
    module_prefix: str,
    out_dir: str,
    lean_cert_out: str | None,
) -> dict[str, Any]:
    """Return the NLAH-style bridge contract for a bridge invocation."""
    return {
        "policy": BRIDGE_HARNESS_POLICY,
        "input_kind": input_kind,
        "acceptance_path": [
            "collect_unknown_atoms",
            "translate_to_lean",
            "run_lake_build",
            "export_lean_certificate",
        ],
        "build_mode": build_mode,
        "module_prefix": module_prefix,
        "state_paths": {
            "generated_lean_dir": out_dir,
            "lean_cert_out": lean_cert_out,
        },
        "artifact_contracts": [
            "Only atoms with z3_check_result == unknown are lifted into Lean.",
            "Generated Lean theorem paths are recorded per atom in lean_metadata.proof_path.",
            "Lake failures are attributed conservatively; unattributable failures prove no atoms.",
            "Exported certificates preserve original atom hashes and mark only proved atoms as lean_verified.",
        ],
        "verifier_gates": {
            "translator_contract": "translator_version and bridge_lemma_hash must match the current bridge.",
            "lean_build": "lake build exits 0 without sorry or generated theorem errors.",
            "manual_review": "partial translations, stale translator metadata, and manual lemma reasons remain unverified.",
        },
    }


def bridge_stage_metadata(
    *,
    input_kind: str,
    build_mode: str,
    module_prefix: str,
    out_dir: str,
    lean_cert_out: str | None,
) -> dict[str, Any]:
    """Return compact bridge-stage metadata for summaries and atom records."""
    return {
        "harness_policy": BRIDGE_HARNESS_POLICY,
        "harness_stage": "lean_bridge_escalation",
        "input_kind": input_kind,
        "build_mode": build_mode,
        "module_prefix": module_prefix,
        "artifact_contract": [
            str(out_dir),
            str(lean_cert_out) if lean_cert_out is not None else "no-export",
        ],
        "verifier_gate": "translator metadata current and Lean build succeeds for the generated theorem.",
    }


def bridge_failure_taxonomy(status: str, diagnostics: list[str]) -> str:
    """Map bridge candidate status/diagnostics into stable failure classes."""
    if status == "lean_verified":
        return "proved"
    if status == "partial_translation":
        return "partial_translation"
    if status == "stale_translator":
        return "stale_translator"
    if any(item.startswith("manual_lemma_reason=") for item in diagnostics):
        return "manual_lemma_required"
    return "lean_proof_unresolved"
