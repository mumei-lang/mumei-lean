"""Build and axiom-audit the independent record authorization model.

This does not export certificates or promote any Mumei atom.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from axiom_audit import DEFAULT_AXIOM_AUDIT_TIMEOUT_S, run_axiom_audit
from bridge import _rebuild_module_for_audit

THEOREMS = {
    "MumeiLean.AuthorizationModel": """
        commit_accepted_current accepted_authorized accepted_same_organization
        accepted_update_authority rejected_commit_unchanged rejected_unchanged
        stale_record_rejected stale_policy_rejected changed_principal_rejected
        changed_proposal_rejected commit_preserves_identity commit_preserves_other_record
        execute_preserves_identity execute_preserves_other_record accepted_update_result
        accepted_read_result stale_version_rejected replayed_update_rejected
        execute_preserves_policy finite_run_preserves_identity finite_trace_authorized
    """.split(),
    "MumeiLean.AuthorizationExamples": """
        owner_update_succeeds read_succeeds administrator_update_succeeds
        update_changes_value_and_version repeated_update_rejected next_version_succeeds
        read_is_repeatable missing_record_rejected missing_policy_rejected empty_store_rejected
        stale_version_rejected future_version_rejected unknown_operation_rejected
        protected_fields_rejected protected_fields_rejected_for_administrator
        changed_target_rejected changed_value_rejected changed_field_rejected
        changed_operation_rejected changed_principal_rejected changed_record_value_rejected
        changed_record_version_rejected changed_record_organization_rejected
        changed_record_owner_rejected changed_policy_revision_rejected
        disabled_updates_rejected disabled_reads_rejected removed_policy_rejected
        removed_record_rejected unrelated_record_preserved mixed_trace_result decision_matrix
    """.split(),
}


def check(repo: Path, out_dir: Path) -> bool:
    out_dir.mkdir(parents=True, exist_ok=True)
    report_path = out_dir / "axiom_audit.json"
    results = {
        f"{module}.{name}": {"status": "error", "axioms": [], "disallowed": []}
        for module, names in THEOREMS.items()
        for name in names
    }
    report_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    for module, names in THEOREMS.items():
        stem = module.replace(".", "_")
        # A failed current build must never be audited using a previous .olean.
        if not _rebuild_module_for_audit(repo, module, out_dir / f"{stem}.build.log"):
            continue
        theorems = [f"{module}.{name}" for name in names]
        audited = run_axiom_audit(
            repo, [module], theorems, out_dir / f"{stem}.audit.log",
            DEFAULT_AXIOM_AUDIT_TIMEOUT_S,
        )
        for theorem in theorems:
            if theorem in audited:
                results[theorem] = audited[theorem]
    report_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    return bool(results) and all(result["status"] == "passed" for result in results.values())


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=Path("out/authorization-model"))
    args = parser.parse_args(argv)
    passed = check(Path(__file__).resolve().parents[1], args.out_dir.resolve())
    print(f"Independent model build and axiom audit: {'PASS' if passed else 'FAIL'}")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
