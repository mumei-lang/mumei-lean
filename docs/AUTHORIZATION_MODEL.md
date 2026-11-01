# Single-record authorization model

This is a limited model for evaluating record access with explicit authority.
The existing `SmartContract` access trace checks the order of `authCheck` and
`stateWrite`; it does not bind a particular principal to a particular record.
`MumeiLean.AuthorizationModel` addresses that separate question without
changing the trace model, its extractor, or any certificate acceptance path.

## Requirements and choices

The model follows a single-record request through a current-state decision and
an update. It is deliberately not an application framework or a policy language.

| Requirement | Model choice |
| --- | --- |
| Identify the actor independently of the proposal | `Principal` has organization, user and role; `Proposal` has only target, expected version and operation |
| Never cross an organization boundary | All accepted reads and updates require equal principal/record organizations, including administrators |
| Make update authority explicit | Writers update their own records; administrators update records in the same organization; readers and unknown roles cannot update |
| Limit the change surface | Only the value field can be updated; organization, owner, version and unknown fields are rejected |
| Fail closed on missing state | A missing record or missing policy rejects; unknown operations reject |
| Use current permissions | Read/update enable flags are checked in the current policy; the complete policy snapshot, including revision, must still match at commit |
| Bind decision and execution | Principal, complete proposal, complete target record and policy must match the internal snapshot |
| Preserve isolation on failure and success | Rejection leaves state unchanged and returns no value; updates leave other records and identity fields unchanged |
| Reject repeated updates to an old version | Updates increment the version by one, even if the value is unchanged |
| Rule out all-deny implementations | Concrete owner/admin update and read witnesses, plus the decision matrix, must build and pass the axiom audit |

All known roles may read records in their own organization if reads are enabled;
only the record value is returned. A read is repeatable and changes no state.
There is no read-only-public or cross-organization exception. Policy flags can
disable reads and updates independently. There are no grants, delegation,
ownership transfers, list/delete/bulk operations, or external effects.

Identifiers and versions are natural numbers, and values are mathematical
integers. Zero is an ordinary identifier, not an empty-input sentinel. Parsing,
malformed JSON, byte encodings, machine integer limits and authentication are
not represented by these types and require separate adapter validation.

## Model entry points and theorem coverage

`prepare` computes an internal `Snapshot` or rejects. `commit` rechecks the
current state and authorization; it does not trust the existence of a snapshot
as evidence of authority. `execute` composes both on one immutable input state.
The snapshot is a mathematical device for testing mismatches, not a permission
token, cryptographic credential, exported API, or proof of a lock implementation.
Other Lean code can construct values freely: this is not a sandbox.

| Theorems | Scope |
| --- | --- |
| `accepted_authorized`, `accepted_same_organization`, `accepted_update_authority` | Accepted requests use the actual target record and current policy, same organization, allowed operation/field and appropriate role/owner |
| `accepted_read_result`, `accepted_update_result` | Reads return the target value without changing state; accepted updates write the proposed value and increment the target version |
| `rejected_unchanged`, `rejected_commit_unchanged` | Rejection leaves the entire state unchanged and returns no record value |
| `execute_preserves_identity`, `execute_preserves_other_record`, `execute_preserves_policy` | Record existence, organization and ownership are preserved; non-target records and policy are unchanged |
| `stale_record_rejected`, `stale_version_rejected`, `stale_policy_rejected` | A snapshot cannot commit against a different current target record, version, missing policy, or changed policy |
| `changed_principal_rejected`, `changed_proposal_rejected` | A different actor, target, operation, field, value or expected version cannot reuse a snapshot |
| `replayed_update_rejected` | The same proposal cannot succeed twice after an accepted update through `execute` |
| `finite_run_preserves_identity`, `finite_trace_authorized` | For any finite request list, identity separation is preserved and every accepted step is authorized against its own current state |

Finite traces consist of `execute` requests. They do not model out-of-band
record replacement or policy administration. Snapshot matching checks equality
at commit, not the history of changes: replacing a record/policy and restoring
all its old fields is indistinguishable from no change. A future adapter must
own state changes and version/revision management; this model is not a
historical revocation or single-use-token protocol. Reads remain repeatable.

## Reproduce the model check

With the pinned toolchain from `lean-toolchain` installed:

```bash
export PATH="$HOME/.elan/bin:$PATH"
python scripts/check_authorization_model.py
python -m pytest tests/test_authorization_model.py -q
```

The check builds both `MumeiLean.AuthorizationModel` and
`MumeiLean.AuthorizationExamples` in the current run, then applies the existing
`scripts/axiom_audit.py` allowlist to every registered theorem. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. A failed build, missing audit
output, user axiom or `sorryAx` fails the check; an older `.olean` cannot turn a
failed rebuild into success. Build and audit logs, and the existing per-theorem
`axiom_audit.json` result format, are saved under `out/authorization-model/`.
They are independent model evidence, not Mumei proof certificates.

Examples include a 128-decision matrix across four roles, two organizations,
two users, two read-flag values, two update-flag values and two operations
(`4 × 2 × 2 × 2 × 2 × 2 = 128`), plus focused success, stale state, protected field,
changed request, replay, missing state and mixed-trace checks. They use
kernel-checked `decide`, not `native_decide`. The live Python regressions also
inject a user axiom, `sorry`, and a failed rebuild after a successful build;
each must fail the same gate. The dedicated CI job has no best-effort fallback
and retains diagnostics even on failure. Making it a branch-protection required
check remains a repository setting, not something the workflow changes.

## Evidence and remaining trust boundary

- **Proved:** the statements above for these Lean definitions and operations.
- **Finite checks:** the concrete example matrix and gate regression tests;
  not a proof about a Python implementation.
- **Declared assumptions:** principal information, initial records and policy
  are supplied by a trusted caller; this fixed role policy is the intended
  requirement; Lean's kernel and the standard axiom allowlist are accepted.
- **Unverified connection:** no extraction/lowering or semantic correspondence
  connects this model to arbitrary `.mm`, Python, deployed artifacts or a
  concurrent host runtime. A future single-process adapter needs separate
  implementation tests and must keep this gap visible.
- **Out of scope:** HTTP, production databases, external authentication,
  cryptography, distributed transactions, policy administration, dynamic grants
  or revocation, arbitrary-code confinement and deployment safety.

No theorem here promotes an atom to `lean_verified` or G5. The translator,
known-witness registry, hashes, certificate schemas and existing CLI/MCP
contracts are unchanged. The next step is a separate, data-only execution
adapter in `mumei-demo`, followed by scenario evidence that keeps model proofs,
local `.mm` contracts and finite implementation observations distinct.
