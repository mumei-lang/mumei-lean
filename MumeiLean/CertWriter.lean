/-!
# MumeiLean.CertWriter

Skeleton placeholder for an in-Lean `.lean-cert.json` writer.

For the initial bridge pipeline, `scripts/export_cert.py` is
responsible for writing mumei-compatible JSON certificates from the
`lake build` output. This module only documents the format and
provides a Lean-side stub so the eventual native path has a stable
home.

The emitted certificate keeps the mumei `ProofCertificate` schema (see
`mumei-lang/mumei` `mumei-core/src/proof_cert.rs`) and only differs in
two fields:

* `z3_check_result` may be `"lean_verified"` for successful Lean
  proofs (the resolver currently treats anything other than `"unsat"`
  as unproven, so this is forward-compatible).
* `lean_version` is added alongside `mumei_version` to record the Lean
  toolchain used.
-/

import MumeiLean.Basic
import MumeiLean.CertParser

namespace MumeiLean

/-- Render a list of atom proof outcomes as a deterministic string
list — used by Python at debug time. The real JSON serialisation
lives in `scripts/export_cert.py`. -/
def renderResults (rs : List (String × ProofResult)) : List String :=
  rs.map fun (n, r) => s!"{n}: {r.toStatus} ({r.toZ3CheckResult})"

end MumeiLean
