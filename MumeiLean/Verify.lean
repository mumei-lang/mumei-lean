/-!
# MumeiLean.Verify

Lean-side helpers for collecting per-atom proof outcomes.

The actual `lake build` invocation is what verifies generated theorems
(any `sorry` causes a warning that `scripts/export_cert.py` treats as
a failure). This module gives Python a stable, named API for the
two-line "did this atom prove?" check that future Lean-only flows can
target.
-/

import MumeiLean.Basic

namespace MumeiLean

/-- Record a successful proof for `atomName`. -/
def recordVerified (atomName : String) : String × ProofResult :=
  (atomName, .verified)

/-- Record a failed proof for `atomName` with a human-readable
reason. -/
def recordFailed (atomName : String) (reason : String) :
    String × ProofResult :=
  (atomName, .failed reason)

/-- Record a timeout for `atomName`. -/
def recordTimeout (atomName : String) : String × ProofResult :=
  (atomName, .timeout)

end MumeiLean
