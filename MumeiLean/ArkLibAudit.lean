/-!
# MumeiLean.ArkLibAudit

Lean witness module for the Phase 6 ArkLib-style audit demo.
-/

namespace MumeiLean.ArkLibAudit

def computeImplementationCommitment
    (preconditionHash postconditionHash invariantHash : Int) : Int :=
  preconditionHash + postconditionHash + invariantHash

def reviewTopLevelTheorem
    (preconditionHash postconditionHash invariantHash _expectedCommitment : Int) : Int :=
  computeImplementationCommitment preconditionHash postconditionHash invariantHash

theorem review_top_level_theorem_matches_commitment
    (preconditionHash postconditionHash invariantHash expectedCommitment : Int)
    (hExpected :
      expectedCommitment =
        preconditionHash + postconditionHash + invariantHash) :
    reviewTopLevelTheorem
      preconditionHash postconditionHash invariantHash expectedCommitment =
        expectedCommitment := by
  unfold reviewTopLevelTheorem computeImplementationCommitment
  rw [hExpected]

end MumeiLean.ArkLibAudit
