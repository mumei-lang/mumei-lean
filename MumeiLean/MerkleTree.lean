/-!
# MumeiLean.MerkleTree

Lean witness module for the Phase 4 Merkle Tree Verification demo.
-/

namespace MumeiLean.MerkleTree

def computeRoot (leaf siblingHash : Int) : Int :=
  leaf + siblingHash

def verifyMerkleRoot
    (_root leaf siblingHash _expectedRoot _hashFunctionSecure : Int) : Int :=
  computeRoot leaf siblingHash

theorem verify_merkle_root_matches_expected
    (root leaf siblingHash expectedRoot hashFunctionSecure : Int)
    (_hNonnegative :
      root ≥ 0 ∧ leaf ≥ 0 ∧ siblingHash ≥ 0 ∧ expectedRoot ≥ 0)
    (_hSecure : hashFunctionSecure = 1)
    (hPath : leaf + siblingHash = expectedRoot)
    (hRoot : root = expectedRoot) :
    verifyMerkleRoot root leaf siblingHash expectedRoot hashFunctionSecure = root ∧
      verifyMerkleRoot root leaf siblingHash expectedRoot hashFunctionSecure = expectedRoot := by
  unfold verifyMerkleRoot computeRoot
  constructor
  · rw [hPath]
    exact hRoot.symm
  · exact hPath

end MumeiLean.MerkleTree
