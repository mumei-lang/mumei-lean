import MumeiLean.MerkleTree
import MumeiLean.DeFi
import MumeiLean.ArkLibAudit

def usage : String :=
  "simple-cli commands:\n  greet <name>\n  add <n> <m>\n  echo <args...>\n  merkle <root> <leaf> <sibling_hash> <expected_root> <hash_secure_flag>\n  defi-transfer <from_balance> <to_balance> <amount>\n  audit-commitment <pre_hash> <post_hash> <invariant_hash> <expected_commitment>"

def joinWithSpace : List String → String
  | [] => ""
  | first :: rest => rest.foldl (fun acc part => acc ++ " " ++ part) first

def addArgs (left : String) (right : String) : Except String Nat := do
  let some l := left.toNat? | throw s!"not a natural number: {left}"
  let some r := right.toNat? | throw s!"not a natural number: {right}"
  pure (l + r)

def parseNatAsInt (value : String) : Except String Int := do
  let some n := value.toNat? | throw s!"not a natural number: {value}"
  pure (Int.ofNat n)

def requireCheck (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

def runMerkle (rootStr leafStr siblingStr expectedStr secureStr : String) : Except String String := do
  let root <- parseNatAsInt rootStr
  let leaf <- parseNatAsInt leafStr
  let siblingHash <- parseNatAsInt siblingStr
  let expectedRoot <- parseNatAsInt expectedStr
  let hashFunctionSecure <- parseNatAsInt secureStr
  _ <- requireCheck
    (decide (root ≥ 0 ∧ leaf ≥ 0 ∧ siblingHash ≥ 0 ∧ expectedRoot ≥ 0))
    "Merkle inputs must be nonnegative"
  _ <- requireCheck (decide (hashFunctionSecure = 1))
    "hash_function_secure must be 1"
  _ <- requireCheck (decide (leaf + siblingHash = expectedRoot ∧ root = expectedRoot))
    "computed Merkle root must match expected_root and root"
  let result :=
    MumeiLean.MerkleTree.verifyMerkleRoot
      root leaf siblingHash expectedRoot hashFunctionSecure
  pure s!"merkle accepted root={result}"

def runDefiTransfer (fromStr toStr amountStr : String) : Except String String := do
  let fromBalance <- parseNatAsInt fromStr
  let toBalance <- parseNatAsInt toStr
  let amount <- parseNatAsInt amountStr
  _ <- requireCheck (decide (fromBalance ≥ amount))
    "from_balance must cover amount"
  _ <- requireCheck (decide (toBalance ≥ 0 ∧ amount ≥ 0))
    "to_balance and amount must be nonnegative"
  _ <- requireCheck (decide (toBalance + amount ≤ MumeiLean.DeFi.uint256Max))
    "receiver balance would exceed Uint256 demo bound"
  let result := MumeiLean.DeFi.safeTransfer fromBalance toBalance amount
  pure s!"defi transfer accepted to_balance={result}"

def runAuditCommitment (preStr postStr invariantStr expectedStr : String) : Except String String := do
  let preconditionHash <- parseNatAsInt preStr
  let postconditionHash <- parseNatAsInt postStr
  let invariantHash <- parseNatAsInt invariantStr
  let expectedCommitment <- parseNatAsInt expectedStr
  _ <- requireCheck
    (decide (expectedCommitment = preconditionHash + postconditionHash + invariantHash))
    "expected_commitment must equal pre_hash + post_hash + invariant_hash"
  let result :=
    MumeiLean.ArkLibAudit.reviewTopLevelTheorem
      preconditionHash postconditionHash invariantHash expectedCommitment
  pure s!"audit commitment accepted commitment={result}"

def printResult : Except String String → IO UInt32
  | .ok line => do
      IO.println line
      pure 0
  | .error message => do
      IO.eprintln message
      pure 2

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.println usage
      pure 0
  | ["--help"] =>
      IO.println usage
      pure 0
  | ["greet", name] =>
      IO.println s!"hello, {name}"
      pure 0
  | ["add", left, right] =>
      match addArgs left right with
      | .ok result =>
          IO.println result
          pure 0
      | .error message =>
          IO.eprintln message
          pure 2
  | "echo" :: rest =>
      IO.println (joinWithSpace rest)
      pure 0
  | ["merkle", root, leaf, siblingHash, expectedRoot, hashFunctionSecure] =>
      printResult (runMerkle root leaf siblingHash expectedRoot hashFunctionSecure)
  | ["defi-transfer", fromBalance, toBalance, amount] =>
      printResult (runDefiTransfer fromBalance toBalance amount)
  | ["audit-commitment", preconditionHash, postconditionHash, invariantHash, expectedCommitment] =>
      printResult
        (runAuditCommitment
          preconditionHash postconditionHash invariantHash expectedCommitment)
  | _ =>
      IO.eprintln usage
      pure 2
