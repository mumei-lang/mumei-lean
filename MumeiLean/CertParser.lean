/-!
# MumeiLean.CertParser

Skeleton for an in-Lean parser of mumei's `.proof-cert.json` files.

The initial bridge pipeline does the JSON ↔ Lean source translation in
Python (`scripts/ingest_cert.py`), so this module currently only
exposes the *shape* the eventual Lean parser will produce. Keeping the
data types in `MumeiLean` lets downstream Lean code already refer to
the parsed records by name.

A full implementation can be filled in later using `Lean.Json`; until
then, generated Lean theorem files do not depend on this module at
runtime.
-/

namespace MumeiLean

/-- Lean-side mirror of mumei `AtomCertificate` (subset of fields used
by the bridge). -/
structure AtomCertificateData where
  name              : String
  z3CheckResult     : String
  status            : String
  contentHash       : String
  proofHash         : String
  requires          : String
  ensures           : String
  dependencies      : List String
  effects           : List String
  deriving Repr, Inhabited

/-- Lean-side mirror of mumei `ProofCertificate` (subset of fields used
by the bridge). -/
structure ProofCertificateData where
  version          : String
  generatedAt      : String
  mumeiVersion     : String
  z3Version        : String
  file             : String
  packageName      : Option String
  packageVersion   : Option String
  certificateHash  : String
  allVerified      : Bool
  atoms            : List AtomCertificateData
  deriving Repr, Inhabited

/-- Placeholder: real implementation will live in `Lean.Json` once the
bridge graduates from the Python-only path. -/
def parseProofCertificate (_json : String) :
    Except String ProofCertificateData :=
  Except.error "MumeiLean.CertParser.parseProofCertificate: not yet implemented; \
use scripts/ingest_cert.py for now"

end MumeiLean
