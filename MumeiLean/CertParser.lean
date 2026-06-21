import Lean.Data.Json

/-!
# MumeiLean.CertParser

Native Lean parser for mumei's `.proof-cert.json` files.

The bridge pipeline still uses Python (`scripts/ingest_cert.py`) for
the JSON ↔ Lean source translation, but this module exposes a
self-contained Lean implementation so downstream tooling (e.g. an
embedded `lake env lean --run` consumer) can decode certificates
without invoking Python.

The schema mirrored here is mumei's `ProofCertificate` (see
`mumei-lang/mumei` `mumei-core/src/proof_cert.rs`); we keep the Lean
structure field names camelCased while reading the canonical
snake_case JSON keys.
-/

namespace MumeiLean

open Lean (Json)

/-- Lean-side mirror of mumei `AtomCertificate` (subset of fields used
by the bridge). -/
structure AtomCertificateData where
  name              : String
  z3CheckResult     : String
  z3ResultClass     : String
  status            : String
  contentHash       : String
  proofHash         : String
  requires          : String
  ensures           : String
  escalationReason  : String
  logicFragmentTags : List String
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

/-- Look up `key` in a JSON object and decode it as `String`. -/
private def getStr (j : Json) (key : String) : Except String String :=
  j.getObjValAs? String key

/-- Look up `key` in a JSON object and decode it as `String`,
falling back to `default` when the key is missing or not a string.
Used for fields whose presence is optional in older mumei outputs. -/
private def getStrOr (j : Json) (key : String) (default : String) : String :=
  match j.getObjValAs? String key with
  | .ok s    => s
  | .error _ => default

/-- Look up `key` in a JSON object and decode it as `Bool`,
defaulting to `false` if missing. -/
private def getBoolOr (j : Json) (key : String) (default : Bool) : Bool :=
  match j.getObjValAs? Bool key with
  | .ok b    => b
  | .error _ => default

/-- Look up `key` in a JSON object and decode it as an optional
`String`. The key may be absent or `null`; both yield `none`. -/
private def getOptStr (j : Json) (key : String) : Option String :=
  match j.getObjVal? key with
  | .ok Json.null => none
  | .ok v         => match v.getStr? with
                     | .ok s    => some s
                     | .error _ => none
  | .error _      => none

/-- Decode a JSON array of strings, returning `[]` if absent. -/
private def getStrArrOr (j : Json) (key : String) : List String :=
  match j.getObjVal? key with
  | .error _ => []
  | .ok arr  =>
    match arr.getArr? with
    | .error _   => []
    | .ok elems  =>
      elems.foldr (init := []) fun e acc =>
        match e.getStr? with
        | .ok s    => s :: acc
        | .error _ => acc

/-- Decode a single `AtomCertificate` JSON object. -/
def parseAtomCertificate (j : Json) : Except String AtomCertificateData := do
  let name          ← getStr j "name"
  let z3CheckResult ← getStr j "z3_check_result"
  return {
    name,
    z3CheckResult,
    z3ResultClass  := getStrOr j "z3_result_class" z3CheckResult,
    status         := getStrOr j "status"        "unknown",
    contentHash    := getStrOr j "content_hash"  "",
    proofHash      := getStrOr j "proof_hash"    "",
    requires       := getStrOr j "requires"      "",
    ensures        := getStrOr j "ensures"       "",
    escalationReason := getStrOr j "escalation_reason" "",
    logicFragmentTags := getStrArrOr j "logic_fragment_tags",
    dependencies   := getStrArrOr j "dependencies",
    effects        := getStrArrOr j "effects",
  }

/-- Parse a mumei `.proof-cert.json` payload into a
`ProofCertificateData`.

The implementation tolerates:

* missing optional fields (`status`, `z3_result_class`, `content_hash`,
  `proof_hash`, `requires`, `ensures`, `escalation_reason`,
  `logic_fragment_tags`, `dependencies`, `effects`,
  `package_name`, `package_version`) by defaulting them to neutral
  values, matching the behaviour of the Python ingester
  (`scripts/ingest_cert.py`).
* both `"timestamp"` and `"generated_at"` keys for the certificate
  emission time (mumei's current schema uses `"timestamp"`; the
  alternate key is accepted for forward-compatibility).

Hard failures only occur when a field that *must* exist is absent or
of the wrong type — most importantly `version`, `file`, and the
`atoms` array. -/
def parseProofCertificate (input : String) :
    Except String ProofCertificateData := do
  let parsed ← Lean.Json.parse input
  let version      ← getStr parsed "version"
  let mumeiVersion ← getStr parsed "mumei_version"
  let z3Version    ← getStr parsed "z3_version"
  let file         ← getStr parsed "file"
  let generatedAt :=
    match parsed.getObjValAs? String "timestamp" with
    | .ok s    => s
    | .error _ => getStrOr parsed "generated_at" ""
  let atomsRaw ← parsed.getObjVal? "atoms"
  let atomsArr ← atomsRaw.getArr?
  let atoms ← atomsArr.foldrM (init := ([] : List AtomCertificateData))
    (fun item acc => do
      let a ← parseAtomCertificate item
      pure (a :: acc))
  return {
    version,
    generatedAt,
    mumeiVersion,
    z3Version,
    file,
    packageName     := getOptStr parsed "package_name",
    packageVersion  := getOptStr parsed "package_version",
    certificateHash := getStrOr parsed "certificate_hash" "",
    allVerified     := getBoolOr parsed "all_verified" false,
    atoms,
  }

end MumeiLean
