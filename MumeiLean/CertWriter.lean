import Lean.Data.Json
import MumeiLean.Basic
import MumeiLean.CertParser

/-!
# MumeiLean.CertWriter

Native Lean serialiser for mumei-compatible `.lean-cert.json`
artefacts.

The bridge pipeline still uses Python (`scripts/export_cert.py`) for
the production path, but this module provides a self-contained Lean
implementation so downstream tooling can emit certificates directly
without shelling out.

The emitted certificate keeps the mumei `ProofCertificate` schema
(see `mumei-lang/mumei` `mumei-core/src/proof_cert.rs`) and only
differs in two fields:

* `z3_check_result` may be `"lean_verified"` for successful Lean
  proofs (the resolver currently treats anything other than `"unsat"`
  as unproven, so this is forward-compatible).
* `lean_version` is added alongside `mumei_version` to record the
  Lean toolchain used.
-/

namespace MumeiLean

open Lean (Json)

/-- Render a list of atom proof outcomes as a deterministic string
list — used by Python at debug time. -/
def renderResults (rs : List (String × ProofResult)) : List String :=
  rs.map fun (n, r) => s!"{n}: {r.toStatus} ({r.toZ3CheckResult})"

/-- Serialise an `AtomCertificateData` back to JSON. -/
def atomToJson (a : AtomCertificateData) : Json :=
  Json.mkObj [
    ("name",            Json.str a.name),
    ("z3_check_result", Json.str a.z3CheckResult),
    ("status",          Json.str a.status),
    ("content_hash",    Json.str a.contentHash),
    ("proof_hash",      Json.str a.proofHash),
    ("requires",        Json.str a.requires),
    ("ensures",         Json.str a.ensures),
    ("dependencies",    Json.arr (a.dependencies.map Json.str).toArray),
    ("effects",         Json.arr (a.effects.map Json.str).toArray),
  ]

/-- Apply a single `(name, result)` pair to an atom: when the proof
result is `verified`, upgrade the atom's `z3_check_result` to
`"lean_verified"` and its `status` to `"verified"`; failed/timeout
results leave the atom's existing fields intact (the mumei resolver
already treats them as unproven, so the original `z3_check_result`
— typically `"unknown"` — is the most informative value to preserve).

This mirrors `scripts/export_cert.py`, which only mutates atoms that
pass `_atom_proved`; failed/timeout atoms are forwarded verbatim. -/
def applyResult
    (results : List (String × ProofResult))
    (a : AtomCertificateData) : AtomCertificateData :=
  match results.find? (fun (n, _) => n == a.name) with
  | some (_, .verified) =>
    { a with
        z3CheckResult := ProofResult.verified.toZ3CheckResult,
        status        := ProofResult.verified.toStatus }
  | _ => a

/-- Optional-string → JSON: `none` becomes `Json.null`. -/
private def optStr : Option String → Json
  | none   => Json.null
  | some s => Json.str s

/-- Compute the `all_verified` field after applying `results`: true iff
every atom in `cert` ends up with `z3_check_result ∈ {"unsat", "lean_verified"}`.
This matches mumei's resolver semantics (`unsat` from Z3 or
`lean_verified` from this bridge are the only two "proved" states). -/
def computeAllVerified
    (atoms : List AtomCertificateData) : Bool :=
  atoms.all fun a =>
    a.z3CheckResult == "unsat" || a.z3CheckResult == "lean_verified"

/-- Build the JSON payload for a `.lean-cert.json` file.

The result keeps mumei's `ProofCertificate` schema field-for-field
and adds a `lean_version` sibling to `mumei_version`. The atom list
is rebuilt with `applyResult`, so verified results upgrade in place. -/
def writeLeanCertificateJson
    (cert : ProofCertificateData)
    (results : List (String × ProofResult))
    (leanVersion : String) : Json :=
  let upgradedAtoms := cert.atoms.map (applyResult results)
  let allVerified   := computeAllVerified upgradedAtoms
  Json.mkObj [
    ("version",          Json.str cert.version),
    ("timestamp",        Json.str cert.generatedAt),
    ("mumei_version",    Json.str cert.mumeiVersion),
    ("lean_version",     Json.str leanVersion),
    ("z3_version",       Json.str cert.z3Version),
    ("file",             Json.str cert.file),
    ("package_name",     optStr cert.packageName),
    ("package_version",  optStr cert.packageVersion),
    ("certificate_hash", Json.str cert.certificateHash),
    ("all_verified",     Json.bool allVerified),
    ("atoms",            Json.arr (upgradedAtoms.map atomToJson).toArray),
  ]

/-- Serialise `cert` (with proof results merged) to a pretty-printed
JSON string suitable for writing to disk as a `.lean-cert.json`
file. -/
def writeLeanCertificate
    (cert : ProofCertificateData)
    (results : List (String × ProofResult))
    (leanVersion : String) : String :=
  (writeLeanCertificateJson cert results leanVersion).pretty

end MumeiLean
