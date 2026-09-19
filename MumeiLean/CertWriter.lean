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

/-- Current translator contract identifiers. Kept in lockstep with
`TRANSLATOR_VERSION` / `BRIDGE_LEMMA_HASH` in `scripts/export_cert.py`:
an atom whose recorded identifiers differ — or are absent — is treated
as stale and is never promoted, matching
`lean_certificate_metadata_is_current` on the mumei side. -/
def currentTranslatorVersion : String := "mumei-lean-translator-ir-v2"

def currentBridgeLemmaHash : String :=
  "ee8cd3ba96c3318b3f07445f4755619744d4e1f9a662af94f3cbce6d41ed4347"

/-- Render a list of atom proof outcomes as a deterministic string
list — used by Python at debug time. -/
def renderResults (rs : List (String × ProofResult)) : List String :=
  rs.map fun (n, r) => s!"{n}: {r.toStatus} ({r.toZ3CheckResult})"

/-- Optional-string → JSON: `none` becomes `Json.null`. -/
private def optStr : Option String → Json
  | none   => Json.null
  | some s => Json.str s

/-- Optional-float → JSON: `none` becomes `Json.null`. -/
private def optFloat : Option Float → Json
  | none   => Json.null
  | some x =>
    match Lean.JsonNumber.fromFloat? x with
    | .inr n => Json.num n
    | .inl _ => Json.null

/-- Serialise Lean result metadata, preserving the escalation cost the
Python bridge measured in `lean_solver_time_s`. -/
def leanResultMetadataToJson (m : LeanResultMetadataData) : Json :=
  Json.mkObj [
    ("status",             Json.str m.status),
    ("theorem_name",       Json.str m.theoremName),
    ("translator_version", Json.str m.translatorVersion),
    ("bridge_lemma_hash",  Json.str m.bridgeLemmaHash),
    ("proof_path",         Json.str m.proofPath),
    ("lean_solver_time_s", optFloat m.leanSolverTimeS),
    ("diagnostics",        Json.arr (m.diagnostics.map Json.str).toArray),
  ]

/-- Serialise an `AtomCertificateData` back to JSON. -/
def atomToJson (a : AtomCertificateData) : Json :=
  Json.mkObj [
    ("name",            Json.str a.name),
    ("z3_check_result", Json.str a.z3CheckResult),
    ("z3_result_class", Json.str a.z3ResultClass),
    ("status",          Json.str a.status),
    ("content_hash",    Json.str a.contentHash),
    ("proof_hash",      Json.str a.proofHash),
    ("requires",        Json.str a.requires),
    ("ensures",         Json.str a.ensures),
    ("escalation_reason", Json.str a.escalationReason),
    ("unknown_obligation_domain", Json.str a.unknownObligationDomain),
    ("logic_fragment_tags", Json.arr (a.logicFragmentTags.map Json.str).toArray),
    ("dependencies",    Json.arr (a.dependencies.map Json.str).toArray),
    ("effects",         Json.arr (a.effects.map Json.str).toArray),
    ("translator_version", Json.str a.translatorVersion),
    ("bridge_lemma_hash",  Json.str a.bridgeLemmaHash),
    ("manual_lemma_reason", optStr a.manualLemmaReason),
    ("lean_result_metadata",
      match a.leanResultMetadata with
      | none   => Json.null
      | some m => leanResultMetadataToJson m),
  ]

/-- Mirror of `_unknown_lean_candidate` in `scripts/export_cert.py`:
the atom's Z3 outcome must be in the unknown/escalation class before a
Lean result may upgrade it. -/
def isUnknownCandidate (a : AtomCertificateData) : Bool :=
  a.z3CheckResult == "unknown"
    || a.z3ResultClass == "unknown"
    || a.z3CheckResult == "spurious_candidate"
    || a.escalationReason == "spurious_candidate"

/-- Mirror of `_translator_contract_current` in `scripts/export_cert.py`:
absent identifiers are stale, not current. -/
def translatorContractCurrent (a : AtomCertificateData) : Bool :=
  a.translatorVersion == currentTranslatorVersion
    && a.bridgeLemmaHash == currentBridgeLemmaHash

/-- Apply a single `(name, result)` pair to an atom: when the proof
result is `verified` *and* the atom passes the `_atom_proved` gates
(unknown-class escalation candidate, current translator contract, no
unsuperseded `manual_lemma_reason`), upgrade the atom's
`z3_check_result` to `"lean_verified"` and its `status` to `"verified"`;
failed/timeout results leave the atom's existing fields intact (the
mumei resolver already treats them as unproven, so the original
`z3_check_result` — typically `"unknown"` — is the most informative
value to preserve).

This mirrors `scripts/export_cert.py`, which only mutates atoms that
pass `_atom_proved`; failed/timeout atoms are forwarded verbatim. The
metadata-dependent supersession check (`_manual_lemma_reason_superseded`)
has no Lean-side input, so any `manual_lemma_reason` is treated
conservatively as blocking. The unknown-escalation metadata
(`z3_result_class`, `escalation_reason`, `logic_fragment_tags`) is never
rewritten: mumei's benchmark consumes it to attribute the escalation
that produced the Lean proof. -/
def applyResult
    (results : List (String × ProofResult))
    (a : AtomCertificateData) : AtomCertificateData :=
  match results.find? (fun (n, _) => n == a.name) with
  | some (_, .verified) =>
    if isUnknownCandidate a
        && translatorContractCurrent a
        && a.manualLemmaReason.isNone then
      { a with
          z3CheckResult := ProofResult.verified.toZ3CheckResult,
          status        := ProofResult.verified.toStatus,
          leanResultMetadata :=
            a.leanResultMetadata.map fun m =>
              { m with status := ProofResult.verified.toZ3CheckResult } }
    else
      a
  | _ => a

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
  -- `certificate_hash` is deliberately omitted: it covers the canonical
  -- serialisation of the *pre-upgrade* atoms, so re-emitting it would
  -- certify stale content (export_cert.py pops it for the same reason).
  Json.mkObj [
    ("version",          Json.str cert.version),
    ("timestamp",        Json.str cert.generatedAt),
    ("mumei_version",    Json.str cert.mumeiVersion),
    ("lean_version",     Json.str leanVersion),
    ("lean_cert_schema_version", Json.str "1.0-lean"),
    ("z3_version",       Json.str cert.z3Version),
    ("file",             Json.str cert.file),
    ("package_name",     optStr cert.packageName),
    ("package_version",  optStr cert.packageVersion),
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
