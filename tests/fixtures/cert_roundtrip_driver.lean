import MumeiLean.CertParser
import MumeiLean.CertWriter
import MumeiLean.Basic

/-!
Driver for `tests/test_cert_roundtrip.py`.

Reads a `.proof-cert.json` path from `args[0]`, parses it, marks
every atom as `verified` via `MumeiLean.applyResult` against a
`ProofResult.verified` for that atom name, writes the result with
`writeLeanCertificate`, parses it again, and prints a small
JSON summary used by the Python test to assert round-trip
consistency.
-/

open Lean MumeiLean

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] => do
    let raw ← IO.FS.readFile path
    match parseProofCertificate raw with
    | .error e => do
      IO.eprintln s!"parse error: {e}"
      pure 1
    | .ok cert => do
      let results : List (String × ProofResult) :=
        cert.atoms.map fun a => (a.name, ProofResult.verified)
      let out := writeLeanCertificate cert results "lean4-test"
      match parseProofCertificate out with
      | .error e => do
        IO.eprintln s!"reparse error: {e}"
        pure 2
      | .ok cert2 => do
        let summary := Json.mkObj [
          ("input_atom_count",  Json.num cert.atoms.length),
          ("output_atom_count", Json.num cert2.atoms.length),
          ("file",              Json.str cert2.file),
          ("version",           Json.str cert2.version),
          ("first_atom_z3",
            match cert2.atoms.head? with
            | some a => Json.str a.z3CheckResult
            | none   => Json.null),
          ("first_atom_translator_version",
            match cert2.atoms.head? with
            | some a => Json.str a.translatorVersion
            | none   => Json.null),
          ("first_atom_z3_result_class",
            match cert2.atoms.head? with
            | some a => Json.str a.z3ResultClass
            | none   => Json.null),
          ("first_atom_escalation_reason",
            match cert2.atoms.head? with
            | some a => Json.str a.escalationReason
            | none   => Json.null),
          ("first_atom_logic_fragment_tags",
            match cert2.atoms.head? with
            | some a => Json.arr (a.logicFragmentTags.map Json.str).toArray
            | none   => Json.null),
          ("first_atom_lean_solver_time_s",
            match cert2.atoms.head? with
            | some a =>
              match a.leanResultMetadata with
              | some m =>
                match m.leanSolverTimeS with
                | some t => Json.str (toString t)
                | none   => Json.null
              | none => Json.null
            | none => Json.null),
          ("written_json",      Json.str out),
        ]
        IO.println summary.compress
        pure 0
  | _ => do
    IO.eprintln "usage: lake env lean --run cert_roundtrip_driver.lean <cert.json>"
    pure 64
