/-!
# MumeiLean.TheoremGen

Helpers used by the Python-generated Lean source files.

`scripts/ingest_cert.py` translates each `unknown` mumei atom into a
Lean `theorem` of the form

```
theorem <name>_correct
    (params...) : <requires_prop> → <ensures_prop> := by
  -- proof obligation
  sorry
```

This module provides:

* `MumeiLean.MumeiBool` – a thin alias used by generated code so
  failures to translate complex contract expressions land on a single,
  greppable identifier instead of leaking ad-hoc terms.
* `MumeiLean.unproven` – a documented `False` placeholder used when
  the translator needs to emit a Prop it cannot yet model. Generated
  theorem files should mention this name in a comment so they are easy
  to find.

Everything here is deliberately tiny: the heavy lifting (string ↔ AST
↔ Prop) is done in Python at generation time. Lean only sees the final
already-typed Prop.
-/

namespace MumeiLean

/-- Boolean-style `Prop` alias used by the Python translator. -/
abbrev MumeiBool := Prop

/-- Marker `Prop` for fragments the translator could not faithfully
encode. Generated Lean files keep a `-- TODO: unproven` comment
beside any use so they can be triaged later. -/
def unproven : Prop := False

/-- Short alias kept for symmetry with the mumei `result` keyword used
inside `ensures` clauses. The Python translator binds `result` as an
explicit theorem parameter, so this is purely documentary. -/
abbrev MumeiResult (α : Type) := α

end MumeiLean
