import Lake
open Lake DSL

package «mumei-lean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Pinned to a mathlib4 release tag matching `lean-toolchain`
-- (leanprover/lean4:v4.15.0). Bump deliberately rather than tracking
-- `master`, which introduces breaking changes regularly.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

@[default_target]
lean_lib «MumeiLean» where
  -- Default `srcDir = "."` is correct: the library root is `MumeiLean.lean`
  -- at the repo root and submodules live under `MumeiLean/`.

-- Theorem files emitted by `scripts/ingest_cert.py` for atoms whose
-- `z3_check_result` is `"unknown"`. They live under `generated/Generated/...`
-- and are not committed (see `.gitignore`); `bridge.py` regenerates them
-- before each `lake build`. Declaring them as a default target ensures
-- `lake build` actually compiles + type-checks them, so
-- `scripts/export_cert.py` can correctly distinguish proved theorems
-- from ones that still contain `sorry` / fail to elaborate.
--
-- `globs := #[.submodules `Generated]` deliberately omits a `Generated.lean`
-- root (the `generated/` directory may be empty or missing on a fresh
-- clone), so lake just walks the namespace and builds whatever submodules
-- exist.
@[default_target]
lean_lib «Generated» where
  srcDir := "generated"
  globs := #[.submodules `Generated]
