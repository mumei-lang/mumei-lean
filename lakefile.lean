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
