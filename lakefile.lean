import Lake
open Lake DSL

package «mumei-lean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib «MumeiLean» where
  -- Default `srcDir = "."` is correct: the library root is `MumeiLean.lean`
  -- at the repo root and submodules live under `MumeiLean/`.
