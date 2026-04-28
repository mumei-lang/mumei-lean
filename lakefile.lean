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
  srcDir := "MumeiLean"
