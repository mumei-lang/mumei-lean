import Lake
open Lake DSL

package «mumei-lean-cli-example» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require «mumei-lean» from "../.."

@[default_target]
lean_exe «simple-cli» where
  root := `SimpleCli
