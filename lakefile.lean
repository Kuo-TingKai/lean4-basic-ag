import Lake
open Lake DSL

package lean4_app {
  -- add package configuration options here
}

@[default_target]
lean_lib lean4_app {
  srcDir := "Lean4App"
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0" 