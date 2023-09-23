import Lake
open Lake DSL

package «Lean4Repl» {
  -- add package configuration options here
}

lean_exe «BuildAllDependencies» {
  root := `BuildAllDependencies
  -- add package configuration options here
}

lean_lib «Lean4Repl» {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean4-example» {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"355541ae7a2455222f179dcf7f074aa2c45eb8aa"
