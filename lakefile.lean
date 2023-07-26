import Lake
open Lake DSL

package «propositional-logic» {
  -- add package configuration options here
}

lean_lib «PropositionalLogic» {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_exe «propositional-logic» {
  root := `Main
}
