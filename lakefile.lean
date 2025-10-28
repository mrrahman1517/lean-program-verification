import Lake
open Lake DSL

package «springphysics» where
  -- add package configuration options here

lean_lib «SpringPhysics» where
  -- add library configuration options here

@[default_target]
lean_exe «rigorous» where
  root := `RigorousSpringPhysics

lean_exe «helloworld» where
  root := `helloworld

lean_exe «test_factorial» where
  root := `test_factorial

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
