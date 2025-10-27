import Lake
open Lake DSL

package «springphysics» where
  -- add package configuration options here

lean_lib «SpringPhysics» where
  -- add library configuration options here

@[default_target]
lean_exe «rigorous» where
  root := `RigorousSpringPhysics

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
