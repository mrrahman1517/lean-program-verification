import Lake
open Lake DSL

package «springphysics» where
  -- add package configuration options here

lean_lib «SpringPhysics» where
  -- add library configuration options here

@[default_target]
lean_exe «simpledemo» where
  root := `SimpleDemo

-- Commented out Mathlib for quick testing
-- require mathlib from git
--   "https://github.com/leanprover-community/mathlib4.git"