import Lake
open Lake DSL

package «m1F-Explained» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «M1FExplained» {
  -- add any library configuration options here
}
