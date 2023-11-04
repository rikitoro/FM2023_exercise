import Lake
open Lake DSL

package «fM2023_exrcise» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «FM2023Exrcise» {
  -- add any library configuration options here
}
