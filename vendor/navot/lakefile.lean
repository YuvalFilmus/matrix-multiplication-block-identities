import Lake
open Lake DSL

package matrixMultiplicationAllFields where
  version := v!"0.1.0"
  description := "OpenAI matrix-multiplication proof extended to arbitrary fields"
  license := "Apache-2.0"
  srcDir := "lean"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "ccbef15ebdb41c2addfac682131f83c75904c3c1"

@[default_target]
lean_lib OAI

lean_lib FixedPointTheorems
