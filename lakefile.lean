import Lake
open Lake DSL

package blockIdentities where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require matrixMultiplicationAllFields from "vendor/navot"

@[default_target]
lean_lib BlockIdentities
