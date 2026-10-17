/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Definitions
public import BlockIdentities.Rectangular.Providers.FormalalphaGeHalf

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem formalAlpha_ge_half (F : Type*) [Field F] :
  (1 : ℝ) / 2 ≤ Arithmetic.formalAlpha F :=
-- BEGIN APPROVED PROOF REGION
by
  exact Providers.formalAlpha_ge_half F
-- END APPROVED PROOF REGION

end BlockIdentities.Rectangular
