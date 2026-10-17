/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Definitions
public import BlockIdentities.Rectangular.Providers.FormalshapeomegaGeneralBound

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem formalShapeOmega_general_bound (F : Type*) [Field F] (a b c : ℝ≥0)
    (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 < c) :
  Arithmetic.formalShapeOmega F a b c ≤
      if (c : ℝ) ≤ (a : ℝ) * (b : ℝ) / ((a : ℝ) + (b : ℝ)) then
        (a : ℝ) + (b : ℝ)
      else ((a : ℝ) + (b : ℝ) + (c : ℝ)) / 2 +
        ((a : ℝ) * (b : ℝ) / (c : ℝ) + (a : ℝ) * (c : ℝ) / (b : ℝ) +
          (b : ℝ) * (c : ℝ) / (a : ℝ)) / 4 :=
-- BEGIN APPROVED PROOF REGION
by
  exact Providers.formalShapeOmega_general_bound F a b c hab hbc hc
-- END APPROVED PROOF REGION

end BlockIdentities.Rectangular
