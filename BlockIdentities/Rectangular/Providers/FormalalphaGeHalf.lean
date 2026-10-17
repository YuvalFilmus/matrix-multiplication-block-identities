/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Frozen.formalRectangularOmega_curve
public import BlockIdentities.Arithmetic.RectangularBasics

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular.Providers
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem formalAlpha_ge_half (F : Type*) [Field F] :
  (1 : ℝ) / 2 ≤ Arithmetic.formalAlpha F :=
by
  have hmem : (1 : ℝ) / 2 ∈ {k : ℝ | k ∈ Set.Icc 0 1 ∧
      Arithmetic.formalRectangularOmega F k = 2} := by
    refine ⟨⟨by norm_num, by norm_num⟩, le_antisymm ?_
      (Arithmetic.formalRectangularOmega_two_le (F := F) _)⟩
    simpa only [if_pos (le_refl ((1 : ℝ) / 2))] using
      BlockIdentities.Rectangular.formalRectangularOmega_curve F ((1 : ℝ) / 2) (by norm_num)
  exact le_csSup (show BddAbove {k : ℝ | k ∈ Set.Icc 0 1 ∧
    Arithmetic.formalRectangularOmega F k = 2} from ⟨1, fun _ h => h.1.2⟩) hmem

end BlockIdentities.Rectangular.Providers
