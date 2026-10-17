/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Frozen.rectangularOmega_curve
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Exponent

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular.Providers
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem rectangular_alpha_ge_half (F : Type*) [Field F] :
  (1 : ℝ) / 2 ≤ sSup {k : ℝ | k ∈ Set.Icc 0 1 ∧
      OAI.MatrixMultiplication.Arithmetic.rectangularOmega F k = 2} :=
by
  apply le_csSup (show BddAbove {k : ℝ | k ∈ Set.Icc 0 1 ∧
    OAI.MatrixMultiplication.Arithmetic.rectangularOmega F k = 2} from ⟨1, fun _ h => h.1.2⟩)
  refine ⟨⟨by norm_num, by norm_num⟩, le_antisymm ?_
    (OAI.MatrixMultiplication.Arithmetic.rectangularOmega_two_le (F := F) _)⟩
  simpa only [if_pos (le_refl ((1 : ℝ) / 2))] using
    BlockIdentities.Rectangular.rectangularOmega_curve F ((1 : ℝ) / 2) (by norm_num)

end BlockIdentities.Rectangular.Providers
