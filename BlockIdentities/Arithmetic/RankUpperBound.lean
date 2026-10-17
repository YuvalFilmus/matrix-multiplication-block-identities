/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Arithmetic.FormalGrowth
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankExponent

/-! One direction of the formal arithmetic/rank exponent comparison. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Arithmetic

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation

/-- Fixed exact tensor-rank algorithms bound the formal-polynomial arithmetic
exponent. This is only the rank-to-program direction of the comparison. -/
theorem formalOmega_le_exactRankExponent (F : Type*) [Field F] :
    formalOmega F ≤ exactRankExponent F := by
  unfold exactRankExponent
  apply le_csInf (exactRankExponentSet_nonempty (K := F))
  rintro τ ⟨n, hn, rfl⟩
  apply formalOmega_le_of_formalAdmissibleExponent
  apply formalAdmissibleExponent_of_rankAtMost (F := F) (n := n)
    (R := exactMatrixRank F n) hn
  · exact exactMatrixRank_spec (K := F) n
  · exact exactMatrixRank_logb_lower (K := F) hn
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hnne : (n : ℝ) ≠ 1 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hRpos : 0 < (exactMatrixRank F n : ℝ) := by
      exact_mod_cast exactMatrixRank_pos (K := F) (show 0 < n by omega)
    exact (Real.rpow_logb hnpos hnne hRpos).symm.le

end BlockIdentities.Arithmetic
