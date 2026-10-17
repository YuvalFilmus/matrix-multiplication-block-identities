/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Arithmetic.ProgramRank
public import BlockIdentities.Arithmetic.FormalBounds
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankExponent
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.ExponentComparison

/-! Formal programs bound the exact-rank exponent, using finite bilinearization. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Arithmetic

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.Arithmetic
open OAI.MatrixMultiplication.AuxiliarySeparation

variable {F : Type*} [Field F]

/-- The fixed factor in finite formal-program bilinearization disappears when
comparing the size-uniform positive-slack growth exponents. -/
theorem exactRankExponent_le_of_formalAdmissibleExponent {τ : ℝ}
    (hτ : FormalAdmissibleExponent F τ) : exactRankExponent F ≤ τ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨C, _hC, hcost⟩ := hτ ε hε
  apply rpow_exponent_le_of_nat_bound (C := 2 * C)
  intro n hn
  obtain ⟨P, hP, hPcost⟩ := hcost n hn
  have hfinite := matrix_rankAtMost_of_formalCorrect P hP
  have hleast : exactMatrixRank F n ≤ 2 * P.cost := exactRank_le hfinite
  calc
    (n : ℝ) ^ exactRankExponent F ≤ (exactMatrixRank F n : ℝ) :=
      exactMatrixRank_rpow_lower_of_pos (K := F) (by omega)
    _ ≤ 2 * (P.cost : ℝ) := by exact_mod_cast hleast
    _ ≤ 2 * (C * (n : ℝ) ^ (τ + ε)) :=
      mul_le_mul_of_nonneg_left hPcost (by norm_num)
    _ = (2 * C) * (n : ℝ) ^ (τ + ε) := by ring

/-- Exact tensor-rank exponent is bounded by the formal-polynomial arithmetic
infimum over every field. This is the program-to-rank direction only. -/
theorem exactRankExponent_le_formalOmega (F : Type*) [Field F] :
    exactRankExponent F ≤ formalOmega F := by
  change exactRankExponent F ≤ sInf {τ : ℝ | FormalAdmissibleExponent F τ}
  apply le_csInf (formalAdmissibleExponent_nonempty (F := F))
  intro τ hτ
  exact exactRankExponent_le_of_formalAdmissibleExponent hτ

end BlockIdentities.Arithmetic
