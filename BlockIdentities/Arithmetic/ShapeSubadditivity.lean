/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.ShapeRankSeeds
public import BlockIdentities.Arithmetic.RectangularRankProduct

/-! Common-size actual rank seeds prove formal shape subadditivity. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Arithmetic
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped NNReal
variable {F : Type*} [Field F]

private theorem rpow_add_le_innerSize_mul (N : ℕ) (hN : 0 < N) (a A : ℝ≥0) :
    (N : ℝ) ^ ((a + A : ℝ≥0) : ℝ) ≤ (innerSize N a * innerSize N A : ℕ) := by
  rw [NNReal.coe_add, Real.rpow_add (by exact_mod_cast hN), Nat.cast_mul]
  exact mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _)
    (Real.rpow_nonneg (Nat.cast_nonneg N) _) (Nat.cast_nonneg _)

/-- Tensoring same-size coefficient seeds retains their literal rectangular
products; recursion then supplies actual polynomial algorithms at summed shapes. -/
theorem formalShapeOmega_add_le (a b c A B C : ℝ≥0) :
    formalShapeOmega F (a + A) (b + B) (c + C) ≤
      formalShapeOmega F a b c + formalShapeOmega F A B C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨N0, hN0, hseed⟩ := formalShapeOmega_eventually_rank_seed (F := F) a b c δ hδ
  obtain ⟨M0, hM0, hseed'⟩ := formalShapeOmega_eventually_rank_seed (F := F) A B C δ hδ
  let N := max N0 M0
  have hN : 2 ≤ N := hN0.trans (le_max_left _ _)
  have hNone : 1 ≤ N := by omega
  have hNpos : 0 < N := by omega
  obtain ⟨R, hRank, hR⟩ := hseed N (le_max_left _ _)
  obtain ⟨S, hRank', hS⟩ := hseed' N (le_max_right _ _)
  have hproduct := rectangular_matrix_rankAtMost_product hRank hRank'
  have hbudget : ((R * S : ℕ) : ℝ) ≤ (N : ℝ) ^
      (formalShapeOmega F a b c + formalShapeOmega F A B C + ε) := by
    rw [Nat.cast_mul]
    calc
      (R : ℝ) * S ≤ (N : ℝ) ^ (formalShapeOmega F a b c + δ) *
          (N : ℝ) ^ (formalShapeOmega F A B C + δ) :=
        mul_le_mul hR hS (Nat.cast_nonneg S) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      _ = _ := by
        rw [← Real.rpow_add (by exact_mod_cast hNpos)]
        congr 1
        dsimp only [δ]
        ring
  exact formalShapeOmega_le_of_rank_seed hN
    (Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one (one_le_innerSize hNone a))
      (lt_of_lt_of_le Nat.zero_lt_one (one_le_innerSize hNone A)))
    (Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one (one_le_innerSize hNone b))
      (lt_of_lt_of_le Nat.zero_lt_one (one_le_innerSize hNone B)))
    (Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one (one_le_innerSize hNone c))
      (lt_of_lt_of_le Nat.zero_lt_one (one_le_innerSize hNone C)))
    hproduct (rpow_add_le_innerSize_mul N hNpos a A)
      (rpow_add_le_innerSize_mul N hNpos b B) (rpow_add_le_innerSize_mul N hNpos c C) hbudget
end BlockIdentities.Arithmetic
