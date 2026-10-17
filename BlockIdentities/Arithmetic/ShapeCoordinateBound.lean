/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.ShapeSubadditivity

/-! Coordinate bounds from actual finite matrix rank products and rank-d dot
factors. No spectral characterization or coordinate bound is assumed. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Arithmetic
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped NNReal BigOperators
variable {F : Type*} [Field F]

/-- The first-coordinate dot factor has an explicit rank-d decomposition over
any field, including characteristics dividing d. -/
theorem rankAtMost_matrix_dot_first (d : ℕ) :
    Tensor.RankAtMost (matrixMultiplicationTensor (K := F) d 1 1) d := by
  classical
  let L : Fin d → Fin d × Fin 1 → F := fun i x => if i = x.1 then 1 else 0
  let M : Fin d → Fin 1 × Fin 1 → F := fun _ _ => 1
  let P : Fin d → Fin 1 × Fin d → F := fun i z => if i = z.2 then 1 else 0
  have heq : matrixMultiplicationTensor (K := F) d 1 1 =
      fun x y z => ∑ i, Tensor.rankOne (L i) (M i) (P i) x y z := by
    funext x y z
    have hxy : x.2 = y.1 := Subsingleton.elim _ _
    have hyz : y.2 = z.1 := Subsingleton.elim _ _
    simp [matrixMultiplicationTensor, Tensor.rankOne, L, M, P, hxy, hyz,
      mul_ite, eq_comm]
  rw [heq]
  simpa using Tensor.rankAtMost_sum_rankOne L M P

theorem rankAtMost_matrix_dot_third (d : ℕ) :
    Tensor.RankAtMost (matrixMultiplicationTensor (K := F) 1 1 d) d :=
  Tensor.matrixCoefficients_cyclic_rank (rankAtMost_matrix_dot_first d)

theorem rankAtMost_matrix_dot_second (d : ℕ) :
    Tensor.RankAtMost (matrixMultiplicationTensor (K := F) 1 d 1) d :=
  Tensor.matrixCoefficients_cyclic_rank (rankAtMost_matrix_dot_third d)

private theorem dot_seed_budget (t : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧
      (innerSize N t : ℝ) ≤ (N : ℝ) ^ ((t : ℝ) + ε) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max ((2 : ℝ) ^ ε⁻¹) 2)
  have hNtwo : 2 ≤ N := by
    exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hN).le
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hfactor : (2 : ℝ) ≤ (N : ℝ) ^ ε :=
    ((Real.rpow_inv_lt_iff_of_pos (by norm_num : (0 : ℝ) ≤ 2)
      (Nat.cast_nonneg N) hε).mp (lt_of_le_of_lt (le_max_left _ _) hN)).le
  refine ⟨N, hNtwo, ?_⟩
  calc
    (innerSize N t : ℝ) ≤ 2 * (N : ℝ) ^ (t : ℝ) :=
      innerSize_cast_le (by omega) t.property
    _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (t : ℝ) :=
      mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hNpos.le _)
    _ = (N : ℝ) ^ ((t : ℝ) + ε) := by
      rw [← Real.rpow_add hNpos, add_comm ε]

/-- Dot factors bound the first coordinate at its actual dimension exponent. -/
theorem formalShapeOmega_dot_first_le (t : ℝ≥0) :
    formalShapeOmega F t 0 0 ≤ (t : ℝ) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N, hN, hbudget⟩ := dot_seed_budget t ε hε
  have hNone : 1 ≤ N := by omega
  apply formalShapeOmega_le_of_rank_seed hN
    (lt_of_lt_of_le Nat.zero_lt_one (one_le_innerSize hNone t))
    Nat.zero_lt_one Nat.zero_lt_one (rankAtMost_matrix_dot_first (innerSize N t))
    (Nat.le_ceil _) (by simp) (by simp) hbudget

theorem formalShapeOmega_dot_second_le (t : ℝ≥0) :
    formalShapeOmega F 0 t 0 ≤ (t : ℝ) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N, hN, hbudget⟩ := dot_seed_budget t ε hε
  have hNone : 1 ≤ N := by omega
  apply formalShapeOmega_le_of_rank_seed hN Nat.zero_lt_one
    (lt_of_lt_of_le Nat.zero_lt_one (one_le_innerSize hNone t))
    Nat.zero_lt_one (rankAtMost_matrix_dot_second (innerSize N t))
    (by simp) (Nat.le_ceil _) (by simp) hbudget

theorem formalShapeOmega_dot_third_le (t : ℝ≥0) :
    formalShapeOmega F 0 0 t ≤ (t : ℝ) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N, hN, hbudget⟩ := dot_seed_budget t ε hε
  have hNone : 1 ≤ N := by omega
  apply formalShapeOmega_le_of_rank_seed hN Nat.zero_lt_one Nat.zero_lt_one
    (lt_of_lt_of_le Nat.zero_lt_one (one_le_innerSize hNone t))
    (rankAtMost_matrix_dot_third (innerSize N t))
    (by simp) (by simp) (Nat.le_ceil _) hbudget

/-- Increasing one shape coordinate costs at most the added coordinate. -/
theorem formalShapeOmega_add_first_le (a b c t : ℝ≥0) :
    formalShapeOmega F (a + t) b c ≤ formalShapeOmega F a b c + (t : ℝ) := by
  have h := formalShapeOmega_add_le (F := F) a b c t 0 0
  simpa only [add_zero] using h.trans
    (add_le_add le_rfl (formalShapeOmega_dot_first_le (F := F) t))

theorem formalShapeOmega_add_second_le (a b c t : ℝ≥0) :
    formalShapeOmega F a (b + t) c ≤ formalShapeOmega F a b c + (t : ℝ) := by
  have h := formalShapeOmega_add_le (F := F) a b c 0 t 0
  simpa only [add_zero] using h.trans
    (add_le_add le_rfl (formalShapeOmega_dot_second_le (F := F) t))

theorem formalShapeOmega_add_third_le (a b c t : ℝ≥0) :
    formalShapeOmega F a b (c + t) ≤ formalShapeOmega F a b c + (t : ℝ) := by
  have h := formalShapeOmega_add_le (F := F) a b c 0 0 t
  simpa only [add_zero] using h.trans
    (add_le_add le_rfl (formalShapeOmega_dot_third_le (F := F) t))

end BlockIdentities.Arithmetic
