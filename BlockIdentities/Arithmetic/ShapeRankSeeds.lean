/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.RectangularProgramRank
public import BlockIdentities.Arithmetic.RectangularGrowth
public import BlockIdentities.Arithmetic.ShapeMonotonicity

/-! Genuine common-size finite rank seeds characterize the formal shape exponent. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Arithmetic
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped NNReal
variable {F : Type*} [Field F]

/-- An actual fixed coefficient rank seed yields an upper bound on the actual
formal shape exponent through formally correct recursive algorithms. -/
theorem formalShapeOmega_le_of_rank_seed
    {N a b c R : ℕ} (hN : 2 ≤ N)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hRank : Tensor.RankAtMost (matrixMultiplicationTensor (K := F) a b c) R)
    {α β γ : ℝ≥0} {τ : ℝ}
    (hα : (N : ℝ) ^ (α : ℝ) ≤ a)
    (hβ : (N : ℝ) ^ (β : ℝ) ≤ b)
    (hγ : (N : ℝ) ^ (γ : ℝ) ≤ c)
    (hR : (R : ℝ) ≤ (N : ℝ) ^ τ) :
    formalShapeOmega F α β γ ≤ τ :=
  csInf_le (formalShapeAdmissibleExponent_bddBelow _ _ _)
    (formalShapeAdmissibleExponent_of_rank_seed hN ha hb hc hRank hα hβ hγ hR)

/-- Every admissible program family supplies actual finite rank decompositions
at every sufficiently large common integer size. The rank cost factor2 is
absorbed into a fixed threshold before any size is chosen. -/
theorem FormalShapeAdmissibleExponent.eventually_rank_seed
    {a b c : ℝ≥0} {τ : ℝ} (h : FormalShapeAdmissibleExponent F a b c τ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∃ R : ℕ,
      Tensor.RankAtMost (matrixMultiplicationTensor (K := F)
        (innerSize N a) (innerSize N b) (innerSize N c)) R ∧
      (R : ℝ) ≤ (N : ℝ) ^ (τ + ε) := by
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨C, hC, hcost⟩ := h δ hδ
  have h2C : 0 < 2 * C := mul_pos (by norm_num) hC
  obtain ⟨N0, hN0⟩ := exists_nat_gt (max ((2 * C) ^ δ⁻¹) 2)
  have hN0two : 2 ≤ N0 := by
    have hh : (2 : ℝ) < N0 := lt_of_le_of_lt (le_max_right _ _) hN0
    exact_mod_cast hh.le
  refine ⟨N0, hN0two, ?_⟩
  intro N hN
  have hNtwo : 2 ≤ N := hN0two.trans hN
  have hNone : 1 ≤ N := by omega
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hthreshold : (2 * C) ^ δ⁻¹ < (N : ℝ) :=
    (lt_of_le_of_lt (le_max_left _ _) hN0).trans_le (by exact_mod_cast hN)
  have hfactor : 2 * C < (N : ℝ) ^ δ :=
    (Real.rpow_inv_lt_iff_of_pos h2C.le (Nat.cast_nonneg N) hδ).mp hthreshold
  obtain ⟨P, hP, hp⟩ := hcost N hNone
  refine ⟨2 * P.cost, rectangular_matrix_rankAtMost_of_formalCorrect P hP, ?_⟩
  calc
    ((2 * P.cost : ℕ) : ℝ) = 2 * (P.cost : ℝ) := by simp only [Nat.cast_mul, Nat.cast_ofNat]
    _ ≤ (2 * C) * (N : ℝ) ^ (τ + δ) := by
      have hh := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
      simpa only [mul_assoc] using hh
    _ ≤ (N : ℝ) ^ δ * (N : ℝ) ^ (τ + δ) :=
      mul_le_mul_of_nonneg_right hfactor.le (Real.rpow_nonneg hNpos.le _)
    _ = (N : ℝ) ^ (τ + ε) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      dsimp only [δ]
      ring

/-- The actual infimum itself supplies these same-size exact coefficient seeds. -/
theorem formalShapeOmega_eventually_rank_seed (a b c : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∃ R : ℕ,
      Tensor.RankAtMost (matrixMultiplicationTensor (K := F)
        (innerSize N a) (innerSize N b) (innerSize N c)) R ∧
      (R : ℝ) ≤ (N : ℝ) ^ (formalShapeOmega F a b c + ε) :=
  (formalShapeAdmissibleExponent_formalShapeOmega (F := F) a b c).eventually_rank_seed ε hε

/-- Rank seeds at arbitrary positive slack characterize the formal exponent.
They are actual finite decompositions, without a rank characterization premise. -/
theorem formalShapeOmega_le_iff_rank_seeds (a b c : ℝ≥0) (τ : ℝ) :
    formalShapeOmega F a b c ≤ τ ↔
      ∀ ε : ℝ, 0 < ε → ∃ N R : ℕ, 2 ≤ N ∧
        Tensor.RankAtMost (matrixMultiplicationTensor (K := F)
          (innerSize N a) (innerSize N b) (innerSize N c)) R ∧
        (R : ℝ) ≤ (N : ℝ) ^ (τ + ε) := by
  constructor
  · intro h ε hε
    obtain ⟨N0, hN0, hseed⟩ :=
      (formalShapeAdmissibleExponent_of_omega_le h).eventually_rank_seed ε hε
    obtain ⟨R, hrank, hR⟩ := hseed N0 le_rfl
    exact ⟨N0, R, hN0, hrank, hR⟩
  · intro h
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨N, R, hN, hrank, hR⟩ := h ε hε
    have hNone : 1 ≤ N := by omega
    exact formalShapeOmega_le_of_rank_seed hN
      (lt_of_lt_of_le Nat.zero_lt_one (one_le_innerSize hNone a))
      (lt_of_lt_of_le Nat.zero_lt_one (one_le_innerSize hNone b))
      (lt_of_lt_of_le Nat.zero_lt_one (one_le_innerSize hNone c)) hrank
      (Nat.le_ceil _) (Nat.le_ceil _) (Nat.le_ceil _) hR
end BlockIdentities.Arithmetic
