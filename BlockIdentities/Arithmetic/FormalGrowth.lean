/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Finite recurrence estimates adapted from Navot's Arithmetic/Growth.lean;
upstream OpenAI provenance and Apache-2.0 license retained.
-/
module

public import BlockIdentities.Arithmetic.FormalPadding
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Growth

/-! Finite coefficient-rank decompositions yield formally correct algorithms.
Only the predicates carried by finite recursion and padding differ from upstream;
the scalar geometric recurrence and operation counts are unchanged. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Arithmetic

open OAI.MatrixMultiplication.Arithmetic
open OAI.MatrixMultiplication.Foundation
open scoped BigOperators

variable {F : Type*} [Field F]

/-- The three-register scalar multiplication program is formally correct. -/
theorem scalarAlgorithm_formalCorrect : FormalCorrect (scalarAlgorithm F) := by
  intro i k
  have hi : i = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst i
  subst k
  simp [polynomialOutputs, scalarAlgorithm, evalProgramIn, evalGateIn]
  rfl

theorem formal_power_cost_padding_bound
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : SquareAlgorithm F m, FormalCorrect P →
      ∃ Q : SquareAlgorithm F n, FormalCorrect Q ∧ Q.cost ≤ P.cost)
    {b : ℕ} (hb : 2 ≤ b) {s C : ℝ} (hs : 0 ≤ s) (hC : 0 < C)
    (hpower : ∀ k : ℕ, ∃ P : SquareAlgorithm F (b ^ k),
      FormalCorrect P ∧ (P.cost : ℝ) ≤ C * ((b : ℝ) ^ s) ^ k) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n → ∃ P : SquareAlgorithm F n,
      FormalCorrect P ∧ (P.cost : ℝ) ≤ D * (n : ℝ) ^ s := by
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  refine ⟨C * (b : ℝ) ^ s, mul_pos hC (Real.rpow_pos_of_pos hbpos s), ?_⟩
  intro n hn
  obtain ⟨k, hnk, hkn⟩ := exists_power_cover hb hn
  obtain ⟨P, hP, hcost⟩ := hpower k
  obtain ⟨Q, hQ, hQP⟩ := hpad hnk P hP
  refine ⟨Q, hQ, ?_⟩
  calc
    (Q.cost : ℝ) ≤ (P.cost : ℝ) := by exact_mod_cast hQP
    _ ≤ C * ((b : ℝ) ^ s) ^ k := hcost
    _ = C * ((b ^ k : ℕ) : ℝ) ^ s := by
      rw [Real.rpow_pow_comm hbpos.le, Nat.cast_pow]
    _ ≤ C * ((b : ℝ) * (n : ℝ)) ^ s :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkn) hs) hC.le
    _ = (C * (b : ℝ) ^ s) * (n : ℝ) ^ s := by
      rw [Real.mul_rpow hbpos.le (Nat.cast_nonneg n)]
      ring


theorem formalAdmissibleExponent_of_power_costs
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : SquareAlgorithm F m, FormalCorrect P →
      ∃ Q : SquareAlgorithm F n, FormalCorrect Q ∧ Q.cost ≤ P.cost)
    {b : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 0 ≤ τ)
    (hpower : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, ∃ P : SquareAlgorithm F (b ^ k),
        FormalCorrect P ∧ (P.cost : ℝ) ≤ C * ((b : ℝ) ^ (τ + ε)) ^ k) :
    FormalAdmissibleExponent F τ := by
  intro ε hε
  obtain ⟨C, hC, hcost⟩ := hpower ε hε
  exact formal_power_cost_padding_bound hpad hb (by linarith) hC hcost


theorem formal_power_programs_of_block_step {b R K : ℕ}
    (hstep : ∀ m : ℕ, ∀ P : SquareAlgorithm F m, FormalCorrect P →
      ∃ Q : SquareAlgorithm F (b * m), FormalCorrect Q ∧
        Q.cost ≤ R * P.cost + K * m ^ 2) :
    ∀ k : ℕ, ∃ P : SquareAlgorithm F (b ^ k), FormalCorrect P ∧
      P.cost ≤ blockRecurrenceCost b R K k := by
  intro k
  induction k with
  | zero =>
    exact ⟨scalarAlgorithm F, scalarAlgorithm_formalCorrect (F := F), by simp⟩
  | succ k ih =>
    obtain ⟨P, hP, hcost⟩ := ih
    obtain ⟨Q, hQ, hQcost⟩ := hstep (b ^ k) P hP
    have hbound : Q.cost ≤ blockRecurrenceCost b R K (k + 1) := by
      exact hQcost.trans (Nat.add_le_add_right (Nat.mul_le_mul_left R hcost) _)
    have hresult : ∃ Q : SquareAlgorithm F (b * b ^ k), FormalCorrect Q ∧
        Q.cost ≤ blockRecurrenceCost b R K (k + 1) := ⟨Q, hQ, hbound⟩
    exact (pow_succ' b k).symm ▸ hresult


theorem formalAdmissibleExponent_of_block_step_of_padding
    (hpad : ∀ {n m : ℕ}, n ≤ m → ∀ P : SquareAlgorithm F m, FormalCorrect P →
      ∃ Q : SquareAlgorithm F n, FormalCorrect Q ∧ Q.cost ≤ P.cost)
    {b R K : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 2 ≤ τ)
    (hR : (R : ℝ) ≤ (b : ℝ) ^ τ)
    (hstep : ∀ m : ℕ, ∀ P : SquareAlgorithm F m, FormalCorrect P →
      ∃ Q : SquareAlgorithm F (b * m), FormalCorrect Q ∧
        Q.cost ≤ R * P.cost + K * m ^ 2) :
    FormalAdmissibleExponent F τ := by
  apply formalAdmissibleExponent_of_power_costs hpad hb (by linarith)
  intro ε hε
  have hbone : 1 < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hrate : (R : ℝ) < (b : ℝ) ^ (τ + ε) :=
    hR.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hbone (by linarith))
  have hquad : (b : ℝ) ^ (2 : ℕ) ≤ (b : ℝ) ^ (τ + ε) := by
    rw [← Real.rpow_natCast]
    change (b : ℝ) ^ (2 : ℝ) ≤ (b : ℝ) ^ (τ + ε)
    exact Real.rpow_le_rpow_of_exponent_le hbone.le (by linarith)
  obtain ⟨C, hC, hbound⟩ := geometric_cost_recurrence_bound
    (fun k => (blockRecurrenceCost b R K k : ℝ))
    (R : ℝ) (K : ℝ) ((b : ℝ) ^ (2 : ℕ)) ((b : ℝ) ^ (τ + ε))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (sq_nonneg _) hrate hquad (fun k => by
      simp only [blockRecurrenceCost_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2])
  refine ⟨C, hC, ?_⟩
  intro k
  obtain ⟨P, hP, hcost⟩ := formal_power_programs_of_block_step hstep k
  exact ⟨P, hP, (by exact_mod_cast hcost : (P.cost : ℝ) ≤
    (blockRecurrenceCost b R K k : ℝ)).trans (hbound k)⟩


theorem formalAdmissibleExponent_of_block_step
    {b R K : ℕ} (hb : 2 ≤ b) {τ : ℝ} (hτ : 2 ≤ τ)
    (hR : (R : ℝ) ≤ (b : ℝ) ^ τ)
    (hstep : ∀ m : ℕ, ∀ P : SquareAlgorithm F m, FormalCorrect P →
      ∃ Q : SquareAlgorithm F (b * m), FormalCorrect Q ∧
        Q.cost ≤ R * P.cost + K * m ^ 2) :
    FormalAdmissibleExponent F τ :=
  formalAdmissibleExponent_of_block_step_of_padding
    (fun h P hP => ⟨P.pad h h h, hP.pad h h h, (MatrixAlgorithm.pad_cost_eq h h h P).le⟩) hb hτ hR hstep


theorem formalAdmissibleExponent_of_rankAtMost {n R : ℕ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matrixCoefficients (K := F) (Fin n) (Fin n) (Fin n)) R)
    {τ : ℝ} (hτ : 2 ≤ τ) (hR : (R : ℝ) ≤ (n : ℝ) ^ τ) :
    FormalAdmissibleExponent F τ := by
  apply formalAdmissibleExponent_of_block_step (K := 6 * R * n ^ 2) hn hτ hR
  intro m P hP
  rcases hRank with ⟨a, b, c, h⟩
  refine ⟨RecursiveBlock.algorithm a b c P, recursiveAlgorithm_formalCorrect a b c h P hP, ?_⟩
  rw [RecursiveBlock.algorithm_cost]
  exact le_of_eq (by ring)


end BlockIdentities.Arithmetic
