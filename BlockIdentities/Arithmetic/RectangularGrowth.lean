/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.RectangularRecursion
public import BlockIdentities.Rectangular.Definitions

/-! Fixed finite rectangular rank seeds give formally correct shape algorithms
by geometric growth and finite padding. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Arithmetic
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped NNReal
variable {F : Type*} [Field F]

private theorem innerSize_le_seed_power {N a n : ℕ} {α : ℝ≥0}
    (hN : 0 < N) (ha : (N : ℝ) ^ (α : ℝ) ≤ a)
    {k : ℕ} (hnk : n ≤ N ^ k) : innerSize n α ≤ a ^ k := by
  apply Nat.ceil_le.mpr
  calc
    (n : ℝ) ^ (α : ℝ) ≤ ((N ^ k : ℕ) : ℝ) ^ (α : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hnk) α.property
    _ = ((N : ℝ) ^ (α : ℝ)) ^ k := by
      rw [Nat.cast_pow, Real.rpow_pow_comm (by exact_mod_cast hN.le)]
    _ ≤ (a : ℝ) ^ k := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) ha k
    _ = ((a ^ k : ℕ) : ℝ) := (Nat.cast_pow a k).symm

/-- A rank seed whose literal dimensions dominate a fixed shape supplies the
approved formal shape admissibility predicate. Constants may depend on the seed,
field and positive slack, but precede every input size. -/
theorem formalShapeAdmissibleExponent_of_rank_seed
    {N a b c R : ℕ} (hN : 2 ≤ N)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hRank : Tensor.RankAtMost (matrixMultiplicationTensor (K := F) a b c) R)
    {α β γ : ℝ≥0} {τ : ℝ}
    (hα : (N : ℝ) ^ (α : ℝ) ≤ a)
    (hβ : (N : ℝ) ^ (β : ℝ) ≤ b)
    (hγ : (N : ℝ) ^ (γ : ℝ) ≤ c)
    (hR : (R : ℝ) ≤ (N : ℝ) ^ τ) :
    FormalShapeAdmissibleExponent F α β γ τ := by
  have hNpos : 0 < N := by omega
  have hNreal : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  obtain ⟨hab, _, _⟩ := Square.matrix_rankAtMost_entry_counts ha hb hc hRank
  have hRone : 1 ≤ R := (Nat.mul_pos ha hb).trans_le hab
  have hτ : 0 ≤ τ := by
    by_contra hneg
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg hNreal (lt_of_not_ge hneg)
    have hone : (1 : ℝ) ≤ R := by exact_mod_cast hRone
    linarith
  intro ε hε
  let q : ℝ := (N : ℝ) ^ (τ + ε)
  have hRq : (R : ℝ) < q := hR.trans_lt
    (Real.rpow_lt_rpow_of_exponent_lt hNreal (by linarith))
  let x : ℕ → ℝ := fun k => (6 * (R : ℝ) + 1) * ((k : ℝ) + 1) * (R : ℝ) ^ k
  obtain ⟨C, hC, hbound⟩ := geometric_cost_recurrence_bound x (R : ℝ)
    ((6 * (R : ℝ) + 1) * R) (R : ℝ) q
    (by dsimp [x]; positivity) (Nat.cast_nonneg _) (by positivity)
    (Nat.cast_nonneg _) hRq hRq.le (fun k => by
      dsimp [x]
      rw [Nat.cast_add, Nat.cast_one, pow_succ]
      exact le_of_eq (by ring))
  refine ⟨C * (N : ℝ) ^ (τ + ε),
    mul_pos hC (Real.rpow_pos_of_pos (by exact_mod_cast hNpos) _), ?_⟩
  intro n hn
  obtain ⟨k, hnk, hkn⟩ := exists_power_cover hN hn
  obtain ⟨P, hP, hcost⟩ := formal_rectangular_power_programs ha hb hc hRank k
  have hpa := innerSize_le_seed_power hNpos hα hnk
  have hpb := innerSize_le_seed_power hNpos hβ hnk
  have hpc := innerSize_le_seed_power hNpos hγ hnk
  refine ⟨P.pad hpa hpb hpc, hP.pad hpa hpb hpc, ?_⟩
  rw [MatrixAlgorithm.pad_cost_eq]
  have hcostreal : (P.cost : ℝ) ≤ x k := by
    dsimp [x]
    exact_mod_cast hcost
  calc
    (P.cost : ℝ) ≤ C * q ^ k := hcostreal.trans (hbound k)
    _ = C * ((N ^ k : ℕ) : ℝ) ^ (τ + ε) := by
      dsimp [q]
      rw [Real.rpow_pow_comm (Nat.cast_nonneg _), Nat.cast_pow]
    _ ≤ C * ((N : ℝ) * n) ^ (τ + ε) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkn)
          (by linarith)) hC.le
    _ = (C * (N : ℝ) ^ (τ + ε)) * (n : ℝ) ^ (τ + ε) := by
      rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      ring

end BlockIdentities.Arithmetic
