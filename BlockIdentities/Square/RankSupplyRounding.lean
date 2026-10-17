/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Square.AbsorptionRounding
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankExponent

/-! One fixed finite rank decomposition supplies rounded matrix dimensions. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open Filter
open scoped Topology BigOperators

variable {K : Type*} [Field K]

/-- Reindex an actual tensor-power decomposition as one matrix dimension.
This is finite coefficient algebra, with no rank-growth premise. -/
private theorem rank_power_bound {b R : ℕ}
    (hRank : Tensor.RankAtMost (matrixMultiplicationTensor (K := K) b b b) R)
    (j : ℕ) : exactMatrixRank K (b ^ j) ≤ R ^ j := by
  classical
  let e : Fin (b ^ j) ≃ (Fin j → Fin b) := Fintype.equivOfCardEq (by simp)
  let f : Fin (b ^ j) × Fin (b ^ j) → Fin j → Fin b × Fin b :=
    fun x i => (e x.1 i, e x.2 i)
  have hp := (hRank.power j).pullback f f f
  have heq : Tensor.pullback f f f (Tensor.power
      (matrixMultiplicationTensor (K := K) b b b) j) =
      matrixMultiplicationTensor (K := K) (b ^ j) (b ^ j) (b ^ j) := by
    funext x y z
    simp only [Tensor.pullback, Tensor.power, matrixMultiplicationTensor, f,
      Fintype.prod_boole, forall_and, ← funext_iff, e.injective.eq_iff]
  rw [heq] at hp
  exact exactRank_le hp

/-- A finite exact decomposition supplies scalar-budget matrix products at
the requested positive-slack exponent rate over every field. The one block
and all its coefficients are fixed before the budget exponent j varies. -/
theorem exists_matrix_rank_supply (h : ℕ) (hh : 2 ≤ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ → ℕ, (∀ j, 1 ≤ N j) ∧
      (∀ j, exactMatrixRank K (N j) ≤ h ^ j) ∧
      Tendsto (fun j : ℕ => Real.log (N j : ℝ) / (j : ℝ)) atTop
        (𝓝 (Real.log (h : ℝ) / (exactRankExponent K + ε))) := by
  obtain ⟨b, R, hb, hRank, hR⟩ := exists_rankAtMost_of_exponent_slack (K := K) hε
  let τ := exactRankExponent K + ε
  have hτpos : 0 < τ := by
    have hν := exactRankExponent_lower (K := K)
    dsimp only [τ]
    linarith
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hbone : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hblog : 0 < Real.log (b : ℝ) := Real.log_pos hbone
  have hhlog : 0 < Real.log (h : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < h by omega))
  have hRlower := matrixMultiplication_rank_lower (K := K) (show 0 < b by omega) hRank
  have hRpos : 0 < (R : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (pow_pos (show 0 < b by omega) 2) hRlower)
  let θ := Real.log (h : ℝ) / (τ * Real.log (b : ℝ))
  have hdenpos : 0 < τ * Real.log (b : ℝ) := mul_pos hτpos hblog
  have hθpos : 0 < θ := div_pos hhlog hdenpos
  let k : ℕ → ℕ := fun j => Nat.floor (θ * (j : ℝ))
  let N : ℕ → ℕ := fun j => b ^ k j
  have hθeq : θ * (τ * Real.log (b : ℝ)) = Real.log (h : ℝ) := by
    dsimp only [θ]
    field_simp [ne_of_gt hdenpos]
  have hRlog : Real.log (R : ℝ) ≤ τ * Real.log (b : ℝ) := by
    have hc := Real.log_le_log hRpos hR
    rw [Real.log_rpow hbpos] at hc
    exact hc
  refine ⟨N, ?_, ?_, ?_⟩
  · intro j
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  · intro j
    have hk : (k j : ℝ) ≤ θ * (j : ℝ) :=
      Nat.floor_le (mul_nonneg hθpos.le (Nat.cast_nonneg j))
    have hsmall := mul_le_mul_of_nonneg_left hRlog (Nat.cast_nonneg (k j))
    have hbig := mul_le_mul_of_nonneg_right hk hdenpos.le
    have hlogs : (k j : ℝ) * Real.log (R : ℝ) ≤ (j : ℝ) * Real.log (h : ℝ) := by
      nlinarith [hsmall, hbig, congrArg (fun x : ℝ => x * (j : ℝ)) hθeq]
    have hbudget : (R : ℝ) ^ k j ≤ (h : ℝ) ^ j := by
      apply (Real.log_le_log_iff (pow_pos hRpos _) (pow_pos (by
        exact_mod_cast (show 0 < h by omega)) _)).1
      simpa only [Real.log_pow] using hlogs
    have hbudgetNat : R ^ k j ≤ h ^ j := by exact_mod_cast hbudget
    exact (rank_power_bound hRank (k j)).trans hbudgetNat
  · have hlim := (floor_linear_div_tendsto θ hθpos.le).mul_const (Real.log (b : ℝ))
    have hrate : θ * Real.log (b : ℝ) = Real.log (h : ℝ) / τ := by
      dsimp only [θ]
      field_simp [ne_of_gt hτpos, ne_of_gt hblog] <;> ring
    rw [hrate] at hlim
    apply hlim.congr'
    apply Eventually.of_forall
    intro j
    simp only [N, k, Nat.cast_pow, Real.log_pow]
    ring

end BlockIdentities.Square
