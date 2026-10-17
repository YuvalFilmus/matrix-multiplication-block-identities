/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Square.MatrixRateLimits
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Rounded square-matrix dimensions give the literal ordinary-value rate. -/

@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open Filter
open scoped Topology

/-- The literal symmetrized matrix candidate is positive at every index,
including zero (whose outer real exponent is zero). -/
theorem matrixValueGain_natFloor_pow_pos (s : ℝ) (hs : 1 ≤ s) (ρ : ℝ) (n : ℕ) :
    0 < (((Nat.floor (s ^ n) ^ 3 : ℕ) : ℝ) ^ ρ) ^ (1 / (3 * (n : ℝ))) := by
  have hf : 0 < (Nat.floor (s ^ n) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_natFloor_pow s hs n))
  apply Real.rpow_pos_of_pos
  apply Real.rpow_pos_of_pos
  simpa only [Nat.cast_pow] using pow_pos hf 3

/-- Exponential flooring loses no ordinary-value rate. The real exponent may
be arbitrary; source applications specialize it to the interval [2,3]. -/
theorem tendsto_matrixValueGain_natFloor_pow (s : ℝ) (hs : 1 ≤ s) (ρ : ℝ) :
    Tendsto (fun n : ℕ =>
      (((Nat.floor (s ^ n) ^ 3 : ℕ) : ℝ) ^ ρ) ^ (1 / (3 * (n : ℝ))))
      atTop (𝓝 (s ^ ρ)) := by
  have hlog := (tendsto_log_natFloor_pow_div s hs).mul_const ρ
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlog
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  rw [← Real.rpow_def_of_pos hspos ρ] at hexp
  apply hexp.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hf : 0 < (Nat.floor (s ^ n) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_natFloor_pow s hs n))
  have hcube : 0 < ((Nat.floor (s ^ n) ^ 3 : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow] using pow_pos hf 3
  change Real.exp (Real.log (Nat.floor (s ^ n) : ℝ) / (n : ℝ) * ρ) =
    (((Nat.floor (s ^ n) ^ 3 : ℕ) : ℝ) ^ ρ) ^ (1 / (3 * (n : ℝ)))
  rw [Real.rpow_def_of_pos (Real.rpow_pos_of_pos hcube ρ),
    Real.log_rpow hcube, Nat.cast_pow, Real.log_pow]
  congr 1
  field_simp [ne_of_gt hnpos] <;> ring

end BlockIdentities.Square
