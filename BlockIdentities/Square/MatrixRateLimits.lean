/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Exact exponential rates and strict margins after natural-number flooring. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open Filter
open scoped Topology

/-- On the positive source domain, flooring loses at most a factor of two.
This bound also handles x=1 and therefore avoids a separate growth assumption. -/
theorem half_le_natFloor (x : ℝ) (hx : 1 ≤ x) : x / 2 ≤ (Nat.floor x : ℝ) := by
  have hfloor : (1 : ℝ) ≤ Nat.floor x := by
    exact_mod_cast (Nat.one_le_floor_iff x).2 hx
  have hlt := Nat.lt_floor_add_one x
  linarith

/-- Every rounded power has at least one copy, including at exponent zero. -/
theorem one_le_natFloor_pow (α : ℝ) (hα : 1 ≤ α) (n : ℕ) :
    1 ≤ Nat.floor (α ^ n) :=
  (Nat.one_le_floor_iff _).2 (one_le_pow₀ hα)

/-- Natural flooring preserves the exponential logarithmic rate. The same
factor-two squeeze covers α=1 and α>1 without exceptional zero floors. -/
theorem tendsto_log_natFloor_pow_div (α : ℝ) (hα : 1 ≤ α) :
    Tendsto (fun n : ℕ => Real.log (Nat.floor (α ^ n) : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log α)) := by
  have hαpos : 0 < α := lt_of_lt_of_le zero_lt_one hα
  have hsmall : Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log 2) atTop (𝓝 (Real.log 2))).div_atTop
      tendsto_natCast_atTop_atTop
  have hlower : Tendsto (fun n : ℕ => Real.log α - Real.log 2 / (n : ℝ))
      atTop (𝓝 (Real.log α)) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log α)
      atTop (𝓝 (Real.log α))).sub hsmall
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hpow : 1 ≤ α ^ n := one_le_pow₀ hα
    have hlog := Real.log_le_log (div_pos (pow_pos hαpos n) (by norm_num))
      (half_le_natFloor (α ^ n) hpow)
    rw [Real.log_div (ne_of_gt (pow_pos hαpos n)) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_pow] at hlog
    calc
      _ = ((n : ℝ) * Real.log α - Real.log 2) / n := by
        field_simp [ne_of_gt hnpos] <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right hlog hnpos.le
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hfloorpos : 0 < (Nat.floor (α ^ n) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_natFloor_pow α hα n))
    have hlog := Real.log_le_log hfloorpos (Nat.floor_le (pow_nonneg hαpos.le n))
    rw [Real.log_pow] at hlog
    calc
      _ ≤ ((n : ℝ) * Real.log α) / n := div_le_div_of_nonneg_right hlog hnpos.le
      _ = _ := by field_simp [ne_of_gt hnpos] <;> ring

/-- A strict exponential product margin eventually survives flooring all three
factors. No equality-boundary claim is made. -/
theorem eventually_natFloor_pow_le_product (a b c : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hmargin : c < a * b) :
    ∀ᶠ n : ℕ in atTop,
      Nat.floor (c ^ n) ≤ Nat.floor (a ^ n) * Nat.floor (b ^ n) := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hratio : 1 < (a * b) / c := (lt_div_iff₀ hcpos).2 (by simpa using hmargin)
  have ht : Tendsto (fun n : ℕ => ((a * b) / c) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hratio
  filter_upwards [ht.eventually (eventually_ge_atTop (4 : ℝ))] with n hn
  have hleft := half_le_natFloor (a ^ n) (one_le_pow₀ ha)
  have hright := half_le_natFloor (b ^ n) (one_le_pow₀ hb)
  have hproduct := mul_le_mul hleft hright
    (div_nonneg (pow_nonneg (zero_le_one.trans hb) n) (by norm_num))
    (Nat.cast_nonneg (Nat.floor (a ^ n)))
  have hcnpos : 0 < c ^ n := pow_pos hcpos n
  rw [div_pow, mul_pow] at hn
  have hfour : 4 * c ^ n ≤ a ^ n * b ^ n := (le_div_iff₀ hcnpos).1 hn
  apply Nat.floor_le_of_le
  push_cast
  nlinarith [hproduct, hfour]

end BlockIdentities.Square
