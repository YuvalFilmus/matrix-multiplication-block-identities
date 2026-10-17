/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Square.MatrixRateLimits
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

/-! Exact quotient/remainder reindexing of matrix-dimension rates. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open Filter
open scoped Topology

theorem natDiv_tendsto_atTop (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => n / k) atTop atTop :=
  Nat.tendsto_div_const_atTop (by omega)

/-- Bounded integer remainders have zero linear rate. -/
theorem natMod_div_tendsto_zero (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => ((n % k : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n : ℕ => (k : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (k : ℝ)) atTop (𝓝 (k : ℝ))).div_atTop
      tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply Eventually.of_forall
    intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact_mod_cast (Nat.mod_lt n (show 0 < k by omega)).le

/-- Exact natural division has the expected linear rate, by its bounded remainder. -/
theorem natDiv_div_tendsto (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => ((n / k : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 (1 / (k : ℝ))) := by
  have hrem := natMod_div_tendsto_zero k hk
  have hlim : Tendsto (fun n : ℕ =>
      (1 - ((n % k : ℕ) : ℝ) / (n : ℝ)) / (k : ℝ)) atTop (𝓝 (1 / (k : ℝ))) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (𝓝 1)).sub hrem).div_const (k : ℝ)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hsplit : (k : ℝ) * ((n / k : ℕ) : ℝ) + ((n % k : ℕ) : ℝ) = n := by
    have hnat : k * (n / k) + n % k = n := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod n k
    exact_mod_cast hnat
  change (1 - ((n % k : ℕ) : ℝ) / (n : ℝ)) / (k : ℝ) =
    ((n / k : ℕ) : ℝ) / (n : ℝ)
  field_simp [ne_of_gt hkpos, ne_of_gt hnpos]
  nlinarith [hsplit]

/-- An arbitrary, possibly nonmonotone, schedule with rate L has rate L/k
when sampled at the actual integer quotient n/k and normalized by n. -/
theorem rate_comp_natDiv (u : ℕ → ℝ) (L : ℝ)
    (hu : Tendsto (fun j : ℕ => u j / (j : ℝ)) atTop (𝓝 L))
    (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => u (n / k) / (n : ℝ)) atTop (𝓝 (L / (k : ℝ))) := by
  have hf := natDiv_tendsto_atTop k hk
  have hprod := (hu.comp hf).mul (natDiv_div_tendsto k hk)
  have hlim : Tendsto (fun n : ℕ =>
      (u (n / k) / ((n / k : ℕ) : ℝ)) * (((n / k : ℕ) : ℝ) / (n : ℝ)))
      atTop (𝓝 (L / (k : ℝ))) := by
    simpa only [Function.comp_apply, one_div, div_eq_mul_inv, one_mul] using hprod
  apply hlim.congr'
  filter_upwards [hf.eventually (eventually_ge_atTop (1 : ℕ)),
    eventually_ge_atTop (1 : ℕ)] with n hquot hn
  have hqpos : 0 < ((n / k : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hquot)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  change (u (n / k) / ((n / k : ℕ) : ℝ)) * (((n / k : ℕ) : ℝ) / (n : ℝ)) =
    u (n / k) / (n : ℝ)
  field_simp [ne_of_gt hqpos, ne_of_gt hnpos] <;> ring

/-- Strictly smaller square dimensions fit the quotient-reindexed output
schedule at every sufficiently large total power, without schedule monotonicity. -/
theorem eventually_natFloor_pow_le_division (d : ℕ → ℕ) (hd : ∀ j, 1 ≤ d j)
    {L : ℝ} (hRate : Tendsto (fun j : ℕ => Real.log (d j : ℝ) / (j : ℝ))
      atTop (𝓝 L)) (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr : 1 ≤ r)
    (hmargin : Real.log r < L / (k : ℝ)) :
    ∀ᶠ n : ℕ in atTop, Nat.floor (r ^ n) ≤ d (n / k) := by
  have hleft := tendsto_log_natFloor_pow_div r hr
  have hright := rate_comp_natDiv (fun j => Real.log (d j : ℝ)) L hRate k hk
  filter_upwards [hleft.eventually_lt hright hmargin, eventually_ge_atTop (1 : ℕ)]
    with n hlog hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hfloorpos : 0 < (Nat.floor (r ^ n) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_natFloor_pow r hr n))
  have hdpos : 0 < (d (n / k) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hd (n / k)))
  have hlogs := (div_lt_div_iff_of_pos_right hnpos).1 hlog
  have hreal := (Real.log_lt_log_iff hfloorpos hdpos).1 hlogs
  exact_mod_cast hreal.le

end BlockIdentities.Square
