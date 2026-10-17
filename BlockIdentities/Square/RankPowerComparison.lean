/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-! The scalar logarithmic comparison after actual tensor bounds are supplied. -/
@[expose] public section
namespace BlockIdentities.Square

theorem exponent_le_of_rank_power_bound (ν d r L : ℝ) (hν : 0 < ν)
    (hd : 0 < d) (hr : 0 < r) (hL : d⁻¹ < L)
    (hbound : L * d ≤ r ^ (3 / ν)) :
    ν ≤ 3 * Real.log r / (Real.log d + Real.log L) := by
  have hLp : 0 < L := lt_trans (inv_pos.mpr hd) hL
  have hprod : 1 < L * d := by
    have hm := mul_lt_mul_of_pos_right hL hd
    simpa only [inv_mul_cancel₀ (ne_of_gt hd)] using hm
  have hden : 0 < Real.log d + Real.log L := by
    have hh := Real.log_pos hprod
    rw [Real.log_mul (ne_of_gt hLp) (ne_of_gt hd)] at hh
    linarith
  have hlog := Real.log_le_log (mul_pos hLp hd) hbound
  rw [Real.log_mul (ne_of_gt hLp) (ne_of_gt hd), Real.log_rpow hr] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog hν.le
  have hid : ν * ((3 / ν) * Real.log r) = 3 * Real.log r := by
    field_simp [ne_of_gt hν] <;> ring
  rw [hid] at hm
  apply (le_div_iff₀ hden).2
  nlinarith

end BlockIdentities.Square
