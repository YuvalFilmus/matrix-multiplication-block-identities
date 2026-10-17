/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Square.Yield
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.OrderClosed

@[expose] public section

namespace BlockIdentities.Square

open Filter
open scoped Topology

/-- The logarithmic ratio used in the final square-certificate limit. -/
theorem tendsto_log_square_ratio :
    Tendsto (fun a : ℕ => Real.log (2 * (a : ℝ) - 1) / Real.log a)
      atTop (𝓝 1) := by
  have hlog : Tendsto (fun a : ℕ => Real.log (a : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun a : ℕ => Real.log 2 / Real.log (a : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log 2) atTop (𝓝 (Real.log 2))).div_atTop hlog
  have hu : Tendsto (fun a : ℕ => 1 + Real.log 2 / Real.log (a : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (𝓝 1)).add hdiv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with a ha
    have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
    have hapos : 0 < (a : ℝ) := by linarith
    have hlpos : 0 < Real.log (a : ℝ) := Real.log_pos (by linarith)
    apply (le_div_iff₀ hlpos).2
    simpa using Real.log_le_log hapos (show (a : ℝ) ≤ 2 * a - 1 by linarith)
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with a ha
    have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
    have hapos : 0 < (a : ℝ) := by linarith
    have hlpos : 0 < Real.log (a : ℝ) := Real.log_pos (by linarith)
    have hlogs := Real.log_le_log (show 0 < 2 * (a : ℝ) - 1 by linarith)
      (show 2 * (a : ℝ) - 1 ≤ 2 * a by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hapos)] at hlogs
    calc
      _ ≤ (Real.log 2 + Real.log (a : ℝ)) / Real.log a :=
        div_le_div_of_nonneg_right hlogs hlpos.le
      _ = _ := by field_simp [ne_of_gt hlpos]; ring

/-- Logarithmic form of the explicit terminal-yield growth bound. -/
theorem convolutionYield_log_lower (a : {n : ℕ // 2 ≤ n}) :
    (4 / 3 : ℝ) * Real.log (a.val : ℝ) ≤
      Real.log 2 + Real.log (convolutionYield a) := by
  have ha : (2 : ℝ) ≤ a.val := by exact_mod_cast a.property
  have hapos : 0 < (a.val : ℝ) := by linarith
  have hL := convolutionYield_pos a
  have hgrowth := convolutionYield_cube_lower a
  have hlog := Real.log_le_log (pow_pos hapos 4) hgrowth
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0)
    (pow_ne_zero 3 (ne_of_gt hL)), Real.log_pow, Real.log_pow] at hlog
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
  rw [h8] at hlog
  norm_num at hlog
  linarith

/-- The finite-certificate denominator is strictly positive on its source domain. -/
theorem convolutionYield_log_pos (a : {n : ℕ // 2 ≤ n}) :
    0 < Real.log 2 + Real.log (convolutionYield a) := by
  have ha : (2 : ℝ) ≤ a.val := by exact_mod_cast a.property
  have hlog : 0 < Real.log (a.val : ℝ) := Real.log_pos (by linarith)
  have hbound := convolutionYield_log_lower a
  linarith

/-- The explicit yield strictly exceeds the terminal threshold for dimension two. -/
theorem convolutionYield_gt_half (a : {n : ℕ // 2 ≤ n}) :
    (1 : ℝ) / 2 < convolutionYield a := by
  have ha : (2 : ℝ) ≤ a.val := by exact_mod_cast a.property
  have hL := convolutionYield_pos a
  have hbound := convolutionYield_cube_lower a
  by_contra! hle
  have hcube := pow_le_pow_left₀ hL.le hle 3
  have hfour := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ha 4
  norm_num at hcube hfour
  nlinarith

/-- Internal scalar closure of the finite-cutoff numerical bounds. This does not
assert that a tensor exponent satisfies the supplied inequalities. -/
theorem le_nine_fourths_of_finite_certificate_bounds (x : ℝ)
    (h : ∀ a : {n : ℕ // 2 ≤ n},
      x ≤ 3 * Real.log (2 * (a.val : ℝ) - 1) /
        (Real.log 2 + Real.log (convolutionYield a))) : x ≤ 9 / 4 := by
  have hlim : Tendsto (fun a : ℕ => (9 / 4 : ℝ) *
      (Real.log (2 * (a : ℝ) - 1) / Real.log a)) atTop (𝓝 (9 / 4)) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (9 / 4 : ℝ))
      atTop (𝓝 (9 / 4 : ℝ))).mul tendsto_log_square_ratio
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with a ha
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hlpos : 0 < Real.log (a : ℝ) := Real.log_pos (by linarith)
  have hlower := convolutionYield_log_lower ⟨a, ha⟩
  have hnum : 0 ≤ 3 * Real.log (2 * (a : ℝ) - 1) := by
    have : 0 ≤ Real.log (2 * (a : ℝ) - 1) := Real.log_nonneg (by linarith)
    positivity
  calc
    x ≤ _ := h ⟨a, ha⟩
    _ ≤ (3 * Real.log (2 * (a : ℝ) - 1)) / ((4 / 3 : ℝ) * Real.log a) :=
      div_le_div_of_nonneg_left hnum (by positivity) hlower
    _ = _ := by field_simp [ne_of_gt hlpos]; ring

end BlockIdentities.Square
