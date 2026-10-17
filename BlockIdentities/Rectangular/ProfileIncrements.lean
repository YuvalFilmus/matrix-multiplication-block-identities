/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.AngularOffsets
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The source finite-increment product bound implies the actual ratio
inequality by a right logarithmic derivative at zero. -/
@[expose] public section
noncomputable section
open Filter Topology
namespace BlockIdentities.Rectangular

private theorem right_derivative_nonneg {f : ℝ → ℝ} {D : ℝ}
    (hd : HasDerivAt f D 0) (hzero : f 0 = 0)
    (hn : ∀ ε : ℝ, 0 < ε → 0 ≤ f ε) : 0 ≤ D := by
  have hlim := hd.tendsto_slope_zero_right
  simp only [zero_add, hzero, sub_zero, smul_eq_mul] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := hε
  exact mul_nonneg (inv_nonneg.mpr hεpos.le) (hn ε hεpos)

/-- Genuine finite-increment product bounds force the source ratio inequality.
There is no ratio, quadratic, or angular conclusion among the assumptions. -/
theorem profile_ratio_of_finite_increment {p q c d r s : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hr : 0 < r) (hs : 0 < s)
    (hfinite : ∀ ε : ℝ, 0 < ε →
      (1 + ε * r / (r + d * s)) ^ q *
        (1 + ε * s / (s + c * (1 + ε) * r)) ^ p ≤ 1 + ε) :
    p * s / (s + c * r) + q * r / (r + d * s) ≤ 1 := by
  have hD₁ : 0 < r + d * s := add_pos_of_pos_of_nonneg hr (mul_nonneg hd hs.le)
  have hD₂ : 0 < s + c * r := add_pos_of_pos_of_nonneg hs (mul_nonneg hc hr.le)
  let f : ℝ → ℝ := fun ε => Real.log (1 + ε) -
    q * Real.log (1 + ε * r / (r + d * s)) -
    p * Real.log (1 + ε * s / (s + c * (1 + ε) * r))
  have hzero : f 0 = 0 := by simp [f]
  have hnonneg (ε : ℝ) (hε : 0 < ε) : 0 ≤ f ε := by
    have hden : 0 < s + c * (1 + ε) * r := by positivity
    have hb₁ : 0 < 1 + ε * r / (r + d * s) := by positivity
    have hb₂ : 0 < 1 + ε * s / (s + c * (1 + ε) * r) := by positivity
    have hlog := Real.log_le_log
      (mul_pos (Real.rpow_pos_of_pos hb₁ q) (Real.rpow_pos_of_pos hb₂ p)) (hfinite ε hε)
    rw [Real.log_mul (Real.rpow_pos_of_pos hb₁ q).ne'
      (Real.rpow_pos_of_pos hb₂ p).ne', Real.log_rpow hb₁, Real.log_rpow hb₂] at hlog
    dsimp only [f]
    linarith only [hlog]
  have hId := hasDerivAt_id (0 : ℝ)
  have hbase : HasDerivAt (fun ε : ℝ => Real.log (1 + ε)) 1 0 := by
    simpa using (hId.const_add 1).log (by norm_num)
  have hfirst : HasDerivAt (fun ε : ℝ => Real.log (1 + ε * r / (r + d * s)))
      (r / (r + d * s)) 0 := by
    simpa using (((hId.mul_const r).div_const (r + d * s)).const_add 1).log (by norm_num)
  have hden : HasDerivAt (fun ε : ℝ => s + c * (1 + ε) * r) (c * r) 0 := by
    simpa only [id_eq, mul_one] using (((hId.const_add 1).const_mul c).mul_const r).const_add s
  have hquot : HasDerivAt (fun ε : ℝ => ε * s / (s + c * (1 + ε) * r))
      (s / (s + c * r)) 0 := by
    convert (hId.mul_const s).fun_div hden (by simpa using hD₂.ne') using 1 <;>
      norm_num [id_eq] <;> field_simp [hD₂.ne']
  have hsecond : HasDerivAt (fun ε : ℝ => Real.log (1 + ε * s / (s + c * (1 + ε) * r)))
      (s / (s + c * r)) 0 := by
    simpa using (hquot.const_add 1).log (by norm_num)
  have hderiv : HasDerivAt f
      (1 - q * (r / (r + d * s)) - p * (s / (s + c * r))) 0 :=
    (hbase.sub (hfirst.const_mul q)).sub (hsecond.const_mul p)
  have h := right_derivative_nonneg hderiv hzero hnonneg
  simp only [← mul_div_assoc] at h
  linarith only [h]

/-- Actual positive homogeneous profiles with both coordinate finite-increment
bounds produce the logarithmic product inequality, and hence the source ratio
bound. This theorem assumes neither that ratio nor its angular consequence. -/
theorem profile_ratio_of_coordinate_increments (g : ℝ → ℝ → ℝ)
    {p q c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hg : ∀ r s : ℝ, 0 < r → 0 < s → 0 < g r s)
    (hhom : ∀ t r s : ℝ, 0 < t → 0 < r → 0 < s → g (t * r) (t * s) = t * g r s)
    (hfirst : ∀ r s t : ℝ, 0 < r → 0 < s → 0 < t →
      (1 + t / (r + d * s)) ^ q ≤ g (r + t) s / g r s)
    (hsecond : ∀ r s t : ℝ, 0 < r → 0 < s → 0 < t →
      (1 + t / (s + c * r)) ^ p ≤ g r (s + t) / g r s)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    p * s / (s + c * r) + q * r / (r + d * s) ≤ 1 := by
  apply profile_ratio_of_finite_increment hc hd hr hs
  intro ε hε
  have ht : 0 < 1 + ε := by linarith
  have hr' : 0 < (1 + ε) * r := mul_pos ht hr
  have hsumr : r + ε * r = (1 + ε) * r := by ring
  have hsums : s + ε * s = (1 + ε) * s := by ring
  have h₁ := hfirst r s (ε * r) hr hs (mul_pos hε hr)
  rw [hsumr] at h₁
  have h₂ := hsecond ((1 + ε) * r) s (ε * s) hr' hs (mul_pos hε hs)
  rw [hsums] at h₂
  have hbase : 0 < 1 + ε * s / (s + c * ((1 + ε) * r)) := by positivity
  have hmul := mul_le_mul h₁ h₂ (Real.rpow_pos_of_pos hbase p).le
    (div_pos (hg _ _ hr' hs) (hg _ _ hr hs)).le
  have hcancel : (g ((1 + ε) * r) s / g r s) *
      (g ((1 + ε) * r) ((1 + ε) * s) / g ((1 + ε) * r) s) = 1 + ε := by
    rw [hhom (1 + ε) r s ht hr hs]
    field_simp [(hg r s hr hs).ne', (hg ((1 + ε) * r) s hr' hs).ne']
  rw [hcancel] at hmul
  simpa only [mul_assoc] using hmul

end BlockIdentities.Rectangular
