/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.LinearCombination

/-! Scalar consequences of the genuine profile finite-increment inequalities.
No tensor profile or angular constraint is asserted by this module. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular

/-- A quadratic nonnegative on the positive axis has the required one-sided
middle-coefficient bound. Both zero leading/constant endpoints are included. -/
theorem quadratic_middle_ge_neg_two_sqrt {A B C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hQ : ∀ t : ℝ, 0 < t → 0 ≤ A * t ^ 2 + B * t + C) :
    -2 * Real.sqrt (A * C) ≤ B := by
  by_cases hAz : A = 0
  · subst A
    simp only [zero_mul, Real.sqrt_zero, mul_zero, neg_zero]
    by_contra hB
    have hBn : B < 0 := lt_of_not_ge hB
    let t : ℝ := (C + 1) / (-B)
    have ht : 0 < t := div_pos (by linarith) (neg_pos.mpr hBn)
    have he : B * t = -(C + 1) := by
      dsimp only [t]
      field_simp [ne_of_lt hBn]
      <;> ring
    have h := hQ t ht
    simp only [zero_mul, zero_add] at h
    linarith only [h, he]
  by_cases hCz : C = 0
  · subst C
    simp only [mul_zero, Real.sqrt_zero, mul_zero, neg_zero]
    by_contra hB
    have hBn : B < 0 := lt_of_not_ge hB
    have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    let t : ℝ := -B / (2 * A)
    have ht : 0 < t := div_pos (neg_pos.mpr hBn) (by positivity)
    have he : A * t = -B / 2 := by
      dsimp only [t]
      field_simp [hAz]
      <;> ring
    have hn : t * (B / 2) < 0 := mul_neg_of_pos_of_neg ht (by linarith)
    have h := hQ t ht
    have het := congrArg (fun z : ℝ => z * t) he
    nlinarith only [het, hn, h]
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hCz)
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hAp
  have hsC : 0 < Real.sqrt C := Real.sqrt_pos.mpr hCp
  have algebra (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
      (x ^ 2 * (y / x) ^ 2 + B * (y / x) + y ^ 2) / (y / x) = 2 * x * y + B := by
    field_simp [hx, hy]
    <;> ring
  have he : (A * (Real.sqrt C / Real.sqrt A) ^ 2 +
      B * (Real.sqrt C / Real.sqrt A) + C) / (Real.sqrt C / Real.sqrt A) =
      2 * Real.sqrt A * Real.sqrt C + B := by
    simpa only [Real.sq_sqrt hA, Real.sq_sqrt hC] using
      algebra (Real.sqrt A) (Real.sqrt C) hsA.ne' hsC.ne'
  have h := div_nonneg (hQ (Real.sqrt C / Real.sqrt A) (div_pos hsC hsA))
    (div_pos hsC hsA).le
  rw [he] at h
  rw [Real.sqrt_mul hA]
  linarith only [h]

/-- The positive-axis finite-increment quadratic forces the source's pairwise
offset-product lower bound. Zero parameters and zero offsets are allowed. -/
theorem offset_sqrt_lower_of_quadratic {p q c d : ℝ}
    (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hQ : ∀ t : ℝ, 0 < t →
      0 ≤ (1 - q) * c * t ^ 2 + (1 - p - q + c * d) * t + (1 - p) * d) :
    max (Real.sqrt (p * q) - Real.sqrt ((1 - p) * (1 - q))) 0 ≤ Real.sqrt (c * d) := by
  have hcomp : 0 ≤ (1 - p) * (1 - q) := mul_nonneg (by linarith [hp.2]) (by linarith [hq.2])
  have hcd : 0 ≤ c * d := mul_nonneg hc hd
  have hpq : 0 ≤ p * q := mul_nonneg hp.1 hq.1
  have hmiddle := quadratic_middle_ge_neg_two_sqrt
    (A := (1 - q) * c) (B := 1 - p - q + c * d) (C := (1 - p) * d)
    (mul_nonneg (by linarith [hq.2]) hc) (mul_nonneg (by linarith [hp.2]) hd) hQ
  have hrearr : (1 - q) * c * ((1 - p) * d) = ((1 - p) * (1 - q)) * (c * d) := by ring
  rw [hrearr, Real.sqrt_mul hcomp] at hmiddle
  have hsquare : p * q ≤ (Real.sqrt (c * d) + Real.sqrt ((1 - p) * (1 - q))) ^ 2 := by
    nlinarith only [hmiddle, Real.sq_sqrt hcd, Real.sq_sqrt hcomp]
  have hsum : Real.sqrt (p * q) ≤ Real.sqrt (c * d) + Real.sqrt ((1 - p) * (1 - q)) := by
    nlinarith only [hsquare, Real.sq_sqrt hpq, Real.sqrt_nonneg (p * q),
      Real.sqrt_nonneg (c * d), Real.sqrt_nonneg ((1 - p) * (1 - q))]
  exact max_le (by linarith only [hsum]) (Real.sqrt_nonneg _)

/-- The pairwise AM–GM estimate used to charge offsets to their two rows. -/
theorem offset_pair_quadratic {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (x y : ℝ) :
    2 * Real.sqrt (c * d) * x * y ≤ c * x ^ 2 + d * y ^ 2 := by
  have h := sq_nonneg (Real.sqrt c * x - Real.sqrt d * y)
  have hec := congrArg (fun t : ℝ => t * x ^ 2) (Real.sq_sqrt hc)
  have hed := congrArg (fun t : ℝ => t * y ^ 2) (Real.sq_sqrt hd)
  rw [Real.sqrt_mul hc]
  nlinarith only [h, hec, hed]

/-- The actual six nonnegative offsets with the three row budgets give the
quadratic upper bound. No angular conclusion is among the premises. -/
theorem offset_budget_quadratic {c₁₂ c₁₃ c₂₁ c₂₃ c₃₁ c₃₂ : ℝ}
    (h₁₂ : 0 ≤ c₁₂) (h₁₃ : 0 ≤ c₁₃) (h₂₁ : 0 ≤ c₂₁)
    (h₂₃ : 0 ≤ c₂₃) (h₃₁ : 0 ≤ c₃₁) (h₃₂ : 0 ≤ c₃₂)
    (hb₁ : c₁₂ + c₁₃ ≤ 1) (hb₂ : c₂₁ + c₂₃ ≤ 1) (hb₃ : c₃₁ + c₃₂ ≤ 1)
    (x₁ x₂ x₃ : ℝ) :
    2 * Real.sqrt (c₁₂ * c₂₁) * x₁ * x₂ +
      2 * Real.sqrt (c₁₃ * c₃₁) * x₁ * x₃ +
      2 * Real.sqrt (c₂₃ * c₃₂) * x₂ * x₃ ≤ x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 := by
  have hp₁ := offset_pair_quadratic h₁₂ h₂₁ x₁ x₂
  have hp₂ := offset_pair_quadratic h₁₃ h₃₁ x₁ x₃
  have hp₃ := offset_pair_quadratic h₂₃ h₃₂ x₂ x₃
  have hr₁ := mul_le_mul_of_nonneg_right hb₁ (sq_nonneg x₁)
  have hr₂ := mul_le_mul_of_nonneg_right hb₂ (sq_nonneg x₂)
  have hr₃ := mul_le_mul_of_nonneg_right hb₃ (sq_nonneg x₃)
  nlinarith only [hp₁, hp₂, hp₃, hr₁, hr₂, hr₃]

private theorem cosine_row_identity (a b c : ℝ) :
    Real.cos (a + b) * Real.cos b + Real.cos (a + c) * Real.cos c =
      Real.cos a + Real.cos (a + b + c) * Real.cos (b - c) := by
  simp only [Real.cos_add, Real.cos_sub, Real.sin_add]
  linear_combination
    (Real.cos a * Real.sin c ^ 2 + Real.sin a * Real.sin c * Real.cos c) *
      Real.sin_sq_add_cos_sq b +
    (Real.cos a * (1 - Real.cos b ^ 2) + Real.sin a * Real.sin b * Real.cos b) *
      Real.sin_sq_add_cos_sq c

private theorem cosine_row_strict {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a + b + c < Real.pi / 2) :
    Real.cos a < Real.cos (a + b) * Real.cos b + Real.cos (a + c) * Real.cos c := by
  rw [cosine_row_identity]
  have hsum : 0 < Real.cos (a + b + c) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hs⟩
  have hdiff : 0 < Real.cos (b - c) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hprod := mul_pos hsum hdiff
  linarith only [hprod]

/-- The source's final offset-budget contradiction, expressed directly with
angles. Pairwise cosine lower bounds are genuine intermediate scalar inputs;
the angular conclusion itself is not assumed. -/
theorem angular_sum_ge_of_offset_budgets
    {c₁₂ c₁₃ c₂₁ c₂₃ c₃₁ c₃₂ θ₁ θ₂ θ₃ : ℝ}
    (h₁₂ : 0 ≤ c₁₂) (h₁₃ : 0 ≤ c₁₃) (h₂₁ : 0 ≤ c₂₁)
    (h₂₃ : 0 ≤ c₂₃) (h₃₁ : 0 ≤ c₃₁) (h₃₂ : 0 ≤ c₃₂)
    (hb₁ : c₁₂ + c₁₃ ≤ 1) (hb₂ : c₂₁ + c₂₃ ≤ 1) (hb₃ : c₃₁ + c₃₂ ≤ 1)
    (ht₁ : 0 ≤ θ₁) (ht₂ : 0 ≤ θ₂) (ht₃ : 0 ≤ θ₃)
    (hp₁₂ : Real.cos (θ₁ + θ₂) ≤ Real.sqrt (c₁₂ * c₂₁))
    (hp₁₃ : Real.cos (θ₁ + θ₃) ≤ Real.sqrt (c₁₃ * c₃₁))
    (hp₂₃ : Real.cos (θ₂ + θ₃) ≤ Real.sqrt (c₂₃ * c₃₂)) :
    Real.pi / 2 ≤ θ₁ + θ₂ + θ₃ := by
  by_contra hneg
  have hs : θ₁ + θ₂ + θ₃ < Real.pi / 2 := lt_of_not_ge hneg
  have hx₁ : 0 < Real.cos θ₁ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hx₂ : 0 < Real.cos θ₂ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hx₃ : 0 < Real.cos θ₃ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hr₁ := cosine_row_strict ht₁ ht₂ ht₃ hs
  have hr₂ := cosine_row_strict ht₂ ht₁ ht₃ (by linarith)
  have hr₃ := cosine_row_strict ht₃ ht₁ ht₂ (by linarith)
  rw [add_comm θ₂ θ₁] at hr₂
  rw [add_comm θ₃ θ₁, add_comm θ₃ θ₂] at hr₃
  have hm₁ := mul_lt_mul_of_pos_left hr₁ hx₁
  have hm₂ := mul_lt_mul_of_pos_left hr₂ hx₂
  have hm₃ := mul_lt_mul_of_pos_left hr₃ hx₃
  have hp₁ := mul_le_mul_of_nonneg_right hp₁₂ (mul_nonneg hx₁.le hx₂.le)
  have hp₂ := mul_le_mul_of_nonneg_right hp₁₃ (mul_nonneg hx₁.le hx₃.le)
  have hp₃ := mul_le_mul_of_nonneg_right hp₂₃ (mul_nonneg hx₂.le hx₃.le)
  have hupper := offset_budget_quadratic h₁₂ h₁₃ h₂₁ h₂₃ h₃₁ h₃₂ hb₁ hb₂ hb₃
    (Real.cos θ₁) (Real.cos θ₂) (Real.cos θ₃)
  nlinarith only [hm₁, hm₂, hm₃, hp₁, hp₂, hp₃, hupper]

/-- Clear the strictly positive denominators of the actual finite-increment
ratio bound. This produces the quadratic used above, not its conclusion. -/
theorem offset_quadratic_of_ratio {p q c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hratio : ∀ t : ℝ, 0 < t → p / (1 + c * t) + q * t / (t + d) ≤ 1) :
    ∀ t : ℝ, 0 < t →
      0 ≤ (1 - q) * c * t ^ 2 + (1 - p - q + c * d) * t + (1 - p) * d := by
  intro t ht
  have hden₁ : 0 < 1 + c * t := by positivity
  have hden₂ : 0 < t + d := add_pos_of_pos_of_nonneg ht hd
  have he : (1 - (p / (1 + c * t) + q * t / (t + d))) *
      ((1 + c * t) * (t + d)) =
      (1 - q) * c * t ^ 2 + (1 - p - q + c * d) * t + (1 - p) * d := by
    field_simp [hden₁.ne', hden₂.ne']
    <;> ring
  have hnonneg := mul_nonneg (sub_nonneg.mpr (hratio t ht)) (mul_pos hden₁ hden₂).le
  rwa [he] at hnonneg

end BlockIdentities.Rectangular
