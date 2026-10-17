/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular

/-- Wolstenholme's inequality, proved by two real squares. The angles need
only sum to pi; no division or positivity assumption on the weights is used. -/
theorem wolstenholme_real {β₁ β₂ β₃ : ℝ} (hβ : β₁ + β₂ + β₃ = Real.pi)
    (u v w : ℝ) :
    2 * (v * w * Real.cos β₁ + w * u * Real.cos β₂ + u * v * Real.cos β₃) ≤
      u ^ 2 + v ^ 2 + w ^ 2 := by
  have hc : Real.cos β₁ =
      -(Real.cos β₂ * Real.cos β₃ - Real.sin β₂ * Real.sin β₃) := by
    have he : β₁ = Real.pi - (β₂ + β₃) := by linarith
    rw [he, Real.cos_pi_sub, Real.cos_add]
  have hid :
      (u - v * Real.cos β₃ - w * Real.cos β₂) ^ 2 +
        (v * Real.sin β₃ - w * Real.sin β₂) ^ 2 =
      u ^ 2 + v ^ 2 + w ^ 2 -
        2 * (v * w * Real.cos β₁ + w * u * Real.cos β₂ + u * v * Real.cos β₃) := by
    rw [hc]
    linear_combination v ^ 2 * Real.sin_sq_add_cos_sq β₃ +
      w ^ 2 * Real.sin_sq_add_cos_sq β₂
  have hnonneg := add_nonneg (sq_nonneg (u - v * Real.cos β₃ - w * Real.cos β₂))
    (sq_nonneg (v * Real.sin β₃ - w * Real.sin β₂))
  rw [hid] at hnonneg
  linarith only [hnonneg]

/-- The positive-weight bound on the exact angular boundary. -/
theorem weighted_cos_sq_le_of_sum_eq {a b c θ₁ θ₂ θ₃ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : θ₁ + θ₂ + θ₃ = Real.pi / 2) :
    a * Real.cos θ₁ ^ 2 + b * Real.cos θ₂ ^ 2 + c * Real.cos θ₃ ^ 2 ≤
      (a + b + c) / 2 + (a * b / c + a * c / b + b * c / a) / 4 := by
  have hw := wolstenholme_real
    (β₁ := 2 * θ₁) (β₂ := 2 * θ₂) (β₃ := 2 * θ₃)
    (by linarith) (b * c) (a * c) (a * b)
  rw [Real.cos_two_mul, Real.cos_two_mul, Real.cos_two_mul] at hw
  have hid : 4 * a * b * c *
      ((a + b + c) / 2 + (a * b / c + a * c / b + b * c / a) / 4 -
        (a * Real.cos θ₁ ^ 2 + b * Real.cos θ₂ ^ 2 + c * Real.cos θ₃ ^ 2)) =
      (b * c) ^ 2 + (a * c) ^ 2 + (a * b) ^ 2 -
        2 * ((a * c) * (a * b) * (2 * Real.cos θ₁ ^ 2 - 1) +
          (a * b) * (b * c) * (2 * Real.cos θ₂ ^ 2 - 1) +
          (b * c) * (a * c) * (2 * Real.cos θ₃ ^ 2 - 1)) := by
    field_simp [ha.ne', hb.ne', hc.ne'] <;> ring
  have hnonneg : 0 ≤ 4 * a * b * c *
      ((a + b + c) / 2 + (a * b / c + a * c / b + b * c / a) / 4 -
        (a * Real.cos θ₁ ^ 2 + b * Real.cos θ₂ ^ 2 + c * Real.cos θ₃ ^ 2)) := by
    rw [hid]
    linarith only [hw]
  have hscale : 0 < 4 * a * b * c := by positivity
  have hdiff := (mul_nonneg_iff_of_pos_left hscale).mp hnonneg
  linarith only [hdiff]

private theorem cos_sq_le_of_angle_le {x y : ℝ}
    (hx : 0 ≤ x) (hy : y ≤ Real.pi / 2) (hxy : x ≤ y) :
    Real.cos y ^ 2 ≤ Real.cos x ^ 2 := by
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hx
    (show y ≤ Real.pi by linarith [Real.pi_pos]) hxy
  have hnonneg := Real.cos_nonneg_of_mem_Icc
    (show y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos])
  nlinarith only [hcos, hnonneg]

/-- Reduce the two last angles monotonically to the angular boundary.
This is a scalar optimization lemma, with the angular constraint explicit. -/
theorem weighted_cos_sq_le {a b c θ₁ θ₂ θ₃ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h₁ : θ₁ ∈ Set.Icc 0 (Real.pi / 2))
    (h₂ : θ₂ ∈ Set.Icc 0 (Real.pi / 2))
    (h₃ : θ₃ ∈ Set.Icc 0 (Real.pi / 2))
    (hsum : Real.pi / 2 ≤ θ₁ + θ₂ + θ₃) :
    a * Real.cos θ₁ ^ 2 + b * Real.cos θ₂ ^ 2 + c * Real.cos θ₃ ^ 2 ≤
      (a + b + c) / 2 + (a * b / c + a * c / b + b * c / a) / 4 := by
  let t₂ := min θ₂ (Real.pi / 2 - θ₁)
  let t₃ := Real.pi / 2 - θ₁ - t₂
  have ht₂ : 0 ≤ t₂ := le_min h₂.1 (sub_nonneg.mpr h₁.2)
  have ht₂le : t₂ ≤ θ₂ := min_le_left _ _
  have ht₂cap : t₂ ≤ Real.pi / 2 - θ₁ := min_le_right _ _
  have ht₃ : 0 ≤ t₃ := by dsimp only [t₃]; linarith
  have ht₃le : t₃ ≤ θ₃ := by
    dsimp only [t₃, t₂]
    rcases le_total θ₂ (Real.pi / 2 - θ₁) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith [h₃.1]
  have hbound := weighted_cos_sq_le_of_sum_eq ha hb hc
    (θ₁ := θ₁) (θ₂ := t₂) (θ₃ := t₃) (by dsimp only [t₃]; ring)
  have hmono₂ := mul_le_mul_of_nonneg_left
    (cos_sq_le_of_angle_le ht₂ h₂.2 ht₂le) hb.le
  have hmono₃ := mul_le_mul_of_nonneg_left
    (cos_sq_le_of_angle_le ht₃ h₃.2 ht₃le) hc.le
  linarith only [hbound, hmono₂, hmono₃]

/-- The small third-weight branch, including zero third weight. -/
theorem weighted_cos_sq_le_threshold {a b c θ₁ θ₂ θ₃ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hthreshold : c ≤ a * b / (a + b))
    (h₁ : θ₁ ∈ Set.Icc 0 (Real.pi / 2))
    (h₂ : θ₂ ∈ Set.Icc 0 (Real.pi / 2))
    (h₃ : θ₃ ∈ Set.Icc 0 (Real.pi / 2))
    (hsum : Real.pi / 2 ≤ θ₁ + θ₂ + θ₃) :
    a * Real.cos θ₁ ^ 2 + b * Real.cos θ₂ ^ 2 + c * Real.cos θ₃ ^ 2 ≤ a + b := by
  have hab : 0 < a + b := add_pos ha hb
  have hc₀ : 0 < a * b / (a + b) := div_pos (mul_pos ha hb) hab
  have hbound := weighted_cos_sq_le ha hb hc₀ h₁ h₂ h₃ hsum
  have heq : (a + b + a * b / (a + b)) / 2 +
      (a * b / (a * b / (a + b)) + a * (a * b / (a + b)) / b +
        b * (a * b / (a + b)) / a) / 4 = a + b := by
    field_simp [ha.ne', hb.ne', hab.ne']; ring
  rw [heq] at hbound
  have hmono := mul_le_mul_of_nonneg_right hthreshold (sq_nonneg (Real.cos θ₃))
  linarith only [hbound, hmono]

end BlockIdentities.Rectangular
