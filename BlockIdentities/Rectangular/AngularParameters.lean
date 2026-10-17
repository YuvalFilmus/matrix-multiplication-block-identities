/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.AngularOffsets
public import BlockIdentities.Rectangular.AngularOptimization

/-! Scalar bridge from actual six offset quadratics and row budgets to the
angular inequality. This module does not claim such offsets exist for tensors. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular

/-- Product-to-angle identity on the full closed parameter domain. -/
theorem cos_sum_arccos_sqrt {p q : ℝ}
    (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    Real.cos (Real.arccos (Real.sqrt p) + Real.arccos (Real.sqrt q)) =
      Real.sqrt (p * q) - Real.sqrt ((1 - p) * (1 - q)) := by
  rw [Real.cos_add,
    Real.cos_arccos (by linarith [Real.sqrt_nonneg p]) (Real.sqrt_le_one.mpr hp.2),
    Real.cos_arccos (by linarith [Real.sqrt_nonneg q]) (Real.sqrt_le_one.mpr hq.2),
    Real.sin_arccos, Real.sin_arccos, Real.sq_sqrt hp.1, Real.sq_sqrt hq.1,
    ← Real.sqrt_mul hp.1, ← Real.sqrt_mul (sub_nonneg.mpr hp.2)]

/-- A genuine pairwise positive-axis quadratic supplies the cosine comparison
needed by the final offset-budget argument. -/
theorem cos_sum_arccos_sqrt_le_offset {p q c d : ℝ}
    (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hQ : ∀ t : ℝ, 0 < t →
      0 ≤ (1 - q) * c * t ^ 2 + (1 - p - q + c * d) * t + (1 - p) * d) :
    Real.cos (Real.arccos (Real.sqrt p) + Real.arccos (Real.sqrt q)) ≤ Real.sqrt (c * d) := by
  rw [cos_sum_arccos_sqrt hp hq]
  exact (le_max_left _ 0).trans (offset_sqrt_lower_of_quadratic hp hq hc hd hQ)

/-- Source-independent scalar consumer of the six actual nonnegative offsets,
three row budgets and pairwise finite-increment quadratics. No angular or
weighted-objective conclusion is included among its assumptions. -/
theorem angular_parameters_of_offset_quadratics
    {p₁ p₂ p₃ c₁₂ c₁₃ c₂₁ c₂₃ c₃₁ c₃₂ : ℝ}
    (hp₁ : p₁ ∈ Set.Icc 0 1) (hp₂ : p₂ ∈ Set.Icc 0 1) (hp₃ : p₃ ∈ Set.Icc 0 1)
    (hc₁₂ : 0 ≤ c₁₂) (hc₁₃ : 0 ≤ c₁₃) (hc₂₁ : 0 ≤ c₂₁)
    (hc₂₃ : 0 ≤ c₂₃) (hc₃₁ : 0 ≤ c₃₁) (hc₃₂ : 0 ≤ c₃₂)
    (hb₁ : c₁₂ + c₁₃ ≤ 1) (hb₂ : c₂₁ + c₂₃ ≤ 1) (hb₃ : c₃₁ + c₃₂ ≤ 1)
    (hQ₁₂ : ∀ t : ℝ, 0 < t → 0 ≤
      (1 - p₂) * c₁₂ * t ^ 2 + (1 - p₁ - p₂ + c₁₂ * c₂₁) * t + (1 - p₁) * c₂₁)
    (hQ₁₃ : ∀ t : ℝ, 0 < t → 0 ≤
      (1 - p₃) * c₁₃ * t ^ 2 + (1 - p₁ - p₃ + c₁₃ * c₃₁) * t + (1 - p₁) * c₃₁)
    (hQ₂₃ : ∀ t : ℝ, 0 < t → 0 ≤
      (1 - p₃) * c₂₃ * t ^ 2 + (1 - p₂ - p₃ + c₂₃ * c₃₂) * t + (1 - p₂) * c₃₂) :
    Real.pi / 2 ≤ Real.arccos (Real.sqrt p₁) +
      Real.arccos (Real.sqrt p₂) + Real.arccos (Real.sqrt p₃) := by
  exact angular_sum_ge_of_offset_budgets hc₁₂ hc₁₃ hc₂₁ hc₂₃ hc₃₁ hc₃₂ hb₁ hb₂ hb₃
    (Real.arccos_nonneg _) (Real.arccos_nonneg _) (Real.arccos_nonneg _)
    (cos_sum_arccos_sqrt_le_offset hp₁ hp₂ hc₁₂ hc₂₁ hQ₁₂)
    (cos_sum_arccos_sqrt_le_offset hp₁ hp₃ hc₁₃ hc₃₁ hQ₁₃)
    (cos_sum_arccos_sqrt_le_offset hp₂ hp₃ hc₂₃ hc₃₂ hQ₂₃)

end BlockIdentities.Rectangular
