/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.WeightedTrigonometry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Pure real consumers of the angular constraint. These do not assert that
any tensor or supporting vector satisfies that constraint. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular

/-- The canonical angle for a parameter in the closed unit interval.
Both endpoints are included. -/
theorem arccos_sqrt_mem_Icc {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    Real.arccos (Real.sqrt p) ∈ Set.Icc 0 (Real.pi / 2) :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.mpr (Real.sqrt_nonneg _)⟩

/-- On the source parameter domain, the canonical angle recovers the parameter
exactly, including p=0 and p=1. -/
theorem cos_sq_arccos_sqrt {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    Real.cos (Real.arccos (Real.sqrt p)) ^ 2 = p := by
  rw [Real.cos_arccos (by linarith [Real.sqrt_nonneg p])
    (Real.sqrt_le_one.mpr hp.2), Real.sq_sqrt hp.1]

/-- Positive shape coefficients and an actual angular constraint imply the
weighted objective bound. All premises are scalar data, independent of tensors. -/
theorem weighted_parameters_le {a b c p₁ p₂ p₃ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h₁ : p₁ ∈ Set.Icc 0 1) (h₂ : p₂ ∈ Set.Icc 0 1) (h₃ : p₃ ∈ Set.Icc 0 1)
    (hangle : Real.pi / 2 ≤ Real.arccos (Real.sqrt p₁) +
      Real.arccos (Real.sqrt p₂) + Real.arccos (Real.sqrt p₃)) :
    a * p₁ + b * p₂ + c * p₃ ≤
      (a + b + c) / 2 + (a * b / c + a * c / b + b * c / a) / 4 := by
  have h := weighted_cos_sq_le ha hb hc
    (arccos_sqrt_mem_Icc h₁) (arccos_sqrt_mem_Icc h₂) (arccos_sqrt_mem_Icc h₃) hangle
  simpa only [cos_sq_arccos_sqrt h₁, cos_sq_arccos_sqrt h₂,
    cos_sq_arccos_sqrt h₃] using h

/-- The small third-coefficient branch, allowing a zero third coefficient and
closed parameter endpoints. -/
theorem weighted_parameters_le_threshold {a b c p₁ p₂ p₃ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hthreshold : c ≤ a * b / (a + b))
    (h₁ : p₁ ∈ Set.Icc 0 1) (h₂ : p₂ ∈ Set.Icc 0 1) (h₃ : p₃ ∈ Set.Icc 0 1)
    (hangle : Real.pi / 2 ≤ Real.arccos (Real.sqrt p₁) +
      Real.arccos (Real.sqrt p₂) + Real.arccos (Real.sqrt p₃)) :
    a * p₁ + b * p₂ + c * p₃ ≤ a + b := by
  have h := weighted_cos_sq_le_threshold ha hb hc hthreshold
    (arccos_sqrt_mem_Icc h₁) (arccos_sqrt_mem_Icc h₂) (arccos_sqrt_mem_Icc h₃) hangle
  simpa only [cos_sq_arccos_sqrt h₁, cos_sq_arccos_sqrt h₂,
    cos_sq_arccos_sqrt h₃] using h

end BlockIdentities.Rectangular
