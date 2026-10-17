/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Square.Certificate
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp

/-! Scalar weak-duality consumption at the actual normalized tensor values. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open scoped BigOperators

/-- Internal scalar criterion: actual feasible node values and an actual source
bound discharge the finite certificate and its logarithmic exponent comparison. -/
theorem exponent_le_of_certificate_values {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (s t : V) (hst : s ≠ t) (σ : E → V)
    (cost μ : E → ℝ) (multiplicity : E → V → ℝ)
    (hterminal : ∀ e, σ e ≠ t) (hμ : ∀ e, 0 ≤ μ e)
    (x : V → ℝ) (hx : ∀ v, 0 ≤ x v)
    (d r : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) (ν : ℝ) (hν : 0 < ν)
    (ht : x t = (d : ℝ)) (hs : x s ≤ (r : ℝ) ^ (3 / ν))
    (hrows : ∀ e, ∑ v, multiplicity e v * x v ≤ cost e * x (σ e))
    (hcertificate : ∀ v, v ≠ t → certificateResidual σ cost μ multiplicity v ≤
      if v = s then 1 else 0)
    (hL : (d : ℝ)⁻¹ < ∑ e, multiplicity e t * μ e) :
    ν ≤ 3 * Real.log (r : ℝ) /
      (Real.log (d : ℝ) + Real.log (∑ e, multiplicity e t * μ e)) := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  let z : V → ℝ := fun v => x v / (d : ℝ)
  have hz : ∀ v, 0 ≤ z v := fun v => div_nonneg (hx v) hdpos.le
  have hzt : z t = 1 := by dsimp only [z]; rw [ht, div_self (ne_of_gt hdpos)]
  have hzrows : ∀ e, ∑ v, multiplicity e v * z v ≤ cost e * z (σ e) := by
    intro e
    simp only [z, ← mul_div_assoc, ← Finset.sum_div]
    exact div_le_div_of_nonneg_right (hrows e) hdpos.le
  have hweak := certificate_weakDuality s t hst σ cost μ multiplicity z
    hz hzt hterminal hμ hzrows hcertificate
  let L := ∑ e, multiplicity e t * μ e
  have hLpos : 0 < L := lt_trans (inv_pos.mpr hdpos) hL
  have hLd : 1 < L * (d : ℝ) := by
    have hm := mul_lt_mul_of_pos_right hL hdpos
    simpa only [inv_mul_cancel₀ (ne_of_gt hdpos)] using hm
  have hscalar : L * (d : ℝ) ≤ (r : ℝ) ^ (3 / ν) := by
    have hweak' : L ≤ x s / (d : ℝ) := hweak
    exact ((le_div_iff₀ hdpos).1 hweak').trans hs
  have hden : 0 < Real.log (d : ℝ) + Real.log L := by
    have hh := Real.log_pos hLd
    rw [Real.log_mul (ne_of_gt hLpos) (ne_of_gt hdpos)] at hh
    linarith
  have hlog := Real.log_le_log (mul_pos hLpos hdpos) hscalar
  rw [Real.log_mul (ne_of_gt hLpos) (ne_of_gt hdpos), Real.log_rpow hrpos] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hν.le
  have hid : ν * ((3 / ν) * Real.log (r : ℝ)) = 3 * Real.log (r : ℝ) := by
    field_simp [ne_of_gt hν] <;> ring
  rw [hid] at hmul
  apply (le_div_iff₀ hden).2
  change ν * (Real.log (d : ℝ) + Real.log L) ≤ _
  nlinarith

end BlockIdentities.Square
