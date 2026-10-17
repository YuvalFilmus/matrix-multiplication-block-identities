/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexFiniteEntropy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! Numerical entropy optimization of actual shared-leg value lower bounds. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open scoped BigOperators

/-- Internal numerical entropy optimization. Its probability-vector premise
is to be supplied by the actual shared-leg extraction argument. -/
theorem normalizedValue_sum_le_of_entropy_bounds {ι : Type*} [Fintype ι]
    (x : ℝ) (y k : ι → ℝ) (c ν : ℝ)
    (hx : 0 < x) (hy : ∀ i, 0 < y i) (hk : ∀ i, 0 < k i)
    (hc : 0 < c) (hν : 0 < ν)
    (hbound : ∀ p : ι → ℝ, (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 →
      (∑ i, p i * Real.log (y i)) +
        ν * ((finiteEntropy p + ∑ i, p i * Real.log (k i) - Real.log c) / 3) ≤ Real.log x) :
    (∑ i, k i * y i ^ (3 / ν)) ≤ c * x ^ (3 / ν) := by
  classical
  let w : ι → ℝ := fun i => k i * y i ^ (3 / ν)
  let S : ℝ := ∑ i, w i
  have hw (i : ι) : 0 < w i := mul_pos (hk i) (Real.rpow_pos_of_pos (hy i) _)
  have hSnonneg : 0 ≤ S := Finset.sum_nonneg (fun i _ => (hw i).le)
  change S ≤ c * x ^ (3 / ν)
  by_cases hSzero : S = 0
  · rw [hSzero]
    exact (mul_pos hc (Real.rpow_pos_of_pos hx _)).le
  have hS : 0 < S := lt_of_le_of_ne hSnonneg (Ne.symm hSzero)
  let p : ι → ℝ := fun i => w i / S
  have hp (i : ι) : 0 < p i := div_pos (hw i) hS
  have hpsum : (∑ i, p i) = 1 := by
    dsimp only [p]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hS)
  have hvariational : finiteEntropy p + (∑ i, p i * Real.log (w i)) = Real.log S := by
    rw [finiteEntropy, ← Finset.sum_add_distrib]
    calc
      (∑ i, (entropyTerm (p i) + p i * Real.log (w i))) =
          ∑ i, p i * Real.log S := by
        apply Finset.sum_congr rfl
        intro i _
        have hlog : Real.log (p i) = Real.log (w i) - Real.log S :=
          Real.log_div (ne_of_gt (hw i)) (ne_of_gt hS)
        rw [entropyTerm, hlog]
        ring
      _ = Real.log S := by rw [← Finset.sum_mul, hpsum, one_mul]
  have hlogw (i : ι) : Real.log (w i) =
      Real.log (k i) + (3 / ν) * Real.log (y i) := by
    dsimp only [w]
    rw [Real.log_mul (ne_of_gt (hk i)) (ne_of_gt (Real.rpow_pos_of_pos (hy i) _)),
      Real.log_rpow (hy i)]
  have hsumw : (∑ i, p i * Real.log (w i)) =
      (∑ i, p i * Real.log (k i)) + (3 / ν) * (∑ i, p i * Real.log (y i)) := by
    simp_rw [hlogw]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have he := hbound p (fun i => (hp i).le) hpsum
  have hscaled : (3 / ν) * (∑ i, p i * Real.log (y i)) + finiteEntropy p +
      (∑ i, p i * Real.log (k i)) - Real.log c ≤ (3 / ν) * Real.log x := by
    have hh := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 3 / ν)
    convert hh using 1 <;> field_simp [ne_of_gt hν] <;> ring
  apply (Real.log_le_log_iff hS (mul_pos hc (Real.rpow_pos_of_pos hx _))).1
  rw [Real.log_mul (ne_of_gt hc) (ne_of_gt (Real.rpow_pos_of_pos hx _)), Real.log_rpow hx]
  rw [hsumw] at hvariational
  linarith

end BlockIdentities.Square
