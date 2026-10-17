/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Scalar logarithmic consumers of actual ordered extraction inequalities. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open Filter
open scoped BigOperators Topology

theorem ordered_extraction_log_bound {ι : Type*} [Fintype ι]
    (VA : ℝ) (VB : ι → ℝ) (hVA : 0 < VA) (hVB : ∀ i, 0 < VB i)
    (σ WD WE : ℝ) (hWD : 0 < WD) (hWE : 0 < WE)
    (n u h : ℕ) (m : ι → ℕ) (hn : 1 ≤ n) (hu : 1 ≤ u) (hh : 1 ≤ h)
    (hfinite : (h : ℝ) * WE * ∏ i, VB i ^ m i ≤
      (u : ℝ) ^ σ * VA ^ n * WD) :
    (∑ i, ((m i : ℝ) / (n : ℝ)) * Real.log (VB i)) +
      Real.log (h : ℝ) / (n : ℝ) + (Real.log WE - Real.log WD) / (n : ℝ) ≤
      Real.log VA + σ * (Real.log (u : ℝ) / (n : ℝ)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hupos : 0 < (u : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hu)
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hp : 0 < ∏ i, VB i ^ m i := Finset.prod_pos fun i _ => pow_pos (hVB i) _
  have hup := Real.rpow_pos_of_pos hupos σ
  have hl := Real.log_le_log (mul_pos (mul_pos hhpos hWE) hp) hfinite
  rw [Real.log_mul (mul_pos hhpos hWE).ne' hp.ne', Real.log_mul hhpos.ne' hWE.ne',
    Real.log_mul (mul_pos hup (pow_pos hVA n)).ne' hWD.ne',
    Real.log_mul hup.ne' (pow_pos hVA n).ne', Real.log_rpow hupos,
    Real.log_pow, Real.log_prod (fun i _ => (pow_pos (hVB i) _).ne')] at hl
  simp only [Real.log_pow] at hl
  have hs : (∑ i, ((m i : ℝ) / (n : ℝ)) * Real.log (VB i)) =
      (∑ i, (m i : ℝ) * Real.log (VB i)) / (n : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  have hd := div_le_div_of_nonneg_right hl hnpos.le
  have hid : (Real.log (h : ℝ) + Real.log WE + ∑ i, (m i : ℝ) * Real.log (VB i)) /
      (n : ℝ) - Real.log WD / (n : ℝ) =
      (∑ i, (m i : ℝ) * Real.log (VB i)) / (n : ℝ) + Real.log (h : ℝ) / (n : ℝ) +
        (Real.log WE - Real.log WD) / (n : ℝ) := by ring
  have hid' : (σ * Real.log (u : ℝ) + (n : ℝ) * Real.log VA + Real.log WD) /
      (n : ℝ) - Real.log WD / (n : ℝ) =
      Real.log VA + σ * (Real.log (u : ℝ) / (n : ℝ)) := by
    field_simp [hnpos.ne']
    <;> ring
  linarith

theorem ordered_extraction_log_limit {ι : Type*} [Fintype ι]
    (VA : ℝ) (VB : ι → ℝ) (hVA : 0 < VA) (hVB : ∀ i, 0 < VB i)
    (σ : ℝ) (WD WE : ℕ → ℝ) (hWD : ∀ j, 0 < WD j) (hWE : ∀ j, 0 < WE j)
    (n u h : ℕ → ℕ) (m : ι → ℕ → ℕ)
    (hn : ∀ j, 1 ≤ n j) (hu : ∀ j, 1 ≤ u j) (hh : ∀ j, 1 ≤ h j)
    (hfinite : ∀ j, (h j : ℝ) * WE j * ∏ i, VB i ^ m i j ≤
      (u j : ℝ) ^ σ * VA ^ n j * WD j)
    (q : ι → ℝ) (α δ : ℝ)
    (hu_rate : Tendsto (fun j => Real.log (u j : ℝ) / (n j : ℝ)) atTop (𝓝 0))
    (hm_rate : ∀ i, Tendsto (fun j => (m i j : ℝ) / (n j : ℝ)) atTop (𝓝 (q i)))
    (hh_rate : Tendsto (fun j => Real.log (h j : ℝ) / (n j : ℝ)) atTop (𝓝 α))
    (hw_rate : Tendsto (fun j => (Real.log (WE j) - Real.log (WD j)) / (n j : ℝ))
      atTop (𝓝 δ)) :
    (∑ i, q i * Real.log (VB i)) + α + δ ≤ Real.log VA := by
  have hs := tendsto_finsetSum Finset.univ (fun i _ => (hm_rate i).mul_const (Real.log (VB i)))
  have hl := (hs.add hh_rate).add hw_rate
  have hr := (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log VA) atTop
    (𝓝 (Real.log VA))).add (hu_rate.const_mul σ)
  have he : ∀ᶠ j : ℕ in atTop,
      (∑ i, ((m i j : ℝ) / (n j : ℝ)) * Real.log (VB i)) + Real.log (h j : ℝ) / (n j : ℝ) +
        (Real.log (WE j) - Real.log (WD j)) / (n j : ℝ) ≤
          Real.log VA + σ * (Real.log (u j : ℝ) / (n j : ℝ)) :=
    Eventually.of_forall fun j => ordered_extraction_log_bound VA VB hVA hVB σ
      (WD j) (WE j) (hWD j) (hWE j) (n j) (u j) (h j) (fun i => m i j)
      (hn j) (hu j) (hh j) (hfinite j)
  have h := le_of_tendsto_of_tendsto hl hr he
  simpa only [mul_zero, add_zero] using h

end BlockIdentities.Rectangular
