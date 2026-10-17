/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Numerical consumption of finite extraction inequalities and their rates. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open Filter
open scoped BigOperators Topology

/-- Internal finite numerical inequality after taking logarithms. -/
theorem extraction_log_bound {ι : Type*} [Fintype ι]
    (VA : ℝ) (VB : ι → ℝ) (hVA : 1 ≤ VA) (hVB : ∀ i, 1 ≤ VB i)
    (ν : ℝ) (n a b u h : ℕ) (m : ι → ℕ)
    (hn : 1 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b) (hu : 1 ≤ u) (hh : 1 ≤ h)
    (hfinite : (h : ℝ) * (b : ℝ) ^ ν * ∏ i, VB i ^ (3 * m i) ≤
      (u : ℝ) ^ ν * VA ^ (3 * n) * (a : ℝ) ^ ν) :
    (∑ i, ((m i : ℝ) / (n : ℝ)) * Real.log (VB i)) +
      Real.log (h : ℝ) / (3 * (n : ℝ)) +
      ν * (Real.log ((b : ℝ) / (a : ℝ)) / (3 * (n : ℝ))) ≤
      Real.log VA + ν * (Real.log (u : ℝ) / (3 * (n : ℝ))) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hapos : 0 < (a : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ha)
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hb)
  have hupos : 0 < (u : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hu)
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hVpos : 0 < VA := lt_of_lt_of_le zero_lt_one hVA
  have hWpos (i : ι) : 0 < VB i := lt_of_lt_of_le zero_lt_one (hVB i)
  have hbp := Real.rpow_pos_of_pos hbpos ν
  have hup := Real.rpow_pos_of_pos hupos ν
  have hap := Real.rpow_pos_of_pos hapos ν
  have hp : 0 < ∏ i, VB i ^ (3 * m i) := Finset.prod_pos fun i _ => pow_pos (hWpos i) _
  have hl := Real.log_le_log (mul_pos (mul_pos hhpos hbp) hp) hfinite
  rw [Real.log_mul (ne_of_gt (mul_pos hhpos hbp)) (ne_of_gt hp),
    Real.log_mul (ne_of_gt hhpos) (ne_of_gt hbp),
    Real.log_mul (ne_of_gt (mul_pos hup (pow_pos hVpos _))) (ne_of_gt hap),
    Real.log_mul (ne_of_gt hup) (ne_of_gt (pow_pos hVpos _)),
    Real.log_rpow hbpos, Real.log_rpow hupos, Real.log_rpow hapos,
    Real.log_pow, Real.log_prod (fun i _ => ne_of_gt (pow_pos (hWpos i) _))] at hl
  simp only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat] at hl
  rw [Real.log_div (ne_of_gt hbpos) (ne_of_gt hapos)]
  have hnorm : (∑ i, ((m i : ℝ) / (n : ℝ)) * Real.log (VB i)) =
      (∑ i, (3 * (m i : ℝ)) * Real.log (VB i)) / (3 * (n : ℝ)) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [ne_of_gt hnpos] <;> ring
  rw [hnorm]
  have hdiv := div_le_div_of_nonneg_right hl (by positivity : 0 ≤ 3 * (n : ℝ))
  have hid :
      (Real.log (h : ℝ) + ν * Real.log (b : ℝ) +
        ∑ i, (3 * (m i : ℝ)) * Real.log (VB i)) / (3 * (n : ℝ)) -
        ν * Real.log (a : ℝ) / (3 * (n : ℝ)) =
      (∑ i, (3 * (m i : ℝ)) * Real.log (VB i)) / (3 * (n : ℝ)) +
        Real.log (h : ℝ) / (3 * (n : ℝ)) +
        ν * ((Real.log (b : ℝ) - Real.log (a : ℝ)) / (3 * (n : ℝ))) := by ring
  have hid' :
      (ν * Real.log (u : ℝ) + (3 * (n : ℝ)) * Real.log VA + ν * Real.log (a : ℝ)) /
        (3 * (n : ℝ)) - ν * Real.log (a : ℝ) / (3 * (n : ℝ)) =
      Real.log VA + ν * (Real.log (u : ℝ) / (3 * (n : ℝ))) := by
    field_simp [ne_of_gt hnpos] <;> ring
  linarith

/-- Internal numerical limit consumer for the exact extraction schedules. -/
theorem extraction_log_limit {ι : Type*} [Fintype ι]
    (VA : ℝ) (VB : ι → ℝ) (hVA : 1 ≤ VA) (hVB : ∀ i, 1 ≤ VB i)
    (ν : ℝ) (n a b u h : ℕ → ℕ) (m : ι → ℕ → ℕ)
    (hn : ∀ j, 1 ≤ n j) (ha : ∀ j, 1 ≤ a j) (hb : ∀ j, 1 ≤ b j)
    (hu : ∀ j, 1 ≤ u j) (hh : ∀ j, 1 ≤ h j)
    (hfinite : ∀ j, (h j : ℝ) * (b j : ℝ) ^ ν * ∏ i, VB i ^ (3 * m i j) ≤
      (u j : ℝ) ^ ν * VA ^ (3 * n j) * (a j : ℝ) ^ ν)
    (p : ι → ℝ) (α β : ℝ)
    (hu_rate : Tendsto (fun j => Real.log (u j : ℝ) / (n j : ℝ)) atTop (𝓝 0))
    (hm_rate : ∀ i, Tendsto (fun j => (m i j : ℝ) / (n j : ℝ)) atTop (𝓝 (p i)))
    (hh_rate : Tendsto (fun j => Real.log (h j : ℝ) / (3 * (n j : ℝ))) atTop (𝓝 α))
    (hab_rate : Tendsto (fun j => Real.log ((b j : ℝ) / (a j : ℝ)) /
      (3 * (n j : ℝ))) atTop (𝓝 β)) :
    (∑ i, p i * Real.log (VB i)) + α + ν * β ≤ Real.log VA := by
  have hs := tendsto_finsetSum Finset.univ (fun i _ => (hm_rate i).mul_const (Real.log (VB i)))
  have hleft := (hs.add hh_rate).add (hab_rate.const_mul ν)
  have hu3 : Tendsto (fun j => Real.log (u j : ℝ) / (3 * (n j : ℝ))) atTop (𝓝 0) := by
    simpa only [zero_div, div_div, mul_comm] using hu_rate.div_const 3
  have hright := (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log VA) atTop
    (𝓝 (Real.log VA))).add (hu3.const_mul ν)
  have hright' : Tendsto (fun j => Real.log VA +
      ν * (Real.log (u j : ℝ) / (3 * (n j : ℝ)))) atTop (𝓝 (Real.log VA)) := by
    simpa only [mul_zero, add_zero] using hright
  apply le_of_tendsto_of_tendsto hleft hright'
  exact Eventually.of_forall fun j => extraction_log_bound VA VB hVA hVB ν
    (n j) (a j) (b j) (u j) (h j) (fun i => m i j)
    (hn j) (ha j) (hb j) (hu j) (hh j) (hfinite j)

end BlockIdentities.Square
