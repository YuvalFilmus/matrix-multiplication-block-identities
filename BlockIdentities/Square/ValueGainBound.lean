/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! A loose finite numerical bound for the ordinary-value extraction gain. -/

@[expose] public section

namespace BlockIdentities.Square

/-- The quadratic flattening bound controls each ordinary-value candidate.
This is purely numerical and assumes no tensor value inequality. The estimate
uses the safe loose bound `h*m^rho ≤ (h*m^2)^3`. -/
theorem valueGain_le_of_quadratic_dimension_bound
    (n h m D : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) (hm : 1 ≤ m) (hD : 1 ≤ D)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (2 : ℝ) 3) (hdim : h * m ^ 2 ≤ D ^ n) :
    ((h : ℝ) * (m : ℝ) ^ ρ) ^ (1 / (3 * (n : ℝ))) ≤ D := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hhlog : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast hh)
  have hmlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hdimR : (h : ℝ) * (m : ℝ) ^ (2 : ℕ) ≤ (D : ℝ) ^ n := by
    exact_mod_cast hdim
  have hdimlog := Real.log_le_log
    (mul_pos hhpos (pow_pos hmpos 2)) hdimR
  rw [Real.log_mul (ne_of_gt hhpos) (pow_ne_zero 2 (ne_of_gt hmpos)),
    Real.log_pow, Real.log_pow] at hdimlog
  norm_num at hdimlog
  have hρlog := mul_le_mul_of_nonneg_right hρ.2 hmlog
  have hbound : Real.log (h : ℝ) + ρ * Real.log (m : ℝ) ≤
      3 * (n : ℝ) * Real.log (D : ℝ) := by
    nlinarith [hdimlog, hρlog]
  apply (Real.rpow_le_iff_le_log
    (mul_pos hhpos (Real.rpow_pos_of_pos hmpos ρ)) hDpos).2
  rw [Real.log_mul (ne_of_gt hhpos) (ne_of_gt (Real.rpow_pos_of_pos hmpos ρ)),
    Real.log_rpow hmpos ρ]
  calc
    _ = (Real.log (h : ℝ) + ρ * Real.log (m : ℝ)) / (3 * (n : ℝ)) := by ring
    _ ≤ Real.log (D : ℝ) := (div_le_iff₀ (by positivity : 0 < 3 * (n : ℝ))).2
      (by nlinarith [hbound])

end BlockIdentities.Square
