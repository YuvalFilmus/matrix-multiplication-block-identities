/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace BlockIdentities.Square

open scoped BigOperators

/-- Literal terminal yield from the explicit convolution certificate, on its
manuscript domain of cutoffs at least two. -/
noncomputable def convolutionYield (a : {n : ℕ // 2 ≤ n}) : ℝ :=
  (3 * (a.val : ℝ) - 1) / 4 *
    ∏ j ∈ Finset.Ico 1 a.val, (1 + 1 / (3 * (j : ℝ)))

theorem convolutionYield_pos (a : {n : ℕ // 2 ≤ n}) : 0 < convolutionYield a := by
  have ha : (2 : ℝ) ≤ a.val := by exact_mod_cast a.property
  unfold convolutionYield
  apply mul_pos
  · exact div_pos (by linarith) (by norm_num)
  · apply Finset.prod_pos
    intro j hj
    have hjpos : 0 < (j : ℝ) := by
      exact_mod_cast (Finset.mem_Ico.mp hj).1
    positivity

/-- The elementary factor estimate used to lower-bound the terminal yield. -/
theorem convolution_factor_cube (j : ℕ) (hj : 1 ≤ j) :
    ((j : ℝ) + 1) / j ≤ (1 + 1 / (3 * (j : ℝ))) ^ 3 := by
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast hj
  have hjne : (j : ℝ) ≠ 0 := ne_of_gt hjpos
  field_simp [hjne]
  nlinarith [sq_nonneg (j : ℝ)]

/-- Cubing the product dominates the telescoping product of `(j+1)/j`. -/
theorem convolution_product_cube (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ≤ (∏ j ∈ Finset.Ico 1 n, (1 + 1 / (3 * (j : ℝ)))) ^ 3 := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn' : 1 ≤ n
      · have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn'
        have hfactor := convolution_factor_cube n hn'
        have hprod := ih hn'
        rw [Finset.prod_Ico_succ_top hn', mul_pow]
        have hfpos : 0 ≤ (1 + 1 / (3 * (n : ℝ))) ^ 3 := by positivity
        have hstep := mul_le_mul_of_nonneg_right hprod hfpos
        have hstep' := mul_le_mul_of_nonneg_left hfactor (le_of_lt hnpos)
        have hcancel : (n : ℝ) * (((n : ℝ) + 1) / n) = (n : ℝ) + 1 := by
          field_simp [ne_of_gt hnpos]
        rw [hcancel] at hstep'
        push_cast
        exact hstep'.trans hstep
      · have : n = 0 := by omega
        subst n
        norm_num

/-- Polynomial form of the source estimate `L ≥ a^(4/3)/2`, avoiding real
fractional powers. This is purely the explicit certificate's scalar growth. -/
theorem convolutionYield_cube_lower (a : {n : ℕ // 2 ≤ n}) :
    (a.val : ℝ) ^ 4 ≤ 8 * convolutionYield a ^ 3 := by
  have ha : (2 : ℝ) ≤ a.val := by exact_mod_cast a.property
  have hap : 0 ≤ (a.val : ℝ) := by positivity
  have hcoef : 0 ≤ 3 * (a.val : ℝ) - 1 := by linarith
  have hp := convolution_product_cube a.val (by omega : 1 ≤ a.val)
  have hc : (a.val : ℝ) ^ 3 ≤ (3 * (a.val : ℝ) - 1) ^ 3 / 8 := by
    have hbase : 2 * (a.val : ℝ) ≤ 3 * (a.val : ℝ) - 1 := by linarith
    have hcub := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (a.val : ℝ)) hbase 3
    nlinarith [hcub]
  have hmul := mul_le_mul hc hp hap (by positivity : 0 ≤ (3 * (a.val : ℝ) - 1) ^ 3 / 8)
  unfold convolutionYield
  rw [mul_pow, div_pow]
  nlinarith [hmul]

end BlockIdentities.Square
