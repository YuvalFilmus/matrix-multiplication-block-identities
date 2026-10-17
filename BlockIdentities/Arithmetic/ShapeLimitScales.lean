/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Definitions
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Genuine positive integer scales for logarithmic shape comparisons. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Arithmetic
open Filter
open scoped NNReal Topology

/-- Ceiling exponential sizes grow to infinity without a change of log rate. -/
theorem tendsto_ceil_exp_nat_atTop :
    Tendsto (fun j : ℕ => ⌈Real.exp ((j : ℝ) + 1)⌉₊) atTop atTop := by
  apply tendsto_atTop_mono (fun j => ?_) tendsto_id
  have he := Real.add_one_le_exp ((j : ℝ) + 1)
  have hh : (j : ℝ) ≤ (⌈Real.exp ((j : ℝ) + 1)⌉₊ : ℝ) :=
    (by linarith : (j : ℝ) ≤ Real.exp ((j : ℝ) + 1)).trans (Nat.le_ceil _)
  exact_mod_cast hh

theorem one_le_ceil_exp_nat (j : ℕ) : 1 ≤ ⌈Real.exp ((j : ℝ) + 1)⌉₊ := by
  have he : (1 : ℝ) ≤ Real.exp ((j : ℝ) + 1) := Real.one_le_exp_iff.mpr (by positivity)
  have hh := he.trans (Nat.le_ceil (Real.exp ((j : ℝ) + 1)))
  exact_mod_cast hh

/-- The integer scale has the same logarithmic growth as exp(j+1). -/
theorem tendsto_log_ceil_exp_nat_div :
    Tendsto (fun j : ℕ => Real.log (⌈Real.exp ((j : ℝ) + 1)⌉₊ : ℝ) /
      ((j : ℝ) + 1)) atTop (𝓝 1) := by
  have hx : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have herror : Tendsto (fun j : ℕ => Real.log 2 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hx
  have hupper : Tendsto (fun j : ℕ => 1 + Real.log 2 / ((j : ℝ) + 1)) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add herror
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · apply Eventually.of_forall
    intro j
    have hpos : 0 < (j : ℝ) + 1 := by positivity
    have hl := Real.log_le_log (Real.exp_pos ((j : ℝ) + 1))
      (Nat.le_ceil (Real.exp ((j : ℝ) + 1)))
    rw [Real.log_exp] at hl
    exact (le_div_iff₀ hpos).mpr (by simpa only [one_mul] using hl)
  · apply Eventually.of_forall
    intro j
    have hpos : 0 < (j : ℝ) + 1 := by positivity
    have he : 1 ≤ Real.exp ((j : ℝ) + 1) := Real.one_le_exp_iff.mpr hpos.le
    have hceil : (⌈Real.exp ((j : ℝ) + 1)⌉₊ : ℝ) ≤ 2 * Real.exp ((j : ℝ) + 1) := by
      have hc := (Nat.ceil_lt_add_one (le_of_lt (Real.exp_pos ((j : ℝ) + 1)))).le
      linarith
    have hn : 0 < (⌈Real.exp ((j : ℝ) + 1)⌉₊ : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_ceil_exp_nat j))
    have hl := Real.log_le_log hn hceil
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hl
    apply (div_le_iff₀ hpos).mpr
    have hid : (1 + Real.log 2 / ((j : ℝ) + 1)) * ((j : ℝ) + 1) =
        Real.log 2 + ((j : ℝ) + 1) := by
      field_simp [ne_of_gt hpos]
      ring
    rw [hid]
    exact hl

/-- A log-rate upper bound gives an actual finite index-size comparison. -/
theorem le_innerSize_ceil_exp_of_log_div_le {d : ℕ} (hd : 1 ≤ d)
    {x : ℝ} (hx : 0 < x) (a : ℝ≥0)
    (h : Real.log (d : ℝ) / x ≤ (a : ℝ)) :
    d ≤ innerSize ⌈Real.exp x⌉₊ a := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hlog : Real.log (d : ℝ) ≤ x * (a : ℝ) := by
    have hh := (div_le_iff₀ hx).mp h
    linarith
  have he : (d : ℝ) ≤ Real.exp (x * (a : ℝ)) := by
    rw [← Real.exp_log hdpos]
    exact Real.exp_le_exp.mpr hlog
  rw [Real.exp_mul] at he
  have hp := Real.rpow_le_rpow (Real.exp_pos x).le (Nat.le_ceil (Real.exp x)) a.property
  have hh := (he.trans hp).trans (Nat.le_ceil ((⌈Real.exp x⌉₊ : ℝ) ^ (a : ℝ)))
  exact_mod_cast hh
end BlockIdentities.Arithmetic
