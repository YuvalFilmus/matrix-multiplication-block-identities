/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! A sublinear number of binary scalar supplies covers subexponential copies. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open Filter
open scoped Topology

/-- The explicit schedule ceil(log(b_n)/log 2) covers every source multiplicity,
including n=0, and has zero linear rate. This is a scalar schedule theorem,
with no tensor extraction or absorption assertion in its premises. -/
theorem exists_subexponential_binary_schedule (b : ℕ → ℕ) (hb : ∀ n, 0 < b n)
    (hRate : Tendsto (fun n : ℕ => Real.log (b n : ℝ) / (n : ℝ)) atTop (𝓝 0)) :
    ∃ ℓ : ℕ → ℕ, (∀ n, b n ≤ 2 ^ ℓ n) ∧
      Tendsto (fun n : ℕ => (ℓ n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  let ℓ : ℕ → ℕ := fun n => Nat.ceil (Real.log (b n : ℝ) / Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb : ∀ n, 0 ≤ Real.log (b n : ℝ) := by
    intro n
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (ne_of_gt (hb n))
  refine ⟨ℓ, ?_, ?_⟩
  · intro n
    have hbpos : 0 < (b n : ℝ) := by exact_mod_cast hb n
    have hceil : Real.log (b n : ℝ) / Real.log 2 ≤ (ℓ n : ℝ) := Nat.le_ceil _
    have hlogs : Real.log (b n : ℝ) ≤ (ℓ n : ℝ) * Real.log 2 :=
      (div_le_iff₀ hlog2).1 hceil
    have hbound : (b n : ℝ) ≤ (2 : ℝ) ^ ℓ n := by
      apply (Real.log_le_log_iff hbpos (pow_pos (by norm_num : (0 : ℝ) < 2) _)).1
      rw [Real.log_pow]
      exact hlogs
    exact_mod_cast hbound
  · have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div_atTop
        tendsto_natCast_atTop_atTop
    have hupper : Tendsto (fun n : ℕ =>
        (Real.log (b n : ℝ) / n) / Real.log 2 + 1 / (n : ℝ)) atTop (𝓝 0) := by
      simpa using (hRate.div_const (Real.log 2)).add hinv
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
    · exact Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · apply Eventually.of_forall
      intro n
      have hceil : (ℓ n : ℝ) ≤ Real.log (b n : ℝ) / Real.log 2 + 1 :=
        (Nat.ceil_lt_add_one (div_nonneg (hlogb n) hlog2.le)).le
      calc
        _ ≤ (Real.log (b n : ℝ) / Real.log 2 + 1) / (n : ℝ) :=
          div_le_div_of_nonneg_right hceil (Nat.cast_nonneg n)
        _ = _ := by ring

end BlockIdentities.Square
