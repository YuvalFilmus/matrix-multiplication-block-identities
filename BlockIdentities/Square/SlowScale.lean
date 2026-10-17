/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! An explicit slow scale for the rounded numerical overhead in cancellation. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open Filter
open scoped Topology

private theorem sqrt_tendsto_atTop : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b * b)] with n hn
  exact Nat.le_sqrt.mpr hn

private theorem sqrt_div_tendsto_zero :
    Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hk : Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp sqrt_tendsto_atTop
  have hi : Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ)⁻¹) atTop (𝓝 0) :=
    hk.inv_tendsto_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hi
  · exact Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hkpos : 0 < (Nat.sqrt n : ℝ) := by
      exact_mod_cast Nat.sqrt_pos.mpr (show 0 < n by omega)
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hnpos hkpos).2
    simpa only [one_mul] using
      (show (Nat.sqrt n : ℝ) * Nat.sqrt n ≤ n by exact_mod_cast Nat.sqrt_le n)

/-- Pure numerical rounding step of asymptotic cancellation. The explicit scale
`k=floor(sqrt n)` diverges while its one-time and remainder costs have zero
exponential rate. This theorem makes no claim about tensor conversions. -/
theorem exists_slowScale_overhead (a : ℕ → ℕ) (ha : ∀ k, 0 < a k)
    (haRate : Tendsto (fun k : ℕ => Real.log (a k : ℝ) / (k : ℝ)) atTop (𝓝 0))
    (R S : ℕ) (hR : 0 < R) (hS : 0 < S) :
    ∃ c : ℕ → ℕ, (∀ n, 0 < c n) ∧
      Tendsto (fun n : ℕ => Real.log (c n : ℝ) / (n : ℝ)) atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
        R ^ k * a k ^ (n / k) * S ^ (n % k) ≤ c n := by
  let c : ℕ → ℕ := fun n =>
    R ^ Nat.sqrt n * a (Nat.sqrt n) ^ (n / Nat.sqrt n) * S ^ (n % Nat.sqrt n)
  have hc : ∀ n, 0 < c n := by
    intro n
    exact Nat.mul_pos (Nat.mul_pos (pow_pos hR _) (pow_pos (ha _) _)) (pow_pos hS _)
  refine ⟨c, hc, ?_, ?_⟩
  · have hupper : Tendsto (fun n : ℕ =>
        (Real.log (R : ℝ) + Real.log (S : ℝ)) * ((Nat.sqrt n : ℝ) / n) +
          Real.log (a (Nat.sqrt n) : ℝ) / Nat.sqrt n) atTop (𝓝 0) := by
      have hfirst := (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => Real.log (R : ℝ) + Real.log (S : ℝ)) atTop
        (𝓝 (Real.log (R : ℝ) + Real.log (S : ℝ)))).mul sqrt_div_tendsto_zero
      simpa using hfirst.add (haRate.comp sqrt_tendsto_atTop)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · exact Eventually.of_forall fun n => div_nonneg
        (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (ne_of_gt (hc n))))
        (Nat.cast_nonneg n)
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      let k := Nat.sqrt n
      have hkNat : 0 < k := Nat.sqrt_pos.mpr (by omega)
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkNat
      have hRpos : 0 < (R : ℝ) := by exact_mod_cast hR
      have hSpos : 0 < (S : ℝ) := by exact_mod_cast hS
      have hapos : 0 < (a k : ℝ) := by exact_mod_cast ha k
      have hloga : 0 ≤ Real.log (a k : ℝ) := Real.log_nonneg (by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (ne_of_gt (ha k)))
      have hlogS : 0 ≤ Real.log (S : ℝ) := Real.log_nonneg (by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (ne_of_gt hS))
      have hquot : ((n / k : ℕ) : ℝ) * k ≤ n := by
        exact_mod_cast Nat.div_mul_le_self n k
      have hrem : ((n % k : ℕ) : ℝ) ≤ k := by
        exact_mod_cast (Nat.mod_lt n hkNat).le
      have hquotlog := mul_le_mul_of_nonneg_right hquot hloga
      have hremlog := mul_le_mul_of_nonneg_right hrem hlogS
      have hdiv : ((n / k : ℕ) : ℝ) * Real.log (a k : ℝ) / n ≤
          Real.log (a k : ℝ) / k := by
        apply (div_le_div_iff₀ hnpos hkpos).2
        nlinarith [hquotlog]
      have hlogc : Real.log (c n : ℝ) =
          (k : ℝ) * Real.log (R : ℝ) + ((n / k : ℕ) : ℝ) * Real.log (a k : ℝ) +
            ((n % k : ℕ) : ℝ) * Real.log (S : ℝ) := by
        simp only [c, Nat.cast_mul, Nat.cast_pow]
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity)]
        simp only [Real.log_pow]
        rfl
      change Real.log (c n : ℝ) / n ≤
        (Real.log (R : ℝ) + Real.log (S : ℝ)) * ((k : ℝ) / n) +
          Real.log (a k : ℝ) / k
      rw [hlogc]
      calc
        _ ≤ ((k : ℝ) * Real.log (R : ℝ) + ((n / k : ℕ) : ℝ) *
            Real.log (a k : ℝ) + (k : ℝ) * Real.log (S : ℝ)) / n :=
          div_le_div_of_nonneg_right (by linarith [hremlog]) hnpos.le
        _ = (Real.log (R : ℝ) + Real.log (S : ℝ)) * ((k : ℝ) / n) +
            ((n / k : ℕ) : ℝ) * Real.log (a k : ℝ) / n := by ring
        _ ≤ _ := add_le_add le_rfl hdiv
  · intro n hn
    refine ⟨Nat.sqrt n, ?_, Nat.sqrt_le_self n, le_rfl⟩
    exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Nat.sqrt_pos.mpr (by omega)))

end BlockIdentities.Square
