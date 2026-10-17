/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Square.MatrixRateLimits

/-! Integer scales with a strict margin for matrix-factor cancellation. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open Filter
open scoped Topology

/-- A strict real margin admits a positive integral block scale whose logarithmic
rate still exceeds the requested output rate. -/
theorem exists_matrixCancellation_scales (d : ℕ) (hd : 1 ≤ d)
    (α s : ℝ) (hs : 1 ≤ s) (hmargin : s < α / (d : ℝ)) :
    ∃ k b : ℕ, 1 ≤ k ∧ 1 ≤ b ∧
      ((d ^ k * b : ℕ) : ℝ) < α ^ k ∧ Real.log s < Real.log (b : ℝ) / (k : ℝ) := by
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  obtain ⟨β, hsβ, hβα⟩ := exists_between hmargin
  have hβ : 1 ≤ β := le_trans hs hsβ.le
  have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hlogs : Real.log s < Real.log β := Real.log_lt_log hspos hsβ
  have hrate := tendsto_log_natFloor_pow_div β hβ
  have hevent : ∀ᶠ k : ℕ in atTop,
      Real.log s < Real.log (Nat.floor (β ^ k) : ℝ) / (k : ℝ) :=
    hrate.eventually (eventually_gt_nhds hlogs)
  obtain ⟨k, hk, hlog⟩ := ((eventually_ge_atTop (1 : ℕ)).and hevent).exists
  refine ⟨k, Nat.floor (β ^ k), hk, one_le_natFloor_pow β hβ k, ?_, hlog⟩
  have hdb : (d : ℝ) * β < α := by
    simpa only [mul_comm] using (lt_div_iff₀ hdpos).1 hβα
  have hdbpos : 0 ≤ (d : ℝ) * β := (mul_pos hdpos hβpos).le
  have hpow : ((d : ℝ) * β) ^ k < α ^ k :=
    pow_lt_pow_left₀ hdb hdbpos (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk))
  have hfloor : (Nat.floor (β ^ k) : ℝ) ≤ β ^ k :=
    Nat.floor_le (pow_nonneg hβpos.le k)
  push_cast
  calc
    (d : ℝ) ^ k * (Nat.floor (β ^ k) : ℝ) ≤ (d : ℝ) ^ k * β ^ k :=
      mul_le_mul_of_nonneg_left hfloor (pow_nonneg hdpos.le k)
    _ = ((d : ℝ) * β) ^ k := (mul_pow _ _ _).symm
    _ < α ^ k := hpow

end BlockIdentities.Square
