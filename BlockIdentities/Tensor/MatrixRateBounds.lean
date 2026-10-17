/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.MatrixRate
public import BlockIdentities.Tensor.ValueBounds
public import BlockIdentities.Square.MatrixRateLimits

/-! A finite bound on the actual matrix-rate witness set, without a value axiom. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped Topology
variable {K : Type*} [Field K]

/-- Dropping a redundant one-copy wrapper gives the usual square flattening bound. -/
theorem Degenerates.square_dimension_le {A : FiniteTensor K} {m : ℕ}
    (hm : 1 ≤ m) (h : Degenerates A (square m)) : m ^ 2 ≤ A.nz := by
  have hc := (classDegenerates_tensorClass_iff A (square m)).2 h
  have hd : Degenerates A (copies 1 (square m)) := by
    apply (classDegenerates_tensorClass_iff _ _).1
    simpa only [tensorClass_copies_eq, Nat.cast_one, one_mul] using hc
  simpa only [one_mul] using hd.copies_square_dimension_le hm

/-- All matrix-dimension rate witnesses are bounded by a fixed coordinate
constant. This is intentionally a loose finite bound, not an asymptotic-rank law. -/
theorem MatrixRate.le_coordinate_bound {A : FiniteTensor K} {r : ℝ}
    (h : MatrixRate A r) : r ≤ (max 1 A.nz : ℕ) := by
  obtain ⟨hr, b, hb, hbrate, h⟩ := h
  let D := max 1 A.nz
  have hD : 1 ≤ D := le_max_left _ _
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hfloor := tendsto_log_natFloor_pow_div r hr
  have hleft : Tendsto (fun n : ℕ => 2 * (Real.log ((Nat.floor (r ^ n) : ℕ) : ℝ) /
      (n : ℝ))) atTop (𝓝 (2 * Real.log r)) := tendsto_const_nhds.mul hfloor
  have hright : Tendsto (fun n : ℕ => Real.log (b n : ℝ) / (n : ℝ) +
      Real.log (D : ℝ)) atTop (𝓝 (Real.log (D : ℝ))) := by
    simpa only [zero_add] using hbrate.add_const (Real.log (D : ℝ))
  have hevent : ∀ᶠ n : ℕ in atTop,
      2 * (Real.log ((Nat.floor (r ^ n) : ℕ) : ℝ) / (n : ℝ)) ≤
        Real.log (b n : ℝ) / (n : ℝ) + Real.log (D : ℝ) := by
    filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with n hn hnpos
    have hm : 1 ≤ Nat.floor (r ^ n) := one_le_natFloor_pow r hr n
    have hdim := hn.square_dimension_le hm
    have hnz : (copies (b n) (power A n)).nz = b n * A.nz ^ n := by
      change Fintype.card (Fin (b n) × Fin (Fintype.card (Fin n → Fin A.nz))) = _
      simp only [Fintype.card_prod, Fintype.card_pi_const, Fintype.card_fin]
    rw [hnz] at hdim
    have hdim' : Nat.floor (r ^ n) ^ 2 ≤ b n * D ^ n :=
      hdim.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (le_max_right 1 A.nz) n))
    have hmpos : 0 < ((Nat.floor (r ^ n) : ℕ) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    have hbpos : 0 < (b n : ℝ) := by exact_mod_cast hb n
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hnpos)
    have hlog := Real.log_le_log (pow_pos hmpos 2)
      (show (((Nat.floor (r ^ n) : ℕ) : ℝ) ^ (2 : ℕ)) ≤
        (b n : ℝ) * (D : ℝ) ^ n by exact_mod_cast hdim')
    rw [Real.log_pow, Real.log_mul (ne_of_gt hbpos) (pow_ne_zero n (ne_of_gt hDpos)),
      Real.log_pow] at hlog
    have hdiv := div_le_div_of_nonneg_right hlog (le_of_lt hnreal)
    convert hdiv using 1 <;> field_simp <;> ring
  have hlog : 2 * Real.log r ≤ Real.log (D : ℝ) :=
    le_of_tendsto_of_tendsto hleft hright hevent
  have hrlog : 0 ≤ Real.log r := Real.log_nonneg hr
  exact (Real.log_le_log_iff hrpos hDpos).1 (by linarith)

end BlockIdentities.Square
