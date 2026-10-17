/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.MatrixRate
public import BlockIdentities.Tensor.MatrixBorderRank
public import BlockIdentities.Square.MatrixRateLimits

/-! Actual diagonal-source matrix rates obey the exact-rank exponent bound. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped BigOperators Topology
variable {K : Type*} [Field K] [Infinite K]

/-- A fixed scalar supply bounds every genuine matrix-dimension rate at the
true exact-rank exponent. The copy overhead vanishes only after taking logs. -/
theorem MatrixRate.diagonal_rpow_le {R : ℕ} (hR : 1 ≤ R) {q : ℝ}
    (hRate : MatrixRate (diagonal (K := K) R) q) :
    q ^ exactRankExponent K ≤ (R : ℝ) := by
  obtain ⟨hq, a, ha, harate, he⟩ := (matrixRate_iff_classes _ _).1 hRate
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hleft : Tendsto (fun n : ℕ => exactRankExponent K *
      (Real.log (Nat.floor (q ^ n) : ℝ) / (n : ℝ))) atTop
      (𝓝 (exactRankExponent K * Real.log q)) :=
    (tendsto_log_natFloor_pow_div q hq).const_mul _
  have hright : Tendsto (fun n : ℕ => Real.log (a n : ℝ) / (n : ℝ) + Real.log (R : ℝ))
      atTop (𝓝 (Real.log (R : ℝ))) := by
    simpa only [zero_add] using harate.add_const (Real.log (R : ℝ))
  have hbound : ∀ᶠ n : ℕ in atTop,
      exactRankExponent K * (Real.log (Nat.floor (q ^ n) : ℝ) / (n : ℝ)) ≤
        Real.log (a n : ℝ) / (n : ℝ) + Real.log (R : ℝ) := by
    filter_upwards [he, eventually_ge_atTop (1 : ℕ)] with n hn hnpos
    have hm : 1 ≤ Nat.floor (q ^ n) := one_le_natFloor_pow q hq n
    have hd : Degenerates (diagonal (K := K) (a n * R ^ n)) (square (Nat.floor (q ^ n))) := by
      apply (classDegenerates_tensorClass_iff _ _).1
      simpa only [tensorClass_diagonal_eq, tensorClass_square_eq, Nat.cast_mul, Nat.cast_pow]
        using hn
    have hf := Degenerates.matrix_rpow_exactRankExponent_le hm hd
    have hmpos : 0 < (Nat.floor (q ^ n) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    have hapos : 0 < (a n : ℝ) := by exact_mod_cast ha n
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hnpos)
    have hlog := Real.log_le_log (Real.rpow_pos_of_pos hmpos _) hf
    simp only [Nat.cast_mul, Nat.cast_pow] at hlog
    rw [Real.log_rpow hmpos, Real.log_mul (ne_of_gt hapos)
      (pow_ne_zero n (ne_of_gt hRpos)), Real.log_pow] at hlog
    have hdiv := div_le_div_of_nonneg_right hlog hnreal.le
    convert hdiv using 1 <;> field_simp <;> ring
  have hlog : exactRankExponent K * Real.log q ≤ Real.log (R : ℝ) :=
    le_of_tendsto_of_tendsto hleft hright hbound
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hqpos _) hRpos).1
  rw [Real.log_rpow hqpos]
  exact hlog

end BlockIdentities.Square
