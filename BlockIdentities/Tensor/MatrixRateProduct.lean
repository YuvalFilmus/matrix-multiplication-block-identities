/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.MatrixRate
public import BlockIdentities.Square.MatrixRateLimits

/-! Multiplication of matrix rates with the strict margin needed for flooring. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped Topology
variable {K : Type*} [Field K]

/-- Tensoring rate witnesses yields every strictly smaller product rate.
The strict margin is essential: products of natural floors need not dominate
the floor of the exact product at each size. -/
theorem MatrixRate.product_of_lt {A B : FiniteTensor K} {r s t : ℝ}
    (hA : MatrixRate A r) (hB : MatrixRate B s) (ht : 1 ≤ t) (hlt : t < r * s) :
    MatrixRate (product A B) t := by
  rw [matrixRate_iff_classes] at hA hB ⊢
  obtain ⟨hr, a, ha, har, hA⟩ := hA
  obtain ⟨hs, b, hb, hbr, hB⟩ := hB
  have hlog : ∀ n : ℕ, Real.log ((a n * b n : ℕ) : ℝ) / (n : ℝ) =
      Real.log (a n : ℝ) / (n : ℝ) + Real.log (b n : ℝ) / (n : ℝ) := by
    intro n
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast ne_of_gt (ha n))
      (by exact_mod_cast ne_of_gt (hb n)), add_div]
  refine ⟨ht, fun n => a n * b n, fun n => Nat.mul_pos (ha n) (hb n), ?_, ?_⟩
  · simpa only [hlog, add_zero] using har.add hbr
  · filter_upwards [hA, hB, eventually_natFloor_pow_le_product r s t hr hs ht hlt]
      with n hnA hnB hfloor
    have hprod := hnA.mul hnB
    have hsource : ((a n : TensorClass K) * tensorClass A ^ n) *
        ((b n : TensorClass K) * tensorClass B ^ n) =
        ((a n * b n : ℕ) : TensorClass K) * tensorClass (product A B) ^ n := by
      rw [tensorClass_product_eq, mul_pow, Nat.cast_mul]
      ring
    rw [hsource, ← matrixClass_mul] at hprod
    exact hprod.trans (ClassDegenerates.of_le (matrixClass_mono hfloor))

end BlockIdentities.Square
