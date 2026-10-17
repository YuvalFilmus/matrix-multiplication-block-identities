/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedGainOperations

/-! Matrix factors are charged exactly in actual gain witnesses. No boundedness
of the oriented gain supremum is assumed. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {F : Type*} [Field F]

/-- Carry a supplied matrix factor to every output copy. -/
theorem oriented_conversion_carry_matrix (T : TensorOf F) (M : MatrixShape)
    (n h : ℕ) (D E : MatrixShape)
    (hconv : AsymptoticallyRestricts (product (power T.val n) D.tensor) (copies h E.tensor)) :
    AsymptoticallyRestricts
      (product (power (T.product M.nonzeroTensor).val n) D.tensor)
      (copies h (E.product (M.power n)).tensor) := by
  apply (hconv.product (AsymptoticallyRestricts.refl (M.power n).tensor)).congr_classes
  · simp only [NonzeroTensor.product, MatrixShape.nonzeroTensor,
      tensorClass_product_eq, tensorClass_power_eq, tensorClass_matrixShape_power,
      mul_pow, mul_assoc, mul_left_comm, mul_comm]
  · simp only [tensorClass_product_eq, tensorClass_copies_eq,
      tensorClass_matrixShape_product, tensorClass_matrixShape_power, mul_assoc]

/-- Reclassify the consumed matrix factor as part of the charged input auxiliary. -/
theorem oriented_conversion_absorb_matrix (T : TensorOf F) (M : MatrixShape)
    (n h : ℕ) (D E : MatrixShape)
    (hconv : AsymptoticallyRestricts
      (product (power (T.product M.nonzeroTensor).val n) D.tensor) (copies h E.tensor)) :
    AsymptoticallyRestricts (product (power T.val n) (D.product (M.power n)).tensor)
      (copies h E.tensor) := by
  apply hconv.congr_classes
  · simp only [NonzeroTensor.product, MatrixShape.nonzeroTensor,
      tensorClass_product_eq, tensorClass_power_eq, tensorClass_matrixShape_product,
      tensorClass_matrixShape_power, mul_pow, mul_assoc, mul_left_comm, mul_comm]
  · rfl

/-- Multiplying by the prescribed matrix weight sends every gain to an actual
gain of the tensor with that matrix factor. -/
theorem matrixWeight_mul_mem_orientedGains (S : InteriorSupport F) (T : TensorOf F)
    (M : MatrixShape) {v : ℝ} (hv : v ∈ orientedGains S T) :
    matrixWeight S M * v ∈ orientedGains S (T.product M.nonzeroTensor) := by
  obtain ⟨n, h, hn, hh, D, E, hconv, hv⟩ := hv
  refine ⟨n, h, hn, hh, D, E.product (M.power n),
    oriented_conversion_carry_matrix T M n h D E hconv, ?_⟩
  have hbase : 0 ≤ (h : ℝ) * matrixWeight S E / matrixWeight S D :=
    (div_pos (mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh))
      (matrixWeight_pos S E)) (matrixWeight_pos S D)).le
  have heq : (h : ℝ) * matrixWeight S (E.product (M.power n)) / matrixWeight S D =
      ((h : ℝ) * matrixWeight S E / matrixWeight S D) * matrixWeight S M ^ n := by
    rw [matrixWeight_product, matrixWeight_power]
    ring
  rw [heq, Real.mul_rpow hbase (pow_nonneg (matrixWeight_pos S M).le _), hv,
    one_div, Real.pow_rpow_inv_natCast (matrixWeight_pos S M).le (by omega)]
  ring

/-- Dividing by the prescribed matrix weight produces an actual source gain;
the auxiliary remains a literal componentwise product of positive matrices. -/
theorem div_matrixWeight_mem_orientedGains (S : InteriorSupport F) (T : TensorOf F)
    (M : MatrixShape) {v : ℝ}
    (hv : v ∈ orientedGains S (T.product M.nonzeroTensor)) :
    v / matrixWeight S M ∈ orientedGains S T := by
  obtain ⟨n, h, hn, hh, D, E, hconv, hv⟩ := hv
  refine ⟨n, h, hn, hh, D.product (M.power n), E,
    oriented_conversion_absorb_matrix T M n h D E hconv, ?_⟩
  have hbase : 0 ≤ (h : ℝ) * matrixWeight S E / matrixWeight S D :=
    (div_pos (mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh))
      (matrixWeight_pos S E)) (matrixWeight_pos S D)).le
  have heq : (h : ℝ) * matrixWeight S E / matrixWeight S (D.product (M.power n)) =
      ((h : ℝ) * matrixWeight S E / matrixWeight S D) / matrixWeight S M ^ n := by
    rw [matrixWeight_product, matrixWeight_power]
    field_simp [(matrixWeight_pos S D).ne', (matrixWeight_pos S M).ne'] <;> ring
  rw [heq, Real.div_rpow hbase (pow_nonneg (matrixWeight_pos S M).le _), hv,
    one_div, Real.pow_rpow_inv_natCast (matrixWeight_pos S M).le (by omega)]

/-- The identity conversion realizes the exact weight of a positive matrix. -/
theorem matrixWeight_mem_orientedGains (S : InteriorSupport F) (M : MatrixShape) :
    matrixWeight S M ∈ orientedGains S (M.nonzeroTensor (K := AlgebraicClosure F)) := by
  refine ⟨1, 1, le_rfl, le_rfl, scalarShape, M, ?_, ?_⟩
  · apply (AsymptoticallyRestricts.refl (M.tensor (K := AlgebraicClosure F))).congr_classes
    · simp only [MatrixShape.nonzeroTensor, tensorClass_product_eq, tensorClass_power_eq,
        pow_one, tensorClass_matrixShape_scalar, mul_one]
    · simp only [tensorClass_copies_eq, Nat.cast_one, one_mul]
  · simp only [Nat.cast_one, one_mul, div_one, Real.rpow_one, matrixWeight_scalar]

end BlockIdentities.Rectangular
