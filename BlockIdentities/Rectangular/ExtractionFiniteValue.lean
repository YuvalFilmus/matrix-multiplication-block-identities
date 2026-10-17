/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedValueCopies
public import BlockIdentities.Rectangular.OrientedValueCopiesLower
public import BlockIdentities.Tensor.ValueProductList

/-! Actual finite oriented-value inequalities for ordered tensor extractions. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open scoped BigOperators
variable {F : Type*} [Field F]

theorem orientedValue_tensorProductList (S : InteriorSupport F) (L : List (TensorOf F)) :
    (L.map (orientedValue S)).prod ≤ orientedValue S (NonzeroTensor.tensorProductList L) := by
  induction L with
  | nil =>
    change 1 ≤ orientedValue S (NonzeroTensor.tensorProductList [])
    exact one_le_orientedValue S _
  | cons T L ih =>
    change orientedValue S T * (L.map (orientedValue S)).prod ≤
      orientedValue S (T.product (NonzeroTensor.tensorProductList L))
    exact (mul_le_mul_of_nonneg_left ih
      (le_trans zero_le_one (one_le_orientedValue S T))).trans
        (orientedValue_product_le S T _)

/-- The finite inequality is obtained from actual conversions and proved value
laws. No cyclicity, symmetrization or tensor-product equality is required. -/
theorem ordered_extraction_finite_value_bound (S : InteriorSupport F) (A : TensorOf F)
    (L : List (TensorOf F)) (D E : MatrixShape) (n u h : ℕ)
    (hu : 1 ≤ u) (hh : 1 ≤ h)
    (hconvert : AsymptoticallyRestricts
      (copies u (product (power A.val n) D.tensor))
      (copies h (product (NonzeroTensor.tensorProductList L).val E.tensor))) :
    (h : ℝ) * matrixWeight S E * (L.map (orientedValue S)).prod ≤
      (u : ℝ) ^ (∑ i, S.weight i) * orientedValue S A ^ n * matrixWeight S D := by
  let Q := NonzeroTensor.tensorProductList L
  let P := (A.power n).product D.nonzeroTensor
  let R := Q.product E.nonzeroTensor
  have hm : orientedValue S (R.copies h hh) ≤ orientedValue S (P.copies u hu) :=
    orientedValue_mono S (P.copies u hu) (R.copies h hh) hconvert
  have hlo := mul_orientedValue_le_copies S R h hh
  have hup := orientedValue_copies_le S P u hu
  have hp : orientedValue S P = matrixWeight S D * orientedValue S A ^ n := by
    rw [orientedValue_product_matrix, orientedValue_power]
  have hr : orientedValue S R = matrixWeight S E * orientedValue S Q :=
    orientedValue_product_matrix S Q E
  have hprod := orientedValue_tensorProductList S L
  calc
    _ ≤ (h : ℝ) * matrixWeight S E * orientedValue S Q :=
      mul_le_mul_of_nonneg_left hprod
        (mul_nonneg (Nat.cast_nonneg _) (matrixWeight_pos S E).le)
    _ = (h : ℝ) * orientedValue S R := by rw [hr]; ring
    _ ≤ orientedValue S (R.copies h hh) := hlo
    _ ≤ orientedValue S (P.copies u hu) := hm
    _ ≤ (u : ℝ) ^ (∑ i, S.weight i) * orientedValue S P := hup
    _ = _ := by rw [hp]; ring

end BlockIdentities.Rectangular
