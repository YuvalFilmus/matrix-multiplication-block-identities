/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedValueOperations
public import BlockIdentities.Tensor.MatrixRestrictions

/-! Independent-copy upper bounds from an actual cubic matrix restriction.
No lower direct-sum or additive-value assertion is used. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {F : Type*} [Field F]

/-- A cubic matrix tensor restricts to u independent scalar copies, over every
field. Carrying T unchanged gives the actual conversion used by the bound. -/
theorem orientedValue_copies_le (S : InteriorSupport F) (T : TensorOf F)
    (u : ℕ) (hu : 1 ≤ u) :
    orientedValue S (T.copies u hu) ≤ (u : ℝ) ^ (∑ i, S.weight i) * orientedValue S T := by
  have hupos : 0 < u := lt_of_lt_of_le Nat.zero_lt_one hu
  let D : MatrixShape := ⟨u, u, u, hupos, hupos, hupos⟩
  have hclass : tensorClass (T.copies u hu).val ≤
      tensorClass (T.product D.nonzeroTensor).val := by
    simp only [NonzeroTensor.copies, NonzeroTensor.product, MatrixShape.nonzeroTensor,
      tensorClass_copies_eq, tensorClass_product_eq]
    have hD : tensorClass (D.tensor (K := AlgebraicClosure F)) = matrixClass u := rfl
    rw [hD]
    simpa only [mul_comm] using
      mul_mono (le_refl (tensorClass T.val)) (natCast_le_matrixClass u)
  have hconv : AsymptoticallyRestricts (T.product D.nonzeroTensor).val (T.copies u hu).val :=
    asymptoticallyRestricts_of_classDegenerates (ClassDegenerates.of_le hclass)
  have hweight : matrixWeight S D = (u : ℝ) ^ (∑ i, S.weight i) := by
    have hur : 0 < (u : ℝ) := by exact_mod_cast hupos
    change (u : ℝ) ^ S.weight 1 * (u : ℝ) ^ S.weight 2 * (u : ℝ) ^ S.weight 0 = _
    rw [← Real.rpow_add hur, ← Real.rpow_add hur]
    congr 1
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    change S.weight 1 + S.weight 2 + S.weight 0 = S.weight 0 + (S.weight 1 + (S.weight 2 + 0))
    ring
  have hh := orientedValue_mono S (T.product D.nonzeroTensor) (T.copies u hu) hconv
  rw [orientedValue_product_matrix, hweight] at hh
  exact hh

end BlockIdentities.Rectangular
