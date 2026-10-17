/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.CyclicClasses

/-! Genuine finite coordinate balancing of rectangular matrix tensors. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

/-- The cyclic triple of a rectangular matrix tensor is a square matrix tensor
on the actual product index type. The coordinate maps are upstream equivalences. -/
theorem classOf_rectangular_cyclic_product {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    classOf (Tensor.product (Tensor.product (Tensor.matrixCoefficients (K := K) A B C)
      (Tensor.matrixCoefficients B C A)) (Tensor.matrixCoefficients C A B)) =
      classOf (Tensor.matrixCoefficients (K := K) (A × B × C) (A × B × C) (A × B × C)) := by
  symm
  exact classOf_eq_of_reindex (Tensor.rectangularSquareX A B C)
    (Tensor.rectangularSquareY A B C) (Tensor.rectangularSquareZ A B C)
    Tensor.matrixCoefficients_cyclic_product_square

/-- A square matrix tensor on any finite index type is its dimension's matrix class. -/
theorem classOf_matrixCoefficients_square {I : Type*} [Fintype I] [DecidableEq I] :
    classOf (Tensor.matrixCoefficients (K := K) I I I) = matrixClass (Fintype.card I) := by
  let e := Fintype.equivFin I
  apply classOf_eq_of_reindex (Equiv.prodCongr e e) (Equiv.prodCongr e e) (Equiv.prodCongr e e)
  funext x y z
  change (if e x.2 = e y.1 ∧ e y.2 = e z.1 ∧ e z.2 = e x.1 then (1 : K) else 0) =
    (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0)
  simp only [e.injective.eq_iff]

/-- Rectangular balancing uses the literal product volume, over every field. -/
theorem tensorClass_symmetrize_matrixShape (D : MatrixShape) :
    tensorClass (symmetrize (D.tensor (K := K))) = matrixClass D.volume := by
  rw [tensorClass_symmetrize_eq]
  change classOf (Tensor.matrixCoefficients (K := K) (Fin D.a) (Fin D.b) (Fin D.c)) *
    cycleClass (classOf (Tensor.matrixCoefficients (K := K) (Fin D.a) (Fin D.b) (Fin D.c))) *
    cycleClass (cycleClass (classOf (Tensor.matrixCoefficients (K := K) (Fin D.a) (Fin D.b) (Fin D.c)))) = _
  simp only [cycleClass_classOf, Tensor.cyclic_matrixCoefficients]
  rw [← classOf_product, ← classOf_product, classOf_rectangular_cyclic_product,
    classOf_matrixCoefficients_square]
  simp only [Fintype.card_prod, Fintype.card_fin, MatrixShape.volume, Nat.mul_assoc]

end BlockIdentities.Square
