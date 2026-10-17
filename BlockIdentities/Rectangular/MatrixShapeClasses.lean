/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.MatrixWeightProducts
public import BlockIdentities.Tensor.ClassIdentities
public import Mathlib.Logic.Equiv.Fin.Basic

/-! Exact mutual-restriction classes of componentwise positive matrix shapes. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

theorem tensorClass_matrixShape_product (D E : MatrixShape) :
    tensorClass ((D.product E).tensor (K := K)) =
      tensorClass D.tensor * tensorClass E.tensor := by
  classical
  let ea : Fin (D.a * E.a) ≃ Fin D.a × Fin E.a := finProdFinEquiv.symm
  let eb : Fin (D.b * E.b) ≃ Fin D.b × Fin E.b := finProdFinEquiv.symm
  let ec : Fin (D.c * E.c) ≃ Fin D.c × Fin E.c := finProdFinEquiv.symm
  change classOf (Tensor.matrixCoefficients (K := K)
    (Fin (D.a * E.a)) (Fin (D.b * E.b)) (Fin (D.c * E.c))) =
      classOf (Tensor.matrixCoefficients (K := K) (Fin D.a) (Fin D.b) (Fin D.c)) *
      classOf (Tensor.matrixCoefficients (K := K) (Fin E.a) (Fin E.b) (Fin E.c))
  calc
    _ = classOf (Tensor.matrixCoefficients (K := K) (Fin D.a × Fin E.a)
        (Fin D.b × Fin E.b) (Fin D.c × Fin E.c)) := by
      apply classOf_eq_of_reindex (Equiv.prodCongr ea eb)
        (Equiv.prodCongr eb ec) (Equiv.prodCongr ec ea)
      funext x y z
      change (if eb x.2 = eb y.1 ∧ ec y.2 = ec z.1 ∧ ea z.2 = ea x.1
        then (1 : K) else 0) = (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0)
      simp only [ea.injective.eq_iff, eb.injective.eq_iff, ec.injective.eq_iff]
    _ = classOf (Tensor.product
        (Tensor.matrixCoefficients (K := K) (Fin D.a) (Fin D.b) (Fin D.c))
        (Tensor.matrixCoefficients (K := K) (Fin E.a) (Fin E.b) (Fin E.c))) := by
      apply classOf_eq_of_reindex
        (Equiv.prodProdProdComm (Fin D.a) (Fin E.a) (Fin D.b) (Fin E.b))
        (Equiv.prodProdProdComm (Fin D.b) (Fin E.b) (Fin D.c) (Fin E.c))
        (Equiv.prodProdProdComm (Fin D.c) (Fin E.c) (Fin D.a) (Fin E.a))
      funext x y z
      exact Tensor.matrixCoefficients_product x y z
    _ = _ := classOf_product _ _

theorem tensorClass_matrixShape_scalar : tensorClass (scalarShape.tensor (K := K)) = 1 := by
  change matrixClass 1 = 1
  exact matrixClass_one

theorem tensorClass_matrixShape_power (D : MatrixShape) (n : ℕ) :
    tensorClass ((D.power n).tensor (K := K)) = tensorClass D.tensor ^ n := by
  induction n with
  | zero =>
    change tensorClass (scalarShape.tensor (K := K)) = _
    rw [tensorClass_matrixShape_scalar, pow_zero]
  | succ n ih =>
    have heq : D.power (n + 1) = (D.power n).product D := by
      cases D
      simp only [MatrixShape.power, MatrixShape.product, pow_succ]
    rw [heq, tensorClass_matrixShape_product, ih, pow_succ]

end BlockIdentities.Rectangular
