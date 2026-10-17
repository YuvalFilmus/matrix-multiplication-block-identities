/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ClassIdentities
public import BlockIdentities.Tensor.MatrixRestrictions
public import Mathlib.Algebra.BigOperators.Fin

/-! Literal product lists represent finite products in the restriction quotient. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K : Type*} [Field K]

theorem tensorClass_tensorProductList (L : List (FiniteTensor K)) :
    tensorClass (tensorProductList L) = (L.map tensorClass).prod := by
  induction L with
  | nil =>
    change tensorClass (square (K := K) 1) = 1
    rw [tensorClass_square_eq, matrixClass_one]
  | cons A L ih =>
    change tensorClass (product A (tensorProductList L)) = tensorClass A * (L.map tensorClass).prod
    rw [tensorClass_product_eq, ih]

theorem tensorClass_tensorProductList_ofFn {n : ℕ} (A : Fin n → FiniteTensor K) :
    tensorClass (tensorProductList (List.ofFn A)) = ∏ i, tensorClass (A i) := by
  rw [tensorClass_tensorProductList, List.map_ofFn, List.prod_ofFn]
  rfl

end BlockIdentities.Square
