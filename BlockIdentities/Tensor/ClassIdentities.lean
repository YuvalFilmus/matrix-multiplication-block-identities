/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.Definitions
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.DirectSumClass

/-! Exact finite coordinate bookkeeping for tensor powers and full copies.
Tensor classes are used only for finite mutual-restriction identifications. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators

variable {K : Type*} [Field K]

/-- Splitting off the first coordinate of a finite function is a bijection. -/
private def splitFirst {X : Type*} (n : ℕ) :
    (Fin (n + 1) → X) ≃ X × (Fin n → X) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := by cases p; rfl

/-- There is exactly one function from the empty coordinate set. -/
private def emptyCoordinates (X : Type*) : (Fin 0 → X) ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := Fin.elim0
  left_inv f := by funext i; exact Fin.elim0 i
  right_inv u := by cases u; rfl

/-- The concrete regrouped tensor product represents multiplication of classes. -/
theorem tensorClass_product_eq (A B : FiniteTensor K) :
    tensorClass (product A B) = tensorClass A * tensorClass B := rfl

/-- Tensor powers have the expected class, including the empty scalar power. -/
theorem tensorClass_power_eq (A : FiniteTensor K) (n : ℕ) :
    tensorClass (power A n) = tensorClass A ^ n := by
  change classOf (Tensor.power A.coeff n) = tensorClass A ^ n
  induction n with
  | zero =>
    rw [pow_zero]
    change classOf (Tensor.power A.coeff 0) =
      classOf (fun (_ _ _ : PUnit.{1}) => (1 : K))
    apply classOf_eq_of_reindex (emptyCoordinates _) (emptyCoordinates _)
      (emptyCoordinates _)
    funext x y z
    simp [Tensor.pullback, Tensor.power]
  | succ n ih =>
    calc
      classOf (Tensor.power A.coeff (n + 1)) =
          classOf (Tensor.product A.coeff (Tensor.power A.coeff n)) := by
        apply classOf_eq_of_reindex (splitFirst n) (splitFirst n) (splitFirst n)
        funext x y z
        simp [Tensor.pullback, Tensor.product, Tensor.power, splitFirst,
          Fin.prod_univ_succ]
      _ = classOf A.coeff * classOf (Tensor.power A.coeff n) :=
        classOf_product _ _
      _ = tensorClass A * tensorClass A ^ n := by rw [classOf_coeff, ih]
      _ = tensorClass A ^ (n + 1) := (pow_succ' _ _).symm

/-- Full direct-sum multiplicity is multiplication by a natural scalar class. -/
theorem tensorClass_copies_eq (m : ℕ) (A : FiniteTensor K) :
    tensorClass (copies m A) = (m : TensorClass K) * tensorClass A := by
  classical
  change classOf (Tensor.directSum (fun _ : Fin m => A.coeff)) = _
  rw [classOf_directSum]
  simp [nsmul_eq_mul]

/-- The diagonal tensor is the natural-number scalar in the tensor semiring. -/
theorem tensorClass_diagonal_eq (m : ℕ) :
    tensorClass (diagonal (K := K) m) = (m : TensorClass K) := by
  classical
  let scalar : Tensor K PUnit.{1} PUnit.{1} PUnit.{1} := fun _ _ _ => 1
  let S := Tensor.directSum (fun _ : Fin m => scalar)
  have hdiag : classOf (diagonal (K := K) m).coeff = classOf S := by
    apply classOf_eq_of_reindex (Equiv.prodUnique _ _).symm
      (Equiv.prodUnique _ _).symm (Equiv.prodUnique _ _).symm
    funext x y z
    change Fin m at x y z
    change (if x = y ∧ x = z then (1 : K) else 0) =
      (if x = y ∧ y = z then 1 else 0)
    by_cases hxy : x = y <;> by_cases hyz : y = z <;> simp_all
  rw [← classOf_coeff (diagonal (K := K) m), hdiag]
  change classOf (Tensor.directSum (fun _ : Fin m => scalar)) = _
  rw [classOf_directSum]
  have hs : classOf scalar = (1 : TensorClass K) := rfl
  simp [hs, nsmul_eq_mul]

end BlockIdentities.Square
