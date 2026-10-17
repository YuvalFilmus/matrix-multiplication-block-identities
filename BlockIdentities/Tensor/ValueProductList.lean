/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ValueSupermultiplicativity
public import BlockIdentities.Tensor.ValuePowers
public import BlockIdentities.Tensor.RankOneValue
public import Mathlib.Algebra.BigOperators.Fin

/-! Literal finite tensor-product lists with produced nonzero/cyclic witnesses. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K : Type*} [Field K]

theorem nonzero_tensorProductList (L : List (NonzeroTensor K)) :
    Nonzero (tensorProductList (L.map Subtype.val)) := by
  induction L with
  | nil => exact nonzero_square le_rfl
  | cons A L ih => exact nonzero_product A.property ih

/-- The exact source product-list constructor, bundled only with nonzeroness. -/
def NonzeroTensor.tensorProductList (L : List (NonzeroTensor K)) : NonzeroTensor K :=
  ⟨BlockIdentities.Square.tensorProductList (L.map Subtype.val), nonzero_tensorProductList L⟩

@[simp] theorem tensorProductList_nil :
    NonzeroTensor.tensorProductList ([] : List (NonzeroTensor K)) = nonzeroSquare 1 le_rfl := rfl

@[simp] theorem tensorProductList_cons (A : NonzeroTensor K) (L : List (NonzeroTensor K)) :
    NonzeroTensor.tensorProductList (A :: L) = A.product (NonzeroTensor.tensorProductList L) := rfl

theorem tensorProductList_cycleClass_fixed (L : List (NonzeroTensor K))
    (hL : ∀ A ∈ L, cycleClass (tensorClass A.val) = tensorClass A.val) :
    cycleClass (tensorClass (NonzeroTensor.tensorProductList L).val) =
      tensorClass (NonzeroTensor.tensorProductList L).val := by
  induction L with
  | nil =>
    change cycleClass (tensorClass (square (K := K) 1)) = tensorClass (square (K := K) 1)
    rw [tensorClass_square_eq, cycleClass_matrixClass]
  | cons A L ih =>
    have hA := hL A (List.mem_cons_self)
    have htail : ∀ B ∈ L, cycleClass (tensorClass B.val) = tensorClass B.val :=
      fun B hB => hL B (List.mem_cons_of_mem A hB)
    change cycleClass (tensorClass (product A.val (NonzeroTensor.tensorProductList L).val)) =
      tensorClass (product A.val (NonzeroTensor.tensorProductList L).val)
    simp only [tensorClass_product_eq, cycleClass_mul, hA, ih htail]

private theorem square_one_rankAtMost : Tensor.RankAtMost (square (K := K) 1).coeff 1 := by
  classical
  refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, ?_⟩
  funext x y z
  simp [square, matrix, FiniteTensor.ofTensor, Tensor.pullback,
    matrixMultiplicationTensor, Tensor.rankOne]
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

@[simp] theorem valueAtOmega_scalar [IsAlgClosed K] :
    valueAtOmega (nonzeroSquare (K := K) 1 le_rfl) = 1 :=
  value_eq_one_of_rankAtMost_one _ _ square_one_rankAtMost

/-- Finite products of nonzero cyclic tensors satisfy the actual value lower bound. -/
theorem valueAtOmega_tensorProductList [IsAlgClosed K] (L : List (NonzeroTensor K))
    (hL : ∀ A ∈ L, cycleClass (tensorClass A.val) = tensorClass A.val) :
    (L.map valueAtOmega).prod ≤ valueAtOmega (NonzeroTensor.tensorProductList L) := by
  induction L with
  | nil => simp
  | cons A L ih =>
    have hA := hL A (List.mem_cons_self)
    have htail : ∀ B ∈ L, cycleClass (tensorClass B.val) = tensorClass B.val :=
      fun B hB => hL B (List.mem_cons_of_mem A hB)
    have hnonneg : 0 ≤ valueAtOmega A :=
      (one_le_value A ⟨Arithmetic.formalOmega K, Arithmetic.formalOmega_mem_Icc (F := K)⟩).trans' zero_le_one
    calc
      ((A :: L).map valueAtOmega).prod = valueAtOmega A * (L.map valueAtOmega).prod := rfl
      _ ≤ valueAtOmega A * valueAtOmega (NonzeroTensor.tensorProductList L) :=
        mul_le_mul_of_nonneg_left (ih htail) hnonneg
      _ ≤ valueAtOmega (A.product (NonzeroTensor.tensorProductList L)) :=
        valueAtOmega_supermultiplicative A (NonzeroTensor.tensorProductList L)
          hA (tensorProductList_cycleClass_fixed L htail)
      _ = valueAtOmega (NonzeroTensor.tensorProductList (A :: L)) := rfl

/-- The finite-index form used for the labelled factors in general extraction. -/
theorem valueAtOmega_tensorProductList_ofFn [IsAlgClosed K] {n : ℕ}
    (A : Fin n → NonzeroTensor K)
    (hA : ∀ i, cycleClass (tensorClass (A i).val) = tensorClass (A i).val) :
    (∏ i, valueAtOmega (A i)) ≤
      valueAtOmega (NonzeroTensor.tensorProductList (List.ofFn A)) := by
  have h := valueAtOmega_tensorProductList (List.ofFn A) (by
    intro B hB
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB
    exact hA i)
  simpa only [List.map_ofFn, List.prod_ofFn, Function.comp_apply] using h

end BlockIdentities.Square
