/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.SwapClasses
public import BlockIdentities.Tensor.MatrixRestrictions

/-! Genuine coordinate symmetries of square matrix tensors and their copies. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

@[simp] theorem cycleClass_matrixClass (m : ℕ) :
    cycleClass (matrixClass (K := K) m) = matrixClass m := by
  change cycleClass (classOf (matrixMultiplicationTensor (K := K) m m m)) =
    classOf (matrixMultiplicationTensor (K := K) m m m)
  rw [cycleClass_classOf]
  congr 1
  funext x y z
  simp only [Tensor.cyclic, matrixMultiplicationTensor, and_assoc, and_comm]

@[simp] theorem swapClass_matrixClass (m : ℕ) :
    swapClass (matrixClass (K := K) m) = matrixClass m := by
  classical
  change swapClass (classOf (matrixMultiplicationTensor (K := K) m m m)) =
    classOf (matrixMultiplicationTensor (K := K) m m m)
  rw [swapClass_classOf]
  apply classOf_eq_of_reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (Equiv.prodComm _ _)
  funext x y z
  simp [Tensor.pullback, swapLast, matrixMultiplicationTensor, eq_comm,
    and_assoc, and_comm] <;> rfl

@[simp] theorem cycleClass_natCast (m : ℕ) :
    cycleClass (m : TensorClass K) = m := by
  classical
  rw [← tensorClass_diagonal_eq (K := K) m, ← classOf_coeff, cycleClass_classOf]
  congr 1
  funext x y z
  change Fin m at x y z
  change (if z = x ∧ x = y then (1 : K) else 0) =
    (if x = y ∧ y = z then 1 else 0)
  by_cases hxy : x = y <;> by_cases hyz : y = z <;> simp_all [eq_comm]

@[simp] theorem swapClass_natCast (m : ℕ) :
    swapClass (m : TensorClass K) = m := by
  classical
  rw [← tensorClass_diagonal_eq (K := K) m, ← classOf_coeff, swapClass_classOf]
  congr 1
  funext x y z
  change Fin m at x y z
  change (if x = z ∧ z = y then (1 : K) else 0) =
    (if x = y ∧ y = z then 1 else 0)
  by_cases hxy : x = y <;> by_cases hyz : y = z <;> simp_all [eq_comm]

/-- Symmetrizing a square matrix tensor gives its third tensor power in class. -/
theorem tensorClass_symmetrize_square (m : ℕ) :
    tensorClass (symmetrize (square (K := K) m)) = matrixClass m ^ 3 := by
  have hcycle : cycleClass (tensorClass (square (K := K) m)) =
      tensorClass (square (K := K) m) := by
    rw [tensorClass_square_eq, cycleClass_matrixClass]
  simpa only [tensorClass_square_eq] using symmetrize_class_eq_cube hcycle

/-- Cyclically permuting an extraction preserves its square output dimensions
and its independent-copy multiplicity. -/
theorem ClassDegenerates.cycle_square_copies {a : TensorClass K} {h m : ℕ}
    (hd : ClassDegenerates a ((h : TensorClass K) * matrixClass m)) :
    ClassDegenerates (cycleClass a) ((h : TensorClass K) * matrixClass m) := by
  simpa only [cycleClass_mul, cycleClass_natCast, cycleClass_matrixClass] using hd.cycle

/-- Swapping the side legs preserves the same square output and multiplicity. -/
theorem ClassDegenerates.swap_square_copies {a : TensorClass K} {h m : ℕ}
    (hd : ClassDegenerates a ((h : TensorClass K) * matrixClass m)) :
    ClassDegenerates (swapClass a) ((h : TensorClass K) * matrixClass m) := by
  simpa only [swapClass_mul, swapClass_natCast, swapClass_matrixClass] using hd.swap

end BlockIdentities.Square
