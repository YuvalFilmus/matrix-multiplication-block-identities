/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ClassIdentities

/-! Coordinate restrictions on matrix multiplication and scalar direct sums. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

/-- The concrete square presentation represents the upstream matrix class. -/
theorem tensorClass_square_eq (n : ℕ) :
    tensorClass (square (K := K) n) = matrixClass n := rfl

theorem matrixClass_mono {a b : ℕ} (hab : a ≤ b) :
    matrixClass (K := K) a ≤ matrixClass b := by
  let e : Fin a → Fin b := Fin.castLE hab
  let f : Fin a × Fin a → Fin b × Fin b := fun p => (e p.1, e p.2)
  have heq : ∀ i j : Fin a, e i = e j ↔ i = j :=
    fun i j => (Fin.castLE_injective hab).eq_iff
  have ht : Tensor.pullback f f f (matrixMultiplicationTensor (K := K) b b b) =
      matrixMultiplicationTensor a a a := by
    funext x y z
    simp only [Tensor.pullback, f, matrixMultiplicationTensor, heq]
  apply (classOf_le_iff _ _).2
  have h := IsRestriction.pullback (matrixMultiplicationTensor (K := K) b b b) f f f
  rw [ht] at h
  exact h

/-- A matrix tensor contains its diagonal scalar direct sum as a restriction. -/
theorem natCast_le_matrixClass (n : ℕ) :
    (n : TensorClass K) ≤ matrixClass n := by
  classical
  let f : Fin n → Fin n × Fin n := fun i => (i, i)
  have ht : Tensor.pullback f f f (matrixMultiplicationTensor (K := K) n n n) =
      (diagonal (K := K) n).coeff := by
    funext x y z
    change Fin n at x y z
    change (if x = y ∧ y = z ∧ z = x then (1 : K) else 0) =
      if x = y ∧ y = z then 1 else 0
    have hi : (x = y ∧ y = z ∧ z = x) ↔ (x = y ∧ y = z) :=
      ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, (h.1.trans h.2).symm⟩⟩
    simp only [hi]
  rw [← tensorClass_diagonal_eq (K := K) n, ← classOf_coeff]
  apply (classOf_le_iff _ _).2
  have h := IsRestriction.pullback (matrixMultiplicationTensor (K := K) n n n) f f f
  rw [ht] at h
  exact h

end BlockIdentities.Square
