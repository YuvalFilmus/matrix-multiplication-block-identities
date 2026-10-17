/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.MatrixRateProduct
public import BlockIdentities.Tensor.MatrixSymmetries

/-! Literal matrix tensors attain their dimension as a matrix rate. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped Topology
variable {K : Type*} [Field K]

theorem matrixRate_square (d : ℕ) (hd : 1 ≤ d) :
    MatrixRate (square (K := K) d) (d : ℝ) := by
  rw [matrixRate_iff_classes]
  refine ⟨by exact_mod_cast hd, fun _ => 1, fun _ => Nat.zero_lt_one, by simp, ?_⟩
  apply Eventually.of_forall
  intro n
  have heq : Nat.floor ((d : ℝ) ^ n) = d ^ n := by
    rw [← Nat.cast_pow, Nat.floor_natCast]
  simp only [Nat.cast_one, one_mul, tensorClass_square_eq, heq, matrixClass_pow]
  exact ClassDegenerates.refl _

theorem product_square_cycleClass_fixed {A : FiniteTensor K}
    (hA : cycleClass (tensorClass A) = tensorClass A) (d : ℕ) :
    cycleClass (tensorClass (product A (square d))) = tensorClass (product A (square d)) := by
  simp only [tensorClass_product_eq, cycleClass_mul, tensorClass_square_eq,
    cycleClass_matrixClass, hA]

end BlockIdentities.Square
