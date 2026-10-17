/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.Value

/-! Genuine independent direct sums preserve a nonzero summand. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

/-- The first summand embeds on independent coordinates of the actual direct sum. -/
theorem nonzero_finiteTensor_sum {A B : FiniteTensor K} (hA : Nonzero A) :
    Nonzero (FiniteTensor.sum A B) := by
  obtain ⟨x, y, z, h⟩ := (nonzero_iff A).1 hA
  apply nonzero_ofTensor
  intro hz
  have he := congrFun (congrFun (congrFun hz (Sum.inl x)) (Sum.inl y)) (Sum.inl z)
  apply h
  simpa only [sumTensor, Pi.zero_apply] using he

/-- Full direct sum on nonzero tensors, with all three variable groups independent. -/
def NonzeroTensor.sum (A B : NonzeroTensor K) : NonzeroTensor K :=
  ⟨FiniteTensor.sum A.val B.val, nonzero_finiteTensor_sum A.property⟩

end BlockIdentities.Square
