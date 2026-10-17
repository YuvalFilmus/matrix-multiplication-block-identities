/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.Value

/-! Positive rectangular matrix shapes give genuine nonzero tensors. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
variable {K : Type*} [Field K]

theorem nonzero_matrixShape (D : MatrixShape) : Nonzero (D.tensor (K := K)) := by
  apply nonzero_ofTensor
  intro h
  let i : Fin D.a := ⟨0, D.a_pos⟩
  let j : Fin D.b := ⟨0, D.b_pos⟩
  let k : Fin D.c := ⟨0, D.c_pos⟩
  have hv := congrFun (congrFun (congrFun h (i, j)) (j, k)) (k, i)
  simpa [matrixMultiplicationTensor] using hv

/-- The same positive matrix tensor, with its proved nonzeroness attached. -/
def MatrixShape.nonzeroTensor (D : MatrixShape) : NonzeroTensor K :=
  ⟨D.tensor, nonzero_matrixShape D⟩

end BlockIdentities.Square
