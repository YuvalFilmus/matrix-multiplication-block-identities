/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.Isomorphism
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
public import Mathlib.Algebra.BigOperators.Pi

/-! Invertible literal local maps give mutual restriction and equal tensor classes. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators

variable {K : Type*} [Field K]

private theorem inverse_coordinate_matrix {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (e : (X → K) ≃ₗ[K] (Y → K)) :
    Tensor.composeRestrictionMatrix
      (fun i u => e.symm (Pi.single u 1) i)
      (fun u j => e (Pi.single j 1) u) =
      fun i j => if j = i then 1 else 0 := by
  funext i j
  have h := congrArg (fun v : Y → K => e.symm v i)
    (pi_eq_sum_univ' (e (Pi.single j 1)))
  simpa [Tensor.composeRestrictionMatrix, map_sum, map_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_comm, eq_comm] using h.symm

/-- Inverting all three local linear equivalences inverts the literal tensor
isomorphism; the proof multiplies their actual coordinate matrices. -/
theorem Isomorphic.symm {A B : FiniteTensor K} (h : Isomorphic A B) : Isomorphic B A := by
  classical
  obtain ⟨ex, ey, ez, h⟩ := h
  refine ⟨ex.symm, ey.symm, ez.symm, ?_⟩
  rw [h, Tensor.restrict_restrict,
    inverse_coordinate_matrix ex, inverse_coordinate_matrix ey,
    inverse_coordinate_matrix ez, Tensor.restrict_identity]

/-- The target of an invertible local change is an actual restriction of its source. -/
theorem Isomorphic.target_le_source {A B : FiniteTensor K} (h : Isomorphic A B) : B ≤ A := by
  obtain ⟨ex, ey, ez, h⟩ := h
  exact ⟨_, _, _, h⟩

/-- Literal tensor isomorphism yields equality in the mutual-restriction quotient. -/
theorem Isomorphic.tensorClass_eq {A B : FiniteTensor K} (h : Isomorphic A B) :
    tensorClass A = tensorClass B :=
  (tensorClass_eq_iff A B).mpr ⟨h.symm.target_le_source, h.target_le_source⟩

end BlockIdentities.Square
