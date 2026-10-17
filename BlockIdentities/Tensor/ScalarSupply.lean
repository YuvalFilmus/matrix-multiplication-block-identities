/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ClassIdentities
public import BlockIdentities.Tensor.ClassDegeneration
public import BlockIdentities.Tensor.ElementaryRestrictions

/-! Exact-rank scalar supply and nonzero scalar recovery on tensor classes. -/

@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

theorem tensorClass_eq_zero_iff (A : FiniteTensor K) :
    tensorClass A = 0 ↔ A.coeff = 0 := by
  simpa only [classOf_coeff] using (classOf_eq_zero_iff A.coeff)

theorem ClassDegenerates.target_zero {b : TensorClass K}
    (h : ClassDegenerates 0 b) : b = 0 := by
  obtain ⟨A, B, hA, hB, hAB⟩ := h
  have hz := hAB.target_zero_of_source_zero ((tensorClass_eq_zero_iff A).mp hA)
  exact hB.symm.trans ((tensorClass_eq_zero_iff B).mpr hz)

theorem rank_scalar_supply (A : FiniteTensor K) :
    ClassDegenerates (exactRank A.coeff : TensorClass K) (tensorClass A) := by
  have h := (classDegenerates_tensorClass_iff (diagonal (exactRank A.coeff)) A).2
    (degenerates_of_rankAtMost (exactRank_spec A.coeff))
  simpa only [tensorClass_diagonal_eq] using h

theorem nonzero_scalar_recovery {A : FiniteTensor K} (hA : Nonzero A) :
    ClassDegenerates (tensorClass A) 1 := by
  have h := (classDegenerates_tensorClass_iff A (diagonal 1)).2
    (degenerates_to_scalar hA)
  simpa only [tensorClass_diagonal_eq, Nat.cast_one] using h

end BlockIdentities.Square
