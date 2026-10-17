/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ValueMonotonicity
public import BlockIdentities.Tensor.MatrixSymmetries

/-! Permutation invariance proved from the literal extraction witnesses. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

/-- Permute the actual coefficient tensor while retaining its nonzero witness. -/
def NonzeroTensor.permute (A : NonzeroTensor K) (π : LegPermutation) : NonzeroTensor K :=
  ⟨BlockIdentities.Square.permute π A.val, nonzero_permute A.property π⟩

/-- Equal symmetrized source classes give the same extraction candidates. -/
theorem value_eq_of_symmetrize_class_eq [IsAlgClosed K] (ρ : Set.Icc (2 : ℝ) 3)
    (A B : NonzeroTensor K)
    (h : tensorClass (symmetrize A.val) = tensorClass (symmetrize B.val)) :
    value ρ A = value ρ B := by
  have hle (A B : NonzeroTensor K)
      (h : tensorClass (symmetrize A.val) = tensorClass (symmetrize B.val)) :
      value ρ A ≤ value ρ B := by
    apply csSup_le (value_witnesses_nonempty A ρ)
    rintro v ⟨n, q, m, hn, hq, hm, hex, rfl⟩
    apply le_csSup (value_witnesses_bddAbove B ρ)
    refine ⟨n, q, m, hn, hq, hm, ?_, rfl⟩
    apply (classDegenerates_tensorClass_iff _ _).1
    have he := (classDegenerates_tensorClass_iff _ _).2 hex
    rw [tensorClass_power_eq, h] at he
    simpa only [tensorClass_power_eq] using he
  exact le_antisymm (hle A B h) (hle B A h.symm)

theorem tensorClass_symmetrize_cycle (A : FiniteTensor K) :
    tensorClass (symmetrize (permute .yzx A)) = tensorClass (symmetrize A) := by
  simp only [tensorClass_symmetrize_eq, ← cycleClass_tensorClass, cycleClass_three]
  ring

theorem tensorClass_symmetrize_swap (A : FiniteTensor K) :
    tensorClass (symmetrize (permute .xzy A)) = swapClass (tensorClass (symmetrize A)) := by
  simp only [tensorClass_symmetrize_eq, swapClass_mul, ← swapClass_tensorClass,
    swapClass_cycleClass, cycleClass_three]
  ring

/-- Cyclic invariance follows from finite factor reordering of symmetrization. -/
theorem value_cycle [IsAlgClosed K] (ρ : Set.Icc (2 : ℝ) 3) (A : NonzeroTensor K) :
    value ρ (A.permute .yzx) = value ρ A := by
  exact value_eq_of_symmetrize_class_eq ρ (A.permute .yzx) A
    (tensorClass_symmetrize_cycle A.val)

private theorem value_le_swap [IsAlgClosed K] (ρ : Set.Icc (2 : ℝ) 3)
    (A : NonzeroTensor K) : value ρ A ≤ value ρ (A.permute .xzy) := by
  apply csSup_le (value_witnesses_nonempty A ρ)
  rintro v ⟨n, q, m, hn, hq, hm, hex, rfl⟩
  apply le_csSup (value_witnesses_bddAbove (A.permute .xzy) ρ)
  refine ⟨n, q, m, hn, hq, hm, ?_, rfl⟩
  have he := (classDegenerates_tensorClass_iff _ _).2 hex
  rw [tensorClass_power_eq, tensorClass_copies_eq, tensorClass_square_eq] at he
  have hs := he.swap_square_copies
  simp only [swapClass_pow] at hs
  rw [← tensorClass_symmetrize_swap] at hs
  apply (classDegenerates_tensorClass_iff _ _).1
  simpa only [tensorClass_power_eq, tensorClass_copies_eq, tensorClass_square_eq,
    NonzeroTensor.permute] using hs

/-- The swap moves the actual local maps and fixes each square matrix output. -/
theorem value_swap [IsAlgClosed K] (ρ : Set.Icc (2 : ℝ) 3) (A : NonzeroTensor K) :
    value ρ (A.permute .xzy) = value ρ A := by
  apply le_antisymm
  · have h := value_le_swap ρ (A.permute .xzy)
    change value ρ (A.permute .xzy) ≤ value ρ A at h
    exact h
  · exact value_le_swap ρ A

/-- All six physical leg permutations preserve the ordinary square-output value. -/
theorem value_permute [IsAlgClosed K] (ρ : Set.Icc (2 : ℝ) 3)
    (A : NonzeroTensor K) (π : LegPermutation) :
    value ρ (A.permute π) = value ρ A := by
  cases π with
  | xyz => rfl
  | xzy => exact value_swap ρ A
  | yzx => exact value_cycle ρ A
  | zxy =>
    change value ρ ((A.permute .yzx).permute .yzx) = value ρ A
    exact (value_cycle ρ (A.permute .yzx)).trans (value_cycle ρ A)
  | zyx =>
    change value ρ ((A.permute .xzy).permute .yzx) = value ρ A
    exact (value_cycle ρ (A.permute .xzy)).trans (value_swap ρ A)
  | yxz =>
    change value ρ (((A.permute .xzy).permute .yzx).permute .yzx) = value ρ A
    exact (value_cycle ρ ((A.permute .xzy).permute .yzx)).trans
      ((value_cycle ρ (A.permute .xzy)).trans (value_swap ρ A))

end BlockIdentities.Square
