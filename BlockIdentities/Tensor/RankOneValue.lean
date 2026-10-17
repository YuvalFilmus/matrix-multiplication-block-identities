/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ValueBounds
public import BlockIdentities.Tensor.CyclicClasses

/-! Rank-one tensors have ordinary value one, directly from finite extractions. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

/-- Rank one supplies every symmetrized power from the scalar tensor. -/
theorem rankOne_scalar_supplies_power {A : FiniteTensor K}
    (hA : Tensor.RankAtMost A.coeff 1) (n : ℕ) :
    Degenerates (diagonal 1) (power (symmetrize A) n) := by
  have hc := (classDegenerates_tensorClass_iff _ _).2 (degenerates_of_rankAtMost hA)
  rw [tensorClass_diagonal_eq, Nat.cast_one] at hc
  have hs := (hc.mul hc.cycle).mul hc.cycle.cycle
  have hs' : ClassDegenerates 1 (tensorClass (symmetrize A)) := by
    simpa only [cycleClass_one, one_mul, tensorClass_symmetrize_eq] using hs
  apply (classDegenerates_tensorClass_iff _ _).1
  simpa only [tensorClass_diagonal_eq, Nat.cast_one, tensorClass_power_eq, one_pow]
    using hs'.pow n

/-- Nonzero tensors of coefficient rank at most one have ordinary value one. -/
theorem value_eq_one_of_rankAtMost_one [IsAlgClosed K]
    (ρ : Set.Icc (2 : ℝ) 3) (A : NonzeroTensor K)
    (hA : Tensor.RankAtMost A.val.coeff 1) : value ρ A = 1 := by
  apply le_antisymm _ (one_le_value A ρ)
  apply csSup_le (value_witnesses_nonempty A ρ)
  rintro v ⟨n, h, m, hn, hh, hm, hd, rfl⟩
  have he := (rankOne_scalar_supplies_power hA n).trans hd
  have hb := he.copies_square_dimension_le hm
  have hb' : h * m ^ 2 ≤ 1 := by
    exact hb
  have hm2 : 1 ≤ m ^ 2 := by nlinarith
  have hhle : h ≤ 1 := by
    calc
      h = h * 1 := (Nat.mul_one h).symm
      _ ≤ h * m ^ 2 := Nat.mul_le_mul_left h hm2
      _ ≤ 1 := hb'
  have heq : h = 1 := by omega
  have hmeq : m = 1 := by
    rw [heq, one_mul] at hb'
    nlinarith
  simp only [heq, hmeq, Nat.cast_one, Real.one_rpow, one_mul, le_refl]

end BlockIdentities.Square
