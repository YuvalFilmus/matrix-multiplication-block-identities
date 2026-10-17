/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ValueBounds
public import BlockIdentities.Tensor.CyclicClasses
public import BlockIdentities.Tensor.MatrixRestrictions

/-! Actual square outputs of cyclic tensors give ordinary-value witnesses. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

theorem cyclic_square_output_symmetrize {A : FiniteTensor K} {n m : ℕ}
    (hcycle : cycleClass (tensorClass A) = tensorClass A)
    (h : Degenerates (power A n) (square m)) :
    Degenerates (power (symmetrize A) n) (square (m ^ 3)) := by
  have hc := ((classDegenerates_tensorClass_iff _ _).2 h).pow 3
  apply (classDegenerates_tensorClass_iff _ _).1
  simp only [tensorClass_power_eq, tensorClass_square_eq] at hc ⊢
  have hsym : tensorClass (symmetrize A) = tensorClass A ^ 3 := by
    rw [tensorClass_symmetrize_eq, hcycle, hcycle]
    ring
  rw [hsym, matrixClass_pow]
  simpa only [← pow_mul, Nat.mul_comm] using hc

/-- The symmetrized source of a cyclic tensor is exactly three source powers
in the genuine restriction quotient. -/
theorem cyclic_value_extraction {A : FiniteTensor K} {n h m : ℕ}
    (hcycle : cycleClass (tensorClass A) = tensorClass A)
    (hex : Degenerates (power (symmetrize A) n) (copies h (square m))) :
    Degenerates (power A (3 * n)) (copies h (square m)) := by
  apply (classDegenerates_tensorClass_iff _ _).1
  have hc := (classDegenerates_tensorClass_iff _ _).2 hex
  simpa only [tensorClass_power_eq, symmetrize_class_eq_cube hcycle, ← pow_mul]
    using hc

theorem cyclic_square_output_le_value [IsAlgClosed K] (ρ : Set.Icc (2 : ℝ) 3)
    (A : NonzeroTensor K) (hcycle : cycleClass (tensorClass A.val) = tensorClass A.val)
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h : Degenerates (power A.val n) (square m)) :
    (((m ^ 3 : ℕ) : ℝ) ^ (ρ : ℝ)) ^ (1 / (3 * (n : ℝ))) ≤ value ρ A := by
  apply le_csSup (value_witnesses_bddAbove A ρ)
  refine ⟨n, 1, m ^ 3, hn, le_rfl, Nat.one_le_pow _ _ hm, ?_, ?_⟩
  · apply (classDegenerates_tensorClass_iff _ _).1
    have hc := (classDegenerates_tensorClass_iff _ _).2
      (cyclic_square_output_symmetrize hcycle h)
    simpa only [tensorClass_copies_eq, Nat.cast_one, one_mul] using hc
  · simp only [Nat.cast_one, one_mul]

end BlockIdentities.Square
