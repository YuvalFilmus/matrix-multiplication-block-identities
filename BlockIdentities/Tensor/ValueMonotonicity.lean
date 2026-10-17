/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ValueBounds
public import BlockIdentities.Tensor.CyclicClasses

/-! Finite degeneration monotonicity for the literal ordinary value. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

theorem Degenerates.symmetrize {A B : FiniteTensor K} (h : Degenerates A B) :
    Degenerates (symmetrize A) (symmetrize B) := by
  have hc := (classDegenerates_tensorClass_iff A B).2 h
  apply (classDegenerates_tensorClass_iff _ _).1
  simpa only [tensorClass_symmetrize_eq] using (hc.mul hc.cycle).mul hc.cycle.cycle

theorem value_mono_of_degeneration [IsAlgClosed K] (ρ : Set.Icc (2 : ℝ) 3)
    (A B : NonzeroTensor K) (h : Degenerates A.val B.val) : value ρ B ≤ value ρ A := by
  apply csSup_le (value_witnesses_nonempty B ρ)
  rintro v ⟨n, q, m, hn, hq, hm, hex, rfl⟩
  apply le_csSup (value_witnesses_bddAbove A ρ)
  refine ⟨n, q, m, hn, hq, hm, ?_, rfl⟩
  have hc := ((classDegenerates_tensorClass_iff _ _).2 h.symmetrize).pow n
  have he := (classDegenerates_tensorClass_iff _ _).2 hex
  apply (classDegenerates_tensorClass_iff _ _).1
  rw [tensorClass_power_eq] at he ⊢
  exact hc.trans he

theorem value_eq_of_tensorClass_eq [IsAlgClosed K] (ρ : Set.Icc (2 : ℝ) 3)
    (A B : NonzeroTensor K) (h : tensorClass A.val = tensorClass B.val) :
    value ρ A = value ρ B := by
  apply le_antisymm
  · apply value_mono_of_degeneration ρ B A
    exact (classDegenerates_tensorClass_iff _ _).1 (ClassDegenerates.of_le h.le)
  · apply value_mono_of_degeneration ρ A B
    exact (classDegenerates_tensorClass_iff _ _).1 (ClassDegenerates.of_le h.ge)

end BlockIdentities.Square
