/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.DegenerationProduct

/-! Polynomial degeneration on mutual-restriction classes. This is exactly the
original relation on representatives, not a larger asymptotic preorder. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring

variable {K : Type*} [Field K]

/-- A scalar restriction is a degree-zero polynomial degeneration. -/
theorem degenerates_of_le {A B : FiniteTensor K} (h : B ≤ A) : Degenerates A B := by
  obtain ⟨Lx, Ly, Lz, h⟩ := h
  exact degenerates_of_restriction Lx Ly Lz h

/-- Degeneration of tensor classes means degeneration of representatives. -/
def ClassDegenerates (a b : TensorClass K) : Prop :=
  ∃ A B : FiniteTensor K, tensorClass A = a ∧ tensorClass B = b ∧ Degenerates A B

theorem classDegenerates_tensorClass_iff (A B : FiniteTensor K) :
    ClassDegenerates (tensorClass A) (tensorClass B) ↔ Degenerates A B := by
  constructor
  · rintro ⟨A', B', hA, hB, h⟩
    have hleft : Degenerates A A' :=
      degenerates_of_le ((tensorClass_eq_iff A' A).mp hA).1
    have hright : Degenerates B' B :=
      degenerates_of_le ((tensorClass_eq_iff B' B).mp hB).2
    exact (hleft.trans h).trans hright
  · intro h
    exact ⟨A, B, rfl, rfl, h⟩

namespace ClassDegenerates

theorem refl (a : TensorClass K) : ClassDegenerates a a := by
  induction a using Quotient.inductionOn with
  | h A => exact ⟨A, A, rfl, rfl, Degenerates.refl A⟩

theorem of_le {a b : TensorClass K} (h : b ≤ a) : ClassDegenerates a b := by
  induction a using Quotient.inductionOn with
  | h A =>
    induction b using Quotient.inductionOn with
    | h B => exact (classDegenerates_tensorClass_iff A B).2 (degenerates_of_le h)

theorem trans {a b c : TensorClass K} (hab : ClassDegenerates a b)
    (hbc : ClassDegenerates b c) : ClassDegenerates a c := by
  obtain ⟨A, B, hA, hB, hAB⟩ := hab
  obtain ⟨C, D, hC, hD, hCD⟩ := hbc
  have hmid : tensorClass B = tensorClass C := hB.trans hC.symm
  have hBC : Degenerates B C :=
    degenerates_of_le ((tensorClass_eq_iff B C).mp hmid).2
  exact ⟨A, D, hA, hD, (hAB.trans hBC).trans hCD⟩

theorem mul {a b c d : TensorClass K} (hab : ClassDegenerates a b)
    (hcd : ClassDegenerates c d) : ClassDegenerates (a * c) (b * d) := by
  obtain ⟨A, B, hA, hB, hAB⟩ := hab
  obtain ⟨C, D, hC, hD, hCD⟩ := hcd
  refine ⟨product A C, product B D, ?_, ?_, hAB.product hCD⟩
  · change tensorClass A * tensorClass C = a * c
    rw [hA, hC]
  · change tensorClass B * tensorClass D = b * d
    rw [hB, hD]

theorem pow {a b : TensorClass K} (hab : ClassDegenerates a b) (n : ℕ) :
    ClassDegenerates (a ^ n) (b ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using refl (1 : TensorClass K)
  | succ n ih => simpa only [pow_succ] using ih.mul hab

end ClassDegenerates

end BlockIdentities.Square
