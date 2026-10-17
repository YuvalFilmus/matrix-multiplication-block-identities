/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ClassIdentities
public import BlockIdentities.Tensor.ClassDegeneration

/-! The exact copy-overhead definition in the tensor semiring. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

theorem asymptoticallyRestricts_iff_classes (A B : FiniteTensor K) :
    AsymptoticallyRestricts A B ↔
    ∃ a : ℕ → ℕ, (∀ n, 0 < a n) ∧
      Filter.Tendsto (fun n : ℕ => Real.log (a n : ℝ) / (n : ℝ))
        Filter.atTop (nhds 0) ∧
      ∀ n : ℕ, 1 ≤ n → ClassDegenerates
        ((a n : TensorClass K) * tensorClass A ^ n) (tensorClass B ^ n) := by
  constructor
  · rintro ⟨a, ha, hrate, h⟩
    refine ⟨a, ha, hrate, ?_⟩
    intro n hn
    have hc := (classDegenerates_tensorClass_iff _ _).2 (h n hn)
    simpa only [tensorClass_copies_eq, tensorClass_power_eq] using hc
  · rintro ⟨a, ha, hrate, h⟩
    refine ⟨a, ha, hrate, ?_⟩
    intro n hn
    apply (classDegenerates_tensorClass_iff _ _).1
    simpa only [tensorClass_copies_eq, tensorClass_power_eq] using h n hn

end BlockIdentities.Square
