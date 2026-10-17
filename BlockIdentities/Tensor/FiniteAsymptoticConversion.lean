/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Providers.Cancellation

/-! Turn genuine fixed conversions into all-power asymptotic conversions. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

theorem asymptoticallyRestricts_of_classDegenerates {A B : FiniteTensor K}
    (h : ClassDegenerates (tensorClass A) (tensorClass B)) : AsymptoticallyRestricts A B := by
  rw [asymptoticallyRestricts_iff_classes]
  refine ⟨fun _ => 1, fun _ => Nat.zero_lt_one, by simp, ?_⟩
  intro n hn
  simpa only [Nat.cast_one, one_mul] using h.pow n

theorem Degenerates.asymptoticallyRestricts {A B : FiniteTensor K}
    (h : Degenerates A B) : AsymptoticallyRestricts A B :=
  asymptoticallyRestricts_of_classDegenerates ((classDegenerates_tensorClass_iff _ _).2 h)

theorem nonzero_diagonal (m : ℕ) (hm : 1 ≤ m) : Nonzero (diagonal (K := K) m) := by
  let i : Fin m := ⟨0, lt_of_lt_of_le Nat.zero_lt_one hm⟩
  apply (nonzero_iff _).2
  exact ⟨i, i, i, by simp [diagonal]⟩

/-- The common finite multiplicity is a genuine nonzero diagonal catalyst. -/
theorem asymptoticallyRestricts_of_common_copies {A B : FiniteTensor K}
    (m : ℕ) (hm : 1 ≤ m)
    (h : ClassDegenerates ((m : TensorClass K) * tensorClass A)
      ((m : TensorClass K) * tensorClass B)) : AsymptoticallyRestricts A B := by
  have hc : ClassDegenerates (tensorClass (product A (diagonal m)))
      (tensorClass (product B (diagonal m))) := by
    simpa only [tensorClass_product_eq, tensorClass_diagonal_eq, mul_comm] using h
  exact Providers.asymptotic_cancellation A B (diagonal m) (nonzero_diagonal m hm)
    (asymptoticallyRestricts_of_classDegenerates hc)

end BlockIdentities.Square
