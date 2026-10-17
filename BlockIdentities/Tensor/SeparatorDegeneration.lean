/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.SeparatorLeading
public import BlockIdentities.Tensor.ClassDegeneration
public import BlockIdentities.Tensor.ClassIdentities

/-! Interpolation followed by integral weights gives the finite separator. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K X Y Z : Type*} [Field K]
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

theorem separatorFiltered_degeneration {M : ℕ} (T : Tensor K X Y Z)
    (sy : Y → Fin M) (sz : Z → Fin M)
    (hsupport : ∀ x y z, T x y z ≠ 0 → sy y = sz z) :
    Degenerates (FiniteTensor.ofTensor (separatorFiltered T sy sz))
      (FiniteTensor.ofTensor (separatorRetained T sy)) := by
  let D := weightPartDegeneration (separatorFiltered T sy sz)
    (fun x => separatorFirstWeight x.2)
    (fun y => separatorSecondWeight (sy y.1) y.2)
    (fun z => separatorThirdWeight (sz z.1) z.2)
    (2 * M ^ 2) (M ^ 2) (2 * M ^ 2) (M ^ 2)
    (by
      intro x
      exact Nat.pow_le_pow_left x.2.isLt.le 2)
    (by
      intro y
      dsimp only [separatorSecondWeight]
      have hp := Nat.mul_le_mul (sy y.1).isLt.le y.2.isLt.le
      have he : (sy y.1).val * y.2.val ≤ M ^ 2 := by simpa only [pow_two] using hp
      omega)
    (by intro z; exact Nat.sub_le _ _)
    (separatorFiltered_minimum T sy sz hsupport)
  have hD := D.ofTensor
  rw [separatorFiltered_weightPart T sy sz hsupport] at hD
  exact ⟨2 * M ^ 2, M ^ 2, 2 * M ^ 2, M ^ 2, ⟨hD⟩⟩

/-- Six times the sector count suffices. The target keeps an independent
sector on its first leg and a rank-M dot on its other two legs. -/
theorem separator_degeneration [Infinite K] {M : ℕ} (hM : 1 ≤ M)
    (T : Tensor K X Y Z) (sy : Y → Fin M) (sz : Z → Fin M)
    (hsupport : ∀ x y z, T x y z ≠ 0 → sy y = sz z) :
    Degenerates (copies (6 * M) (FiniteTensor.ofTensor T))
      (FiniteTensor.ofTensor (separatorRetained T sy)) := by
  classical
  have hi := separatorPolynomial_coefficient_isRestriction T sy sz hsupport
  have hc : ClassDegenerates
      (classOf (Tensor.directSum (fun _ : Fin (6 * (M - 1) + 1) => T)))
      (classOf (separatorFiltered T sy sz)) :=
    ClassDegenerates.of_le ((classOf_le_iff _ _).2 hi)
  have hw := (classDegenerates_tensorClass_iff _ _).2
    (separatorFiltered_degeneration T sy sz hsupport)
  have hsum : classOf (Tensor.directSum (fun _ : Fin (6 * (M - 1) + 1) => T)) =
      ((6 * (M - 1) + 1 : ℕ) : TensorClass K) * classOf T := by
    rw [classOf_directSum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum] at hc
  have hpad : ClassDegenerates ((6 * M : ℕ) : TensorClass K)
      ((6 * (M - 1) + 1 : ℕ) : TensorClass K) :=
    ClassDegenerates.of_le (Nat.mono_cast (by omega))
  have hout := (((hpad.mul (ClassDegenerates.refl (classOf T))).trans hc).trans hw)
  apply (classDegenerates_tensorClass_iff _ _).1
  simpa only [tensorClass_copies_eq, classOf] using hout

end BlockIdentities.Square
