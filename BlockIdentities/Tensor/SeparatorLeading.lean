/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.SeparatorPolynomial
public import BlockIdentities.Tensor.DegenerationWeights

/-! The literal coefficient filter and its minimum integral weight. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
variable {K X Y Z : Type*} [Field K]
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

def separatorFiltered {M : ℕ} (T : Tensor K X Y Z)
    (sy : Y → Fin M) (sz : Z → Fin M) :
    Tensor K (X × Fin M) (Y × Fin M) (Z × Fin M) :=
  fun x y z => (separatorPolynomial T sy sz x y z).coeff (3 * (M - 1))

def separatorRetained {M : ℕ} (T : Tensor K X Y Z) (sy : Y → Fin M) :
    Tensor K (X × Fin M) (Y × Fin M) (Z × Fin M) :=
  fun x y z => if x.2 = sy y.1 ∧ y.2 = z.2 then T x.1 y.1 z.1 else 0

theorem separatorFiltered_apply {M : ℕ} (T : Tensor K X Y Z)
    (sy : Y → Fin M) (sz : Z → Fin M)
    (hsupport : ∀ x y z, T x y z ≠ 0 → sy y = sz z)
    (x : X × Fin M) (y : Y × Fin M) (z : Z × Fin M) :
    separatorFiltered T sy sz x y z =
      if separatorFilterDegree x.2 (sy y.1) y.2 z.2 = 3 * (M - 1)
      then T x.1 y.1 z.1 else 0 := by
  rw [separatorFiltered, separatorPolynomial_apply T sy sz hsupport]
  by_cases h : separatorFilterDegree x.2 (sy y.1) y.2 z.2 = 3 * (M - 1)
  · simp [h]
  · simp [h, Ne.symm h]

theorem separatorFiltered_minimum {M : ℕ} (T : Tensor K X Y Z)
    (sy : Y → Fin M) (sz : Z → Fin M)
    (hsupport : ∀ x y z, T x y z ≠ 0 → sy y = sz z)
    (x : X × Fin M) (y : Y × Fin M) (z : Z × Fin M)
    (h : separatorFiltered T sy sz x y z ≠ 0) :
    2 * M ^ 2 ≤ separatorFirstWeight x.2 + separatorSecondWeight (sy y.1) y.2 +
      separatorThirdWeight (sz z.1) z.2 := by
  rw [separatorFiltered_apply T sy sz hsupport] at h
  split_ifs at h with hf
  · rw [← hsupport x.1 y.1 z.1 h]
    exact separator_weight_ge _ _ _ _ ((separatorFilterDegree_eq_iff _ _ _ _).1 hf)
  · exact False.elim (h rfl)

theorem separatorFiltered_weightPart {M : ℕ} (T : Tensor K X Y Z)
    (sy : Y → Fin M) (sz : Z → Fin M)
    (hsupport : ∀ x y z, T x y z ≠ 0 → sy y = sz z) :
    weightPart (separatorFiltered T sy sz)
      (fun x => separatorFirstWeight x.2)
      (fun y => separatorSecondWeight (sy y.1) y.2)
      (fun z => separatorThirdWeight (sz z.1) z.2) (2 * M ^ 2) =
      separatorRetained T sy := by
  funext x y z
  rw [weightPart, separatorFiltered_apply T sy sz hsupport]
  by_cases ht : T x.1 y.1 z.1 = 0
  · simp [ht, separatorRetained]
  have hsector := hsupport x.1 y.1 z.1 ht
  rw [← hsector]
  have hiff :
      (separatorFirstWeight x.2 + separatorSecondWeight (sy y.1) y.2 +
        separatorThirdWeight (sy y.1) z.2 = 2 * M ^ 2 ∧
        separatorFilterDegree x.2 (sy y.1) y.2 z.2 = 3 * (M - 1)) ↔
      x.2 = sy y.1 ∧ y.2 = z.2 := by
    constructor
    · rintro ⟨hw, hf⟩
      exact (separator_weight_eq_iff _ _ _ _ ((separatorFilterDegree_eq_iff _ _ _ _).1 hf)).1 hw
    · rintro ⟨hg, hu⟩
      have hf : separatorFilterDegree x.2 (sy y.1) y.2 z.2 = 3 * (M - 1) := by
        apply (separatorFilterDegree_eq_iff _ _ _ _).2
        simp [hg, hu]
      exact ⟨(separator_weight_eq_iff _ _ _ _
        ((separatorFilterDegree_eq_iff _ _ _ _).1 hf)).2 ⟨hg, hu⟩, hf⟩
  simp only [separatorRetained]
  split_ifs <;> simp_all

end BlockIdentities.Square
