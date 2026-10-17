/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.TypeSectorModels
public import BlockIdentities.Tensor.SeparatorDegeneration
public import BlockIdentities.Tensor.DegenerationSum

/-! Actual fixed-type sectors, separation, and independent prescribed block maps. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K X Y Z ι : Type*} [Field K] [Infinite K]
variable [Fintype X] [Fintype Y] [Fintype Z] [Fintype ι] [DecidableEq ι]

theorem type_separator_conversion (T : Tensor K X Y Z)
    (sy : Y → ι) (sz : Z → ι)
    (hsupport : ∀ x y z, T x y z ≠ 0 → sy y = sz z)
    (counts : ι → ℕ) (Q : ι → TensorClass K)
    (hQ : ∀ i, ClassDegenerates (classOf (sectorBlock T sy i)) (Q i)) :
    ClassDegenerates
      (((6 * Fintype.card (ExactWords counts) : ℕ) : TensorClass K) *
        classOf T ^ (∑ i, counts i))
      ((Fintype.card (ExactWords counts) : TensorClass K) *
        (∏ i, Q i ^ counts i) * classOf (dotTensor (K := K) (Fintype.card (ExactWords counts)))) := by
  classical
  let N := Fintype.card (ExactWords counts)
  let e : ExactWords counts ≃ Fin N := Fintype.equivFin _
  let U := typeSectorTensor T sy sz counts
  let sy' := e ∘ typeSectorLabel sy counts
  let sz' := e ∘ typeSectorLabel sz counts
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (typeSector_card_pos counts))
  have hU : ∀ x y z, U x y z ≠ 0 → sy' y = sz' z := by
    intro x y z h
    exact congrArg e (typeSectorTensor_support T sy sz counts hsupport x y z h)
  have hmodels : ∀ l : Fin N, classOf (sectorBlock U sy' l) =
      ∏ i, classOf (sectorBlock T sy i) ^ counts i := by
    intro l
    have he : sectorBlock U sy' l = typeSectorBlock T sy sz counts (e.symm l) := by
      funext x y z
      simp only [sectorBlock, typeSectorBlock, sy', Function.comp_apply,
        Equiv.apply_eq_iff_eq_symm_apply]
      rfl
    rw [he]
    exact classOf_typeSectorBlock T sy sz counts (e.symm l) hsupport
  have hret : classOf (separatorRetained U sy') = (N : TensorClass K) *
      (∏ i, classOf (sectorBlock T sy i) ^ counts i) * classOf (dotTensor (K := K) N) := by
    rw [classOf_separatorRetained U sy' sz' hU]
    calc
      _ = ∑ _ : Fin N, (∏ i, classOf (sectorBlock T sy i) ^ counts i) *
          classOf (dotTensor (K := K) N) := by
        apply Finset.sum_congr rfl
        intro l hl
        exact (classOf_sectorDotBlock U sy' l).trans
          (congrArg (fun a : TensorClass K => a * classOf (dotTensor (K := K) N)) (hmodels l))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hsep := (classDegenerates_tensorClass_iff _ _).2
    (separator_degeneration hN U sy' sz' hU)
  have hsep' : ClassDegenerates (((6 * N : ℕ) : TensorClass K) * classOf U)
      (classOf (separatorRetained U sy')) := by
    simpa only [tensorClass_copies_eq, classOf] using hsep
  rw [hret] at hsep'
  have hrestrict := (ClassDegenerates.refl ((6 * N : ℕ) : TensorClass K)).mul
    (ClassDegenerates.of_le ((classOf_le_iff _ _).2
      (typeSectorTensor_isRestriction T sy sz counts)))
  rw [classOf_tensorPower] at hrestrict
  have hprod := ClassDegenerates.prod Finset.univ (fun i _ => (hQ i).pow (counts i))
  have hout := ((ClassDegenerates.refl (N : TensorClass K)).mul hprod).mul
    (ClassDegenerates.refl (classOf (dotTensor (K := K) N)))
  exact (hrestrict.trans hsep').trans hout

end BlockIdentities.Square
