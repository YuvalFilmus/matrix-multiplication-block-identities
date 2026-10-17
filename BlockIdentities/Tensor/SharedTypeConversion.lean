/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.TypeSeparatorConversion

/-! Consume the actual shared-leg identity in the finite type conversion. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K : Type*} [Field K] [Infinite K]

/-- Actual block maps, source map, and side support supply the finite type
conversion; no common first-leg independence is required before separation. -/
theorem SharedLegIdentity.type_conversion {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : FiniteTensor K} {B : ι → FiniteTensor K} {D : MatrixShape} {E : ι → MatrixShape}
    (identity : SharedLegIdentity A B D E) (counts : ι → ℕ) :
    ClassDegenerates
      (((6 * Fintype.card (ExactWords counts) : ℕ) : TensorClass K) *
        tensorClass (permute identity.sourcePermutation (product A D.tensor)) ^ (∑ i, counts i))
      ((Fintype.card (ExactWords counts) : TensorClass K) *
        (∏ i, tensorClass (permute (identity.outputPermutation i) (product (B i) (E i).tensor)) ^ counts i) *
        classOf (dotTensor (K := K) (Fintype.card (ExactWords counts)))) := by
  classical
  have hsupport : ∀ x y z, identity.ambient.coeff x y z ≠ 0 →
      identity.ySector y = identity.zSector z := by
    intro x y z hn
    have hex : ∃ i, identity.blocks i x y z ≠ 0 := by
      by_contra hnone
      apply hn
      have hz : ∀ i, identity.blocks i x y z = 0 := by
        intro i
        by_contra hi
        exact hnone ⟨i, hi⟩
      have hs := congrFun (congrFun (congrFun identity.sum_eq x) y) z
      simpa only [Finset.sum_apply, hz, Finset.sum_const_zero] using hs
    obtain ⟨i, hi⟩ := hex
    exact (identity.support i x y z hi).1.trans (identity.support i x y z hi).2.symm
  have hmasks (i : ι) : identity.blocks i =
      sectorBlock identity.ambient.coeff identity.ySector i :=
    blocks_eq_sectorBlock identity.ambient.coeff identity.blocks identity.ySector identity.sum_eq
      (fun j x y z hj => (identity.support j x y z hj).1) i
  have hQ (i : ι) : ClassDegenerates
      (classOf (sectorBlock identity.ambient.coeff identity.ySector i))
      (tensorClass (permute (identity.outputPermutation i) (product (B i) (E i).tensor))) := by
    have h := (classDegenerates_tensorClass_iff _ _).2 (identity.block_degeneration i)
    have heq : classOf (identity.blocks i) =
        tensorClass (⟨identity.ambient.nx, identity.ambient.ny, identity.ambient.nz,
          identity.blocks i⟩ : FiniteTensor K) :=
      classOf_coeff (⟨identity.ambient.nx, identity.ambient.ny, identity.ambient.nz,
        identity.blocks i⟩ : FiniteTensor K)
    rw [← heq, hmasks i] at h
    exact h
  have hconvert := type_separator_conversion identity.ambient.coeff
    identity.ySector identity.zSector hsupport counts
    (fun i => tensorClass (permute (identity.outputPermutation i) (product (B i) (E i).tensor))) hQ
  rw [classOf_coeff] at hconvert
  have hsource := ((classDegenerates_tensorClass_iff _ _).2
    identity.source_degeneration).pow (∑ i, counts i)
  exact ((ClassDegenerates.refl
    (((6 * Fintype.card (ExactWords counts) : ℕ) : TensorClass K))).mul hsource).trans hconvert

end BlockIdentities.Square
