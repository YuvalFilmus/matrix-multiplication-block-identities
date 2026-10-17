/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.SharedTypeConversion
public import BlockIdentities.Tensor.FiniteAsymptoticConversion
public import BlockIdentities.Tensor.ListClasses

/-! The ordered shared-leg extraction, retaining the actual products before
permuting their tensor legs. A single common word multiplicity is cancelled. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K : Type*} [Field K] [Infinite K]

/-- This finite ordered extraction uses one separator, with six full source
copies. The retained dot factor stays on the physical first tensor leg. -/
theorem SharedLegIdentity.oriented_extraction_conversion
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : FiniteTensor K} {B : ι → FiniteTensor K}
    {D : MatrixShape} {E : ι → MatrixShape}
    (identity : SharedLegIdentity A B D E) (counts : ι → ℕ) :
    AsymptoticallyRestricts
      (copies 6 (power (permute identity.sourcePermutation (product A D.tensor))
        (∑ i, counts i)))
      (product (tensorProductList (List.ofFn (fun l : Fin (Fintype.card ι) =>
        let i := (Fintype.equivFin ι).symm l
        power (permute (identity.outputPermutation i) (product (B i) (E i).tensor))
          (counts i)))) (matrix 1 1 (Fintype.card (ExactWords counts)))) := by
  classical
  let M := Fintype.card (ExactWords counts)
  have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (exactWords_card_pos counts))
  have hc := identity.type_conversion counts
  have hl : tensorClass (tensorProductList (List.ofFn (fun l : Fin (Fintype.card ι) =>
      let i := (Fintype.equivFin ι).symm l
      power (permute (identity.outputPermutation i) (product (B i) (E i).tensor))
        (counts i)))) =
      ∏ i, tensorClass (permute (identity.outputPermutation i)
        (product (B i) (E i).tensor)) ^ counts i := by
    rw [tensorClass_tensorProductList_ofFn]
    simp only [tensorClass_power_eq]
    exact (Fintype.equivFin ι).symm.prod_comp
      (fun i => tensorClass (permute (identity.outputPermutation i)
        (product (B i) (E i).tensor)) ^ counts i)
  apply asymptoticallyRestricts_of_common_copies M hM
  simp only [tensorClass_copies_eq, tensorClass_power_eq, tensorClass_product_eq, hl]
  rw [classOf_dotTensor] at hc
  convert hc using 1
  · simp only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  · ring

end BlockIdentities.Square
