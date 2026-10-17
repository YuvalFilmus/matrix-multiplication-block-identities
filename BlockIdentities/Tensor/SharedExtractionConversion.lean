/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.SharedCyclicConversion
public import BlockIdentities.Tensor.FiniteAsymptoticConversion
public import BlockIdentities.Tensor.ListClasses

/-! Cancel the common exact word multiplicity in the actual finite extraction. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K : Type*} [Field K] [Infinite K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem SharedLegIdentity.extraction_conversion
    {A : FiniteTensor K} {B : ι → FiniteTensor K} {D : MatrixShape} {E : ι → MatrixShape}
    (identity : SharedLegIdentity A B D E) (counts : ι → ℕ) :
    AsymptoticallyRestricts
      (copies 216 (product
        (power (symmetrize (permute identity.sourcePermutation A)) (∑ i, counts i))
        (square (D.volume ^ (∑ i, counts i)))))
      (product (square (Fintype.card (ExactWords counts) * ∏ i, (E i).volume ^ counts i))
        (tensorProductList (List.ofFn (fun l : Fin (Fintype.card ι) =>
          let i := (Fintype.equivFin ι).symm l
          power (symmetrize (permute (identity.outputPermutation i) (B i))) (counts i))))) := by
  classical
  let M := Fintype.card (ExactWords counts)
  have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (exactWords_card_pos counts))
  have hc := identity.cyclic_type_conversion counts
  have hl : tensorClass (tensorProductList (List.ofFn (fun l : Fin (Fintype.card ι) =>
      let i := (Fintype.equivFin ι).symm l
      power (symmetrize (permute (identity.outputPermutation i) (B i))) (counts i)))) =
      ∏ i, tensorClass (symmetrize (permute (identity.outputPermutation i) (B i))) ^ counts i := by
    rw [tensorClass_tensorProductList_ofFn]
    simp only [tensorClass_power_eq]
    exact (Fintype.equivFin ι).symm.prod_comp
      (fun i => tensorClass (symmetrize (permute (identity.outputPermutation i) (B i))) ^ counts i)
  apply asymptoticallyRestricts_of_common_copies (M ^ 3) (Nat.one_le_pow _ _ hM)
  simp only [tensorClass_copies_eq, tensorClass_product_eq, tensorClass_power_eq,
    tensorClass_square_eq, hl]
  convert hc using 1
  · simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
    ring

end BlockIdentities.Square
