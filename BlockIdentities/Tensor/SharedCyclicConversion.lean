/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.SharedTypeConversion
public import BlockIdentities.Tensor.CyclicProductClasses

/-! Three actual cyclic orientations balance the finite shared-leg conversion. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K : Type*} [Field K] [Infinite K]

/-- Tensor the actual type conversion in its three cyclic orientations and
balance every rectangular factor and the retained dot product. -/
theorem SharedLegIdentity.cyclic_type_conversion {ι : Type}
    [Fintype ι] [DecidableEq ι]
    {A : FiniteTensor K} {B : ι → FiniteTensor K}
    {D : MatrixShape} {E : ι → MatrixShape}
    (identity : SharedLegIdentity A B D E) (counts : ι → ℕ) :
    ClassDegenerates
      ((((6 * Fintype.card (ExactWords counts)) ^ 3 : ℕ) : TensorClass K) *
        (tensorClass (symmetrize (permute identity.sourcePermutation A)) ^ (∑ i, counts i) *
          matrixClass (D.volume ^ (∑ i, counts i))))
      (((Fintype.card (ExactWords counts) ^ 3 : ℕ) : TensorClass K) *
        (matrixClass (Fintype.card (ExactWords counts) * ∏ i, (E i).volume ^ counts i) *
          ∏ i, tensorClass (symmetrize (permute (identity.outputPermutation i) (B i))) ^ counts i)) := by
  classical
  have hM : 1 ≤ Fintype.card (ExactWords counts) :=
    Nat.one_le_iff_ne_zero.mpr (ne_of_gt (exactWords_card_pos counts))
  have hc := (identity.type_conversion counts).cyclicProduct
  have hs : cyclicProduct
      (((6 * Fintype.card (ExactWords counts) : ℕ) : TensorClass K) *
        tensorClass (permute identity.sourcePermutation (product A D.tensor)) ^ (∑ i, counts i)) =
      ((((6 * Fintype.card (ExactWords counts)) ^ 3 : ℕ) : TensorClass K) *
        (tensorClass (symmetrize (permute identity.sourcePermutation A)) ^ (∑ i, counts i) *
          matrixClass (D.volume ^ (∑ i, counts i)))) := by
    simp only [cyclicProduct_mul, cyclicProduct_natCast, cyclicProduct_pow,
      cyclicProduct_permute_product_matrixShape, mul_pow, matrixClass_pow]
  have ht : cyclicProduct
      ((Fintype.card (ExactWords counts) : TensorClass K) *
        (∏ i, tensorClass (permute (identity.outputPermutation i) (product (B i) (E i).tensor)) ^ counts i) *
        classOf (dotTensor (K := K) (Fintype.card (ExactWords counts)))) =
      (((Fintype.card (ExactWords counts) ^ 3 : ℕ) : TensorClass K) *
        (matrixClass (Fintype.card (ExactWords counts) * ∏ i, (E i).volume ^ counts i) *
          ∏ i, tensorClass (symmetrize (permute (identity.outputPermutation i) (B i))) ^ counts i)) := by
    simp only [cyclicProduct_mul, cyclicProduct_natCast, cyclicProduct_prod,
      cyclicProduct_pow, cyclicProduct_permute_product_matrixShape,
      cyclicProduct_dotTensor _ hM, matrixClass_mul, matrixClass_prod, matrixClass_pow,
      mul_pow, Finset.prod_mul_distrib]
    ring
  rw [hs, ht] at hc
  exact hc

end BlockIdentities.Square
