/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Definitions
public import BlockIdentities.Rectangular.Providers.OrientedSharedLegEntropy

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem oriented_shared_leg_entropy {F : Type*} [Field F]
    {ι : Type} [Fintype ι] (S : InteriorSupport F)
    (A : TensorOf F) (B : ι → TensorOf F) (D : MatrixShape) (E : ι → MatrixShape)
    (identity : SharedLegIdentity A.val (fun i => (B i).val) D E)
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, q i = 1) :
  Real.log (orientedValue S
      ((A.product (D.nonzeroTensor (K := AlgebraicClosure F))).permute
        identity.sourcePermutation)) ≥ S.weight 0 * OAI.MatrixMultiplication.Foundation.finiteEntropy q +
      ∑ i, q i * Real.log (orientedValue S
        (((B i).product ((E i).nonzeroTensor (K := AlgebraicClosure F))).permute
          (identity.outputPermutation i))) :=
-- BEGIN APPROVED PROOF REGION
by
  exact Providers.oriented_shared_leg_entropy S A B D E identity q hq hsum
-- END APPROVED PROOF REGION

end BlockIdentities.Rectangular
