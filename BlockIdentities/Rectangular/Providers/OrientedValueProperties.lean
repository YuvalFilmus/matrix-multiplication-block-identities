/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedValueSums

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular.Providers
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem oriented_value_properties {F : Type*} [Field F]
    (S : InteriorSupport F) :
  (∀ T U : TensorOf F, AsymptoticallyRestricts T.val U.val →
      orientedValue S U ≤ orientedValue S T) ∧
    (∀ (T : TensorOf F) k, orientedValue S (T.power k) = orientedValue S T ^ k) ∧
    (∀ T U : TensorOf F, orientedValue S T * orientedValue S U ≤
      orientedValue S (T.product U)) ∧
    (∀ T U : TensorOf F, orientedValue S T + orientedValue S U ≤
      orientedValue S (T.sum U)) ∧
    (∀ (T : TensorOf F) (D : MatrixShape),
      orientedValue S (T.product (D.nonzeroTensor (K := AlgebraicClosure F))) =
        matrixWeight S D * orientedValue S T) ∧
    (∀ D : MatrixShape, orientedValue S (D.nonzeroTensor (K := AlgebraicClosure F)) =
      matrixWeight S D) :=
by
  exact ⟨orientedValue_mono S, orientedValue_power S, orientedValue_product_le S,
    orientedValue_sum_le S, orientedValue_product_matrix S, orientedValue_matrix S⟩

end BlockIdentities.Rectangular.Providers
