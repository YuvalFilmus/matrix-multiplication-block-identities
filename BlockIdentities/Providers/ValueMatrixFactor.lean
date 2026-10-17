/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ValueCopiesBound

/-! Assemble the manuscript's value theorem from actual rate constructions. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Providers
open BlockIdentities.Square

theorem value_matrix_factor {K : Type*} [Field K] [IsAlgClosed K]
    (T : NonzeroTensor K) (hcyclic : Isomorphic T.val (permute .yzx T.val)) :
    (∀ U : NonzeroTensor K, Isomorphic U.val (permute .yzx U.val) →
        AsymptoticallyRestricts T.val U.val → valueAtOmega U ≤ valueAtOmega T) ∧
      (∀ d : ℕ, ∀ hd : 1 ≤ d,
        valueAtOmega (T.product (nonzeroSquare d hd)) =
          (d : ℝ) ^ Arithmetic.formalOmega K * valueAtOmega T) ∧
      (∀ b : ℕ, ∀ hb : 1 ≤ b,
        valueAtOmega (T.copies b hb) ≤ (b : ℝ) ^ Arithmetic.formalOmega K * valueAtOmega T) := by
  have hT := hcyclic.cycleClass_fixed
  refine ⟨?_, ?_, ?_⟩
  · intro U hU hTU
    exact valueAtOmega_mono_of_asymptoticallyRestricts T U hT hU.cycleClass_fixed hTU
  · exact valueAtOmega_product_square T hT
  · exact valueAtOmega_copies_le T hT

end BlockIdentities.Providers
