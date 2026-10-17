/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.FamilyClasses
public import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexTypeCounting

/-! Exact-population words reorder finite products through genuine tensor classes. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators

/-- Group a finite product by the actual fibers counted by wordPopulation. -/
theorem prod_word_eq_prod_population {J ι C : Type*}
    [Fintype J] [Fintype ι] [DecidableEq ι] [CommMonoid C]
    (w : J → ι) (a : ι → C) :
    (∏ j, a (w j)) = ∏ i, a i ^ wordPopulation w i := by
  classical
  simpa only [Finset.prod_const, Finset.card_univ, wordPopulation]
    using (Fintype.prod_fiberwise' w a).symm

/-- An exact-population word has precisely the prescribed product multiplicities. -/
theorem prod_exactWord_eq_prod_powers {ι C : Type*}
    [Fintype ι] [DecidableEq ι] [CommMonoid C]
    (counts : ι → ℕ) (w : ExactWords counts) (a : ι → C) :
    (∏ j, a (w.val j)) = ∏ i, a i ^ counts i := by
  rw [prod_word_eq_prod_population]
  apply Finset.prod_congr rfl
  intro i _
  rw [w.property i]

/-- Reordering a type-word product uses genuine finite tensor-class equality. -/
theorem classOf_familyProduct_exactWord {K X Y Z ι : Type*}
    [Field K] [Fintype X] [Fintype Y] [Fintype Z] [Fintype ι] [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (counts : ι → ℕ) (w : ExactWords counts) :
    classOf (familyProduct (fun j => T (w.val j))) =
      ∏ i, classOf (T i) ^ counts i := by
  rw [classOf_familyProduct]
  exact prod_exactWord_eq_prod_powers counts w (fun i => classOf (T i))

end BlockIdentities.Square
