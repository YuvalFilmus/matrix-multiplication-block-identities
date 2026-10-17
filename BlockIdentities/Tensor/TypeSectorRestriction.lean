/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.Definitions
public import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexTypeCounting

/-! Actual fixed-population restriction and its two independent word sectors. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K X Y Z ι : Type*} [Field K]
variable [Fintype X] [Fintype Y] [Fintype Z] [Fintype ι] [DecidableEq ι]

/-- Keep precisely coordinates whose label word has the prescribed population. -/
abbrev TypeSectorCoordinates (s : Y → ι) (counts : ι → ℕ) :=
  {y : Fin (∑ i, counts i) → Y // ∀ i, wordPopulation (s ∘ y) i = counts i}

/-- The sector label is the actual coordinate's label word. -/
def typeSectorLabel (s : Y → ι) (counts : ι → ℕ)
    (y : TypeSectorCoordinates s counts) : ExactWords counts :=
  ⟨s ∘ y.val, y.property⟩

/-- Pull back the raw tensor power to the two fixed-population coordinate sets. -/
def typeSectorTensor (T : Tensor K X Y Z) (sy : Y → ι) (sz : Z → ι)
    (counts : ι → ℕ) : Tensor K (Fin (∑ i, counts i) → X)
      (TypeSectorCoordinates sy counts) (TypeSectorCoordinates sz counts) :=
  Tensor.pullback id Subtype.val Subtype.val (Tensor.power T (∑ i, counts i))

/-- The fixed-population operation is a genuine finite coordinate restriction. -/
theorem typeSectorTensor_isRestriction (T : Tensor K X Y Z)
    (sy : Y → ι) (sz : Z → ι) (counts : ι → ℕ) :
    IsRestriction (typeSectorTensor T sy sz counts) (Tensor.power T (∑ i, counts i)) := by
  classical
  exact IsRestriction.pullback _ id Subtype.val Subtype.val

/-- Every surviving coefficient has the same word on the two independent legs. -/
theorem typeSectorTensor_support (T : Tensor K X Y Z)
    (sy : Y → ι) (sz : Z → ι) (counts : ι → ℕ)
    (hsupport : ∀ x y z, T x y z ≠ 0 → sy y = sz z)
    (x : Fin (∑ i, counts i) → X)
    (y : TypeSectorCoordinates sy counts) (z : TypeSectorCoordinates sz counts)
    (hne : typeSectorTensor T sy sz counts x y z ≠ 0) :
    typeSectorLabel sy counts y = typeSectorLabel sz counts z := by
  apply Subtype.ext
  funext t
  apply hsupport (x t) (y.val t) (z.val t)
  intro hzero
  apply hne
  change (∏ i, T (x i) (y.val i) (z.val i)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ t) hzero

/-- Literal sector block, with the shared first coordinates left untouched. -/
def typeSectorBlock (T : Tensor K X Y Z) (sy : Y → ι) (sz : Z → ι)
    (counts : ι → ℕ) (w : ExactWords counts) :
    Tensor K (Fin (∑ i, counts i) → X)
      (TypeSectorCoordinates sy counts) (TypeSectorCoordinates sz counts) := by
  classical
  exact fun x y z => if typeSectorLabel sy counts y = w then
    typeSectorTensor T sy sz counts x y z else 0

/-- The actual restricted tensor is the sum of its literal word sectors. -/
theorem typeSectorBlock_sum (T : Tensor K X Y Z)
    (sy : Y → ι) (sz : Z → ι) (counts : ι → ℕ) :
    (fun x y z => ∑ w : ExactWords counts, typeSectorBlock T sy sz counts w x y z) =
      typeSectorTensor T sy sz counts := by
  classical
  funext x y z
  simp [typeSectorBlock]

/-- Both side coordinates of each nonzero sector coefficient carry its label. -/
theorem typeSectorBlock_support (T : Tensor K X Y Z)
    (sy : Y → ι) (sz : Z → ι) (counts : ι → ℕ)
    (hsupport : ∀ x y z, T x y z ≠ 0 → sy y = sz z)
    (w : ExactWords counts) (x : Fin (∑ i, counts i) → X)
    (y : TypeSectorCoordinates sy counts) (z : TypeSectorCoordinates sz counts)
    (hne : typeSectorBlock T sy sz counts w x y z ≠ 0) :
    typeSectorLabel sy counts y = w ∧ typeSectorLabel sz counts z = w := by
  classical
  have hy : typeSectorLabel sy counts y = w := by
    by_contra hn
    simp only [typeSectorBlock, if_neg hn, ne_eq, not_true_eq_false] at hne
  have ht : typeSectorTensor T sy sz counts x y z ≠ 0 := by
    simpa only [typeSectorBlock, if_pos hy] using hne
  exact ⟨hy, (typeSectorTensor_support T sy sz counts hsupport x y z ht).symm.trans hy⟩

/-- The number of retained words is the exact multinomial count. -/
theorem typeSector_card (counts : ι → ℕ) :
    Fintype.card (ExactWords counts) = Nat.multinomial Finset.univ counts :=
  exactWords_card counts

/-- At least one exact-population word always exists, including the empty word. -/
theorem typeSector_card_pos (counts : ι → ℕ) : 0 < Fintype.card (ExactWords counts) :=
  exactWords_card_pos counts

end BlockIdentities.Square
