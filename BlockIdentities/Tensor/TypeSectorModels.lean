/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.TypeSectorRestriction
public import BlockIdentities.Tensor.SupportClasses
public import BlockIdentities.Tensor.WordProductClasses
public import BlockIdentities.Tensor.SectorDotClasses

/-! Literal fixed-word blocks model the actual products of their sector tensors. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K X Y Z ι : Type*} [Field K]
variable [Fintype X] [Fintype Y] [Fintype Z] [Fintype ι] [DecidableEq ι]

/-- Multiplying literal sector masks retains exactly the specified label word. -/
theorem familyProduct_sectorBlock_apply {n : ℕ} (T : Tensor K X Y Z)
    (sy : Y → ι) (w : Fin n → ι) (x : Fin n → X)
    (y : Fin n → Y) (z : Fin n → Z) :
    familyProduct (fun j => sectorBlock T sy (w j)) x y z =
      if sy ∘ y = w then Tensor.power T n x y z else 0 := by
  classical
  by_cases he : sy ∘ y = w
  · have hj (j : Fin n) : sy (y j) = w j := congrFun he j
    simp [familyProduct, sectorBlock, hj, he, Tensor.power]
  · have hex : ∃ j, sy (y j) ≠ w j := by
      by_contra h
      apply he
      funext j
      by_contra hj
      exact h ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hex
    rw [if_neg he]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [sectorBlock, hj]

/-- Nonzero coefficients of the word product lie on both true population subtypes. -/
theorem familyProduct_sectorBlock_supported (T : Tensor K X Y Z)
    (sy : Y → ι) (sz : Z → ι) (counts : ι → ℕ) (w : ExactWords counts)
    (hsupport : ∀ x y z, T x y z ≠ 0 → sy y = sz z)
    (x : Fin (∑ i, counts i) → X) (y : Fin (∑ i, counts i) → Y)
    (z : Fin (∑ i, counts i) → Z)
    (hne : familyProduct (fun j => sectorBlock T sy (w.val j)) x y z ≠ 0) :
    (∀ i, wordPopulation (sy ∘ y) i = counts i) ∧
      (∀ i, wordPopulation (sz ∘ z) i = counts i) := by
  classical
  rw [familyProduct_sectorBlock_apply] at hne
  have hy : sy ∘ y = w.val := by
    by_contra h
    exact hne (if_neg h)
  have ht : Tensor.power T (∑ i, counts i) x y z ≠ 0 := by
    simpa only [if_pos hy] using hne
  have hz : sz ∘ z = w.val := by
    funext j
    have hn : T (x j) (y j) (z j) ≠ 0 := by
      intro hzero
      exact ht (Finset.prod_eq_zero (Finset.mem_univ j) hzero)
    exact (hsupport _ _ _ hn).symm.trans (congrFun hy j)
  constructor
  · simpa only [hy] using w.property
  · simpa only [hz] using w.property

/-- Actual fixed-word blocks have the product class prescribed by their counts. -/
theorem classOf_typeSectorBlock (T : Tensor K X Y Z)
    (sy : Y → ι) (sz : Z → ι) (counts : ι → ℕ) (w : ExactWords counts)
    (hsupport : ∀ x y z, T x y z ≠ 0 → sy y = sz z) :
    classOf (typeSectorBlock T sy sz counts w) =
      ∏ i, classOf (sectorBlock T sy i) ^ counts i := by
  classical
  let F := familyProduct (fun j => sectorBlock T sy (w.val j))
  have heq : (Tensor.pullback id Subtype.val Subtype.val F :
      Tensor K (Fin (∑ i, counts i) → X)
        (TypeSectorCoordinates sy counts) (TypeSectorCoordinates sz counts)) =
      typeSectorBlock T sy sz counts w := by
    funext x y z
    change familyProduct (fun j => sectorBlock T sy (w.val j)) x y.val z.val = _
    rw [familyProduct_sectorBlock_apply]
    have hh : (sy ∘ y.val = w.val) ↔ typeSectorLabel sy counts y = w := by
      constructor
      · intro he
        exact Subtype.ext he
      · intro he
        exact congrArg Subtype.val he
    simp only [typeSectorBlock, typeSectorTensor, Tensor.pullback, hh, id_eq]
  have hc := classOf_restrict_supported_sides F
    (fun y => ∀ i, wordPopulation (sy ∘ y) i = counts i)
    (fun z => ∀ i, wordPopulation (sz ∘ z) i = counts i)
    (familyProduct_sectorBlock_supported T sy sz counts w hsupport)
  rw [heq] at hc
  exact hc.trans (classOf_familyProduct_exactWord (fun i => sectorBlock T sy i) counts w)
end BlockIdentities.Square
