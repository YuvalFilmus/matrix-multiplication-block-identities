/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ConvolutionSplittings
public import BlockIdentities.Tensor.SectorDotClasses
public import BlockIdentities.Tensor.ClassDegeneration
public import Mathlib.Tactic.FinCases

/-! Construct genuine shared-leg identities from supported raw sums. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K : Type*} [Field K]

/-- Canonical finite-coordinate transport of a raw two-leg-supported sum.
The only degeneration inputs are actual source and constituent maps. -/
def sharedLegIdentityOfSupportedSum {ι X Y Z : Type}
    [Fintype ι] [DecidableEq ι] [Fintype X] [Fintype Y] [Fintype Z]
    (A : FiniteTensor K) (B : ι → FiniteTensor K)
    (D : MatrixShape) (E : ι → MatrixShape)
    (T : Tensor K X Y Z) (sy : Y → ι) (sz : Z → ι)
    (hsupport : ∀ x y z, T x y z ≠ 0 → sy y = sz z)
    (π : LegPermutation) (σ : ι → LegPermutation)
    (hsource : Degenerates (permute π (product A D.tensor)) (FiniteTensor.ofTensor T))
    (hblocks : ∀ i, ClassDegenerates (classOf (sectorBlock T sy i))
      (tensorClass (permute (σ i) (product (B i) (E i).tensor)))) :
    SharedLegIdentity A B D E := by
  classical
  let ex := Fintype.equivFin X
  let ey := Fintype.equivFin Y
  let ez := Fintype.equivFin Z
  let U := FiniteTensor.ofTensor T
  let blocks : ι → Tensor K (Fin U.nx) (Fin U.ny) (Fin U.nz) :=
    fun i => Tensor.pullback ex.symm ey.symm ez.symm (sectorBlock T sy i)
  refine ⟨U, blocks, (fun y => sy (ey.symm y)), (fun z => sz (ez.symm z)),
    ?_, ?_, π, hsource, σ, ?_⟩
  · intro i x y z hn
    change (if sy (ey.symm y) = i then T (ex.symm x) (ey.symm y) (ez.symm z) else 0) ≠ 0 at hn
    have hy : sy (ey.symm y) = i := by
      by_contra h
      exact hn (if_neg h)
    have ht : T (ex.symm x) (ey.symm y) (ez.symm z) ≠ 0 := by
      simpa only [if_pos hy] using hn
    exact ⟨hy, (hsupport _ _ _ ht).symm.trans hy⟩
  · funext x y z
    simp only [Finset.sum_apply]
    change T (ex.symm x) (ey.symm y) (ez.symm z) =
      ∑ i, if sy (ey.symm y) = i then T (ex.symm x) (ey.symm y) (ez.symm z) else 0
    simp
  · intro i
    apply (classDegenerates_tensorClass_iff _ _).1
    have heq : tensorClass (⟨U.nx, U.ny, U.nz, blocks i⟩ : FiniteTensor K) =
        classOf (sectorBlock T sy i) := by
      rw [← classOf_coeff]
      change classOf (Tensor.pullback ex.symm ey.symm ez.symm (sectorBlock T sy i)) = _
      exact classOf_eq_of_reindex ex.symm ey.symm ez.symm rfl
    rw [heq]
    exact hblocks i

/-- Extend the first summand by zeros on the unused side coordinates. -/
def pairLeftBlock {X Y₀ Z₀ Y₁ Z₁ : Type} (T : Tensor K X Y₀ Z₀) :
    Tensor K X (Y₀ ⊕ Y₁) (Z₀ ⊕ Z₁) :=
  fun x y z => match y, z with
    | .inl y, .inl z => T x y z
    | _, _ => 0

/-- Zero padding is mutual restriction, even when a side space is empty. -/
theorem classOf_pairLeftBlock {X Y₀ Z₀ Y₁ Z₁ : Type}
    [Fintype X] [Fintype Y₀] [Fintype Z₀] [Fintype Y₁] [Fintype Z₁]
    (T : Tensor K X Y₀ Z₀) : classOf (pairLeftBlock (Y₁ := Y₁) (Z₁ := Z₁) T) = classOf T := by
  classical
  apply le_antisymm
  · apply (classOf_le_iff _ _).2
    refine ⟨(fun x i => if i = x then 1 else 0),
      (fun y i => match y with | .inl y => if i = y then 1 else 0 | .inr _ => 0),
      (fun z i => match z with | .inl z => if i = z then 1 else 0 | .inr _ => 0), ?_⟩
    funext x y z
    cases y <;> cases z <;> simp [Tensor.restrict, pairLeftBlock, mul_ite, ite_mul]
  · apply (classOf_le_iff _ _).2
    have h := IsRestriction.pullback (pairLeftBlock (Y₁ := Y₁) (Z₁ := Z₁) T)
      id Sum.inl Sum.inl
    have he : Tensor.pullback id Sum.inl Sum.inl
        (pairLeftBlock (Y₁ := Y₁) (Z₁ := Z₁) T) = T := by
      funext x y z
      rfl
    rw [he] at h
    exact h

/-- Extend the second summand by zeros on the unused side coordinates. -/
def pairRightBlock {X Y₀ Z₀ Y₁ Z₁ : Type} (T : Tensor K X Y₁ Z₁) :
    Tensor K X (Y₀ ⊕ Y₁) (Z₀ ⊕ Z₁) :=
  fun x y z => match y, z with
    | .inr y, .inr z => T x y z
    | _, _ => 0

theorem classOf_pairRightBlock {X Y₀ Z₀ Y₁ Z₁ : Type}
    [Fintype X] [Fintype Y₀] [Fintype Z₀] [Fintype Y₁] [Fintype Z₁]
    (T : Tensor K X Y₁ Z₁) :
    classOf (pairRightBlock (Y₀ := Y₀) (Z₀ := Z₀) T) = classOf T := by
  have he : classOf (pairRightBlock (Y₀ := Y₀) (Z₀ := Z₀) T) =
      classOf (pairLeftBlock (Y₁ := Y₀) (Z₁ := Z₀) T) := by
    apply classOf_eq_of_reindex (Equiv.refl X) (Equiv.sumComm _ _) (Equiv.sumComm _ _)
    funext x y z
    cases y <;> cases z <;> rfl
  exact he.trans (classOf_pairLeftBlock T)

/-- Two intrinsic block maps extend to a genuine identity on the shared sum.
The first-leg spaces remain shared; only side zero padding is removed. -/
def sharedFirstPairIdentity {X Y₀ Z₀ Y₁ Z₁ : Type}
    [Fintype X] [Fintype Y₀] [Fintype Z₀] [Fintype Y₁] [Fintype Z₁]
    (T₀ : Tensor K X Y₀ Z₀) (T₁ : Tensor K X Y₁ Z₁)
    (A : FiniteTensor K) (B : Fin 2 → FiniteTensor K)
    (D : MatrixShape) (E : Fin 2 → MatrixShape)
    (π : LegPermutation) (σ : Fin 2 → LegPermutation)
    (hsource : Degenerates (permute π (product A D.tensor)) (sharedFirstPair T₀ T₁))
    (h₀ : ClassDegenerates (classOf T₀)
      (tensorClass (permute (σ 0) (product (B 0) (E 0).tensor))))
    (h₁ : ClassDegenerates (classOf T₁)
      (tensorClass (permute (σ 1) (product (B 1) (E 1).tensor)))) :
    SharedLegIdentity A B D E := by
  classical
  let T : Tensor K X (Y₀ ⊕ Y₁) (Z₀ ⊕ Z₁) := fun x y z =>
    match y, z with
    | .inl y, .inl z => T₀ x y z
    | .inr y, .inr z => T₁ x y z
    | _, _ => 0
  let sy : Y₀ ⊕ Y₁ → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)
  let sz : Z₀ ⊕ Z₁ → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)
  have hs : ∀ x y z, T x y z ≠ 0 → sy y = sz z := by
    intro x y z hn
    cases y <;> cases z <;> simp_all [T, sy, sz]
  apply sharedLegIdentityOfSupportedSum A B D E T sy sz hs π σ hsource
  intro i
  fin_cases i
  · have he : sectorBlock T sy 0 = pairLeftBlock T₀ := by
      funext x y z
      cases y <;> cases z <;> simp [sectorBlock, T, sy, pairLeftBlock]
    change ClassDegenerates (classOf (sectorBlock T sy 0))
      (tensorClass (permute (σ 0) (product (B 0) (E 0).tensor)))
    rw [he, classOf_pairLeftBlock]
    exact h₀
  · have he : sectorBlock T sy 1 = pairRightBlock T₁ := by
      funext x y z
      cases y <;> cases z <;> simp [sectorBlock, T, sy, pairRightBlock]
    change ClassDegenerates (classOf (sectorBlock T sy 1))
      (tensorClass (permute (σ 1) (product (B 1) (E 1).tensor)))
    rw [he, classOf_pairRightBlock]
    exact h₁

/-- Three intrinsic maps become independent only on their side coordinates. -/
def sharedFirstThreeIdentity {X Y₀ Z₀ Y₁ Z₁ Y₂ Z₂ : Type}
    [Fintype X] [Fintype Y₀] [Fintype Z₀] [Fintype Y₁] [Fintype Z₁]
    [Fintype Y₂] [Fintype Z₂]
    (T₀ : Tensor K X Y₀ Z₀) (T₁ : Tensor K X Y₁ Z₁) (T₂ : Tensor K X Y₂ Z₂)
    (A : FiniteTensor K) (B : Fin 3 → FiniteTensor K)
    (D : MatrixShape) (E : Fin 3 → MatrixShape)
    (π : LegPermutation) (σ : Fin 3 → LegPermutation)
    (hsource : Degenerates (permute π (product A D.tensor))
      (sharedFirstThree T₀ T₁ T₂))
    (h₀ : ClassDegenerates (classOf T₀)
      (tensorClass (permute (σ 0) (product (B 0) (E 0).tensor))))
    (h₁ : ClassDegenerates (classOf T₁)
      (tensorClass (permute (σ 1) (product (B 1) (E 1).tensor))))
    (h₂ : ClassDegenerates (classOf T₂)
      (tensorClass (permute (σ 2) (product (B 2) (E 2).tensor)))) :
    SharedLegIdentity A B D E := by
  classical
  let T : Tensor K X (Y₀ ⊕ (Y₁ ⊕ Y₂)) (Z₀ ⊕ (Z₁ ⊕ Z₂)) := fun x y z =>
    match y, z with
    | .inl y, .inl z => T₀ x y z
    | .inr (.inl y), .inr (.inl z) => T₁ x y z
    | .inr (.inr y), .inr (.inr z) => T₂ x y z
    | _, _ => 0
  let sy : Y₀ ⊕ (Y₁ ⊕ Y₂) → Fin 3 :=
    Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2))
  let sz : Z₀ ⊕ (Z₁ ⊕ Z₂) → Fin 3 :=
    Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2))
  have hs : ∀ x y z, T x y z ≠ 0 → sy y = sz z := by
    intro x y z hn
    rcases y with y | y <;> rcases z with z | z
    · rfl
    · rcases z with z | z <;> simp_all [T]
    · rcases y with y | y <;> simp_all [T]
    · rcases y with y | y <;> rcases z with z | z <;> simp_all [T, sy, sz]
  apply sharedLegIdentityOfSupportedSum A B D E T sy sz hs π σ hsource
  intro i
  fin_cases i
  · have he : sectorBlock T sy 0 = pairLeftBlock T₀ := by
      funext x y z
      rcases y with y | y <;> rcases z with z | z
      · simp [sectorBlock, T, sy, pairLeftBlock]
      · rcases z with z | z <;> simp [sectorBlock, T, sy, pairLeftBlock]
      · rcases y with y | y <;> simp [sectorBlock, T, sy, pairLeftBlock]
      · rcases y with y | y <;> rcases z with z | z <;>
          simp [sectorBlock, T, sy, pairLeftBlock]
    change ClassDegenerates (classOf (sectorBlock T sy 0))
      (tensorClass (permute (σ 0) (product (B 0) (E 0).tensor)))
    rw [he, classOf_pairLeftBlock]
    exact h₀
  · have he : sectorBlock T sy 1 = pairRightBlock (pairLeftBlock T₁) := by
      funext x y z
      rcases y with y | y <;> rcases z with z | z
      · simp [sectorBlock, T, sy, pairRightBlock]
      · rcases z with z | z <;> simp [sectorBlock, T, sy, pairRightBlock]
      · rcases y with y | y <;> simp [sectorBlock, T, sy, pairRightBlock, pairLeftBlock]
      · rcases y with y | y <;> rcases z with z | z <;>
          simp [sectorBlock, T, sy, pairRightBlock, pairLeftBlock]
    change ClassDegenerates (classOf (sectorBlock T sy 1))
      (tensorClass (permute (σ 1) (product (B 1) (E 1).tensor)))
    rw [he, classOf_pairRightBlock, classOf_pairLeftBlock]
    exact h₁
  · have he : sectorBlock T sy 2 = pairRightBlock (pairRightBlock T₂) := by
      funext x y z
      rcases y with y | y <;> rcases z with z | z
      · simp [sectorBlock, T, sy, pairRightBlock]
      · rcases z with z | z <;> simp [sectorBlock, T, sy, pairRightBlock]
      · rcases y with y | y <;> simp [sectorBlock, T, sy, pairRightBlock]
      · rcases y with y | y <;> rcases z with z | z <;>
          simp [sectorBlock, T, sy, pairRightBlock]
    change ClassDegenerates (classOf (sectorBlock T sy 2))
      (tensorClass (permute (σ 2) (product (B 2) (E 2).tensor)))
    rw [he, classOf_pairRightBlock, classOf_pairRightBlock]
    exact h₂

end BlockIdentities.Square
