/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ClassDegeneration

/-! Removing coordinates outside the actual support preserves the tensor class. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K X Y Z : Type*} [Field K] [Fintype X] [Fintype Y] [Fintype Z]

theorem classOf_restrict_supported_sides (T : Tensor K X Y Z)
    (P : Y → Prop) (Q : Z → Prop) [DecidablePred P] [DecidablePred Q]
    (hsupport : ∀ x y z, T x y z ≠ 0 → P y ∧ Q z) :
    classOf (Tensor.pullback id Subtype.val Subtype.val T : Tensor K X {y // P y} {z // Q z}) =
      classOf T := by
  classical
  apply le_antisymm
  · exact (classOf_le_iff _ _).2 (IsRestriction.pullback T id Subtype.val Subtype.val)
  · apply (classOf_le_iff _ _).2
    let L : X → X → K := fun x i => if i = x then 1 else 0
    let M : Y → {y // P y} → K := fun y i => if i.val = y then 1 else 0
    let N : Z → {z // Q z} → K := fun z i => if i.val = z then 1 else 0
    refine ⟨L, M, N, ?_⟩
    funext x y z
    by_cases hp : P y
    · by_cases hq : Q z
      · have hy : ∀ i : {y // P y}, i.val = y ↔ i = ⟨y, hp⟩ := by
          intro i; exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
        have hz : ∀ i : {z // Q z}, i.val = z ↔ i = ⟨z, hq⟩ := by
          intro i; exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
        simp [Tensor.restrict, Tensor.pullback, L, M, N, hy, hz]
      · have hzero : T x y z = 0 := by
          by_contra ht; exact hq (hsupport x y z ht).2
        have hn : ∀ i : {z // Q z}, N z i = 0 := by
          intro i
          have hi : i.val ≠ z := by intro he; exact hq (he ▸ i.property)
          simp only [N, if_neg hi]
        simp [Tensor.restrict, hn, hzero]
    · have hzero : T x y z = 0 := by
        by_contra ht; exact hp (hsupport x y z ht).1
      have hm : ∀ i : {y // P y}, M y i = 0 := by
        intro i
        have hi : i.val ≠ y := by intro he; exact hp (he ▸ i.property)
        simp only [M, if_neg hi]
      simp [Tensor.restrict, hm, hzero]

end BlockIdentities.Square
