/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.SeparatorLeading
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.DirectSumClass

/-! The retained filter is the genuine direct sum of its sector-dot blocks. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K X Y Z : Type*} [Field K]
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- The literal retained block, including its dot-product coordinates. -/
def sectorDotBlock {M : ℕ} (T : Tensor K X Y Z) (sy : Y → Fin M) (i : Fin M) :
    Tensor K X (Y × Fin M) (Z × Fin M) :=
  fun x y z => if sy y.1 = i ∧ y.2 = z.2 then T x y.1 z.1 else 0

/-- Identifying redundant sector coordinates recovers the retained tensor. -/
theorem separatorRetained_isRestriction_directSum {M : ℕ}
    (T : Tensor K X Y Z) (sy : Y → Fin M) (sz : Z → Fin M)
    (hsupport : ∀ x y z, T x y z ≠ 0 → sy y = sz z) :
    IsRestriction (separatorRetained T sy) (Tensor.directSum (sectorDotBlock T sy)) := by
  classical
  have hp := IsRestriction.pullback (Tensor.directSum (sectorDotBlock T sy))
    (fun x : X × Fin M => (x.2, x.1))
    (fun y : Y × Fin M => (sy y.1, y))
    (fun z : Z × Fin M => (sz z.1, z))
  have he : Tensor.pullback (fun x : X × Fin M => (x.2, x.1))
      (fun y : Y × Fin M => (sy y.1, y))
      (fun z : Z × Fin M => (sz z.1, z))
      (Tensor.directSum (sectorDotBlock T sy)) = separatorRetained T sy := by
    funext x y z
    by_cases ht : T x.1 y.1 z.1 = 0
    · simp [Tensor.pullback, Tensor.directSum, sectorDotBlock, separatorRetained, ht]
    · have hs := hsupport x.1 y.1 z.1 ht
      simp only [Tensor.pullback, Tensor.directSum, sectorDotBlock, separatorRetained]
      simp only [← hs]
      clear hsupport hs ht
      by_cases hg : x.2 = sy y.1 <;> by_cases hu : y.2 = z.2 <;>
        simp [hg, hu, eq_comm]
  rw [he] at hp
  exact hp

/-- Sector masks remove the redundant coordinates in the opposite direction. -/
theorem separatorDirectSum_isRestriction_retained {M : ℕ}
    (T : Tensor K X Y Z) (sy : Y → Fin M) (sz : Z → Fin M)
    (hsupport : ∀ x y z, T x y z ≠ 0 → sy y = sz z) :
    IsRestriction (Tensor.directSum (sectorDotBlock T sy)) (separatorRetained T sy) := by
  classical
  let L : (Fin M × X) → (X × Fin M) → K :=
    fun x q => if q = (x.2, x.1) then 1 else 0
  let N : (Fin M × (Y × Fin M)) → (Y × Fin M) → K :=
    fun y q => if y.1 = sy y.2.1 then if q = y.2 then 1 else 0 else 0
  let P : (Fin M × (Z × Fin M)) → (Z × Fin M) → K :=
    fun z q => if z.1 = sz z.2.1 then if q = z.2 then 1 else 0 else 0
  refine ⟨L, N, P, ?_⟩
  funext x y z
  have hr : Tensor.restrict L N P (separatorRetained T sy) x y z =
      if y.1 = sy y.2.1 then
        if z.1 = sz z.2.1 then separatorRetained T sy (x.2, x.1) y.2 z.2 else 0
      else 0 := by
    simp [Tensor.restrict, L, N, P, ite_mul, mul_ite]
    split_ifs <;> rfl
  rw [hr]
  by_cases ht : T x.2 y.2.1 z.2.1 = 0
  · simp [Tensor.directSum, sectorDotBlock, separatorRetained, ht]
  · have hs := hsupport x.2 y.2.1 z.2.1 ht
    simp only [Tensor.directSum, sectorDotBlock, separatorRetained]
    simp only [← hs]
    clear hsupport hs ht
    by_cases hx : x.1 = sy y.2.1 <;>
      by_cases hy : y.1 = sy y.2.1 <;>
      by_cases hz : z.1 = sy y.2.1 <;>
      by_cases hu : y.2.2 = z.2.2 <;> simp [hx, hy, hz, hu, eq_comm]

/-- Genuine mutual restriction identifies the retained tensor with a sum of blocks. -/
theorem classOf_separatorRetained {M : ℕ} (T : Tensor K X Y Z)
    (sy : Y → Fin M) (sz : Z → Fin M)
    (hsupport : ∀ x y z, T x y z ≠ 0 → sy y = sz z) :
    classOf (separatorRetained T sy) = ∑ i : Fin M, classOf (sectorDotBlock T sy i) := by
  rw [← classOf_directSum]
  apply le_antisymm
  · exact (classOf_le_iff _ _).2 (separatorRetained_isRestriction_directSum T sy sz hsupport)
  · exact (classOf_le_iff _ _).2 (separatorDirectSum_isRestriction_retained T sy sz hsupport)

end BlockIdentities.Square
