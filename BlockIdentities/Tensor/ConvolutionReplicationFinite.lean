/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ConvolutionReplicationDegeneration
public import Mathlib.SetTheory.Cardinal.Basic

/-! Exact finite presentation of the characteristic-free replication maps. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace BlockIdentities.Square
open Polynomial
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
variable {K : Type*} [Field K]

private theorem sum_reindex_three {X Y Z R : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [AddCommMonoid R] (f : X → Y → Z → R) :
    (∑ x : Fin (Fintype.card X), ∑ y : Fin (Fintype.card Y),
      ∑ z : Fin (Fintype.card Z), f ((Fintype.equivFin X).symm x)
        ((Fintype.equivFin Y).symm y) ((Fintype.equivFin Z).symm z)) =
      ∑ x, ∑ y, ∑ z, f x y z := by
  rw [(Fintype.equivFin X).symm.sum_comp
    (fun x => ∑ y : Fin (Fintype.card Y), ∑ z : Fin (Fintype.card Z),
      f x ((Fintype.equivFin Y).symm y) ((Fintype.equivFin Z).symm z))]
  apply Finset.sum_congr rfl
  intro x _
  rw [(Fintype.equivFin Y).symm.sum_comp
    (fun y => ∑ z : Fin (Fintype.card Z), f x y ((Fintype.equivFin Z).symm z))]
  apply Finset.sum_congr rfl
  intro y _
  exact (Fintype.equivFin Z).symm.sum_comp (f x y)

private def finiteDegeneration {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {B : FiniteTensor K}
    {k Lx Ly Lz : ℕ} (D : Tensor.PolynomialRestrictionDegeneration T S k Lx Ly Lz)
    (dx : Fin B.nx → U) (dy : Fin B.ny → V) (dz : Fin B.nz → W)
    (hB : ∀ x y z, S (dx x) (dy y) (dz z) = B.coeff x y z) :
    Tensor.PolynomialRestrictionDegeneration
      (TensorSemiring.FiniteTensor.ofTensor T).coeff B.coeff k Lx Ly Lz where
  leftMap := fun x i => D.leftMap (dx x) ((Fintype.equivFin X).symm i)
  middleMap := fun y j => D.middleMap (dy y) ((Fintype.equivFin Y).symm j)
  rightMap := fun z l => D.rightMap (dz z) ((Fintype.equivFin Z).symm l)
  left_degree := fun x i => D.left_degree _ _
  middle_degree := fun y j => D.middle_degree _ _
  right_degree := fun z l => D.right_degree _ _
  vanishes := by
    intro x y z j hj
    have hs := sum_reindex_three (fun i l n =>
      D.leftMap (dx x) i * D.middleMap (dy y) l * D.rightMap (dz z) n * C (T i l n))
    exact (congrArg (fun f : K[X] => f.coeff j) hs).trans (D.vanishes _ _ _ j hj)
  leading := by
    intro x y z
    have hs := sum_reindex_three (fun i l n =>
      D.leftMap (dx x) i * D.middleMap (dy y) l * D.rightMap (dz z) n * C (T i l n))
    exact (congrArg (fun f : K[X] => f.coeff k) hs).trans
      ((D.leading _ _ _).trans (hB x y z))

/-- Characteristic-free convolution replication over an arbitrary infinite field.
The node family is selected injectively, without any roots-of-unity assumption. -/
theorem convolution_replication_of_infinite [Infinite K] (m r s : ℕ+) :
    Degenerates (convolution (K := K) (m * r) (m * s))
      (copies (m : ℕ) (convolution r s)) := by
  classical
  let nodes : Fin (m : ℕ) → K := fun i => Infinite.natEmbedding K i.val
  have hinj : Function.Injective nodes := fun i j he =>
    Fin.ext ((Infinite.natEmbedding K).injective he)
  let A := convolution (K := K) r s
  let B := copies (m : ℕ) A
  let dx : Fin B.nx → Fin (m : ℕ) × Fin (r : ℕ) := fun x =>
    let hx := (Fintype.equivFin (Fin (m : ℕ) × Fin A.nx)).symm x
    (hx.1, (Fintype.equivFin (Fin (r : ℕ))).symm hx.2)
  let dy : Fin B.ny → Fin (m : ℕ) × Fin (s : ℕ) := fun y =>
    let hy := (Fintype.equivFin (Fin (m : ℕ) × Fin A.ny)).symm y
    (hy.1, (Fintype.equivFin (Fin (s : ℕ))).symm hy.2)
  let dz : Fin B.nz → Fin (m : ℕ) × Fin ((r : ℕ) + (s : ℕ) - 1) := fun z =>
    let hz := (Fintype.equivFin (Fin (m : ℕ) × Fin A.nz)).symm z
    (hz.1, (Fintype.equivFin (Fin ((r : ℕ) + (s : ℕ) - 1))).symm hz.2)
  have hB : ∀ x y z,
      convolutionReplicationTarget (K := K) m r s (dx x) (dy y) (dz z) = B.coeff x y z := by
    intro x y z
    change Fin (Fintype.card (Fin (m : ℕ) × Fin A.nx)) at x
    change Fin (Fintype.card (Fin (m : ℕ) × Fin A.ny)) at y
    change Fin (Fintype.card (Fin (m : ℕ) × Fin A.nz)) at z
    change (if (dx x).1 = (dy y).1 ∧ (dy y).1 = (dz z).1 then
      OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r s
        (dx x).2 (dy y).2 (dz z).2 else 0) = _
    change _ = if (dx x).1 = (dy y).1 ∧ (dx x).1 = (dz z).1 then
      OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r s
        (dx x).2 (dy y).2 (dz z).2 else 0
    by_cases hxy : (dx x).1 = (dy y).1
    · simp only [hxy, true_and]
    · simp only [hxy, false_and, ite_false]
  have D := finiteDegeneration (convolutionReplicationRawDegeneration nodes hinj m.property)
    dx dy dz hB
  exact ⟨(r : ℕ) + (s : ℕ) - 2, (r : ℕ) - 1, (s : ℕ) - 1,
    (r : ℕ) + (s : ℕ) - 2, ⟨D⟩⟩

end BlockIdentities.Square
