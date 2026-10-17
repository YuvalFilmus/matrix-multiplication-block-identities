/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Rectangular.Definitions

/-! General characteristic-free three-sector splitting at arbitrary positive lengths.
The original shared first leg and intrinsic middle reversal are retained. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Rectangular.Providers

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open BlockIdentities.Square
open scoped BigOperators

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

private def ofTensorDegeneration {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype X'] [Fintype Y'] [Fintype Z']
    {T : Tensor K X Y Z} {U : Tensor K X' Y' Z'} {k Lx Ly Lz : ℕ}
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    Tensor.PolynomialRestrictionDegeneration
      (TensorSemiring.FiniteTensor.ofTensor T).coeff
      (TensorSemiring.FiniteTensor.ofTensor U).coeff k Lx Ly Lz where
  leftMap := fun x i => L.leftMap ((Fintype.equivFin X').symm x) ((Fintype.equivFin X).symm i)
  middleMap := fun y j => L.middleMap ((Fintype.equivFin Y').symm y) ((Fintype.equivFin Y).symm j)
  rightMap := fun z l => L.rightMap ((Fintype.equivFin Z').symm z) ((Fintype.equivFin Z).symm l)
  left_degree := fun x i => L.left_degree _ _
  middle_degree := fun y j => L.middle_degree _ _
  right_degree := fun z l => L.right_degree _ _
  vanishes := by
    intro x y z j hj
    have hs := sum_reindex_three (fun i l m =>
      L.leftMap ((Fintype.equivFin X').symm x) i *
      L.middleMap ((Fintype.equivFin Y').symm y) l *
      L.rightMap ((Fintype.equivFin Z').symm z) m * Polynomial.C (T i l m))
    exact (congrArg (fun P : Polynomial K => P.coeff j) hs).trans (L.vanishes _ _ _ j hj)
  leading := by
    intro x y z
    have hs := sum_reindex_three (fun i l m =>
      L.leftMap ((Fintype.equivFin X').symm x) i *
      L.middleMap ((Fintype.equivFin Y').symm y) l *
      L.rightMap ((Fintype.equivFin Z').symm z) m * Polynomial.C (T i l m))
    exact (congrArg (fun P : Polynomial K => P.coeff k) hs).trans (L.leading _ _ _)

private abbrev SideY (r s : ℕ) := Fin s ⊕ (Fin (r + s - 1) ⊕ Fin s)
private abbrev SideZ (r s : ℕ) := Fin (r + s - 1) ⊕ (Fin s ⊕ Fin (r + s - 1))

private def embedY (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) : SideY r s → Fin (3 * s + r - 1)
  | .inl j => ⟨j.val, by have := j.isLt; omega⟩
  | .inr (.inl j) => ⟨s + j.val, by have := j.isLt; omega⟩
  | .inr (.inr j) => ⟨2 * s + r - 1 + j.val, by have := j.isLt; omega⟩

private def embedZ (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) : SideZ r s → Fin (r + (3 * s + r - 1) - 1)
  | .inl j => ⟨j.val, by have := j.isLt; omega⟩
  | .inr (.inl j) => ⟨s + r - 1 + j.val, by have := j.isLt; omega⟩
  | .inr (.inr j) => ⟨2 * s + r - 1 + j.val, by have := j.isLt; omega⟩

private def factorY (r s : ℕ) : SideY r s → Polynomial K
  | .inl _ => 1
  | .inr (.inl _) => Polynomial.X
  | .inr (.inr _) => 1

private def factorZ (r s : ℕ) : SideZ r s → Polynomial K
  | .inl _ => Polynomial.X
  | .inr (.inl _) => 1
  | .inr (.inr _) => Polynomial.X

private def rawTripling (r s : ℕ) : Tensor K (Fin r) (SideY r s) (SideZ r s) :=
  fun x y z => match y, z with
  | .inl y, .inl z => OAI.MatrixMultiplication.AuxiliarySeparation.convolution r s x y z
  | .inr (.inl y), .inr (.inl z) =>
      OAI.MatrixMultiplication.AuxiliarySeparation.convolution r s x.rev z y
  | .inr (.inr y), .inr (.inr z) =>
      OAI.MatrixMultiplication.AuxiliarySeparation.convolution r s x y z
  | _, _ => 0

private def leftMap (r s : ℕ) : Fin r → Fin r → Polynomial K :=
  fun x i => if i = x then 1 else 0

private def middleMap (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) : SideY r s → Fin (3 * s + r - 1) → Polynomial K :=
  fun y j => if j = embedY r s hr hs y then factorY r s y else 0

private def rightMap (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    SideZ r s → Fin (r + (3 * s + r - 1) - 1) → Polynomial K :=
  fun z l => if l = embedZ r s hr hs z then factorZ r s z else 0

private theorem restricted_formula (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (x : Fin r) (y : SideY r s) (z : SideZ r s) :
    Tensor.restrict (leftMap r s) (middleMap r s hr hs) (rightMap r s hr hs)
      (fun i j l => Polynomial.C
        (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r (3 * s + r - 1) i j l)) x y z =
    factorY r s y * factorZ r s z * Polynomial.C
      (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K)
        r (3 * s + r - 1) x (embedY r s hr hs y) (embedZ r s hr hs z)) := by
  classical
  simp only [Tensor.restrict, leftMap, middleMap, rightMap, ite_mul, mul_ite,
    one_mul, zero_mul, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

private theorem filtered_vanishes (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (x : Fin r) (y : SideY r s) (z : SideZ r s) :
    (factorY r s y * factorZ r s z * Polynomial.C
      (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K)
        r (3 * s + r - 1) x (embedY r s hr hs y) (embedZ r s hr hs z))).coeff 0 = 0 := by
  rcases y with y | (y | y) <;> rcases z with z | (z | z) <;>
    simp [factorY, factorZ, embedY, embedZ,
      OAI.MatrixMultiplication.AuxiliarySeparation.convolution, ← pow_two,
      Polynomial.coeff_X_pow] <;>
    split_ifs <;> have hx := x.isLt <;> have hy := y.isLt <;> have hz := z.isLt <;>
    simp_all <;> omega

private theorem filtered_leading (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (x : Fin r) (y : SideY r s) (z : SideZ r s) :
    (factorY r s y * factorZ r s z * Polynomial.C
      (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K)
        r (3 * s + r - 1) x (embedY r s hr hs y) (embedZ r s hr hs z))).coeff 1 =
      rawTripling r s x y z := by
  rcases y with y | (y | y) <;> rcases z with z | (z | z) <;>
    simp [factorY, factorZ, embedY, embedZ, rawTripling,
      OAI.MatrixMultiplication.AuxiliarySeparation.convolution, ← pow_two,
      Polynomial.coeff_X_pow, Fin.val_rev] <;>
    split_ifs <;> have hx := x.isLt <;> have hy := y.isLt <;> have hz := z.isLt <;>
    simp_all <;> omega

private def rawDegeneration (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    Tensor.PolynomialRestrictionDegeneration
      (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r (3 * s + r - 1))
      (rawTripling r s) 1 0 1 1 where
  leftMap := leftMap r s
  middleMap := middleMap r s hr hs
  rightMap := rightMap r s hr hs
  left_degree := by
    intro x i
    simp only [leftMap]
    split_ifs <;> simp
  middle_degree := by
    intro y j
    rcases y with y | (y | y) <;> simp only [middleMap, factorY] <;> split_ifs <;> simp
  right_degree := by
    intro z l
    rcases z with z | (z | z) <;> simp only [rightMap, factorZ] <;> split_ifs <;> simp
  vanishes := by
    intro x y z j hj
    have hj0 : j = 0 := by omega
    subst j
    rw [restricted_formula]
    exact filtered_vanishes r s hr hs x y z
  leading := by
    intro x y z
    rw [restricted_formula]
    exact filtered_leading r s hr hs x y z

/-- Actual general three-sector degeneration, valid in every characteristic. -/
theorem convolution_general_tripling {K : Type*} [Field K] (r s : ℕ+) :
    Degenerates
      (Square.convolution (K := K) r ⟨3 * (s : ℕ) + (r : ℕ) - 1, by
        show 0 < (3 * (s : ℕ) + (r : ℕ) - 1 : ℕ)
        have hr : 0 < (r : ℕ) := r.property
        have hs : 0 < (s : ℕ) := s.property
        omega⟩)
      (generalTriplingSplit r s) := by
  have hr : 1 ≤ (r : ℕ) := r.property
  have hs : 1 ≤ (s : ℕ) := s.property
  have htarget : TensorSemiring.FiniteTensor.ofTensor
      (rawTripling (K := K) (r : ℕ) (s : ℕ)) = generalTriplingSplit r s := by
    unfold generalTriplingSplit sharedFirstThree
    congr 1
    funext x y z
    rcases y with y | (y | y) <;> rcases z with z | (z | z) <;> rfl
  have H : Degenerates
      (TensorSemiring.FiniteTensor.ofTensor
        (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K)
          (r : ℕ) (3 * (s : ℕ) + (r : ℕ) - 1)))
      (TensorSemiring.FiniteTensor.ofTensor (rawTripling (K := K) (r : ℕ) (s : ℕ))) :=
    ⟨1, 0, 1, 1, ⟨ofTensorDegeneration
      (rawDegeneration (K := K) (r : ℕ) (s : ℕ) hr hs)⟩⟩
  rw [htarget] at H
  exact H

end BlockIdentities.Rectangular.Providers
