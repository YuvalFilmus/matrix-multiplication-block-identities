/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.ConvolutionSplittings

/-! Characteristic-free tripling with the original shared first coordinate.
The middle first-coordinate reversal is retained in the target shared sum. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Providers

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

private abbrev SideY (r : ℕ) := Fin r ⊕ (Fin (r + r - 1) ⊕ Fin r)
private abbrev SideZ (r : ℕ) := Fin (r + r - 1) ⊕ (Fin r ⊕ Fin (r + r - 1))

private def embedY (r : ℕ) (hr : 2 ≤ r) : SideY r → Fin (4 * r - 1)
  | .inl j => ⟨j.val, by have := j.isLt; omega⟩
  | .inr (.inl j) => ⟨r + j.val, by have := j.isLt; omega⟩
  | .inr (.inr j) => ⟨3 * r - 1 + j.val, by have := j.isLt; omega⟩

private def embedZ (r : ℕ) (hr : 2 ≤ r) : SideZ r → Fin (r + (4 * r - 1) - 1)
  | .inl j => ⟨j.val, by have := j.isLt; omega⟩
  | .inr (.inl j) => ⟨2 * r - 1 + j.val, by have := j.isLt; omega⟩
  | .inr (.inr j) => ⟨3 * r - 1 + j.val, by have := j.isLt; omega⟩

private def factorY (r : ℕ) : SideY r → Polynomial K
  | .inl _ => 1
  | .inr (.inl _) => Polynomial.X
  | .inr (.inr _) => 1

private def factorZ (r : ℕ) : SideZ r → Polynomial K
  | .inl _ => Polynomial.X
  | .inr (.inl _) => 1
  | .inr (.inr _) => Polynomial.X

private def rawTripling (r : ℕ) : Tensor K (Fin r) (SideY r) (SideZ r) :=
  fun x y z => match y, z with
  | .inl y, .inl z => OAI.MatrixMultiplication.AuxiliarySeparation.convolution r r x y z
  | .inr (.inl y), .inr (.inl z) =>
      OAI.MatrixMultiplication.AuxiliarySeparation.convolution r r x.rev z y
  | .inr (.inr y), .inr (.inr z) =>
      OAI.MatrixMultiplication.AuxiliarySeparation.convolution r r x y z
  | _, _ => 0

private def leftMap (r : ℕ) : Fin r → Fin r → Polynomial K :=
  fun x i => if i = x then 1 else 0

private def middleMap (r : ℕ) (hr : 2 ≤ r) : SideY r → Fin (4 * r - 1) → Polynomial K :=
  fun y j => if j = embedY r hr y then factorY r y else 0

private def rightMap (r : ℕ) (hr : 2 ≤ r) :
    SideZ r → Fin (r + (4 * r - 1) - 1) → Polynomial K :=
  fun z l => if l = embedZ r hr z then factorZ r z else 0

private theorem restricted_formula (r : ℕ) (hr : 2 ≤ r)
    (x : Fin r) (y : SideY r) (z : SideZ r) :
    Tensor.restrict (leftMap r) (middleMap r hr) (rightMap r hr)
      (fun i j l => Polynomial.C
        (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r (4 * r - 1) i j l)) x y z =
    factorY r y * factorZ r z * Polynomial.C
      (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K)
        r (4 * r - 1) x (embedY r hr y) (embedZ r hr z)) := by
  classical
  simp only [Tensor.restrict, leftMap, middleMap, rightMap, ite_mul, mul_ite,
    one_mul, zero_mul, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

private theorem filtered_vanishes (r : ℕ) (hr : 2 ≤ r)
    (x : Fin r) (y : SideY r) (z : SideZ r) :
    (factorY r y * factorZ r z * Polynomial.C
      (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K)
        r (4 * r - 1) x (embedY r hr y) (embedZ r hr z))).coeff 0 = 0 := by
  rcases y with y | (y | y) <;> rcases z with z | (z | z) <;>
    simp [factorY, factorZ, embedY, embedZ,
      OAI.MatrixMultiplication.AuxiliarySeparation.convolution, ← pow_two,
      Polynomial.coeff_X_pow] <;>
    split_ifs <;> have hx := x.isLt <;> have hy := y.isLt <;> have hz := z.isLt <;>
    simp_all <;> omega

private theorem filtered_leading (r : ℕ) (hr : 2 ≤ r)
    (x : Fin r) (y : SideY r) (z : SideZ r) :
    (factorY r y * factorZ r z * Polynomial.C
      (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K)
        r (4 * r - 1) x (embedY r hr y) (embedZ r hr z))).coeff 1 =
      rawTripling r x y z := by
  rcases y with y | (y | y) <;> rcases z with z | (z | z) <;>
    simp [factorY, factorZ, embedY, embedZ, rawTripling,
      OAI.MatrixMultiplication.AuxiliarySeparation.convolution, ← pow_two,
      Polynomial.coeff_X_pow, Fin.val_rev] <;>
    split_ifs <;> have hx := x.isLt <;> have hy := y.isLt <;> have hz := z.isLt <;>
    simp_all <;> omega

private def rawDegeneration (r : ℕ) (hr : 2 ≤ r) :
    Tensor.PolynomialRestrictionDegeneration
      (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r (4 * r - 1))
      (rawTripling r) 1 0 1 1 where
  leftMap := leftMap r
  middleMap := middleMap r hr
  rightMap := rightMap r hr
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
    exact filtered_vanishes r hr x y z
  leading := by
    intro x y z
    rw [restricted_formula]
    exact filtered_leading r hr x y z

/-- The actual raw tripling degeneration, preserving the common first leg. -/
theorem convolution_tripling_degeneration {K : Type*} [Field K] (r : ℕ+)
    (hr : 2 ≤ (r : ℕ)) :
    Degenerates
      (Square.convolution (K := K) r ⟨4 * (r : ℕ) - 1, by omega⟩)
      (triplingSplit r hr) := by
  have htarget : TensorSemiring.FiniteTensor.ofTensor (rawTripling (K := K) (r : ℕ)) =
      triplingSplit r hr := by
    unfold triplingSplit sharedFirstThree
    congr 1
    funext x y z
    rcases y with y | (y | y) <;> rcases z with z | (z | z) <;> rfl
  have H : Degenerates
      (TensorSemiring.FiniteTensor.ofTensor
        (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) (r : ℕ) (4 * (r : ℕ) - 1)))
      (TensorSemiring.FiniteTensor.ofTensor (rawTripling (K := K) (r : ℕ))) :=
    ⟨1, 0, 1, 1, ⟨ofTensorDegeneration (rawDegeneration (K := K) (r : ℕ) hr)⟩⟩
  rw [htarget] at H
  exact H

end BlockIdentities.Providers
