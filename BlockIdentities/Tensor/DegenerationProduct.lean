/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.DegenerationComposition

/-! Products and canonical finite-coordinate presentations of polynomial maps. -/

@[expose] public section
noncomputable section

namespace OAI.MatrixMultiplication.Foundation.Tensor.PolynomialRestrictionDegeneration

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
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

def ofTensor {X Y Z X' Y' Z' : Type*}
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

variable {X Y Z U V W X' Y' Z' U' V' W' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]
variable {T : Tensor K X Y Z} {S : Tensor K U V W}
variable {T' : Tensor K X' Y' Z'} {S' : Tensor K U' V' W'}
variable {d e Lx Ly Lz Mx My Mz : ℕ}

private def quotientBase (L : Tensor.PolynomialRestrictionDegeneration T T' d Lx Ly Lz) :
    Tensor (Polynomial K) X' Y' Z' :=
  fun x y z => Classical.choose (Polynomial.X_pow_dvd_iff.mpr (L.vanishes x y z))

private theorem quotientBase_spec (L : Tensor.PolynomialRestrictionDegeneration T T' d Lx Ly Lz)
    (x : X') (y : Y') (z : Z') :
    L.basePolynomial x y z = Polynomial.X ^ d * quotientBase L x y z :=
  Classical.choose_spec (Polynomial.X_pow_dvd_iff.mpr (L.vanishes x y z))

private theorem quotientBase_constant (L : Tensor.PolynomialRestrictionDegeneration T T' d Lx Ly Lz)
    (x : X') (y : Y') (z : Z') : (quotientBase L x y z).coeff 0 = T' x y z := by
  have h := L.leading x y z
  change (L.basePolynomial x y z).coeff d = T' x y z at h
  rw [quotientBase_spec] at h
  simpa only [Polynomial.coeff_X_pow_mul', le_rfl, ite_true, Nat.sub_self] using h

def productLeft
    (L : Tensor.PolynomialRestrictionDegeneration T T' d Lx Ly Lz)
    (M : Tensor.PolynomialRestrictionDegeneration S S' e Mx My Mz) :
    X' × U' → X × U → Polynomial K := fun x i => L.leftMap x.1 i.1 * M.leftMap x.2 i.2

def productMiddle
    (L : Tensor.PolynomialRestrictionDegeneration T T' d Lx Ly Lz)
    (M : Tensor.PolynomialRestrictionDegeneration S S' e Mx My Mz) :
    Y' × V' → Y × V → Polynomial K := fun y j => L.middleMap y.1 j.1 * M.middleMap y.2 j.2

def productRight
    (L : Tensor.PolynomialRestrictionDegeneration T T' d Lx Ly Lz)
    (M : Tensor.PolynomialRestrictionDegeneration S S' e Mx My Mz) :
    Z' × W' → Z × W → Polynomial K := fun z k => L.rightMap z.1 k.1 * M.rightMap z.2 k.2

private theorem product_base
    (L : Tensor.PolynomialRestrictionDegeneration T T' d Lx Ly Lz)
    (M : Tensor.PolynomialRestrictionDegeneration S S' e Mx My Mz)
    (x : X' × U') (y : Y' × V') (z : Z' × W') :
    Tensor.restrict (productLeft L M) (productMiddle L M) (productRight L M)
      (fun i j k => Polynomial.C (Tensor.product T S i j k)) x y z =
      L.basePolynomial x.1 y.1 z.1 * M.basePolynomial x.2 y.2 z.2 := by
  have hc : (fun i j k => Polynomial.C (Tensor.product T S i j k)) =
      Tensor.product (fun i j k => Polynomial.C (T i j k))
        (fun i j k => Polynomial.C (S i j k)) := by
    funext i j k
    simp only [Tensor.product, map_mul]
  unfold productLeft productMiddle productRight
  rw [hc, Tensor.restrict_product]
  rfl

private theorem product_factor
    (L : Tensor.PolynomialRestrictionDegeneration T T' d Lx Ly Lz)
    (M : Tensor.PolynomialRestrictionDegeneration S S' e Mx My Mz)
    (x : X' × U') (y : Y' × V') (z : Z' × W') :
    Tensor.restrict (productLeft L M) (productMiddle L M) (productRight L M)
      (fun i j k => Polynomial.C (Tensor.product T S i j k)) x y z =
      Polynomial.X ^ (d + e) *
        (quotientBase L x.1 y.1 z.1 * quotientBase M x.2 y.2 z.2) := by
  rw [product_base, quotientBase_spec, quotientBase_spec, pow_add]
  ring

/-- Tensor products of the three polynomial maps add their leading orders. -/
def product
    (L : Tensor.PolynomialRestrictionDegeneration T T' d Lx Ly Lz)
    (M : Tensor.PolynomialRestrictionDegeneration S S' e Mx My Mz) :
    Tensor.PolynomialRestrictionDegeneration (Tensor.product T S) (Tensor.product T' S')
      (d + e) (Lx + Mx) (Ly + My) (Lz + Mz) where
  leftMap := productLeft L M
  middleMap := productMiddle L M
  rightMap := productRight L M
  left_degree := by
    intro x i
    exact Polynomial.degree_le_of_natDegree_le
      (Polynomial.natDegree_mul_le_of_le
        (Polynomial.natDegree_le_of_degree_le (L.left_degree x.1 i.1))
        (Polynomial.natDegree_le_of_degree_le (M.left_degree x.2 i.2)))
  middle_degree := by
    intro y j
    exact Polynomial.degree_le_of_natDegree_le
      (Polynomial.natDegree_mul_le_of_le
        (Polynomial.natDegree_le_of_degree_le (L.middle_degree y.1 j.1))
        (Polynomial.natDegree_le_of_degree_le (M.middle_degree y.2 j.2)))
  right_degree := by
    intro z k
    exact Polynomial.degree_le_of_natDegree_le
      (Polynomial.natDegree_mul_le_of_le
        (Polynomial.natDegree_le_of_degree_le (L.right_degree z.1 k.1))
        (Polynomial.natDegree_le_of_degree_le (M.right_degree z.2 k.2)))
  vanishes := by
    intro x y z j hj
    rw [product_factor, Polynomial.coeff_X_pow_mul']
    simp only [Nat.not_le_of_lt hj, ite_false]
  leading := by
    intro x y z
    rw [product_factor, Polynomial.coeff_X_pow_mul']
    simp only [le_rfl, ite_true, Nat.sub_self, Polynomial.mul_coeff_zero,
      quotientBase_constant, Tensor.product]

end OAI.MatrixMultiplication.Foundation.Tensor.PolynomialRestrictionDegeneration

namespace BlockIdentities.Square

variable {K : Type*} [Field K]

/-- Tensoring exact degenerations is valid in every characteristic. -/
theorem Degenerates.product {A B C D : FiniteTensor K}
    (hAB : Degenerates A B) (hCD : Degenerates C D) :
    Degenerates (product A C) (product B D) := by
  obtain ⟨d, Lx, Ly, Lz, ⟨L⟩⟩ := hAB
  obtain ⟨e, Mx, My, Mz, ⟨M⟩⟩ := hCD
  exact ⟨d + e, Lx + Mx, Ly + My, Lz + Mz, ⟨(L.product M).ofTensor⟩⟩

end BlockIdentities.Square
