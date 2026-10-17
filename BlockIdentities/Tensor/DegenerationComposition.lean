/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.PolynomialMaps
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition

/-! Compose exact polynomial local maps with a strict parameter-scale separation. -/

@[expose] public section
noncomputable section

namespace OAI.MatrixMultiplication.Foundation.Tensor.PolynomialRestrictionDegeneration

open OAI.MatrixMultiplication.Foundation
open scoped BigOperators

variable {K X Y Z U V W A B C : Type*} [Field K]
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]
variable {T : Tensor K X Y Z} {S : Tensor K U V W} {Q : Tensor K A B C}
variable {d k Mx My Mz Lx Ly Lz : ℕ}

private def divided (D : Tensor.PolynomialRestrictionDegeneration T S d Mx My Mz) :
    Tensor (Polynomial K) U V W :=
  fun u v w => Classical.choose (Polynomial.X_pow_dvd_iff.mpr (D.vanishes u v w))

private theorem base_eq (D : Tensor.PolynomialRestrictionDegeneration T S d Mx My Mz)
    (u : U) (v : V) (w : W) :
    D.basePolynomial u v w = Polynomial.X ^ d * divided D u v w :=
  Classical.choose_spec (Polynomial.X_pow_dvd_iff.mpr (D.vanishes u v w))

private theorem divided_zero (D : Tensor.PolynomialRestrictionDegeneration T S d Mx My Mz)
    (u : U) (v : V) (w : W) : (divided D u v w).coeff 0 = S u v w := by
  have h := D.leading u v w
  change (D.basePolynomial u v w).coeff d = S u v w at h
  rw [base_eq] at h
  simpa only [Polynomial.coeff_X_pow_mul', le_rfl, ite_true, Nat.sub_self] using h

private theorem expand_restrict (n : ℕ)
    (E : U → X → Polynomial K) (F : V → Y → Polynomial K)
    (G : W → Z → Polynomial K) (P : Tensor (Polynomial K) X Y Z) :
    (fun u v w => Polynomial.expand K n (Tensor.restrict E F G P u v w)) =
      Tensor.restrict (fun u x => Polynomial.expand K n (E u x))
        (fun v y => Polynomial.expand K n (F v y))
        (fun w z => Polynomial.expand K n (G w z))
        (fun x y z => Polynomial.expand K n (P x y z)) := by
  funext u v w
  simp only [Tensor.restrict, map_sum, map_mul]

def combinedLeft
    (D : Tensor.PolynomialRestrictionDegeneration T S d Mx My Mz)
    (L : Tensor.PolynomialRestrictionDegeneration S Q k Lx Ly Lz) :
    A → X → Polynomial K :=
  Tensor.composeRestrictionMatrix L.leftMap (fun u x => Polynomial.expand K (k + 1) (D.leftMap u x))

def combinedMiddle
    (D : Tensor.PolynomialRestrictionDegeneration T S d Mx My Mz)
    (L : Tensor.PolynomialRestrictionDegeneration S Q k Lx Ly Lz) :
    B → Y → Polynomial K :=
  Tensor.composeRestrictionMatrix L.middleMap (fun v y => Polynomial.expand K (k + 1) (D.middleMap v y))

def combinedRight
    (D : Tensor.PolynomialRestrictionDegeneration T S d Mx My Mz)
    (L : Tensor.PolynomialRestrictionDegeneration S Q k Lx Ly Lz) :
    C → Z → Polynomial K :=
  Tensor.composeRestrictionMatrix L.rightMap (fun w z => Polynomial.expand K (k + 1) (D.rightMap w z))

private def normalizedProduct
    (D : Tensor.PolynomialRestrictionDegeneration T S d Mx My Mz)
    (L : Tensor.PolynomialRestrictionDegeneration S Q k Lx Ly Lz) :
    Tensor (Polynomial K) A B C :=
  Tensor.restrict L.leftMap L.middleMap L.rightMap
    (fun u v w => Polynomial.expand K (k + 1) (divided D u v w))

private theorem combined_eq
    (D : Tensor.PolynomialRestrictionDegeneration T S d Mx My Mz)
    (L : Tensor.PolynomialRestrictionDegeneration S Q k Lx Ly Lz) :
    Tensor.restrict (combinedLeft D L) (combinedMiddle D L) (combinedRight D L)
      (fun x y z => Polynomial.C (T x y z)) =
      fun a b c => Polynomial.X ^ (d * (k + 1)) * normalizedProduct D L a b c := by
  have he := expand_restrict (k + 1) D.leftMap D.middleMap D.rightMap
    (fun x y z => Polynomial.C (T x y z))
  simp only [Polynomial.expand_C] at he
  have hpoint : (fun u v w => Polynomial.expand K (k + 1) (D.basePolynomial u v w)) =
      fun u v w => Polynomial.X ^ (d * (k + 1)) *
        Polynomial.expand K (k + 1) (divided D u v w) := by
    funext u v w
    rw [base_eq, map_mul, map_pow, Polynomial.expand_X]
    simp only [← pow_mul, Nat.mul_comm]
  unfold combinedLeft combinedMiddle combinedRight
  rw [← Tensor.restrict_restrict, ← he]
  change Tensor.restrict L.leftMap L.middleMap L.rightMap
    (fun u v w => Polynomial.expand K (k + 1) (D.basePolynomial u v w)) = _
  rw [hpoint, Tensor.restrict_scalar_mul]
  rfl

private theorem normalizedProduct_coeff
    (D : Tensor.PolynomialRestrictionDegeneration T S d Mx My Mz)
    (L : Tensor.PolynomialRestrictionDegeneration S Q k Lx Ly Lz)
    (j : ℕ) (hj : j ≤ k) (a : A) (b : B) (c : C) :
    (normalizedProduct D L a b c).coeff j = (L.basePolynomial a b c).coeff j := by
  simp only [normalizedProduct, basePolynomial, Tensor.restrict, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  exact Tensor.coeff_mul_expand_eq_constant
    (L.leftMap a u * L.middleMap b v * L.rightMap c w)
    (divided D u v w) (S u v w) (divided_zero D u v w) k j hj

theorem degree_composed_matrix {I J H : Type*} [Fintype J]
    (E : I → J → Polynomial K) (F : J → H → Polynomial K)
    (e f n : ℕ) (hE : ∀ i j, (E i j).degree ≤ e)
    (hF : ∀ j h, (F j h).degree ≤ f) (i : I) (h : H) :
    (Tensor.composeRestrictionMatrix E
      (fun j h => Polynomial.expand K n (F j h)) i h).degree ≤ e + f * n := by
  apply Polynomial.degree_le_of_natDegree_le
  unfold Tensor.composeRestrictionMatrix
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  apply Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_le_of_degree_le (hE i j))
  rw [Polynomial.natDegree_expand]
  exact Nat.mul_le_mul_right n (Polynomial.natDegree_le_of_degree_le (hF j h))

/-- Substitute the inner parameter by t^(k+1), then compose the three local maps.
The strict scale separation preserves the outer leading coefficient. -/
def trans
    (D : Tensor.PolynomialRestrictionDegeneration T S d Mx My Mz)
    (L : Tensor.PolynomialRestrictionDegeneration S Q k Lx Ly Lz) :
    Tensor.PolynomialRestrictionDegeneration T Q (d * (k + 1) + k)
      (Lx + Mx * (k + 1)) (Ly + My * (k + 1)) (Lz + Mz * (k + 1)) where
  leftMap := combinedLeft D L
  middleMap := combinedMiddle D L
  rightMap := combinedRight D L
  left_degree := degree_composed_matrix L.leftMap D.leftMap Lx Mx (k + 1)
    L.left_degree D.left_degree
  middle_degree := degree_composed_matrix L.middleMap D.middleMap Ly My (k + 1)
    L.middle_degree D.middle_degree
  right_degree := degree_composed_matrix L.rightMap D.rightMap Lz Mz (k + 1)
    L.right_degree D.right_degree
  vanishes := by
    intro a b c j hj
    rw [combined_eq, Polynomial.coeff_X_pow_mul']
    split_ifs with hdj
    · have hjk : j - d * (k + 1) < k := by omega
      rw [normalizedProduct_coeff D L _ (Nat.le_of_lt hjk)]
      exact L.vanishes a b c _ hjk
    · rfl
  leading := by
    intro a b c
    rw [combined_eq, Polynomial.coeff_X_pow_mul']
    simp only [Nat.le_add_right, ite_true, Nat.add_sub_cancel_left]
    rw [normalizedProduct_coeff D L k le_rfl]
    exact L.leading a b c

end OAI.MatrixMultiplication.Foundation.Tensor.PolynomialRestrictionDegeneration

namespace BlockIdentities.Square

variable {K : Type*} [Field K]

/-- Exact polynomial degeneration is transitive over every field. -/
theorem Degenerates.trans {A B C : FiniteTensor K}
    (hAB : Degenerates A B) (hBC : Degenerates B C) : Degenerates A C := by
  obtain ⟨d, Mx, My, Mz, ⟨D⟩⟩ := hAB
  obtain ⟨k, Lx, Ly, Lz, ⟨L⟩⟩ := hBC
  exact ⟨d * (k + 1) + k, Lx + Mx * (k + 1), Ly + My * (k + 1),
    Lz + Mz * (k + 1), ⟨D.trans L⟩⟩

end BlockIdentities.Square
