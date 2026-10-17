/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.DegenerationProduct

/-! Finite leading-degree alignment for blockwise polynomial degenerations. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open scoped BigOperators
variable {K : Type*} [Field K]

/-- Literal dependent direct sum. Formula adapted from Navot's
`Tensor.dependentDirectSum`; no separation theorem is imported. -/
def dependentTensorSum {ι : Type*} [DecidableEq ι] {U V W : ι → Type*}
    (S : ∀ i, Tensor K (U i) (V i) (W i)) :
    Tensor K (Σ i, U i) (Σ i, V i) (Σ i, W i) :=
  fun x y z => if hxy : y.1 = x.1 then
    if hxz : z.1 = x.1 then S x.1 x.2 (hxy ▸ y.2) (hxz ▸ z.2) else 0 else 0

@[simp] theorem dependentTensorSum_matching {ι : Type*} [DecidableEq ι]
    {U V W : ι → Type*} (S : ∀ i, Tensor K (U i) (V i) (W i))
    (i : ι) (u : U i) (v : V i) (w : W i) :
    dependentTensorSum S ⟨i,u⟩ ⟨i,v⟩ ⟨i,w⟩ = S i u v w := by
  simp [dependentTensorSum]

end BlockIdentities.Square

namespace OAI.MatrixMultiplication.Foundation.Tensor.PolynomialRestrictionDegeneration
open OAI.MatrixMultiplication.Foundation
open scoped BigOperators
variable {K X Y Z U V W : Type*} [Field K]
variable [Fintype X] [Fintype Y] [Fintype Z]
variable {T : Tensor K X Y Z} {S : Tensor K U V W} {k Lx Ly Lz : ℕ}

/-- Multiplying the first local map by a parameter monomial shifts the entire
base polynomial, including all its coefficients, by the same degree. -/
theorem shiftLeft_base (D : PolynomialRestrictionDegeneration T S k Lx Ly Lz)
    (e : ℕ) (u : U) (v : V) (w : W) :
    Tensor.restrict (fun u x => Polynomial.X ^ e * D.leftMap u x)
      D.middleMap D.rightMap (fun x y z => Polynomial.C (T x y z)) u v w =
      Polynomial.X ^ e * D.basePolynomial u v w := by
  simp only [Tensor.restrict, basePolynomial, Finset.mul_sum, mul_assoc]

/-- Actual polynomial maps with an arbitrary additional leading delay.
No characteristic or nonzero-source assumption is required. -/
def shiftLeft (D : PolynomialRestrictionDegeneration T S k Lx Ly Lz) (e : ℕ) :
    PolynomialRestrictionDegeneration T S (e + k) (e + Lx) Ly Lz where
  leftMap := fun u x => Polynomial.X ^ e * D.leftMap u x
  middleMap := D.middleMap
  rightMap := D.rightMap
  left_degree := by
    intro u x
    apply Polynomial.degree_le_of_natDegree_le
    have hd := Polynomial.natDegree_le_of_degree_le (D.left_degree u x)
    exact Polynomial.natDegree_mul_le.trans
      (by simpa using Nat.add_le_add (le_refl e) hd)
  middle_degree := D.middle_degree
  right_degree := D.right_degree
  vanishes := by
    intro u v w j hj
    rw [shiftLeft_base, Polynomial.coeff_X_pow_mul']
    split_ifs with he
    · exact D.vanishes u v w (j - e) (by omega)
    · rfl
  leading := by
    intro u v w
    rw [shiftLeft_base, Polynomial.coeff_X_pow_mul']
    simpa [basePolynomial] using D.leading u v w

/-- Alignment to any common upper bound on the leading index. -/
def alignLeading (D : PolynomialRestrictionDegeneration T S k Lx Ly Lz)
    (q : ℕ) (hk : k ≤ q) :
    PolynomialRestrictionDegeneration T S q (q - k + Lx) Ly Lz := by
  have he : q - k + k = q := Nat.sub_add_cancel hk
  simpa only [he] using D.shiftLeft (q - k)

end OAI.MatrixMultiplication.Foundation.Tensor.PolynomialRestrictionDegeneration
