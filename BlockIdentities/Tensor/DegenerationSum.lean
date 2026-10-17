/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.DirectSumDegeneration
public import BlockIdentities.Tensor.ClassDegeneration
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.DirectSum

/-! Actual block-diagonal polynomial maps and finite additive closure. -/
@[expose] public section
noncomputable section
namespace OAI.MatrixMultiplication.Foundation.Tensor.PolynomialRestrictionDegeneration
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
variable {K X Y Z U V W X' Y' Z' U' V' W' : Type*} [Field K]
variable [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
variable {T : Tensor K X Y Z} {S : Tensor K U V W}
variable {T' : Tensor K X' Y' Z'} {S' : Tensor K U' V' W'}
variable {k d e Lx Ly Lz Mx My Mz : ℕ}

private theorem sum_base
    (D : PolynomialRestrictionDegeneration T T' k Lx Ly Lz)
    (E : PolynomialRestrictionDegeneration S S' k Mx My Mz) :
    Tensor.restrict (sumRestriction D.leftMap E.leftMap)
      (sumRestriction D.middleMap E.middleMap) (sumRestriction D.rightMap E.rightMap)
      (fun x y z => Polynomial.C (sumTensor T S x y z)) =
      sumTensor D.basePolynomial E.basePolynomial := by
  have hc : (fun x y z => Polynomial.C (sumTensor T S x y z)) =
      sumTensor (fun x y z => Polynomial.C (T x y z))
        (fun x y z => Polynomial.C (S x y z)) := by
    funext x y z
    cases x <;> cases y <;> cases z <;> simp [sumTensor]
  rw [hc, sumTensor_restrict]
  rfl

/-- Block-diagonal maps at a common leading coefficient. -/
def sumSameLeading (D : PolynomialRestrictionDegeneration T T' k Lx Ly Lz)
    (E : PolynomialRestrictionDegeneration S S' k Mx My Mz) :
    PolynomialRestrictionDegeneration (sumTensor T S) (sumTensor T' S') k
      (max Lx Mx) (max Ly My) (max Lz Mz) where
  leftMap := sumRestriction D.leftMap E.leftMap
  middleMap := sumRestriction D.middleMap E.middleMap
  rightMap := sumRestriction D.rightMap E.rightMap
  left_degree := by
    intro x i
    cases x <;> cases i
    · exact (D.left_degree _ _).trans (WithBot.coe_le_coe.mpr (le_max_left _ _))
    · simp [sumRestriction]
    · simp [sumRestriction]
    · exact (E.left_degree _ _).trans (WithBot.coe_le_coe.mpr (le_max_right _ _))
  middle_degree := by
    intro x i
    cases x <;> cases i
    · exact (D.middle_degree _ _).trans (WithBot.coe_le_coe.mpr (le_max_left _ _))
    · simp [sumRestriction]
    · simp [sumRestriction]
    · exact (E.middle_degree _ _).trans (WithBot.coe_le_coe.mpr (le_max_right _ _))
  right_degree := by
    intro x i
    cases x <;> cases i
    · exact (D.right_degree _ _).trans (WithBot.coe_le_coe.mpr (le_max_left _ _))
    · simp [sumRestriction]
    · simp [sumRestriction]
    · exact (E.right_degree _ _).trans (WithBot.coe_le_coe.mpr (le_max_right _ _))
  vanishes := by
    intro x y z j hj
    rw [sum_base]
    cases x <;> cases y <;> cases z <;>
      simp only [sumTensor, Polynomial.coeff_zero]
    · exact D.vanishes _ _ _ j hj
    · exact E.vanishes _ _ _ j hj
  leading := by
    intro x y z
    rw [sum_base]
    cases x <;> cases y <;> cases z <;>
      simp only [sumTensor, Polynomial.coeff_zero]
    · exact D.leading _ _ _
    · exact E.leading _ _ _

/-- Arbitrary leading degrees are aligned by genuine first-leg monomial maps. -/
def sum (D : PolynomialRestrictionDegeneration T T' d Lx Ly Lz)
    (E : PolynomialRestrictionDegeneration S S' e Mx My Mz) :
    PolynomialRestrictionDegeneration (sumTensor T S) (sumTensor T' S') (max d e)
      (max (max d e - d + Lx) (max d e - e + Mx)) (max Ly My) (max Lz Mz) :=
  (D.alignLeading (max d e) (le_max_left _ _)).sumSameLeading
    (E.alignLeading (max d e) (le_max_right _ _))
end OAI.MatrixMultiplication.Foundation.Tensor.PolynomialRestrictionDegeneration

namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K : Type*} [Field K]

/-- Genuine degeneration is closed under adding independent full blocks. -/
theorem ClassDegenerates.add {a b c d : TensorClass K}
    (h : ClassDegenerates a b) (g : ClassDegenerates c d) :
    ClassDegenerates (a + c) (b + d) := by
  obtain ⟨A, B, hA, hB, k, Lx, Ly, Lz, ⟨D⟩⟩ := h
  obtain ⟨C, E, hC, hE, q, Mx, My, Mz, ⟨F⟩⟩ := g
  refine ⟨FiniteTensor.ofTensor (sumTensor A.coeff C.coeff),
    FiniteTensor.ofTensor (sumTensor B.coeff E.coeff), ?_, ?_, ?_⟩
  · change classOf (sumTensor A.coeff C.coeff) = a + c
    rw [classOf_sum, classOf_coeff, classOf_coeff, hA, hC]
  · change classOf (sumTensor B.coeff E.coeff) = b + d
    rw [classOf_sum, classOf_coeff, classOf_coeff, hB, hE]
  · exact ⟨_, _, _, _, ⟨(D.sum F).ofTensor⟩⟩

/-- Finite addition consumes independently supplied finite block maps. -/
theorem ClassDegenerates.sum {ι : Type*} (s : Finset ι)
    (a b : ι → TensorClass K) (h : ∀ i ∈ s, ClassDegenerates (a i) (b i)) :
    ClassDegenerates (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ClassDegenerates.refl (0 : TensorClass K)
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (h i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
end BlockIdentities.Square
