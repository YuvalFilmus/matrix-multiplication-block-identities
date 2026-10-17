/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ConvolutionReplicationMaps
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Basic

/-! The finite coefficient contraction behind polynomial convolution maps. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace BlockIdentities.Square
open Polynomial
open OAI.MatrixMultiplication.AuxiliarySeparation
variable {K : Type*} [Field K]

private theorem polynomial_fin_expansion {A : ℕ} (f : K[X]) (hf : f.degree < A) :
    f = ∑ i : Fin A, f.coeff i.val • (X : K[X]) ^ i.val := by
  simpa only [smul_X_eq_monomial, sum_monomial_eq] using
    (f.sum_fin (fun i t => monomial i t) (fun _ => monomial_zero_right _) hf).symm

/-- Every low-degree product is the literal finite convolution of its
coefficient vectors, before any choice of output coordinates. -/
theorem convolutionReplication_product_expansion {A B : ℕ}
    (f g : K[X]) (hf : f.degree < A) (hg : g.degree < B) :
    f * g = ∑ i : Fin A, ∑ j : Fin B,
      (f.coeff i.val * g.coeff j.val) • (X : K[X]) ^ (i.val + j.val) := by
  calc
    f * g = (∑ i : Fin A, f.coeff i.val • (X : K[X]) ^ i.val) *
        (∑ j : Fin B, g.coeff j.val • (X : K[X]) ^ j.val) :=
      congrArg₂ (fun u v : K[X] => u * v)
        (polynomial_fin_expansion f hf) (polynomial_fin_expansion g hg)
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add]

/-- Contracting the actual convolution coefficient tensor with any linear
output functional computes that functional on the polynomial product. -/
theorem convolutionReplication_contraction {A B : ℕ}
    (f g : K[X]) (hf : f.degree < A) (hg : g.degree < B) (ℓ : K[X] →ₗ[K] K) :
    (∑ i : Fin A, ∑ j : Fin B, ∑ k : Fin (A + B - 1),
      f.coeff i.val * g.coeff j.val * ℓ (X ^ k.val) *
        convolution (K := K) A B i j k) = ℓ (f * g) := by
  classical
  rw [convolutionReplication_product_expansion f g hf hg, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single (convolutionOutput i j)]
  · rw [convolution_at_output, mul_one]
    rfl
  · intro k _ hk
    have hne : i.val + j.val ≠ k.val := by
      intro he
      apply hk
      exact Fin.ext he.symm
    simp only [convolution, hne, ite_false, mul_zero]
  · simp

end BlockIdentities.Square
