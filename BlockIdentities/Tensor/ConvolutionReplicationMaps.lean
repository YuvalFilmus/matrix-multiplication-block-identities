/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ConvolutionReplicationBasis
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Tactic.Linarith

/-! Actual P-adic block evaluation maps for characteristic-free replication.
The scalar polynomial variable here is the convolution variable, not epsilon. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace BlockIdentities.Square
open Polynomial
variable {K : Type*} [Field K]

/-- Evaluate one genuine P-adic coefficient block. This is a linear output map
on the entire polynomial ring, so no arbitrary off-domain extension is needed. -/
def convolutionReplicationBlockEval (P : K[X]) (hP : P.Monic)
    {m : ℕ} (hm : 0 < m) (hdegree : P.natDegree = m) (c : ℕ) (x : K) :
    K[X] →ₗ[K] K where
  toFun f := ∑ d : Fin m,
    (convolutionReplicationBasis P hP hm hdegree).repr f (m * c + d.val) * x ^ d.val
  map_add' f g := by simp only [map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' t f := by
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp only [mul_assoc, Finset.mul_sum]

private theorem block_index_eq {m : ℕ} (hm : 0 < m) (a c : ℕ) (d e : Fin m) :
    m * a + d.val = m * c + e.val ↔ a = c ∧ d = e := by
  constructor
  · intro h
    have hdiv := congrArg (fun n => n / m) h
    simp only [Nat.mul_add_div hm, Nat.div_eq_of_lt d.isLt,
      Nat.div_eq_of_lt e.isLt, Nat.add_zero] at hdiv
    refine ⟨hdiv, ?_⟩
    subst c
    exact Fin.ext (Nat.add_left_cancel h)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The literal coordinate functional on a basis vector. -/
theorem convolutionReplicationBlockEval_basis (P : K[X]) (hP : P.Monic)
    {m : ℕ} (hm : 0 < m) (hdegree : P.natDegree = m)
    (a c : ℕ) (d : Fin m) (x : K) :
    convolutionReplicationBlockEval P hP hm hdegree c x
      (convolutionReplicationBasis P hP hm hdegree (m * a + d.val)) =
      if a = c then x ^ d.val else 0 := by
  classical
  simp only [convolutionReplicationBlockEval, LinearMap.coe_mk, AddHom.coe_mk,
    Module.Basis.repr_self, Finsupp.single_apply, block_index_eq hm]
  by_cases hac : a = c
  · simp only [hac, true_and, ite_mul, one_mul, zero_mul]
    simp
  · simp only [hac, false_and, ite_false, zero_mul, Finset.sum_const_zero]

/-- Low-degree polynomial blocks are evaluated in exactly their own block. -/
theorem convolutionReplicationBlockEval_block (P : K[X]) (hP : P.Monic)
    {m : ℕ} (hm : 0 < m) (hdegree : P.natDegree = m)
    (q : K[X]) (hq : q.degree < m) (a c : ℕ) (x : K) :
    convolutionReplicationBlockEval P hP hm hdegree c x (q * P ^ a) =
      if a = c then q.eval x else 0 := by
  classical
  have hsum : q = ∑ d : Fin m, q.coeff d.val • (X : K[X]) ^ d.val := by
    simpa only [smul_X_eq_monomial, sum_monomial_eq] using
      (q.sum_fin (fun i t => monomial i t) (fun _ => monomial_zero_right _) hq).symm
  have hexpand : q * P ^ a = ∑ d : Fin m, q.coeff d.val •
      convolutionReplicationBasis P hP hm hdegree (m * a + d.val) := by
    nth_rw 1 [hsum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    rw [convolutionReplicationBasis_block]
    exact smul_mul_assoc (q.coeff d.val) ((X : K[X]) ^ d.val) (P ^ a)
  rw [hexpand, map_sum]
  simp only [map_smul, smul_eq_mul, convolutionReplicationBlockEval_basis]
  by_cases hac : a = c
  · simp only [hac, ite_true]
    have heval := congrArg (fun f : K[X] => f.eval x) hsum
    simpa only [eval_finsetSum, eval_smul, eval_pow, eval_X, smul_eq_mul] using heval.symm
  · simp only [hac, ite_false, mul_zero, Finset.sum_const_zero]

/-- Actual polynomial division supplies both low blocks of a product.
There is one carry and no higher block under the explicit degree bound. -/
theorem convolutionReplicationBlockEval_division (P : K[X]) (hP : P.Monic)
    {m : ℕ} (hm : 0 < m) (hdegree : P.natDegree = m)
    (f : K[X]) (hf : f.degree < 2 * m) (a c : ℕ) (x : K) :
    convolutionReplicationBlockEval P hP hm hdegree c x (f * P ^ a) =
      (if a = c then (f %ₘ P).eval x else 0) +
      if a + 1 = c then (f /ₘ P).eval x else 0 := by
  have hrem : (f %ₘ P).degree < m := by
    simpa only [degree_eq_natDegree hP.ne_zero, hdegree] using degree_modByMonic_lt f hP
  have hquot := convolutionReplication_div_degree_lt P hP hm hdegree f hf
  have he : f * P ^ a = (f %ₘ P) * P ^ a + (f /ₘ P) * P ^ (a + 1) := by
    nth_rw 1 [← modByMonic_add_div f P]
    rw [pow_succ]
    ring
  rw [he, map_add, convolutionReplicationBlockEval_block P hP hm hdegree _ hrem,
    convolutionReplicationBlockEval_block P hP hm hdegree _ hquot]

/-- Evaluating the remainder at a root preserves the product exactly.
No root multiplicity, derivative, or characteristic condition is involved. -/
theorem convolutionReplication_remainder_eval (P f g : K[X]) {x : K}
    (hx : P.eval x = 0) : ((f * g) %ₘ P).eval x = f.eval x * g.eval x := by
  have he := congrArg (fun t : K[X] => t.eval x) (modByMonic_add_div (f * g) P)
  simpa only [eval_add, eval_mul, hx, zero_mul, add_zero] using he

end BlockIdentities.Square
