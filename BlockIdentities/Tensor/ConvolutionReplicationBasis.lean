/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! The actual triangular polynomial basis used in characteristic-free
convolution replication. This module does not assert a tensor degeneration. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace BlockIdentities.Square
open Polynomial
variable {K : Type*} [Field K]

/-- The source's monic P-adic triangular sequence, in increasing leading degree.
For positive m, writing n=a*m+d gives the literal polynomial X^d*P^a. -/
def convolutionReplicationSequence (P : K[X]) (hP : P.Monic)
    {m : ℕ} (hm : 0 < m) (hdegree : P.natDegree = m) : Polynomial.Sequence K where
  elems' n := X ^ (n % m) * P ^ (n / m)
  degree_eq' n := by
    have hmonic : (X ^ (n % m) * P ^ (n / m)).Monic :=
      (monic_X_pow _).mul (hP.pow _)
    rw [degree_eq_natDegree hmonic.ne_zero,
      (monic_X_pow _).natDegree_mul (hP.pow _), natDegree_X_pow,
      hP.natDegree_pow, hdegree]
    congr 1
    rw [Nat.mul_comm (n / m) m]
    exact Nat.mod_add_div n m

/-- A proved basis of the entire polynomial ring. Its existence uses the actual
triangular sequence theorem, not an assumed P-adic coordinate decomposition. -/
def convolutionReplicationBasis (P : K[X]) (hP : P.Monic)
    {m : ℕ} (hm : 0 < m) (hdegree : P.natDegree = m) :
    Module.Basis ℕ K K[X] :=
  (convolutionReplicationSequence P hP hm hdegree).basis (fun n => by
    have hmonic : ((convolutionReplicationSequence P hP hm hdegree) n).Monic :=
      (monic_X_pow _).mul (hP.pow _)
    rw [hmonic.leadingCoeff]
    exact isUnit_one)

@[simp] theorem convolutionReplicationBasis_apply (P : K[X]) (hP : P.Monic)
    {m : ℕ} (hm : 0 < m) (hdegree : P.natDegree = m) (n : ℕ) :
    convolutionReplicationBasis P hP hm hdegree n = X ^ (n % m) * P ^ (n / m) := by
  exact (convolutionReplicationSequence P hP hm hdegree).basis_eq_self _ n

/-- Every initial segment spans exactly the polynomials of its degree range. -/
theorem convolutionReplicationBasis_span (P : K[X]) (hP : P.Monic)
    {m : ℕ} (hm : 0 < m) (hdegree : P.natDegree = m) (n : ℕ) :
    Submodule.span K (convolutionReplicationBasis P hP hm hdegree '' Set.Iio n) =
      Polynomial.degreeLT K n := by
  have heq : (convolutionReplicationBasis P hP hm hdegree : ℕ → K[X]) =
      convolutionReplicationSequence P hP hm hdegree := by
    funext i
    exact (convolutionReplicationSequence P hP hm hdegree).basis_eq_self _ i
  rw [heq]
  apply Polynomial.Sequence.span_degreeLT
  intro i _
  have hmonic : ((convolutionReplicationSequence P hP hm hdegree) i).Monic :=
    (monic_X_pow _).mul (hP.pow _)
  rw [hmonic.leadingCoeff]
  exact isUnit_one

/-- At a literal block index, the triangular basis is exactly the manuscript
monomial times a power of P. -/
theorem convolutionReplicationBasis_block (P : K[X]) (hP : P.Monic)
    {m : ℕ} (hm : 0 < m) (hdegree : P.natDegree = m)
    (a : ℕ) (d : Fin m) :
    convolutionReplicationBasis P hP hm hdegree (m * a + d.val) = X ^ d.val * P ^ a := by
  rw [convolutionReplicationBasis_apply, Nat.mul_add_mod,
    Nat.mod_eq_of_lt d.isLt, Nat.mul_add_div hm,
    Nat.div_eq_of_lt d.isLt, Nat.add_zero]

/-- Low-degree blocks have genuinely computed finite P-adic coordinates. -/
theorem convolutionReplicationBasis_repr_block (P : K[X]) (hP : P.Monic)
    {m : ℕ} (hm : 0 < m) (hdegree : P.natDegree = m)
    (q : K[X]) (hq : q.degree < m) (a : ℕ) :
    (convolutionReplicationBasis P hP hm hdegree).repr (q * P ^ a) =
      ∑ d : Fin m, q.coeff d.val • Finsupp.single (m * a + d.val) (1 : K) := by
  classical
  have hqsum : q = ∑ d : Fin m, q.coeff d.val • (X : K[X]) ^ d.val := by
    simpa only [smul_X_eq_monomial, sum_monomial_eq] using
      (q.sum_fin (fun i c => monomial i c) (fun _ => monomial_zero_right _) hq).symm
  have hexpand : q * P ^ a = ∑ d : Fin m,
      q.coeff d.val • convolutionReplicationBasis P hP hm hdegree (m * a + d.val) := by
    nth_rw 1 [hqsum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    rw [convolutionReplicationBasis_block]
    exact smul_mul_assoc (q.coeff d.val) ((X : K[X]) ^ d.val) (P ^ a)
  rw [hexpand, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [map_smul, Module.Basis.repr_self]

/-- Literal remainder/one-carry coordinates, with no existence assertion hidden
in a coordinate hypothesis. This is the algebraic identity before epsilon grading. -/
theorem convolutionReplicationBasis_repr_carry (P : K[X]) (hP : P.Monic)
    {m : ℕ} (hm : 0 < m) (hdegree : P.natDegree = m)
    (q t : K[X]) (hq : q.degree < m) (ht : t.degree < m) (a : ℕ) :
    (convolutionReplicationBasis P hP hm hdegree).repr ((q + P * t) * P ^ a) =
      (∑ d : Fin m, q.coeff d.val • Finsupp.single (m * a + d.val) (1 : K)) +
      ∑ d : Fin m, t.coeff d.val • Finsupp.single (m * (a + 1) + d.val) (1 : K) := by
  have he : (q + P * t) * P ^ a = q * P ^ a + t * P ^ (a + 1) := by
    rw [pow_succ]
    ring
  rw [he, map_add, convolutionReplicationBasis_repr_block P hP hm hdegree q hq,
    convolutionReplicationBasis_repr_block P hP hm hdegree t ht]

/-- The quotient in one block multiplication really is a low-degree block. -/
theorem convolutionReplication_div_degree_lt (P : K[X]) (hP : P.Monic)
    {m : ℕ} (hm : 0 < m) (hdegree : P.natDegree = m)
    (f : K[X]) (hf : f.degree < 2 * m) : (f /ₘ P).degree < m := by
  by_cases hz : f /ₘ P = 0
  · rw [hz, degree_zero]
    exact WithBot.bot_lt_coe m
  have hnat : f.natDegree < 2 * m := by
    by_cases hfzero : f = 0
    · simp only [hfzero, natDegree_zero]
      omega
    · exact (natDegree_lt_iff_degree_lt hfzero).mpr hf
  rw [← natDegree_lt_iff_degree_lt hz, natDegree_divByMonic f hP, hdegree]
  omega

end BlockIdentities.Square
