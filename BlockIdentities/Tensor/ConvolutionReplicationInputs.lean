/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ConvolutionReplicationContraction

/-! Actual distinct-node polynomials and the input coordinate vectors used by
convolution replication. Node injectivity is possible over every infinite field. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace BlockIdentities.Square
open Polynomial
variable {K : Type*} [Field K]

/-- The manuscript's separable monic polynomial, with arbitrary distinct nodes. -/
def convolutionReplicationPolynomial {m : ℕ} (nodes : Fin m → K) : K[X] :=
  Lagrange.nodal Finset.univ nodes

theorem convolutionReplicationPolynomial_monic {m : ℕ} (nodes : Fin m → K) :
    (convolutionReplicationPolynomial nodes).Monic := Lagrange.nodal_monic

@[simp] theorem convolutionReplicationPolynomial_natDegree {m : ℕ} (nodes : Fin m → K) :
    (convolutionReplicationPolynomial nodes).natDegree = m := by
  simp only [convolutionReplicationPolynomial, Lagrange.natDegree_nodal,
    Finset.card_univ, Fintype.card_fin]

@[simp] theorem convolutionReplicationPolynomial_eval {m : ℕ} (nodes : Fin m → K) (i : Fin m) :
    (convolutionReplicationPolynomial nodes).eval (nodes i) = 0 :=
  Lagrange.eval_nodal_at_node (Finset.mem_univ i)

/-- A delta polynomial for each node, with degree below the number of nodes. -/
def convolutionReplicationLagrange {m : ℕ} (nodes : Fin m → K) (h : Fin m) : K[X] :=
  Lagrange.basis Finset.univ nodes h

theorem convolutionReplicationLagrange_natDegree {m : ℕ}
    (nodes : Fin m → K) (hinj : Function.Injective nodes) (h : Fin m) :
    (convolutionReplicationLagrange nodes h).natDegree = m - 1 := by
  simpa only [convolutionReplicationLagrange, Finset.card_univ, Fintype.card_fin] using
    Lagrange.natDegree_basis (s := Finset.univ) (v := nodes)
      (fun _ _ _ _ he => hinj he) (Finset.mem_univ h)

@[simp] theorem convolutionReplicationLagrange_eval {m : ℕ}
    (nodes : Fin m → K) (hinj : Function.Injective nodes) (h i : Fin m) :
    (convolutionReplicationLagrange nodes h).eval (nodes i) = if h = i then 1 else 0 := by
  classical
  by_cases he : h = i
  · subst i
    exact (Lagrange.eval_basis_self (s := Finset.univ) (v := nodes)
      (fun _ _ _ _ he => hinj he) (Finset.mem_univ h)).trans (if_pos rfl).symm
  · exact (Lagrange.eval_basis_of_ne (s := Finset.univ) (v := nodes) he
      (Finset.mem_univ i)).trans (if_neg he).symm

/-- The actual input polynomial for a copy h and block a. -/
def convolutionReplicationInput {m : ℕ} (nodes : Fin m → K) (h : Fin m) (a : ℕ) : K[X] :=
  convolutionReplicationLagrange nodes h * convolutionReplicationPolynomial nodes ^ a

/-- Every input polynomial fits in the original m*r input coordinates. -/
theorem convolutionReplicationInput_degree_lt {m r : ℕ}
    (nodes : Fin m → K) (hinj : Function.Injective nodes) (hm : 0 < m)
    (h : Fin m) (a : Fin r) :
    (convolutionReplicationInput nodes h a.val).degree < m * r := by
  have hbound := natDegree_mul_le
    (p := convolutionReplicationLagrange nodes h)
    (q := convolutionReplicationPolynomial nodes ^ a.val)
  rw [convolutionReplicationLagrange_natDegree nodes hinj,
    (convolutionReplicationPolynomial_monic nodes).natDegree_pow,
    convolutionReplicationPolynomial_natDegree] at hbound
  have hdim := Nat.mul_le_mul_left m (Nat.succ_le_of_lt a.isLt)
  have hnat : (convolutionReplicationInput nodes h a.val).natDegree < m * r := by
    dsimp only [convolutionReplicationInput]
    have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
    nlinarith only [hbound, hdim, hm']
  have hcast : ((convolutionReplicationInput nodes h a.val).natDegree : WithBot ℕ) <
      ((m * r : ℕ) : WithBot ℕ) := WithBot.coe_lt_coe.mpr hnat
  exact degree_le_natDegree.trans_lt (by simpa only [Nat.cast_mul] using hcast)

/-- A product of two delta polynomials has at most a single P-adic carry. -/
theorem convolutionReplicationLagrange_product_degree_lt {m : ℕ}
    (nodes : Fin m → K) (hinj : Function.Injective nodes) (hm : 0 < m)
    (h i : Fin m) :
    (convolutionReplicationLagrange nodes h *
      convolutionReplicationLagrange nodes i).degree < 2 * m := by
  have hbound := natDegree_mul_le
    (p := convolutionReplicationLagrange nodes h) (q := convolutionReplicationLagrange nodes i)
  rw [convolutionReplicationLagrange_natDegree nodes hinj,
    convolutionReplicationLagrange_natDegree nodes hinj] at hbound
  have hnat : (convolutionReplicationLagrange nodes h *
      convolutionReplicationLagrange nodes i).natDegree < (2 * m : ℕ) := by omega
  have hcast : ((convolutionReplicationLagrange nodes h *
      convolutionReplicationLagrange nodes i).natDegree : WithBot ℕ) <
      ((2 * m : ℕ) : WithBot ℕ) := WithBot.coe_lt_coe.mpr hnat
  exact degree_le_natDegree.trans_lt (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcast)

/-- The actual transformed product has the desired independent-copy coefficient
and exactly one explicitly displayed carry. This is a polynomial identity,
including when the field characteristic divides the number of nodes. -/
theorem convolutionReplicationInput_block_product {m : ℕ}
    (nodes : Fin m → K) (hinj : Function.Injective nodes) (hm : 0 < m)
    (h j i : Fin m) (a b c : ℕ) :
    convolutionReplicationBlockEval (convolutionReplicationPolynomial nodes)
      (convolutionReplicationPolynomial_monic nodes) hm
      (convolutionReplicationPolynomial_natDegree nodes) c (nodes i)
      (convolutionReplicationInput nodes h a * convolutionReplicationInput nodes j b) =
      (if a + b = c then (if h = i then 1 else 0) * (if j = i then 1 else 0) else 0) +
      if a + b + 1 = c then
        ((convolutionReplicationLagrange nodes h * convolutionReplicationLagrange nodes j) /ₘ
          convolutionReplicationPolynomial nodes).eval (nodes i) else 0 := by
  classical
  have he : convolutionReplicationInput nodes h a * convolutionReplicationInput nodes j b =
      (convolutionReplicationLagrange nodes h * convolutionReplicationLagrange nodes j) *
        convolutionReplicationPolynomial nodes ^ (a + b) := by
    dsimp only [convolutionReplicationInput]
    rw [pow_add]
    ring
  rw [he, convolutionReplicationBlockEval_division _ _ hm _ _
    (convolutionReplicationLagrange_product_degree_lt nodes hinj hm h j)]
  rw [convolutionReplication_remainder_eval _ _ _
    (convolutionReplicationPolynomial_eval nodes i),
    convolutionReplicationLagrange_eval nodes hinj,
    convolutionReplicationLagrange_eval nodes hinj]

end BlockIdentities.Square
