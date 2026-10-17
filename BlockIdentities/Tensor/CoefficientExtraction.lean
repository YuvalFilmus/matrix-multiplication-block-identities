/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.Definitions
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Interpolation

/-! Exact finite interpolation, with actual coordinate restriction maps. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K : Type*} [Field K]

/-- Each coefficient functional is an explicit finite combination of evaluations.
No characteristic assumption is used; the nodes are arbitrary distinct elements. -/
theorem coefficient_eq_sum_evaluations {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → K) (hinj : Function.Injective nodes)
    (p : Polynomial K) (k : ℕ) (hdegree : p.degree < Fintype.card ι) :
    p.coeff k = ∑ i, (Lagrange.basis Finset.univ nodes i).coeff k * p.eval (nodes i) := by
  simpa only [mul_comm] using Tensor.coeff_eq_sum_eval nodes hinj p k hdegree

/-- A weighted sum of restrictions is a restriction from one source copy per term.
The weights are absorbed into the first coordinate map. -/
theorem weighted_sum_isRestriction_directSum
    {ι X Y Z U V W : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype U] [Fintype V] [Fintype W]
    (A : Tensor K U V W) (T : ι → Tensor K X Y Z) (w : ι → K)
    (hres : ∀ i, IsRestriction (T i) A) :
    IsRestriction (fun x y z => ∑ i, w i * T i x y z)
      (Tensor.directSum (fun _ : ι => A)) := by
  classical
  choose L M N h using hres
  refine ⟨(fun x i => w i.1 * L i.1 x i.2),
    (fun y i => M i.1 y i.2), (fun z i => N i.1 z i.2), ?_⟩
  funext x y z
  simp [h, Tensor.restrict, Fintype.sum_prod_type, Tensor.directSum,
    ite_and, mul_ite, Finset.mul_sum, Finset.sum_mul, mul_assoc]

/-- Coefficient extraction uses one full source copy at each distinct node. -/
theorem coefficient_isRestriction_directSum_of_nodes
    {ι X Y Z U V W : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype U] [Fintype V] [Fintype W]
    (nodes : ι → K) (hinj : Function.Injective nodes)
    (P : Tensor (Polynomial K) X Y Z) (A : Tensor K U V W) (k : ℕ)
    (hdegree : ∀ x y z, (P x y z).degree < Fintype.card ι)
    (hres : ∀ i, IsRestriction (fun x y z => (P x y z).eval (nodes i)) A) :
    IsRestriction (fun x y z => (P x y z).coeff k)
      (Tensor.directSum (fun _ : ι => A)) := by
  have heq : (fun x y z => (P x y z).coeff k) =
      fun x y z => ∑ i, (Lagrange.basis Finset.univ nodes i).coeff k *
        (P x y z).eval (nodes i) := by
    funext x y z
    exact coefficient_eq_sum_evaluations nodes hinj _ k (hdegree x y z)
  rw [heq]
  exact weighted_sum_isRestriction_directSum A _ _ hres

/-- Over any infinite field, degree at most `D` needs exactly `D + 1` full copies.
The hypothesis supplies actual restrictions at every field element. -/
theorem coefficient_isRestriction_directSum [Infinite K]
    {X Y Z U V W : Type*} [Fintype U] [Fintype V] [Fintype W]
    (P : Tensor (Polynomial K) X Y Z) (A : Tensor K U V W) (D k : ℕ)
    (hdegree : ∀ x y z, (P x y z).degree ≤ D)
    (hres : ∀ α : K, IsRestriction (fun x y z => (P x y z).eval α) A) :
    IsRestriction (fun x y z => (P x y z).coeff k)
      (Tensor.directSum (fun _ : Fin (D + 1) => A)) := by
  apply coefficient_isRestriction_directSum_of_nodes
    (interpolationNode D) (interpolationNode_injective D) P A k
  · intro x y z
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt (hdegree x y z)
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self D))
  · intro i
    exact hres _
end BlockIdentities.Square
