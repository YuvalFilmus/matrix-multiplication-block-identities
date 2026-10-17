/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ConvolutionReplicationInputs
public import BlockIdentities.Tensor.PolynomialMaps

/-! Polynomial epsilon maps for the actual independent replicated convolutions. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace BlockIdentities.Square
open Polynomial
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
variable {K : Type*} [Field K]

private theorem monomial_contraction {A B : ℕ} (f g : K[X])
    (hf : f.degree < A) (hg : g.degree < B) (ℓ : K[X] →ₗ[K] K) (l v c : ℕ) :
    (∑ i : Fin A, ∑ j : Fin B, ∑ k : Fin (A + B - 1),
      monomial l (f.coeff i.val) * monomial v (g.coeff j.val) *
        monomial c (ℓ (X ^ k.val)) * C (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) A B i j k)) =
      monomial (l + v + c) (ℓ (f * g)) := by
  classical
  have h := congrArg (monomial (l + v + c))
    (convolutionReplication_contraction f g hf hg ℓ)
  rw [map_sum] at h
  simp_rw [map_sum] at h
  convert h using 3 <;>
    simp only [← monomial_zero_left, monomial_mul_monomial, Nat.add_zero]

/-- First actual epsilon map, with nonnegative cleared grading. -/
def convolutionReplicationLeft {m r : ℕ} (nodes : Fin m → K) :
    (Fin m × Fin r) → Fin (m * r) → K[X] :=
  fun ha i => monomial (r - 1 - ha.2.val)
    ((convolutionReplicationInput nodes ha.1 ha.2.val).coeff i.val)

/-- Second actual epsilon map, with nonnegative cleared grading. -/
def convolutionReplicationMiddle {m s : ℕ} (nodes : Fin m → K) :
    (Fin m × Fin s) → Fin (m * s) → K[X] :=
  fun hb j => monomial (s - 1 - hb.2.val)
    ((convolutionReplicationInput nodes hb.1 hb.2.val).coeff j.val)

/-- Last epsilon map uses the proved P-adic output functional on source monomials. -/
def convolutionReplicationRight {m r s : ℕ} (nodes : Fin m → K) (hm : 0 < m) :
    (Fin m × Fin (r + s - 1)) → Fin (m * r + m * s - 1) → K[X] :=
  fun hc k => monomial hc.2.val
    (convolutionReplicationBlockEval (convolutionReplicationPolynomial nodes)
      (convolutionReplicationPolynomial_monic nodes) hm
      (convolutionReplicationPolynomial_natDegree nodes) hc.2.val (nodes hc.1) (X ^ k.val))

/-- The full transformed contraction is a single epsilon monomial whose scalar
coefficient is the actual P-adic block of the input product. -/
theorem convolutionReplication_restricted_formula {m r s : ℕ}
    (nodes : Fin m → K) (hinj : Function.Injective nodes) (hm : 0 < m)
    (ha : Fin m × Fin r) (hb : Fin m × Fin s) (hc : Fin m × Fin (r + s - 1)) :
    Tensor.restrict (convolutionReplicationLeft nodes) (convolutionReplicationMiddle nodes)
      (convolutionReplicationRight (r := r) (s := s) nodes hm)
      (fun i j k => C (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) (m * r) (m * s) i j k)) ha hb hc =
    monomial (r - 1 - ha.2.val + (s - 1 - hb.2.val) + hc.2.val)
      (convolutionReplicationBlockEval (convolutionReplicationPolynomial nodes)
        (convolutionReplicationPolynomial_monic nodes) hm
        (convolutionReplicationPolynomial_natDegree nodes) hc.2.val (nodes hc.1)
        (convolutionReplicationInput nodes ha.1 ha.2.val *
          convolutionReplicationInput nodes hb.1 hb.2.val)) := by
  exact monomial_contraction _ _
    (convolutionReplicationInput_degree_lt nodes hinj hm ha.1 ha.2)
    (convolutionReplicationInput_degree_lt nodes hinj hm hb.1 hb.2) _ _ _ _

/-- Independent copies in literal product coordinates, before canonical finite
presentation transport. -/
def convolutionReplicationTarget (m r s : ℕ) :
    Tensor K (Fin m × Fin r) (Fin m × Fin s) (Fin m × Fin (r + s - 1)) :=
  fun ha hb hc => if ha.1 = hb.1 ∧ hb.1 = hc.1 then
    OAI.MatrixMultiplication.AuxiliarySeparation.convolution r s ha.2 hb.2 hc.2 else 0

private theorem main_coefficient {m r s : ℕ}
    (ha : Fin m × Fin r) (hb : Fin m × Fin s) (hc : Fin m × Fin (r + s - 1)) :
    (if ha.2.val + hb.2.val = hc.2.val then
      (if ha.1 = hc.1 then (1 : K) else 0) * (if hb.1 = hc.1 then 1 else 0) else 0) =
      convolutionReplicationTarget m r s ha hb hc := by
  classical
  unfold convolutionReplicationTarget OAI.MatrixMultiplication.AuxiliarySeparation.convolution
  split_ifs <;> simp_all

/-- Exact epsilon polynomial normal form: desired copies plus one carry.
The carry coefficient is explicit and may be zero; no cancellation is assumed. -/
theorem convolutionReplication_filtered {m r s : ℕ}
    (nodes : Fin m → K) (hinj : Function.Injective nodes) (hm : 0 < m)
    (ha : Fin m × Fin r) (hb : Fin m × Fin s) (hc : Fin m × Fin (r + s - 1)) :
    Tensor.restrict (convolutionReplicationLeft nodes) (convolutionReplicationMiddle nodes)
      (convolutionReplicationRight (r := r) (s := s) nodes hm)
      (fun i j k => C (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) (m * r) (m * s) i j k)) ha hb hc =
    monomial (r + s - 2) (convolutionReplicationTarget m r s ha hb hc) +
      monomial (r + s - 2 + 1)
        (if ha.2.val + hb.2.val + 1 = hc.2.val then
          ((convolutionReplicationLagrange nodes ha.1 * convolutionReplicationLagrange nodes hb.1) /ₘ
            convolutionReplicationPolynomial nodes).eval (nodes hc.1) else 0) := by
  classical
  rw [convolutionReplication_restricted_formula nodes hinj hm,
    convolutionReplicationInput_block_product nodes hinj hm]
  rw [map_add, ← main_coefficient ha hb hc]
  apply congrArg₂ (fun f g : K[X] => f + g)
  · by_cases he : ha.2.val + hb.2.val = hc.2.val
    · simp only [he, ite_true]
      have hexponent : r - 1 - ha.2.val + (s - 1 - hb.2.val) + hc.2.val = r + s - 2 := by
        have h₁ : ha.2.val < r := ha.2.isLt
        have h₂ : hb.2.val < s := hb.2.isLt
        omega
      rw [hexponent]
    · simp only [he, ite_false, map_zero]
  · by_cases he : ha.2.val + hb.2.val + 1 = hc.2.val
    · simp only [he, ite_true]
      have hexponent : r - 1 - ha.2.val + (s - 1 - hb.2.val) + hc.2.val = r + s - 2 + 1 := by
        have h₁ : ha.2.val < r := ha.2.isLt
        have h₂ : hb.2.val < s := hb.2.isLt
        omega
      rw [hexponent]
    · simp only [he, ite_false, map_zero]

/-- A genuine raw coefficientwise degeneration with explicit cleared polynomial
maps, over every field in which the given nodes are distinct. -/
def convolutionReplicationRawDegeneration {m r s : ℕ}
    (nodes : Fin m → K) (hinj : Function.Injective nodes) (hm : 0 < m) :
    Tensor.PolynomialRestrictionDegeneration
      (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) (m * r) (m * s))
      (convolutionReplicationTarget m r s) (r + s - 2) (r - 1) (s - 1) (r + s - 2) where
  leftMap := convolutionReplicationLeft nodes
  middleMap := convolutionReplicationMiddle nodes
  rightMap := convolutionReplicationRight nodes hm
  left_degree := by
    intro ha i
    exact (degree_monomial_le _ _).trans (by exact_mod_cast (Nat.sub_le (r - 1) ha.2.val))
  middle_degree := by
    intro hb j
    exact (degree_monomial_le _ _).trans (by exact_mod_cast (Nat.sub_le (s - 1) hb.2.val))
  right_degree := by
    intro hc k
    apply (degree_monomial_le _ _).trans
    have h := hc.2.isLt
    exact_mod_cast (show hc.2.val ≤ r + s - 2 by omega)
  vanishes := by
    intro ha hb hc j hj
    change (Tensor.restrict (convolutionReplicationLeft nodes) (convolutionReplicationMiddle nodes)
      (convolutionReplicationRight (r := r) (s := s) nodes hm)
      (fun i j k => C (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) (m * r) (m * s) i j k)) ha hb hc).coeff j = 0
    rw [convolutionReplication_filtered nodes hinj hm, coeff_add]
    have hn : r + s - 2 ≠ j := by omega
    have hn' : r + s - 2 + 1 ≠ j := by omega
    simp only [coeff_monomial, hn, hn', ite_false, add_zero]
  leading := by
    intro ha hb hc
    change (Tensor.restrict (convolutionReplicationLeft nodes) (convolutionReplicationMiddle nodes)
      (convolutionReplicationRight (r := r) (s := s) nodes hm)
      (fun i j k => C (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) (m * r) (m * s) i j k)) ha hb hc).coeff (r + s - 2) = _
    rw [convolutionReplication_filtered nodes hinj hm, coeff_add]
    have hn : r + s - 2 + 1 ≠ r + s - 2 := by omega
    simp only [coeff_monomial, ite_true, hn, ite_false, add_zero]

end BlockIdentities.Square
