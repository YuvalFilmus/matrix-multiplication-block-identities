/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.DegenerationProduct
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Identity minors cannot increase a flattening dimension under degeneration.
The argument uses polynomial matrices over an integral domain, so no infinitude
or field-characteristic assumption is needed. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open OAI.MatrixMultiplication.Foundation
open scoped BigOperators

variable {K : Type*} [Field K]

private theorem polynomial_identity_minor_full_rank {ι : Type*}
    [Fintype ι] [DecidableEq ι] (P : Matrix ι ι (Polynomial K)) (k : ℕ)
    (hzero : ∀ i j d, d < k → (P i j).coeff d = 0)
    (hlead : ∀ i j, (P i j).coeff k = if i = j then 1 else 0) :
    P.rank = Fintype.card ι := by
  let N : Matrix ι ι (Polynomial K) := fun i j =>
    Classical.choose (Polynomial.X_pow_dvd_iff.mpr (hzero i j))
  have hP : P = ((Polynomial.X : Polynomial K) ^ k) • N := by
    funext i j
    exact Classical.choose_spec (Polynomial.X_pow_dvd_iff.mpr (hzero i j))
  have hN : ∀ i j, (N i j).coeff 0 = if i = j then 1 else 0 := by
    intro i j
    have h := hlead i j
    rw [hP] at h
    simpa only [Matrix.smul_apply, smul_eq_mul, Polynomial.coeff_X_pow_mul',
      le_rfl, ite_true, Nat.sub_self] using h
  have heval : N.map (Polynomial.evalRingHom (0 : K)) = 1 := by
    funext i j
    change (N i j).eval 0 = if i = j then 1 else 0
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact hN i j
  have hdetN : N.det ≠ 0 := by
    intro hz
    have h := congrArg (Polynomial.evalRingHom (0 : K)) hz
    rw [(Polynomial.evalRingHom (0 : K)).map_det] at h
    change (N.map (Polynomial.evalRingHom (0 : K))).det =
      (Polynomial.evalRingHom (0 : K)) 0 at h
    rw [heval, Matrix.det_one, map_zero] at h
    exact one_ne_zero h
  have hdetP : P.det ≠ 0 := by
    rw [hP, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero k Polynomial.X_ne_zero)) hdetN
  exact Matrix.rank_of_det_ne_zero hdetP

/-- A leading identity minor of a polynomial degeneration factors through the
source third coordinate space. The target first two coordinates may depend on i
independently; no shared-generator conclusion is assumed. -/
theorem polynomialDegeneration_identityMinor_card_le
    {X Y Z X' Y' Z' ι : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype ι] [DecidableEq ι]
    {T : Tensor K X Y Z} {U : Tensor K X' Y' Z'}
    {k Lx Ly Lz : ℕ}
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (x : ι → X') (y : ι → Y') (z : ι → Z')
    (hidentity : ∀ i j, U (x i) (y i) (z j) = if i = j then 1 else 0) :
    Fintype.card ι ≤ Fintype.card Z := by
  classical
  let P : Matrix ι ι (Polynomial K) := fun i j => L.basePolynomial (x i) (y i) (z j)
  let A : Matrix ι Z (Polynomial K) := fun i t =>
    ∑ a, ∑ b, L.leftMap (x i) a * L.middleMap (y i) b * Polynomial.C (T a b t)
  let B : Matrix Z ι (Polynomial K) := fun t j => L.rightMap (z j) t
  have hfull : P.rank = Fintype.card ι :=
    polynomial_identity_minor_full_rank P k
      (fun i j d hd => L.vanishes (x i) (y i) (z j) d hd)
      (fun i j => (L.leading (x i) (y i) (z j)).trans (hidentity i j))
  have hfactor : P = A * B := by
    funext i j
    change L.basePolynomial (x i) (y i) (z j) = ∑ t, A i t * B t j
    symm
    simp only [A, B, Finset.sum_mul,
      Tensor.PolynomialRestrictionDegeneration.basePolynomial, Tensor.restrict]
    calc
      (∑ t, ∑ a, ∑ b,
          (L.leftMap (x i) a * L.middleMap (y i) b * Polynomial.C (T a b t)) *
            L.rightMap (z j) t) =
          ∑ a, ∑ t, ∑ b,
            (L.leftMap (x i) a * L.middleMap (y i) b * Polynomial.C (T a b t)) *
              L.rightMap (z j) t := Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ t,
            (L.leftMap (x i) a * L.middleMap (y i) b * Polynomial.C (T a b t)) *
              L.rightMap (z j) t := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro t _
        ring
  calc
    Fintype.card ι = P.rank := hfull.symm
    _ = (A * B).rank := congrArg Matrix.rank hfactor
    _ ≤ A.rank := Matrix.rank_mul_le_left A B
    _ ≤ Fintype.card Z := Matrix.rank_le_card_width A

/-- The same identity-minor obstruction for the public finite-tensor relation. -/
theorem Degenerates.identityMinor_card_le {A B : FiniteTensor K}
    (h : Degenerates A B) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Fin B.nx) (y : ι → Fin B.ny) (z : ι → Fin B.nz)
    (hidentity : ∀ i j, B.coeff (x i) (y i) (z j) = if i = j then 1 else 0) :
    Fintype.card ι ≤ A.nz := by
  obtain ⟨k, Lx, Ly, Lz, ⟨L⟩⟩ := h
  simpa only [Fintype.card_fin] using
    polynomialDegeneration_identityMinor_card_le L x y z hidentity

end BlockIdentities.Square
