/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.CoefficientExtraction
public import BlockIdentities.Square.SeparatorWeights

/-! Explicit polynomial maps for the characteristic-free sector filter. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K X Y Z : Type*} [Field K]
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- First-leg substitution with the extra sector coordinate. -/
def separatorPolynomialLeft {M : ℕ} (p : X × Fin M) (x : X) : Polynomial K :=
  if p.1 = x then Polynomial.X ^ (2 * p.2.val) else 0

/-- Second-leg substitution, shifted to have nonnegative exponents. -/
def separatorPolynomialMiddle {M : ℕ} (sy : Y → Fin M)
    (p : Y × Fin M) (y : Y) : Polynomial K :=
  if p.1 = y then Polynomial.X ^ (p.2.val + (M - 1) - (sy p.1).val) else 0

/-- Third-leg substitution, shifted to have nonnegative exponents. -/
def separatorPolynomialRight {M : ℕ} (sz : Z → Fin M)
    (p : Z × Fin M) (z : Z) : Polynomial K :=
  if p.1 = z then Polynomial.X ^ (2 * (M - 1) - p.2.val - (sz p.1).val) else 0

/-- The actual tensor obtained by applying the three polynomial local maps. -/
def separatorPolynomial {M : ℕ} (T : Tensor K X Y Z)
    (sy : Y → Fin M) (sz : Z → Fin M) :
    Tensor (Polynomial K) (X × Fin M) (Y × Fin M) (Z × Fin M) :=
  Tensor.restrict separatorPolynomialLeft (separatorPolynomialMiddle sy)
    (separatorPolynomialRight sz) (fun x y z => Polynomial.C (T x y z))

/-- Sector support identifies the middle and right source-sector labels. -/
theorem separatorPolynomial_apply {M : ℕ} (T : Tensor K X Y Z)
    (sy : Y → Fin M) (sz : Z → Fin M)
    (hsupport : ∀ x y z, T x y z ≠ 0 → sy y = sz z)
    (x : X) (y : Y) (z : Z) (g u v : Fin M) :
    separatorPolynomial T sy sz (x, g) (y, u) (z, v) =
      Polynomial.C (T x y z) * Polynomial.X ^ (separatorFilterDegree g (sy y) u v) := by
  have hraw : separatorPolynomial T sy sz (x, g) (y, u) (z, v) =
      Polynomial.X ^ (2 * g.val) *
      Polynomial.X ^ (u.val + (M - 1) - (sy y).val) *
      Polynomial.X ^ (2 * (M - 1) - v.val - (sz z).val) * Polynomial.C (T x y z) := by
    simp [separatorPolynomial, Tensor.restrict, separatorPolynomialLeft,
      separatorPolynomialMiddle, separatorPolynomialRight, mul_ite, ite_mul,
      Finset.mul_sum, Finset.sum_mul]
  rw [hraw]
  by_cases ht : T x y z = 0
  · simp only [ht, Polynomial.C_0, mul_zero, zero_mul]
  · rw [← hsupport x y z ht]
    simp only [separatorFilterDegree, pow_add]
    ring

/-- Every scalar evaluation is an actual restriction using evaluated local maps. -/
theorem separatorPolynomial_eval_isRestriction {M : ℕ} (T : Tensor K X Y Z)
    (sy : Y → Fin M) (sz : Z → Fin M) (α : K) :
    IsRestriction (fun x y z => (separatorPolynomial T sy sz x y z).eval α) T := by
  refine ⟨(fun x y => (separatorPolynomialLeft x y).eval α),
    (fun x y => (separatorPolynomialMiddle sy x y).eval α),
    (fun x y => (separatorPolynomialRight sz x y).eval α), ?_⟩
  funext x y z
  simp [separatorPolynomial, Tensor.restrict, Polynomial.eval_finsetSum]

/-- The actual filter polynomial has the manuscript's linear degree bound. -/
theorem separatorPolynomial_natDegree_le {M : ℕ} (T : Tensor K X Y Z)
    (sy : Y → Fin M) (sz : Z → Fin M)
    (hsupport : ∀ x y z, T x y z ≠ 0 → sy y = sz z)
    (x : X × Fin M) (y : Y × Fin M) (z : Z × Fin M) :
    (separatorPolynomial T sy sz x y z).natDegree ≤ 6 * (M - 1) := by
  rw [separatorPolynomial_apply T sy sz hsupport x.1 y.1 z.1 x.2 y.2 z.2]
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (separatorFilterDegree_le _ _ _ _)

/-- Interpolation extracts the desired filter with one full source copy per node.
The infinite-field assumption is only the availability of distinct nodes. -/
theorem separatorPolynomial_coefficient_isRestriction [Infinite K] {M : ℕ}
    (T : Tensor K X Y Z) (sy : Y → Fin M) (sz : Z → Fin M)
    (hsupport : ∀ x y z, T x y z ≠ 0 → sy y = sz z) :
    IsRestriction
      (fun x y z => (separatorPolynomial T sy sz x y z).coeff (3 * (M - 1)))
      (Tensor.directSum (fun _ : Fin (6 * (M - 1) + 1) => T)) := by
  apply coefficient_isRestriction_directSum
    (separatorPolynomial T sy sz) T (6 * (M - 1)) (3 * (M - 1))
  · intro x y z
    exact Polynomial.degree_le_natDegree.trans
      (WithBot.coe_le_coe.mpr (separatorPolynomial_natDegree_le T sy sz hsupport x y z))
  · intro α
    exact separatorPolynomial_eval_isRestriction T sy sz α

end BlockIdentities.Square
