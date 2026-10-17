/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Frozen.finite_convolution_bound_v2
public import BlockIdentities.Square.Limit
public import BlockIdentities.Arithmetic.FormalInfimum

/-! Assemble the square exponent and formally correct algorithm conclusions. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Providers
open scoped BigOperators
open BlockIdentities.Square BlockIdentities.Arithmetic

/-- The actual finite convolution bounds imply the square exponent bound over
an arbitrary field, using the explicit yield limit. -/
theorem formalOmega_le_nine_quarters (F : Type*) [Field F] :
    formalOmega F ≤ (9 : ℝ) / 4 := by
  apply le_nine_fourths_of_finite_certificate_bounds
  intro a
  have hyield : convolutionYield a = ((3 * (a.val : ℝ) - 1) / 4) *
      ∏ j ∈ Finset.Icc 1 (a.val - 1), (1 + 1 / (3 * (j : ℝ))) := by
    unfold convolutionYield
    congr 1
  rw [hyield]
  exact BlockIdentities.Square.finite_convolution_bound F a.val a.property

/-- Formally correct polynomial matrix algorithms attain every positive slack
above 9/4, with the original register-program operation costs. -/
theorem formal_matrix_multiplication_cost_le (F : Type*) [Field F]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : OAI.MatrixMultiplication.Arithmetic.MatrixAlgorithm F n n n,
        FormalCorrect P ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ ((9 : ℝ) / 4 + ε) := by
  obtain ⟨C, hC, hcost⟩ := formalAdmissibleExponent_formalOmega (F := F) ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hPcost⟩ := hcost n hn
  refine ⟨P, hP, hPcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast hn
  · exact add_le_add (formalOmega_le_nine_quarters F) le_rfl

/-- The preserved upstream functional-correctness exponent obeys the same
bound because formal polynomial correctness supplies functional correctness. -/
theorem omega_le_nine_quarters (F : Type*) [Field F] :
    OAI.MatrixMultiplication.Arithmetic.omega F ≤ (9 : ℝ) / 4 :=
  (omega_le_formalOmega (F := F)).trans (formalOmega_le_nine_quarters F)

end BlockIdentities.Providers
