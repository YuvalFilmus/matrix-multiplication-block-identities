module
public import BlockIdentities.Providers.FinalSquare
public import BlockIdentities.Arithmetic.FormalPolynomial
public import BlockIdentities.Tensor.Value
public import BlockIdentities.Tensor.ConvolutionSplittings
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankExponent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open scoped BigOperators
open OAI.MatrixMultiplication
open BlockIdentities BlockIdentities.Square BlockIdentities.Arithmetic

@[expose] public section
namespace BlockIdentities.Square

theorem formal_matrix_multiplication_cost_le
(F : Type*) [Field F] (ε : ℝ) (hε : 0 < ε)
    : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        ∃ P : OAI.MatrixMultiplication.Arithmetic.MatrixAlgorithm F n n n,
          FormalCorrect P ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ ((9 : ℝ) / 4 + ε) :=
-- BEGIN APPROVED PROOF REGION
by
  exact BlockIdentities.Providers.formal_matrix_multiplication_cost_le F ε hε
-- END APPROVED PROOF REGION

end BlockIdentities.Square
