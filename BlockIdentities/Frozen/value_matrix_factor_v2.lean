module
public import BlockIdentities.Providers.ValueMatrixFactor
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

theorem value_matrix_factor
{K : Type*} [Field K] [IsAlgClosed K]
    (T : NonzeroTensor K)
    (hcyclic : Isomorphic T.val (permute .yzx T.val))
    : (∀ U : NonzeroTensor K, Isomorphic U.val (permute .yzx U.val) →
        AsymptoticallyRestricts T.val U.val → valueAtOmega U ≤ valueAtOmega T) ∧
      (∀ d : ℕ, ∀ hd : 1 ≤ d,
        valueAtOmega (T.product (nonzeroSquare d hd)) =
          (d : ℝ) ^ formalOmega K * valueAtOmega T) ∧
      (∀ b : ℕ, ∀ hb : 1 ≤ b,
        valueAtOmega (T.copies b hb) ≤ (b : ℝ) ^ formalOmega K * valueAtOmega T) :=
-- BEGIN APPROVED PROOF REGION
by
  exact BlockIdentities.Providers.value_matrix_factor T hcyclic
-- END APPROVED PROOF REGION

end BlockIdentities.Square
