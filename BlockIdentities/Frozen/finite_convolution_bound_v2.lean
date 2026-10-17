module
public import BlockIdentities.Providers.FiniteConvolutionBound
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

theorem finite_convolution_bound
(F : Type*) [Field F] (a : ℕ) (ha : 2 ≤ a)
    : formalOmega F ≤ 3 * Real.log (2 * (a : ℝ) - 1) /
      (Real.log 2 + Real.log (((3 * (a : ℝ) - 1) / 4) *
        ∏ j ∈ Finset.Icc 1 (a - 1), (1 + 1 / (3 * (j : ℝ))))) :=
-- BEGIN APPROVED PROOF REGION
by
  exact BlockIdentities.Providers.finite_convolution_bound F a ha
-- END APPROVED PROOF REGION

end BlockIdentities.Square
