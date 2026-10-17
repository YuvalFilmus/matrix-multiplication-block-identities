module
public import BlockIdentities.Tensor.Isomorphism
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

theorem tripling_middle_isomorphism
{K : Type*} [Field K] (r : ℕ+)
    : Isomorphic (middleConvolution (K := K) r)
        (permute .xzy (convolution r r)) :=
-- BEGIN APPROVED PROOF REGION
by
  exact BlockIdentities.Square.middleConvolution_isomorphic r
-- END APPROVED PROOF REGION

end BlockIdentities.Square
