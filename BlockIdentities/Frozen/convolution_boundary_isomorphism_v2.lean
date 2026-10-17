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

theorem convolution_boundary_isomorphism
{K : Type*} [Field K] (r : ℕ+) (hr : 2 ≤ (r : ℕ))
    : Isomorphic
        (convolution (K := K) r ⟨(r : ℕ) - 1, by omega⟩)
        (permute .yxz (convolution ⟨(r : ℕ) - 1, by omega⟩ r)) :=
-- BEGIN APPROVED PROOF REGION
by
  exact BlockIdentities.Square.convolution_boundary_isomorphic r hr
-- END APPROVED PROOF REGION

end BlockIdentities.Square
