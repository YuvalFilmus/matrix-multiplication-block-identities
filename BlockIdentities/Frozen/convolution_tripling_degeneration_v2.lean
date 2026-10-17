module
public import BlockIdentities.Providers.ConvolutionTripling
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

theorem convolution_tripling_degeneration
{K : Type*} [Field K] (r : ℕ+) (hr : 2 ≤ (r : ℕ))
    : Degenerates
        (convolution (K := K) r ⟨4 * (r : ℕ) - 1, by omega⟩)
        (triplingSplit r hr) :=
-- BEGIN APPROVED PROOF REGION
by
  exact BlockIdentities.Providers.convolution_tripling_degeneration r hr
-- END APPROVED PROOF REGION

end BlockIdentities.Square
