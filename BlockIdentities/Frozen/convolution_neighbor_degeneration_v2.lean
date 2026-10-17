module
public import BlockIdentities.Providers.ConvolutionNeighbor
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

theorem convolution_neighbor_degeneration
{K : Type*} [Field K] (r b : ℕ+) (hb : 2 ≤ (b : ℕ))
    : Degenerates (product (convolution (K := K) r b) dotShape.tensor)
        (neighborSplit r b hb) :=
-- BEGIN APPROVED PROOF REGION
by
  exact BlockIdentities.Providers.Neighbor.convolution_neighbor_degeneration r b hb
-- END APPROVED PROOF REGION

end BlockIdentities.Square
