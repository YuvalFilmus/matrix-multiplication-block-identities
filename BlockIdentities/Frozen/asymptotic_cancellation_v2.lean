module
public import BlockIdentities.Providers.Cancellation
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

theorem asymptotic_cancellation
{K : Type*} [Field K] [IsAlgClosed K]
    (A B Z : FiniteTensor K) (hZ : Nonzero Z)
    (h : AsymptoticallyRestricts (product A Z) (product B Z))
    : AsymptoticallyRestricts A B :=
-- BEGIN APPROVED PROOF REGION
by
  exact BlockIdentities.Providers.asymptotic_cancellation A B Z hZ h
-- END APPROVED PROOF REGION

end BlockIdentities.Square
