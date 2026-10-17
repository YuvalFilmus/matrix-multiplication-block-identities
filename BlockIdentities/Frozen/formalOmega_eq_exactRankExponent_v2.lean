module
public import BlockIdentities.Providers.RankAndField
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

theorem formalOmega_eq_exactRankExponent
(F : Type*) [Field F]
    : formalOmega F = AuxiliarySeparation.exactRankExponent F :=
-- BEGIN APPROVED PROOF REGION
by
  exact BlockIdentities.Providers.formalOmega_eq_exactRankExponent F
-- END APPROVED PROOF REGION

end BlockIdentities.Square
