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

theorem formalOmega_le_nine_quarters
(F : Type*) [Field F]
    : formalOmega F ≤ (9 : ℝ) / 4 :=
-- BEGIN APPROVED PROOF REGION
by
  exact BlockIdentities.Providers.formalOmega_le_nine_quarters F
-- END APPROVED PROOF REGION

end BlockIdentities.Square
