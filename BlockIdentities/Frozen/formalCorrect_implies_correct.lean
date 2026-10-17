module
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

theorem formalCorrect_implies_correct
{F : Type*} [Field F] {a b c : ℕ}
    (P : OAI.MatrixMultiplication.Arithmetic.MatrixAlgorithm F a b c) (hP : FormalCorrect P)
    : P.Correct :=
-- BEGIN APPROVED PROOF REGION
by exact BlockIdentities.Arithmetic.formalCorrect_implies_correct P hP
-- END APPROVED PROOF REGION

end BlockIdentities.Square
