module
public import BlockIdentities.Providers.SharedLegValue
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

theorem shared_leg_value_inequality
{K : Type*} [Field K] [IsAlgClosed K]
    {ι : Type} [Fintype ι]
    (A : NonzeroTensor K) (B : ι → NonzeroTensor K)
    (D : MatrixShape) (E : ι → MatrixShape)
    (identity : SharedLegIdentity A.val (fun i => (B i).val) D E)
    : (D.volume : ℝ) * normalizedValueAtOmega A ≥
        ∑ i, ((E i).volume : ℝ) * normalizedValueAtOmega (B i) :=
-- BEGIN APPROVED PROOF REGION
by
  exact BlockIdentities.Providers.shared_leg_value_inequality A B D E identity
-- END APPROVED PROOF REGION

end BlockIdentities.Square
