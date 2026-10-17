module
public import BlockIdentities.Square.FieldDescent
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

theorem scalar_descent
{F X Y Z : Type*} [Field F] [Fintype X] [Fintype Y] [Fintype Z]
    (T : OAI.MatrixMultiplication.Foundation.Tensor F X Y Z) (r : ℕ)
    (h : OAI.MatrixMultiplication.Foundation.Tensor.RankAtMost
      (fun x y z => algebraMap F (AlgebraicClosure F) (T x y z)) r)
    : ∃ q : ℕ, 1 ≤ q ∧ ∀ m : ℕ, 1 ≤ m →
        OAI.MatrixMultiplication.Foundation.Tensor.RankAtMost
          (OAI.MatrixMultiplication.Foundation.Tensor.power T m) (q ^ 2 * r ^ m) :=
-- BEGIN APPROVED PROOF REGION
by
  exact BlockIdentities.Square.scalar_descent_bound T r h
-- END APPROVED PROOF REGION

end BlockIdentities.Square
