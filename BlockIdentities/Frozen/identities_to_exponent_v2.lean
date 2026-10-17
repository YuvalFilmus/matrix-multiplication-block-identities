module
public import BlockIdentities.Providers.IdentitiesToExponent
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

theorem identities_to_exponent
{F : Type*} [Field F]
    {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (A : V → FiniteTensor (AlgebraicClosure F)) (hA : ∀ v, Nonzero (A v))
    (q : E → ℕ) (σ : E → V) (w : (e : E) → Fin (q e) → V)
    (D : E → MatrixShape) (Dout : (e : E) → Fin (q e) → MatrixShape)
    (identities : ∀ e, SharedLegIdentity (A (σ e)) (fun i => A (w e i)) (D e) (Dout e))
    (s t : V) (hst : s ≠ t) (hterminal : ∀ e, σ e ≠ t)
    (d r : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r)
    (ht : Isomorphic (symmetrize (A t)) (square d))
    (hs : BorderRankAtMost (A s) r)
    (μ : E → ℝ) (hμ : ∀ e, 0 ≤ μ e)
    (hcertificate : ∀ v, v ≠ t →
      (∑ e, if σ e = v then ((D e).volume : ℝ) * μ e else 0) -
      (∑ e, (∑ i : Fin (q e), if w e i = v then ((Dout e i).volume : ℝ) else 0) * μ e)
      ≤ if v = s then 1 else 0)
    (hL : (d : ℝ)⁻¹ <
      ∑ e, (∑ i : Fin (q e), if w e i = t then ((Dout e i).volume : ℝ) else 0) * μ e)
    : formalOmega F ≤ 3 * Real.log (r : ℝ) /
      (Real.log (d : ℝ) + Real.log
        (∑ e, (∑ i : Fin (q e), if w e i = t then ((Dout e i).volume : ℝ) else 0) * μ e)) :=
-- BEGIN APPROVED PROOF REGION
by
  exact BlockIdentities.Providers.identities_to_exponent (F := F) A hA q σ w D Dout identities
    s t hst hterminal d r hd hr ht hs μ hμ hcertificate hL
-- END APPROVED PROOF REGION

end BlockIdentities.Square
