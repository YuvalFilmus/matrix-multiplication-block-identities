/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Frozen.shared_leg_value_inequality_v2
public import BlockIdentities.Frozen.formalOmega_eq_algebraicClosure_v2
public import BlockIdentities.Tensor.ValueBorderRank
public import BlockIdentities.Tensor.ValueMatrices
public import BlockIdentities.Square.CertificateMultiplicity
public import BlockIdentities.Square.ExponentCriterionNumerics

/-! The exact finite certificate criterion, consumed at actual tensor values. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Providers
open BlockIdentities.Square BlockIdentities.Arithmetic
open scoped BigOperators

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
by
  classical
  let K := AlgebraicClosure F
  let T : V → NonzeroTensor K := fun v => ⟨A v, hA v⟩
  let x : V → ℝ := fun v => normalizedValueAtOmega (T v)
  let cost : E → ℝ := fun e => ((D e).volume : ℝ)
  let multiplicity : E → V → ℝ := fun e v =>
    ∑ i : Fin (q e), if w e i = v then ((Dout e i).volume : ℝ) else 0
  have hν : 0 < formalOmega K := by
    have h := formalOmega_mem_Icc (F := K)
    linarith [h.1]
  have hx (v : V) : 0 ≤ x v := by
    exact Real.rpow_nonneg
      (le_trans zero_le_one (one_le_value (T v) ⟨_, formalOmega_mem_Icc (F := K)⟩)) _
  have hxt : x t = (d : ℝ) :=
    normalizedValueAtOmega_terminal (T t) d (by omega) ht
  have hxs : x s ≤ (r : ℝ) ^ (3 / formalOmega K) :=
    normalizedValueAtOmega_le_of_borderRankAtMost (T s) r hr hs
  have hrows (e : E) : ∑ v, multiplicity e v * x v ≤ cost e * x (σ e) := by
    have hi := shared_leg_value_inequality (T (σ e)) (fun i => T (w e i))
      (D e) (Dout e) (identities e)
    change (∑ v, (∑ i : Fin (q e), if w e i = v then ((Dout e i).volume : ℝ) else 0) *
      x v) ≤ cost e * x (σ e)
    rw [sum_multiplicity_mul]
    exact hi
  have hcert (v : V) (hvt : v ≠ t) :
      certificateResidual σ cost μ multiplicity v ≤ if v = s then 1 else 0 := by
    exact hcertificate v hvt
  have hout := exponent_le_of_certificate_values s t hst σ cost μ multiplicity hterminal hμ
    x hx d r hd hr (formalOmega K) hν hxt hxs hrows hcert hL
  rw [formalOmega_eq_algebraicClosure F]
  exact hout

end BlockIdentities.Providers
