/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.ShapeBasics
public import BlockIdentities.Arithmetic.FormalPadding

/-! Actual zero padding gives monotonicity of the formal shape exponent. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Arithmetic
open scoped NNReal
variable {F : Type*} [Field F]

theorem FormalShapeAdmissibleExponent.mono_shape {a b c A B C : ℝ≥0} {τ : ℝ}
    (h : FormalShapeAdmissibleExponent F A B C τ)
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) :
    FormalShapeAdmissibleExponent F a b c τ := by
  intro ε hε
  obtain ⟨R, hR, hcost⟩ := h ε hε
  refine ⟨R, hR, ?_⟩
  intro n hn
  obtain ⟨P, hP, hp⟩ := hcost n hn
  let ia := innerSize_mono hn (show (a : ℝ) ≤ A from ha)
  let ib := innerSize_mono hn (show (b : ℝ) ≤ B from hb)
  let ic := innerSize_mono hn (show (c : ℝ) ≤ C from hc)
  exact ⟨P.pad ia ib ic, hP.pad ia ib ic, by simpa only [MatrixAlgorithm.pad_cost_eq] using hp⟩

theorem formalShapeAdmissibleExponent_of_omega_le {a b c : ℝ≥0} {τ : ℝ}
    (h : formalShapeOmega F a b c ≤ τ) : FormalShapeAdmissibleExponent F a b c τ := by
  intro ε hε
  obtain ⟨R, hR, hcost⟩ := formalShapeAdmissibleExponent_formalShapeOmega (F := F) a b c ε hε
  refine ⟨R, hR, ?_⟩
  intro n hn
  obtain ⟨P, hP, hp⟩ := hcost n hn
  refine ⟨P, hP, hp.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hR.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith only [h])

theorem formalShapeOmega_mono {a b c A B C : ℝ≥0}
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) :
    formalShapeOmega F a b c ≤ formalShapeOmega F A B C :=
  csInf_le (formalShapeAdmissibleExponent_bddBelow a b c)
    ((formalShapeAdmissibleExponent_formalShapeOmega (F := F) A B C).mono_shape ha hb hc)
end BlockIdentities.Arithmetic
