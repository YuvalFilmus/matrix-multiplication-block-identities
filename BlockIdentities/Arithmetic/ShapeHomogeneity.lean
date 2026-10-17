/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.ShapeMonotonicity

/-! Integer changes of size parameter preserve the actual formal shape exponent. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Arithmetic
open scoped NNReal
variable {F : Type*} [Field F]

private theorem innerSize_mul_le (n : ℕ) (_hn : 1 ≤ n) (t a : ℝ≥0) :
    innerSize n ((t * a : ℝ≥0) : ℝ) ≤ innerSize (innerSize n t) a := by
  apply Nat.ceil_mono
  simp only [NNReal.coe_mul]
  change (n : ℝ) ^ ((t : ℝ) * a) ≤ (innerSize n t : ℝ) ^ (a : ℝ)
  rw [Real.rpow_mul (Nat.cast_nonneg n)]
  exact Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (Nat.le_ceil _) a.property

/-- A genuine rounded integer size change; the coefficient constant stays uniform. -/
theorem FormalShapeAdmissibleExponent.scale {a b c : ℝ≥0} {τ : ℝ}
    (h : FormalShapeAdmissibleExponent F a b c τ) (t : ℝ≥0) :
    FormalShapeAdmissibleExponent F (t * a) (t * b) (t * c) ((t : ℝ) * τ) := by
  by_cases ht : t = 0
  · subst t
    simpa using
      (formalShapeAdmissibleExponent_naive (F := F) 0 0 0)
  have htpos : 0 < (t : ℝ) := by
    have htReal : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    exact lt_of_le_of_ne t.property (Ne.symm htReal)
  have hτ : 0 ≤ τ :=
    (add_nonneg a.property c.property).trans (formalShapeAdmissibleExponent_output_le h)
  intro ε hε
  let δ : ℝ := ε / (t : ℝ)
  have hδ : 0 < δ := div_pos hε htpos
  obtain ⟨R, hR, hcost⟩ := h δ hδ
  let γ : ℝ := τ + δ
  have hγ : 0 ≤ γ := add_nonneg hτ hδ.le
  refine ⟨R * (2 : ℝ) ^ γ, mul_pos hR (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro n hn
  let m := innerSize n t
  have hm : 1 ≤ m := one_le_innerSize hn t
  obtain ⟨P, hP, hp⟩ := hcost m hm
  let ia := innerSize_mul_le n hn t a
  let ib := innerSize_mul_le n hn t b
  let ic := innerSize_mul_le n hn t c
  refine ⟨P.pad ia ib ic, hP.pad ia ib ic, ?_⟩
  rw [MatrixAlgorithm.pad_cost_eq]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hmp : (m : ℝ) ≤ 2 * (n : ℝ) ^ (t : ℝ) := innerSize_cast_le hn t.property
  calc
    (P.cost : ℝ) ≤ R * (m : ℝ) ^ γ := hp
    _ ≤ R * (2 * (n : ℝ) ^ (t : ℝ)) ^ γ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hmp hγ) hR.le
    _ = (R * (2 : ℝ) ^ γ) * (n : ℝ) ^ ((t : ℝ) * τ + ε) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (Real.rpow_nonneg hnpos.le _), ← Real.rpow_mul hnpos.le]
      have he : (t : ℝ) * γ = (t : ℝ) * τ + ε := by
        dsimp only [γ, δ]
        field_simp [ne_of_gt htpos]
      rw [he]
      ring

theorem formalShapeOmega_scale_le (t a b c : ℝ≥0) :
    formalShapeOmega F (t * a) (t * b) (t * c) ≤
      (t : ℝ) * formalShapeOmega F a b c :=
  csInf_le (formalShapeAdmissibleExponent_bddBelow _ _ _)
    ((formalShapeAdmissibleExponent_formalShapeOmega (F := F) a b c).scale t)

/-- Positive homogeneity, including its genuine all-zero endpoint. -/
theorem formalShapeOmega_mul (t a b c : ℝ≥0) :
    formalShapeOmega F (t * a) (t * b) (t * c) =
      (t : ℝ) * formalShapeOmega F a b c := by
  apply le_antisymm (formalShapeOmega_scale_le t a b c)
  by_cases ht : t = 0
  · subst t
    simp only [zero_mul, NNReal.coe_zero, formalShapeOmega_zero_zero_zero, le_refl]
  have htpos : 0 < (t : ℝ) := by
    have htReal : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    exact lt_of_le_of_ne t.property (Ne.symm htReal)
  have hrev := formalShapeOmega_scale_le (F := F) t⁻¹ (t * a) (t * b) (t * c)
  simp only [← mul_assoc, inv_mul_cancel₀ ht, one_mul, NNReal.coe_inv] at hrev
  have hm := mul_le_mul_of_nonneg_left hrev htpos.le
  simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt htpos), one_mul] using hm
end BlockIdentities.Arithmetic
