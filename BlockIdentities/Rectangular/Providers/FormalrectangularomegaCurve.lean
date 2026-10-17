/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Frozen.formalShapeOmega_general_bound
public import BlockIdentities.Arithmetic.ShapeSymmetry
public import BlockIdentities.Arithmetic.RectangularBasics

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular.Providers
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem formalRectangularOmega_curve (F : Type*) [Field F] (k : ℝ) (hk : 0 ≤ k) :
  Arithmetic.formalRectangularOmega F k ≤ (if k ≤ (1 : ℝ) / 2 then 2 else 1 + k + 1 / (4 * k)) :=
by
  by_cases hk0 : k = 0
  · subst k
    rw [Arithmetic.formalRectangularOmega_zero]
    norm_num
  have hkpos : 0 < k := lt_of_le_of_ne hk (Ne.symm hk0)
  let K : ℝ≥0 := ⟨k, hk⟩
  have hK : (K : ℝ) = k := rfl
  have hKpos : 0 < K := by exact_mod_cast hkpos
  have hspecial : Arithmetic.formalShapeOmega F 1 K 1 =
      Arithmetic.formalRectangularOmega F k := by
    simpa only [hK] using (Arithmetic.formalShapeOmega_one_k_one (F := F) K)
  by_cases hk1 : k ≤ 1
  · have horder : K ≤ 1 := by exact_mod_cast hk1
    have H := BlockIdentities.Rectangular.formalShapeOmega_general_bound F 1 1 K le_rfl horder hKpos
    have hperm : Arithmetic.formalShapeOmega F 1 1 K =
        Arithmetic.formalRectangularOmega F k :=
      (Arithmetic.formalShapeOmega_cyclic (F := F) 1 1 K).symm.trans hspecial
    rw [hperm] at H
    norm_num only [NNReal.coe_one, hK, one_mul, mul_one, div_one] at H
    by_cases hhalf : k ≤ (1 : ℝ) / 2
    · simp only [if_pos hhalf] at H ⊢
      exact H
    · simp only [if_neg hhalf] at H ⊢
      convert H using 1 <;> field_simp [hkpos.ne'] <;> ring
  · have hkgt : 1 < k := lt_of_not_ge hk1
    have horder : (1 : ℝ≥0) ≤ K := by exact_mod_cast hkgt.le
    have H := BlockIdentities.Rectangular.formalShapeOmega_general_bound F K 1 1 horder le_rfl zero_lt_one
    have hperm : Arithmetic.formalShapeOmega F K 1 1 =
        Arithmetic.formalRectangularOmega F k :=
      (Arithmetic.formalShapeOmega_swap_first (F := F) 1 K 1).trans hspecial
    rw [hperm] at H
    norm_num only [NNReal.coe_one, hK, one_mul, mul_one, div_one] at H
    have hthreshold : ¬ (1 : ℝ) ≤ k / (k + 1) := by
      intro h
      have hd : 0 < k + 1 := by linarith only [hkpos]
      have hh := (le_div_iff₀ hd).mp h
      linarith only [hh]
    have hhalf : ¬ k ≤ (1 : ℝ) / 2 := by linarith only [hkgt]
    simp only [if_neg hthreshold] at H
    simp only [if_neg hhalf]
    convert H using 1 <;> field_simp [hkpos.ne'] <;> ring

end BlockIdentities.Rectangular.Providers
