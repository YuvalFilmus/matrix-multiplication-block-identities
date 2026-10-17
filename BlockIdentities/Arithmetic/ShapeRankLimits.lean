/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.ShapeRankSeeds
public import BlockIdentities.Arithmetic.ShapeHomogeneity

/-! Finite coefficient rank comparisons for logarithmic shape limits. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Arithmetic
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped NNReal
variable {F : Type*} [Field F]

/-- Selecting initial index segments is an actual coefficient restriction. -/
theorem rectangular_matrix_rankAtMost_mono {a b c A B C R : ℕ}
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (h : Tensor.RankAtMost (matrixMultiplicationTensor (K := F) A B C) R) :
    Tensor.RankAtMost (matrixMultiplicationTensor (K := F) a b c) R := by
  have hr := h.pullback
    (fun x : Fin a × Fin b => (Fin.castLE ha x.1, Fin.castLE hb x.2))
    (fun y : Fin b × Fin c => (Fin.castLE hb y.1, Fin.castLE hc y.2))
    (fun z : Fin c × Fin a => (Fin.castLE hc z.1, Fin.castLE ha z.2))
  have heq : Tensor.pullback
      (fun x : Fin a × Fin b => (Fin.castLE ha x.1, Fin.castLE hb x.2))
      (fun y : Fin b × Fin c => (Fin.castLE hb y.1, Fin.castLE hc y.2))
      (fun z : Fin c × Fin a => (Fin.castLE hc z.1, Fin.castLE ha z.2))
      (matrixMultiplicationTensor (K := F) A B C) = matrixMultiplicationTensor a b c := by
    funext x y z
    simp only [Tensor.pullback, matrixMultiplicationTensor, Fin.castLE_inj]
  rw [heq] at hr
  exact hr

/-- A genuine finite matrix rank seed bounds the actual shape exponent at its
natural logarithmic dimensions, without a rank-asymptotics premise. -/
theorem formalShapeOmega_log_dimensions_le_log_rank {a b c R : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : Tensor.RankAtMost (matrixMultiplicationTensor (K := F) a b c) R) :
    formalShapeOmega F
      ⟨Real.log (a : ℝ), Real.log_nonneg (by exact_mod_cast ha)⟩
      ⟨Real.log (b : ℝ), Real.log_nonneg (by exact_mod_cast hb)⟩
      ⟨Real.log (c : ℝ), Real.log_nonneg (by exact_mod_cast hc)⟩ ≤ Real.log (R : ℝ) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hapos : 0 < a := lt_of_lt_of_le Nat.zero_lt_one ha
  have hbpos : 0 < b := lt_of_lt_of_le Nat.zero_lt_one hb
  have hcpos : 0 < c := lt_of_lt_of_le Nat.zero_lt_one hc
  have hR : 1 ≤ R :=
    (Nat.mul_pos hapos hbpos).trans_le (Square.matrix_rankAtMost_entry_counts hapos hbpos hcpos h).1
  let α : ℝ≥0 := ⟨Real.log (a : ℝ) / Real.log 2,
    div_nonneg (Real.log_nonneg (by exact_mod_cast ha)) htwo.le⟩
  let β : ℝ≥0 := ⟨Real.log (b : ℝ) / Real.log 2,
    div_nonneg (Real.log_nonneg (by exact_mod_cast hb)) htwo.le⟩
  let γ : ℝ≥0 := ⟨Real.log (c : ℝ) / Real.log 2,
    div_nonneg (Real.log_nonneg (by exact_mod_cast hc)) htwo.le⟩
  have hpow (q : ℕ) (hq : 1 ≤ q) :
      (2 : ℝ) ^ (Real.log (q : ℝ) / Real.log 2) = (q : ℝ) := by
    rw [Real.log_div_log]
    exact Real.rpow_logb (by norm_num) (by norm_num)
      (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq))
  have hseed : formalShapeOmega F α β γ ≤ Real.log (R : ℝ) / Real.log 2 := by
    apply formalShapeOmega_le_of_rank_seed (by decide : 2 ≤ (2 : ℕ)) hapos hbpos hcpos h
    · exact (hpow a ha).le
    · exact (hpow b hb).le
    · exact (hpow c hc).le
    · exact (hpow R hR).symm.le
  let t : ℝ≥0 := ⟨Real.log 2, htwo.le⟩
  let la : ℝ≥0 := ⟨Real.log (a : ℝ), Real.log_nonneg (by exact_mod_cast ha)⟩
  let lb : ℝ≥0 := ⟨Real.log (b : ℝ), Real.log_nonneg (by exact_mod_cast hb)⟩
  let lc : ℝ≥0 := ⟨Real.log (c : ℝ), Real.log_nonneg (by exact_mod_cast hc)⟩
  have hα : t * α = la := by
    apply NNReal.coe_injective
    change Real.log 2 * (Real.log (a : ℝ) / Real.log 2) = Real.log (a : ℝ)
    field_simp [ne_of_gt htwo]
  have hβ : t * β = lb := by
    apply NNReal.coe_injective
    change Real.log 2 * (Real.log (b : ℝ) / Real.log 2) = Real.log (b : ℝ)
    field_simp [ne_of_gt htwo]
  have hγ : t * γ = lc := by
    apply NNReal.coe_injective
    change Real.log 2 * (Real.log (c : ℝ) / Real.log 2) = Real.log (c : ℝ)
    field_simp [ne_of_gt htwo]
  have hm := mul_le_mul_of_nonneg_left hseed htwo.le
  change (t : ℝ) * formalShapeOmega F α β γ ≤ _ at hm
  rw [← formalShapeOmega_mul t α β γ] at hm
  rw [hα, hβ, hγ] at hm
  have hright : Real.log 2 * (Real.log (R : ℝ) / Real.log 2) = Real.log (R : ℝ) := by
    field_simp [ne_of_gt htwo]
  exact hm.trans_eq hright
end BlockIdentities.Arithmetic
