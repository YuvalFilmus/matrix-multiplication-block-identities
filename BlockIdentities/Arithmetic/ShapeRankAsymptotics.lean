/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.ShapeRankLimits
public import BlockIdentities.Arithmetic.ShapeContinuity
public import BlockIdentities.Arithmetic.ShapeLimitScales

/-! Actual finite matrix coefficient ranks at varying logarithmic dimensions. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.Arithmetic
open Filter
open scoped NNReal Topology
variable {F : Type*} [Field F]

/-- Positive matrix dimensions force positive exact coefficient rank. -/
theorem one_le_exactRank_matrix {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    1 ≤ exactRank (matrixMultiplicationTensor (K := F) a b c) := by
  have hp := Square.matrix_rankAtMost_entry_counts
    (lt_of_lt_of_le Nat.zero_lt_one ha) (lt_of_lt_of_le Nat.zero_lt_one hb)
    (lt_of_lt_of_le Nat.zero_lt_one hc)
    (exactRank_spec (matrixMultiplicationTensor (K := F) a b c))
  exact (Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one ha)
    (lt_of_lt_of_le Nat.zero_lt_one hb)).trans_le hp.1

private theorem normalized_log_shape_le_log_rank {a b c R : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : Tensor.RankAtMost (matrixMultiplicationTensor (K := F) a b c) R)
    (s : ℝ) (hs : 0 < s) :
    formalShapeOmega F
      ⟨Real.log (a : ℝ) / s, div_nonneg (Real.log_nonneg (by exact_mod_cast ha)) hs.le⟩
      ⟨Real.log (b : ℝ) / s, div_nonneg (Real.log_nonneg (by exact_mod_cast hb)) hs.le⟩
      ⟨Real.log (c : ℝ) / s, div_nonneg (Real.log_nonneg (by exact_mod_cast hc)) hs.le⟩ ≤
        Real.log (R : ℝ) / s := by
  let la : ℝ≥0 := ⟨Real.log (a : ℝ), Real.log_nonneg (by exact_mod_cast ha)⟩
  let lb : ℝ≥0 := ⟨Real.log (b : ℝ), Real.log_nonneg (by exact_mod_cast hb)⟩
  let lc : ℝ≥0 := ⟨Real.log (c : ℝ), Real.log_nonneg (by exact_mod_cast hc)⟩
  let t : ℝ≥0 := ⟨1 / s, by positivity⟩
  let baseLog (q : ℕ) (hq : 1 ≤ q) : ℝ≥0 :=
    ⟨Real.log (q : ℝ), Real.log_nonneg (by exact_mod_cast hq)⟩
  let normalizedLog (q : ℕ) (hq : 1 ≤ q) : ℝ≥0 :=
    ⟨Real.log (q : ℝ) / s, div_nonneg (Real.log_nonneg (by exact_mod_cast hq)) hs.le⟩
  have he (q : ℕ) (hq : 1 ≤ q) : t * baseLog q hq = normalizedLog q hq := by
    apply NNReal.coe_injective
    change (1 / s) * Real.log (q : ℝ) = Real.log (q : ℝ) / s
    ring
  have hl := formalShapeOmega_log_dimensions_le_log_rank ha hb hc h
  change formalShapeOmega F la lb lc ≤ Real.log (R : ℝ) at hl
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ (t : ℝ) from t.property)
  rw [← formalShapeOmega_mul t la lb lc] at hm
  have hea := he a ha
  have heb := he b hb
  have hec := he c hc
  change t * la = _ at hea
  change t * lb = _ at heb
  change t * lc = _ at hec
  rw [hea, heb, hec] at hm
  have hr : (t : ℝ) * Real.log (R : ℝ) = Real.log (R : ℝ) / s := by
    change (1 / s) * Real.log (R : ℝ) = Real.log (R : ℝ) / s
    ring
  exact hm.trans_eq hr

/-- Every positive slack gives an eventual upper bound for the actual finite
rank rate. The common integer seed scale and all coordinate padding are produced. -/
theorem eventually_log_exactRank_matrix_lt
    (α β γ : ℝ≥0) (a b c : ℕ → ℕ)
    (ha : ∀ j, 1 ≤ a j) (hb : ∀ j, 1 ≤ b j) (hc : ∀ j, 1 ≤ c j)
    (hα : Tendsto (fun j => Real.log (a j : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 (α : ℝ)))
    (hβ : Tendsto (fun j => Real.log (b j : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 (β : ℝ)))
    (hγ : Tendsto (fun j => Real.log (c j : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 (γ : ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop,
      Real.log (exactRank (matrixMultiplicationTensor (K := F) (a j) (b j) (c j)) : ℝ) /
        ((j : ℝ) + 1) < formalShapeOmega F α β γ + ε := by
  let δ : ℝ := ε / 8
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  let d : ℝ≥0 := ⟨δ, hδ.le⟩
  let τ : ℝ := formalShapeOmega F (α + d) (β + d) (γ + d) + δ
  have hτbound : τ < formalShapeOmega F α β γ + ε := by
    have hs := formalShapeOmega_add_le (F := F) α β γ d d d
    have hn := formalShapeOmega_le_naive (F := F) d d d
    change formalShapeOmega F d d d ≤ δ + δ + δ at hn
    dsimp only [τ]
    dsimp only [δ] at hs hn ⊢
    linarith
  obtain ⟨N0, hN0, hseeds⟩ :=
    formalShapeOmega_eventually_rank_seed (F := F) (α + d) (β + d) (γ + d) δ hδ
  have hscale : ∀ᶠ j : ℕ in atTop, N0 ≤ ⌈Real.exp ((j : ℝ) + 1)⌉₊ :=
    tendsto_ceil_exp_nat_atTop.eventually (eventually_ge_atTop N0)
  have hea : ∀ᶠ j : ℕ in atTop, Real.log (a j : ℝ) / ((j : ℝ) + 1) < (α : ℝ) + δ :=
    hα.eventually (eventually_lt_nhds (by linarith))
  have heb : ∀ᶠ j : ℕ in atTop, Real.log (b j : ℝ) / ((j : ℝ) + 1) < (β : ℝ) + δ :=
    hβ.eventually (eventually_lt_nhds (by linarith))
  have hec : ∀ᶠ j : ℕ in atTop, Real.log (c j : ℝ) / ((j : ℝ) + 1) < (γ : ℝ) + δ :=
    hγ.eventually (eventually_lt_nhds (by linarith))
  have hlim : Tendsto (fun j : ℕ => τ *
      (Real.log (⌈Real.exp ((j : ℝ) + 1)⌉₊ : ℝ) / ((j : ℝ) + 1))) atTop (𝓝 τ) := by
    simpa only [mul_one] using tendsto_log_ceil_exp_nat_div.const_mul τ
  have hτevent := hlim.eventually (eventually_lt_nhds hτbound)
  filter_upwards [hscale, hea, heb, hec, hτevent] with j hj hja hjb hjc hjτ
  have hx : 0 < (j : ℝ) + 1 := by positivity
  let N : ℕ := ⌈Real.exp ((j : ℝ) + 1)⌉₊
  have hna : a j ≤ innerSize N (α + d) :=
    le_innerSize_ceil_exp_of_log_div_le (ha j) hx (α + d) (by change _ ≤ _ + δ; exact hja.le)
  have hnb : b j ≤ innerSize N (β + d) :=
    le_innerSize_ceil_exp_of_log_div_le (hb j) hx (β + d) (by change _ ≤ _ + δ; exact hjb.le)
  have hnc : c j ≤ innerSize N (γ + d) :=
    le_innerSize_ceil_exp_of_log_div_le (hc j) hx (γ + d) (by change _ ≤ _ + δ; exact hjc.le)
  obtain ⟨R, hRank, hR⟩ := hseeds N hj
  have hsmall := rectangular_matrix_rankAtMost_mono hna hnb hnc hRank
  have hrank := exactRank_le hsmall
  have hrpos : 0 < (exactRank
      (matrixMultiplicationTensor (K := F) (a j) (b j) (c j)) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_exactRank_matrix (F := F) (ha j) (hb j) (hc j)))
  have hrankreal : (exactRank
      (matrixMultiplicationTensor (K := F) (a j) (b j) (c j)) : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hrank
  have hupper : (exactRank
      (matrixMultiplicationTensor (K := F) (a j) (b j) (c j)) : ℝ) ≤ (N : ℝ) ^ τ :=
    hrankreal.trans hR
  have hlog := Real.log_le_log hrpos hupper
  have hNpos : 0 < (N : ℝ) := by
    change 0 < (⌈Real.exp ((j : ℝ) + 1)⌉₊ : ℝ)
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_ceil_exp_nat j))
  rw [Real.log_rpow hNpos] at hlog
  calc
    _ ≤ (τ * Real.log (N : ℝ)) / ((j : ℝ) + 1) :=
      div_le_div_of_nonneg_right hlog hx.le
    _ = τ * (Real.log (N : ℝ) / ((j : ℝ) + 1)) := by ring
    _ < _ := hjτ

/-- Exact finite coefficient rank has the actual formal shape rate for arbitrary
varying positive dimensions, including directions on the boundary of the cone. -/
theorem tendsto_log_exactRank_matrix_of_log_dimensions
    (α β γ : ℝ≥0) (a b c : ℕ → ℕ)
    (ha : ∀ j, 1 ≤ a j) (hb : ∀ j, 1 ≤ b j) (hc : ∀ j, 1 ≤ c j)
    (hα : Tendsto (fun j => Real.log (a j : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 (α : ℝ)))
    (hβ : Tendsto (fun j => Real.log (b j : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 (β : ℝ)))
    (hγ : Tendsto (fun j => Real.log (c j : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 (γ : ℝ))) :
    Tendsto (fun j => Real.log (exactRank
      (matrixMultiplicationTensor (K := F) (a j) (b j) (c j)) : ℝ) / ((j : ℝ) + 1))
      atTop (𝓝 (formalShapeOmega F α β γ)) := by
  let A : ℕ → ℝ≥0 := fun j => ⟨Real.log (a j : ℝ) / ((j : ℝ) + 1),
    div_nonneg (Real.log_nonneg (by exact_mod_cast ha j)) (by positivity)⟩
  let B : ℕ → ℝ≥0 := fun j => ⟨Real.log (b j : ℝ) / ((j : ℝ) + 1),
    div_nonneg (Real.log_nonneg (by exact_mod_cast hb j)) (by positivity)⟩
  let C : ℕ → ℝ≥0 := fun j => ⟨Real.log (c j : ℝ) / ((j : ℝ) + 1),
    div_nonneg (Real.log_nonneg (by exact_mod_cast hc j)) (by positivity)⟩
  have hlower : Tendsto (fun j => formalShapeOmega F (A j) (B j) (C j)) atTop
      (𝓝 (formalShapeOmega F α β γ)) := tendsto_formalShapeOmega hα hβ hγ
  have hpoint (j : ℕ) : formalShapeOmega F (A j) (B j) (C j) ≤
      Real.log (exactRank
        (matrixMultiplicationTensor (K := F) (a j) (b j) (c j)) : ℝ) / ((j : ℝ) + 1) :=
    normalized_log_shape_le_log_rank (ha j) (hb j) (hc j)
      (exactRank_spec (matrixMultiplicationTensor (K := F) (a j) (b j) (c j)))
      ((j : ℝ) + 1) (by positivity)
  apply tendsto_order.mpr
  constructor
  · intro l hl
    filter_upwards [hlower.eventually (eventually_gt_nhds hl)] with j hj
    exact hj.trans_le (hpoint j)
  · intro u hu
    have he := eventually_log_exactRank_matrix_lt (F := F) α β γ a b c ha hb hc hα hβ hγ
      (u - formalShapeOmega F α β γ) (sub_pos.mpr hu)
    have hid : formalShapeOmega F α β γ + (u - formalShapeOmega F α β γ) = u := by ring
    simpa only [hid] using he
end BlockIdentities.Arithmetic
