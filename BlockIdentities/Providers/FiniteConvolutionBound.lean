/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ConvolutionValueRows
public import BlockIdentities.Square.RankPowerComparison
public import BlockIdentities.Square.Limit
public import BlockIdentities.Frozen.formalOmega_eq_algebraicClosure_v2

/-! The manuscript's explicit row certificate at actual convolution values. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Providers
open BlockIdentities.Square BlockIdentities.Arithmetic
open scoped BigOperators

theorem finite_convolution_bound (F : Type*) [Field F] (a : ℕ) (ha : 2 ≤ a) :
    formalOmega F ≤ 3 * Real.log (2 * (a : ℝ) - 1) /
      (Real.log 2 + Real.log (((3 * (a : ℝ) - 1) / 4) *
        ∏ j ∈ Finset.Icc 1 (a - 1), (1 + 1 / (3 * (j : ℝ))))) := by
  let K := AlgebraicClosure F
  let A : ℕ+ := ⟨a, by omega⟩
  have hl := convolution_normalized_diagonal_lower (K := K) a ha
  have hu := convolutionNormalizedValue_diagonal_upper (K := K) A
  change normalizedValueAtOmega (nonzeroConvolution (K := K) A A) ≤
    ((2 * a - 1 : ℕ) : ℝ) ^ (3 / formalOmega K) at hu
  have hcast : ((2 * a - 1 : ℕ) : ℝ) = 2 * (a : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * a)]
    norm_num
  have hbound : convolutionYield ⟨a, ha⟩ * 2 ≤
      (2 * (a : ℝ) - 1) ^ (3 / formalOmega K) := by
    rw [hcast] at hu
    have hl' : convolutionYield ⟨a, ha⟩ * 2 ≤
        normalizedValueAtOmega (nonzeroConvolution (K := K) A A) := by
      simpa only [mul_comm] using hl
    exact hl'.trans hu
  have hν : 0 < formalOmega K := by
    have h := formalOmega_mem_Icc (F := K)
    linarith [h.1]
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hL : (2 : ℝ)⁻¹ < convolutionYield ⟨a, ha⟩ := by
    simpa only [one_div] using convolutionYield_gt_half ⟨a, ha⟩
  have hout := exponent_le_of_rank_power_bound (formalOmega K) 2
    (2 * (a : ℝ) - 1) (convolutionYield ⟨a, ha⟩) hν (by norm_num)
    (by linarith) hL hbound
  have hy : convolutionYield ⟨a, ha⟩ = ((3 * (a : ℝ) - 1) / 4) *
      ∏ j ∈ Finset.Icc 1 (a - 1), (1 + 1 / (3 * (j : ℝ))) := by
    unfold convolutionYield
    congr 1
  rw [hy] at hout
  rw [formalOmega_eq_algebraicClosure F]
  exact hout

end BlockIdentities.Providers
