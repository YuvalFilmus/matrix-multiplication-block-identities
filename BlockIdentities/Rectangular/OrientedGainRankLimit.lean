/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedGainRankBound
public import BlockIdentities.Rectangular.OrientedGainBasics

/-! Closing the actual large-auxiliary comparison by logarithmic limits. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open Filter
open BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped Topology NNReal BigOperators
variable {F : Type*} [Field F]

/-- Each literal oriented extraction gain is bounded by the actual asymptotic
rank. All auxiliary matrices and finite rank budgets are constructed. -/
theorem orientedGain_le_tensorAsymptoticRank (S : InteriorSupport F) (T : TensorOf F)
    {n h : ℕ} (hn : 1 ≤ n) (hh : 1 ≤ h) (D E : MatrixShape)
    (hconv : AsymptoticallyRestricts (product (power T.val n) D.tensor) (copies h E.tensor)) :
    ((h : ℝ) * matrixWeight S E / matrixWeight S D) ^ (1 / (n : ℝ)) ≤
      tensorAsymptoticRank T := by
  obtain ⟨L, hLpos, hLstrict⟩ := exists_auxiliary_scale S D
  have hL (i : Axis) := (hLstrict i).le
  let l : ℝ≥0 := ⟨L, hLpos.le⟩
  let r : ℝ := tensorAsymptoticRank T
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one (one_le_tensorAsymptoticRank T)
  have hWpos := interiorSupport_exponent_pos S
  obtain ⟨a, ha, harate, hfinite⟩ := repeated_gain_log_bound S T hconv
  have hshift : Tendsto (fun j : ℕ => j + 1) atTop atTop :=
    tendsto_atTop_mono (fun j : ℕ => Nat.le_succ j)
      (tendsto_id : Tendsto (fun j : ℕ => j) atTop atTop)
  have harate' : Tendsto (fun j : ℕ => Real.log (a (j + 1) : ℝ) / ((j : ℝ) + 1))
      atTop (𝓝 0) := by
    have hx := harate.comp hshift
    change Tendsto (fun j : ℕ => Real.log (a (j + 1) : ℝ) / ((j + 1 : ℕ) : ℝ))
      atTop (𝓝 0) at hx
    simpa only [Nat.cast_add, Nat.cast_one] using hx
  have hslack (ε : ℝ) (hε : 0 < ε) :
      diagonalSupplyScale S h ε * orientedExponent F S.direction +
        Real.log (matrixWeight S E) - Real.log (matrixWeight S D) ≤
          (n : ℝ) * Real.log r := by
    let P : ℕ → MatrixShape := auxiliaryPaddingShape S D L hL
    let Q : ℕ → MatrixShape := diagonalSupplyShape S h hh ε hε
    let B : ℕ → MatrixShape := fun j => (D.power (j + 1)).product (P j)
    let O : ℕ → MatrixShape := gainOutputShape S D E L hL h hh ε hε
    have hBraw (j : ℕ) : exactRank ((B j).tensor (K := AlgebraicClosure F)).coeff =
        exactRank (matrixMultiplicationTensor (K := AlgebraicClosure F)
          (D.a ^ (j + 1) * auxiliaryPadding (L * (S.direction 1 : ℝ) - Real.log (D.a : ℝ)) j)
          (D.b ^ (j + 1) * auxiliaryPadding (L * (S.direction 2 : ℝ) - Real.log (D.b : ℝ)) j)
          (D.c ^ (j + 1) * auxiliaryPadding (L * (S.direction 0 : ℝ) - Real.log (D.c : ℝ)) j)) := by
      exact exactRank_ofTensor _
    have hBrate : Tendsto (fun j : ℕ => Real.log
        (exactRank ((B j).tensor (K := AlgebraicClosure F)).coeff : ℝ) / ((j : ℝ) + 1))
        atTop (𝓝 (L * orientedExponent F S.direction)) := by
      simp_rw [hBraw]
      exact auxiliary_matrix_rank_log_rate S D l hL
    have hupper : Tendsto (fun j : ℕ => Real.log (a (j + 1) : ℝ) / ((j : ℝ) + 1) +
        (n : ℝ) * Real.log r + Real.log
          (exactRank ((B j).tensor (K := AlgebraicClosure F)).coeff : ℝ) / ((j : ℝ) + 1))
        atTop (𝓝 ((n : ℝ) * Real.log r + L * orientedExponent F S.direction)) := by
      simpa only [zero_add] using (harate'.add_const ((n : ℝ) * Real.log r)).add hBrate
    let u : Axis → ℝ := fun i => (L + diagonalSupplyScale S h ε) * (S.direction i : ℝ) +
      logDotDimensions E i - logDotDimensions D i
    have hOrate := matrixWeight_log_rate S O u
      (gainOutputShape_log_dimension_rate S D E L hL h hh ε hε)
    have htouch : S.weight 1 * (S.direction 1 : ℝ) + S.weight 2 * (S.direction 2 : ℝ) +
        S.weight 0 * (S.direction 0 : ℝ) = orientedExponent F S.direction := by
      have ht := S.touching
      simp only [Fin.sum_univ_succ] at ht
      change S.weight 0 * (S.direction 0 : ℝ) +
        (S.weight 1 * (S.direction 1 : ℝ) + (S.weight 2 * (S.direction 2 : ℝ) + 0)) =
          orientedExponent F S.direction at ht
      linarith only [ht]
    have htarget : S.weight 1 * u 1 + S.weight 2 * u 2 + S.weight 0 * u 0 =
        (L + diagonalSupplyScale S h ε) * orientedExponent F S.direction +
          Real.log (matrixWeight S E) - Real.log (matrixWeight S D) := by
      rw [← htouch, log_matrixWeight, log_matrixWeight]
      simp [u, Fin.sum_univ_succ]
      ring
    rw [htarget] at hOrate
    have hevent := eventually_diagonalSupply_degeneration S hh hε
    have hineq : ∀ᶠ j : ℕ in atTop,
        Real.log (matrixWeight S (O j)) / ((j : ℝ) + 1) ≤
          Real.log (a (j + 1) : ℝ) / ((j : ℝ) + 1) + (n : ℝ) * Real.log r +
            Real.log (exactRank ((B j).tensor (K := AlgebraicClosure F)).coeff : ℝ) /
              ((j : ℝ) + 1) := by
      filter_upwards [hevent] with j hj
      have hx := hfinite (j + 1) (by omega) (P j) (Q j) hj
      change Real.log (matrixWeight S (O j)) / ((j + 1 : ℕ) : ℝ) ≤
        Real.log (a (j + 1) : ℝ) / ((j + 1 : ℕ) : ℝ) + (n : ℝ) * Real.log r +
          Real.log (exactRank ((B j).tensor (K := AlgebraicClosure F)).coeff : ℝ) /
            ((j + 1 : ℕ) : ℝ) at hx
      simpa only [Nat.cast_add, Nat.cast_one] using hx
    have hlim := le_of_tendsto_of_tendsto hOrate hupper hineq
    nlinarith
  have htlim : Tendsto (fun ε : ℝ => diagonalSupplyScale S h ε * orientedExponent F S.direction)
      (𝓝[>] 0) (𝓝 (Real.log (h : ℝ))) := by
    have hden : Tendsto (fun ε : ℝ => orientedExponent F S.direction + ε)
        (𝓝[>] 0) (𝓝 (orientedExponent F S.direction)) := by
      have hc : Tendsto (fun _ : ℝ => orientedExponent F S.direction)
          (𝓝[>] 0) (𝓝 (orientedExponent F S.direction)) := tendsto_const_nhds
      have hi : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left inf_le_left
      simpa only [add_zero] using hc.add hi
    have hc : Tendsto (fun _ : ℝ => Real.log (h : ℝ)) (𝓝[>] 0)
        (𝓝 (Real.log (h : ℝ))) := tendsto_const_nhds
    have hx := (hc.div hden hWpos.ne').mul_const (orientedExponent F S.direction)
    simpa [diagonalSupplyScale, hWpos.ne'] using hx
  have hlog : Real.log (h : ℝ) + Real.log (matrixWeight S E) - Real.log (matrixWeight S D) ≤
      (n : ℝ) * Real.log r := by
    apply le_of_tendsto_of_tendsto
      ((htlim.add_const (Real.log (matrixWeight S E))).sub_const (Real.log (matrixWeight S D)))
      tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hslack ε hε
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hgpos : 0 < (h : ℝ) * matrixWeight S E / matrixWeight S D :=
    div_pos (mul_pos hhpos (matrixWeight_pos S E)) (matrixWeight_pos S D)
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hgpos _) hrpos).mp
  rw [Real.log_rpow hgpos, Real.log_div (mul_pos hhpos (matrixWeight_pos S E)).ne'
    (matrixWeight_pos S D).ne', Real.log_mul hhpos.ne' (matrixWeight_pos S E).ne']
  have hx := div_le_div_of_nonneg_right hlog hnpos.le
  convert hx using 1 <;> field_simp [hnpos.ne'] <;> ring

theorem orientedGains_bddAbove (S : InteriorSupport F) (T : TensorOf F) :
    BddAbove (orientedGains S T) := by
  refine ⟨tensorAsymptoticRank T, ?_⟩
  rintro v ⟨n, h, hn, hh, D, E, hconv, rfl⟩
  exact orientedGain_le_tensorAsymptoticRank S T hn hh D E hconv

theorem orientedValue_le_tensorAsymptoticRank (S : InteriorSupport F) (T : TensorOf F) :
    orientedValue S T ≤ tensorAsymptoticRank T := by
  apply csSup_le (orientedGains_nonempty S T)
  rintro v ⟨n, h, hn, hh, D, E, hconv, rfl⟩
  exact orientedGain_le_tensorAsymptoticRank S T hn hh D E hconv

theorem one_le_orientedValue (S : InteriorSupport F) (T : TensorOf F) :
    1 ≤ orientedValue S T :=
  le_csSup (orientedGains_bddAbove S T) (one_mem_orientedGains S T)

end BlockIdentities.Rectangular
