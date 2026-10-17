/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ElementaryRestrictions
public import BlockIdentities.Tensor.ValueBounds
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Interpolation
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.FieldExtension
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega

/-! Fixed polynomial degeneration degrees disappear in the matrix-rank exponent. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped BigOperators Topology
variable {K : Type*} [Field K] [Infinite K]

private theorem diagonal_rankAtMost (R : ℕ) : Tensor.RankAtMost (diagonal (K := K) R).coeff R := by
  classical
  change Tensor.RankAtMost (fun i j k : Fin R => if i = j ∧ j = k then (1 : K) else 0) R
  refine ⟨(fun i x => if x = i then 1 else 0), (fun i y => if y = i then 1 else 0),
    (fun i z => if z = i then 1 else 0), ?_⟩
  funext x y z
  simp [diagonal, Tensor.rankOne, mul_ite, ite_and]
  split_ifs <;> simp_all

/-- The polynomial degree constant is selected once, before all tensor powers. -/
theorem Degenerates.exists_matrix_power_rank_bound {R m : ℕ}
    (h : Degenerates (diagonal (K := K) R) (square m)) :
    ∃ C : ℕ, ∀ n : ℕ, exactMatrixRank K (m ^ n) ≤ (C * n + 1) * R ^ n := by
  obtain ⟨k, Lx, Ly, Lz, ⟨D⟩⟩ := h
  refine ⟨Lx + Ly + Lz, ?_⟩
  intro n
  have hp := restrictionDegeneration_power_rankAtMost D (diagonal_rankAtMost R) n
  let e := Fintype.equivFin (Fin m × Fin m)
  let f : (Fin n → Fin m × Fin m) → (Fin n → Fin (square (K := K) m).nx) :=
    fun x j => e (x j)
  have hcoeff (x y z : Fin m × Fin m) :
      (square (K := K) m).coeff (e x) (e y) (e z) = matrixMultiplicationTensor m m m x y z := by
    change matrixMultiplicationTensor m m m (e.symm (e x)) (e.symm (e y)) (e.symm (e z)) = _
    rw [e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply]
  have hr := hp.pullback f f f
  have heq : Tensor.pullback f f f (Tensor.power (square (K := K) m).coeff n) =
      Tensor.power (matrixMultiplicationTensor (K := K) m m m) n := by
    funext x y z
    simp only [Tensor.pullback, Tensor.power, f, hcoeff]
  have hr' : Tensor.RankAtMost (Tensor.power (matrixMultiplicationTensor (K := K) m m m) n)
      (((Lx + Ly + Lz) * n + 1) * R ^ n) :=
    (congrArg (fun T : Tensor K (Fin n → Fin m × Fin m) (Fin n → Fin m × Fin m)
      (Fin n → Fin m × Fin m) => Tensor.RankAtMost T (((Lx + Ly + Lz) * n + 1) * R ^ n)) heq).mp hr
  exact exactRank_le (rankAtMost_matrixMultiplication_of_power hr')

private theorem log_linear_div_tendsto_zero (C : ℕ) :
    Tendsto (fun n : ℕ => Real.log ((C * n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hsucc := (Real.tendsto_log_nat_add_one_sub_log.div_atTop hnat).add hlog
  have hsucc' : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ =>
        (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) / (n : ℝ) +
          Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by simpa using hsucc
    apply hh.congr
    intro n
    ring
  have hu : Tendsto (fun n : ℕ =>
      (Real.log ((C : ℝ) + 1) + Real.log ((n : ℝ) + 1)) / (n : ℝ)) atTop (𝓝 0) := by
    have hc : Tendsto (fun n : ℕ => Real.log ((C : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hnat
    simpa only [zero_add, ← add_div] using hc.add hsucc'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun n => div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ C * n + 1 by omega))) (Nat.cast_nonneg n)
  · apply Eventually.of_forall
    intro n
    have hp : (0 : ℝ) < ((C * n + 1 : ℕ) : ℝ) := by positivity
    have hb : ((C * n + 1 : ℕ) : ℝ) ≤ ((C : ℝ) + 1) * ((n : ℝ) + 1) := by
      push_cast
      nlinarith [show (0 : ℝ) ≤ C from Nat.cast_nonneg C,
        show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    have hl := Real.log_le_log hp hb
    rw [Real.log_mul (by positivity) (by positivity)] at hl
    exact div_le_div_of_nonneg_right hl (Nat.cast_nonneg n)

/-- A genuine matrix degeneration from rank R bounds the true exact-rank exponent.
Interpolation is performed only after tensor powering, at the fixed map degrees. -/
theorem Degenerates.matrix_rpow_exactRankExponent_le {R m : ℕ} (hm : 1 ≤ m)
    (h : Degenerates (diagonal (K := K) R) (square m)) :
    (m : ℝ) ^ exactRankExponent K ≤ (R : ℝ) := by
  have hR : 1 ≤ R := by
    by_contra hn
    have hz : R = 0 := by omega
    subst R
    have hs := h.source_nonzero (nonzero_square hm)
    apply hs
    funext x y z
    exact Fin.elim0 x
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  let q := (m : ℝ) ^ exactRankExponent K
  have hq : 0 < q := Real.rpow_pos_of_pos hmpos _
  obtain ⟨C, hC⟩ := h.exists_matrix_power_rank_bound
  have hupper : ∀ n : ℕ, q ^ n ≤ ((C * n + 1 : ℕ) : ℝ) * (R : ℝ) ^ n := by
    intro n
    calc
      q ^ n = ((m ^ n : ℕ) : ℝ) ^ exactRankExponent K := by
        dsimp only [q]
        rw [Real.rpow_pow_comm (Nat.cast_nonneg m), Nat.cast_pow]
      _ ≤ (exactMatrixRank K (m ^ n) : ℝ) :=
        exactMatrixRank_rpow_lower_of_pos (pow_pos (lt_of_lt_of_le Nat.zero_lt_one hm) n)
      _ ≤ ((C * n + 1 : ℕ) : ℝ) * (R : ℝ) ^ n := by exact_mod_cast hC n
  have he : ∀ᶠ n : ℕ in atTop, Real.log q ≤
      Real.log ((C * n + 1 : ℕ) : ℝ) / (n : ℝ) + Real.log (R : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hl := Real.log_le_log (pow_pos hq n) (hupper n)
    rw [Real.log_pow, Real.log_mul (by positivity) (ne_of_gt (pow_pos hRpos n)), Real.log_pow] at hl
    have hd := div_le_div_of_nonneg_right hl hnpos.le
    change Real.log q ≤ _
    convert hd using 1 <;> field_simp [ne_of_gt hnpos] <;> ring
  have hlim : Tendsto (fun n : ℕ => Real.log ((C * n + 1 : ℕ) : ℝ) / (n : ℝ) +
      Real.log (R : ℝ)) atTop (𝓝 (Real.log (R : ℝ))) := by
    simpa using (log_linear_div_tendsto_zero C).add_const (Real.log (R : ℝ))
  exact (Real.log_le_log_iff hq hRpos).1 (le_of_tendsto_of_tendsto tendsto_const_nhds hlim he)

end BlockIdentities.Square
