/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Definitions
public import BlockIdentities.Tensor.ElementaryRestrictions
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Interpolation
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Basic bounds on the literal infimum of exact tensor-power rank roots.
The border-rank endpoint uses interpolation after powering one fixed degeneration. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped BigOperators Topology
variable {K : Type*} [Field K]

theorem exactRank_ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : exactRank (FiniteTensor.ofTensor T).coeff = exactRank T :=
  exactRank_reindex T (Fintype.equivFin X).symm
    (Fintype.equivFin Y).symm (Fintype.equivFin Z).symm

theorem exactRank_power_coeff (T : BlockIdentities.FiniteTensor K) (n : ℕ) :
    exactRank (power T n).coeff = exactRank (Tensor.power T.coeff n) :=
  exactRank_ofTensor _

theorem one_le_exactRank_of_nonzero (T : BlockIdentities.FiniteTensor K) (hT : Nonzero T) :
    1 ≤ exactRank T.coeff := by
  by_contra h
  have hz : exactRank T.coeff = 0 := by omega
  have hr := exactRank_spec T.coeff
  rw [hz] at hr
  obtain ⟨L, M, N, heq⟩ := hr
  apply hT
  funext x y z
  change T.coeff x y z = 0
  simpa using congrFun (congrFun (congrFun heq x) y) z

theorem tensorRankRoots_nonempty (T : NonzeroTensor K) :
    {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧
      r = (exactRank (power T.val n).coeff : ℝ) ^ (1 / (n : ℝ))}.Nonempty :=
  ⟨_, 1, le_rfl, rfl⟩

theorem tensorRankRoots_one_le (T : NonzeroTensor K) {r : ℝ}
    (hr : ∃ n : ℕ, 1 ≤ n ∧
      r = (exactRank (power T.val n).coeff : ℝ) ^ (1 / (n : ℝ))) : 1 ≤ r := by
  obtain ⟨n, hn, rfl⟩ := hr
  have hpos := one_le_exactRank_of_nonzero _ (nonzero_power T.property n)
  apply Real.one_le_rpow
  · exact_mod_cast hpos
  · positivity

theorem tensorRankRoots_bddBelow (T : NonzeroTensor K) :
    BddBelow {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧
      r = (exactRank (power T.val n).coeff : ℝ) ^ (1 / (n : ℝ))} :=
  ⟨1, fun _ hr => tensorRankRoots_one_le T hr⟩

theorem one_le_tensorAsymptoticRank (T : NonzeroTensor K) :
    1 ≤ tensorAsymptoticRank T :=
  le_csInf (tensorRankRoots_nonempty T) (fun _ hr => tensorRankRoots_one_le T hr)

theorem tensorAsymptoticRank_le_power_root (T : NonzeroTensor K) (n : ℕ) (hn : 1 ≤ n) :
    tensorAsymptoticRank T ≤ (exactRank (power T.val n).coeff : ℝ) ^ (1 / (n : ℝ)) :=
  csInf_le (tensorRankRoots_bddBelow T) ⟨n, hn, rfl⟩

theorem tensorAsymptoticRank_le_exactRank (T : NonzeroTensor K) :
    tensorAsymptoticRank T ≤ (exactRank T.val.coeff : ℝ) := by
  have h := tensorAsymptoticRank_le_power_root T 1 le_rfl
  simp only [Nat.cast_one, div_one, Real.rpow_one] at h
  apply h.trans
  exact_mod_cast (show exactRank (power T.val 1).coeff ≤ exactRank T.val.coeff by
    rw [exactRank_power_coeff]
    simpa using exactRank_le ((exactRank_spec T.val.coeff).power 1))

private theorem diagonal_rankAtMost (R : ℕ) :
    Tensor.RankAtMost (diagonal (K := K) R).coeff R := by
  classical
  change Tensor.RankAtMost (fun i j k : Fin R => if i = j ∧ j = k then (1 : K) else 0) R
  refine ⟨(fun i x => if x = i then 1 else 0),
    (fun i y => if y = i then 1 else 0),
    (fun i z => if z = i then 1 else 0), ?_⟩
  funext x y z
  simp [Tensor.rankOne, mul_ite, ite_and]
  split_ifs <;> simp_all

/-- One fixed degeneration supplies a single degree constant before n varies. -/
theorem BorderRankAtMost.exists_exact_power_rank_bound [Infinite K]
    (T : NonzeroTensor K) {R : ℕ} (h : BorderRankAtMost T.val R) :
    ∃ C : ℕ, ∀ n : ℕ, exactRank (power T.val n).coeff ≤ (C * n + 1) * R ^ n := by
  obtain ⟨k, Lx, Ly, Lz, ⟨D⟩⟩ := h
  refine ⟨Lx + Ly + Lz, ?_⟩
  intro n
  rw [exactRank_power_coeff]
  exact exactRank_le (restrictionDegeneration_power_rankAtMost D (diagonal_rankAtMost R) n)

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

/-- The literal asymptotic rank is bounded by any actual polynomial border-rank
certificate. Interpolation needs an infinite scalar field, with no characteristic
restriction; every algebraic closure has this property. -/
theorem tensorAsymptoticRank_le_of_borderRankAtMost [Infinite K]
    (T : NonzeroTensor K) {R : ℕ} (h : BorderRankAtMost T.val R) :
    tensorAsymptoticRank T ≤ (R : ℝ) := by
  have hR : 1 ≤ R := by
    by_contra hn
    have hz : R = 0 := by omega
    subst R
    have hs := h.source_nonzero T.property
    apply hs
    funext x y z
    exact Fin.elim0 x
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
  have hApos : 0 < tensorAsymptoticRank T :=
    lt_of_lt_of_le zero_lt_one (one_le_tensorAsymptoticRank T)
  obtain ⟨C, hC⟩ := BorderRankAtMost.exists_exact_power_rank_bound T h
  have hlog : ∀ᶠ n : ℕ in atTop, Real.log (tensorAsymptoticRank T) ≤
      Real.log ((C * n + 1 : ℕ) : ℝ) / (n : ℝ) + Real.log (R : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hrankone := one_le_exactRank_of_nonzero _ (nonzero_power T.property n)
    have hrankpos : 0 < (exactRank (power T.val n).coeff : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hrankone)
    have hrootlog := Real.log_le_log hApos (tensorAsymptoticRank_le_power_root T n hn)
    rw [Real.log_rpow hrankpos] at hrootlog
    have hupper : (exactRank (power T.val n).coeff : ℝ) ≤
        ((C * n + 1 : ℕ) : ℝ) * (R : ℝ) ^ n := by exact_mod_cast hC n
    have hl := Real.log_le_log hrankpos hupper
    rw [Real.log_mul (by positivity) (ne_of_gt (pow_pos hRpos n)), Real.log_pow] at hl
    have hd := div_le_div_of_nonneg_right hl hnpos.le
    have hfirst : Real.log (tensorAsymptoticRank T) ≤
        Real.log (exactRank (power T.val n).coeff : ℝ) / (n : ℝ) := by
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hrootlog
    apply hfirst.trans
    convert hd using 1 <;> field_simp [ne_of_gt hnpos] <;> ring
  have hlim : Tendsto (fun n : ℕ => Real.log ((C * n + 1 : ℕ) : ℝ) / (n : ℝ) +
      Real.log (R : ℝ)) atTop (𝓝 (Real.log (R : ℝ))) := by
    simpa using (log_linear_div_tendsto_zero C).add_const (Real.log (R : ℝ))
  exact (Real.log_le_log_iff hApos hRpos).1
    (le_of_tendsto_of_tendsto tendsto_const_nhds hlim hlog)

end BlockIdentities.Rectangular
