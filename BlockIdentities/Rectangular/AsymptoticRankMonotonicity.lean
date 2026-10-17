/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.AsymptoticRankGrowth
public import BlockIdentities.Tensor.ClassDegeneration
public import BlockIdentities.Tensor.ClassIdentities
public import BlockIdentities.Tensor.ScalarRank

/-! Finite tensor-power identifications and quantitative consumers of genuine
all-power rank bounds. -/
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

/-- This rank equality is finite mutual restriction, not a limiting claim. -/
theorem exactRank_power_power (A : BlockIdentities.FiniteTensor K) (k n : ℕ) :
    exactRank (power (power A k) n).coeff = exactRank (power A (k * n)).coeff := by
  change rank (tensorClass (power (power A k) n)) = rank (tensorClass (power A (k * n)))
  rw [tensorClass_power_eq, tensorClass_power_eq, tensorClass_power_eq, pow_mul]

theorem exactRank_power_product_le (A B : BlockIdentities.FiniteTensor K) (n : ℕ) :
    exactRank (power (product A B) n).coeff ≤
      exactRank (power A n).coeff * exactRank (power B n).coeff := by
  change rank (tensorClass (power (product A B) n)) ≤
    rank (tensorClass (power A n)) * rank (tensorClass (power B n))
  rw [tensorClass_power_eq, tensorClass_product_eq, tensorClass_power_eq,
    tensorClass_power_eq, mul_pow]
  exact rank_mul_le _ _

theorem exactRank_copies_le (A : BlockIdentities.FiniteTensor K) (a : ℕ) :
    exactRank (copies a A).coeff ≤ a * exactRank A.coeff := by
  change rank (tensorClass (copies a A)) ≤ a * rank (tensorClass A)
  rw [tensorClass_copies_eq]
  exact (rank_mul_le (a : TensorClass K) (tensorClass A)).trans
    (Nat.mul_le_mul_right _ (Square.rank_natCast_le a))

/-- A genuine uniform geometric bound bounds the literal infimum. -/
theorem tensorAsymptoticRank_le_of_uniform_bound (T : NonzeroTensor K)
    {C r : ℝ} (hC : 0 < C) (hr : 0 < r)
    (hbound : ∀ n : ℕ, (exactRank (power T.val n).coeff : ℝ) ≤ C * r ^ n) :
    tensorAsymptoticRank T ≤ r := by
  have hTpos : 0 < tensorAsymptoticRank T :=
    lt_of_lt_of_le zero_lt_one (one_le_tensorAsymptoticRank T)
  have he : ∀ᶠ n : ℕ in atTop, Real.log (tensorAsymptoticRank T) ≤
      Real.log C / (n : ℝ) + Real.log r := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hRankpos : 0 < (exactRank (power T.val n).coeff : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
        (one_le_exactRank_of_nonzero _ (nonzero_power T.property n)))
    have hl := Real.log_le_log hTpos (tensorAsymptoticRank_le_power_root T n hn)
    rw [Real.log_rpow hRankpos] at hl
    have hu := Real.log_le_log hRankpos (hbound n)
    rw [Real.log_mul hC.ne' (pow_pos hr n).ne', Real.log_pow] at hu
    have hd := div_le_div_of_nonneg_right hu hnpos.le
    have hh : Real.log (tensorAsymptoticRank T) ≤
        Real.log (exactRank (power T.val n).coeff : ℝ) / (n : ℝ) := by
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hl
    apply hh.trans
    convert hd using 1 <;> field_simp [ne_of_gt hnpos] <;> ring
  have hlim : Tendsto (fun n : ℕ => Real.log C / (n : ℝ) + Real.log r)
      atTop (𝓝 (Real.log r)) := by
    have hc : Tendsto (fun n : ℕ => Real.log C / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using hc.add_const (Real.log r)
  exact (Real.log_le_log_iff hTpos hr).mp
    (le_of_tendsto_of_tendsto tendsto_const_nhds hlim he)

/-- Any rate for all source powers gives its k-th power as a rate for the
actual regrouped k-th tensor power. -/
theorem tensorAsymptoticRank_power_le_rate (T : NonzeroTensor K) (k : ℕ) {r : ℝ}
    (hr : tensorAsymptoticRank T < r) :
    tensorAsymptoticRank (T.power k) ≤ r ^ k := by
  obtain ⟨C, hC, hbound⟩ := exists_exact_power_rank_bound T hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one
    ((one_le_tensorAsymptoticRank T).trans hr.le)
  apply tensorAsymptoticRank_le_of_uniform_bound (T.power k) hC (pow_pos hrpos k)
  intro n
  change (exactRank (power (power T.val k) n).coeff : ℝ) ≤ _
  rw [exactRank_power_power]
  simpa only [pow_mul] using hbound (k * n)

/-- Upper power inequality obtained from rates strictly above the genuine
infimum, then continuity; no submultiplicative limit is assumed. -/
theorem tensorAsymptoticRank_power_le (T : NonzeroTensor K) (k : ℕ) :
    tensorAsymptoticRank (T.power k) ≤ tensorAsymptoticRank T ^ k := by
  have hlim : Tendsto (fun r : ℝ => r ^ k) (𝓝[>] tensorAsymptoticRank T)
      (𝓝 (tensorAsymptoticRank T ^ k)) :=
    (continuous_pow k).continuousAt.tendsto.mono_left inf_le_left
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact tensorAsymptoticRank_power_le_rate T k hr

/-- Raising the literal root lower bound recovers a bound at every positive power. -/
theorem tensorAsymptoticRank_pow_le_exactRank_power (T : NonzeroTensor K)
    (n : ℕ) (hn : 1 ≤ n) :
    tensorAsymptoticRank T ^ n ≤ (exactRank (power T.val n).coeff : ℝ) := by
  have hh := pow_le_pow_left₀
    (show 0 ≤ tensorAsymptoticRank T from (one_le_tensorAsymptoticRank T).trans' zero_le_one)
    (tensorAsymptoticRank_le_power_root T n hn) n
  rw [one_div, Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega)] at hh
  exact hh

/-- The reverse power inequality follows by testing every exact power root. -/
theorem tensorAsymptoticRank_power_ge (T : NonzeroTensor K) (k : ℕ) :
    tensorAsymptoticRank T ^ k ≤ tensorAsymptoticRank (T.power k) := by
  by_cases hk : k = 0
  · subst k
    simpa only [pow_zero] using one_le_tensorAsymptoticRank (T.power 0)
  apply le_csInf (tensorRankRoots_nonempty (T.power k))
  rintro r ⟨n, hn, rfl⟩
  change tensorAsymptoticRank T ^ k ≤
    (exactRank (power (power T.val k) n).coeff : ℝ) ^ (1 / (n : ℝ))
  apply le_of_pow_le_pow_left₀ (by omega : n ≠ 0)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [one_div, Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega),
    ← pow_mul, exactRank_power_power]
  exact tensorAsymptoticRank_pow_le_exactRank_power T (k * n)
    (by have := Nat.mul_pos (Nat.pos_of_ne_zero hk) (by omega : 0 < n); omega)

theorem tensorAsymptoticRank_power (T : NonzeroTensor K) (k : ℕ) :
    tensorAsymptoticRank (T.power k) = tensorAsymptoticRank T ^ k :=
  le_antisymm (tensorAsymptoticRank_power_le T k) (tensorAsymptoticRank_power_ge T k)

/-- Fixed degeneration is compared at each fixed outer power; its interpolation
constant may depend on that power and disappears only in the inner limit. -/
theorem tensorAsymptoticRank_mono_degeneration [Infinite K]
    (A B : NonzeroTensor K) (h : Degenerates A.val B.val) :
    tensorAsymptoticRank B ≤ tensorAsymptoticRank A := by
  apply le_csInf (tensorRankRoots_nonempty A)
  rintro r ⟨k, hk, rfl⟩
  have hp : Degenerates (power A.val k) (power B.val k) := by
    apply (classDegenerates_tensorClass_iff _ _).mp
    simpa only [tensorClass_power_eq] using
      ((classDegenerates_tensorClass_iff _ _).mpr h).pow k
  have hb : BorderRankAtMost (power B.val k) (exactRank (power A.val k).coeff) :=
    (degenerates_of_rankAtMost (exactRank_spec (power A.val k).coeff)).trans hp
  have hh := tensorAsymptoticRank_le_of_borderRankAtMost (B.power k) hb
  rw [tensorAsymptoticRank_power] at hh
  apply le_of_pow_le_pow_left₀ (by omega : k ≠ 0)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [one_div, Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega)]
  exact hh

/-- The source-copy overhead is subexponential. Each outer conversion is handled
by the fixed-degeneration theorem separately; no uniform degree bound is assumed. -/
theorem tensorAsymptoticRank_mono_asymptotic [Infinite K]
    (A B : NonzeroTensor K) (h : AsymptoticallyRestricts A.val B.val) :
    tensorAsymptoticRank B ≤ tensorAsymptoticRank A := by
  obtain ⟨a, ha, halim, hconv⟩ := h
  apply le_of_forall_pos_le_add
  intro ε hε
  let r : ℝ := tensorAsymptoticRank A + ε
  have hr : tensorAsymptoticRank A < r := by dsimp [r]; linarith
  have hrpos : 0 < r := lt_trans
    (lt_of_lt_of_le zero_lt_one (one_le_tensorAsymptoticRank A)) hr
  obtain ⟨C, hC, hbound⟩ := exists_exact_power_rank_bound A hr
  have hBpos : 0 < tensorAsymptoticRank B :=
    lt_of_lt_of_le zero_lt_one (one_le_tensorAsymptoticRank B)
  have hlog : ∀ᶠ n : ℕ in atTop, Real.log (tensorAsymptoticRank B) ≤
      Real.log (a n : ℝ) / (n : ℝ) + Real.log C / (n : ℝ) + Real.log r := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hapos : 0 < (a n : ℝ) := by exact_mod_cast ha n
    have hb : BorderRankAtMost (power B.val n)
        (exactRank (copies (a n) (power A.val n)).coeff) :=
      (degenerates_of_rankAtMost
        (exactRank_spec (copies (a n) (power A.val n)).coeff)).trans (hconv n hn)
    have hpow : tensorAsymptoticRank B ^ n ≤
        (a n : ℝ) * (exactRank (power A.val n).coeff : ℝ) := by
      have hh := tensorAsymptoticRank_le_of_borderRankAtMost (B.power n) hb
      rw [tensorAsymptoticRank_power] at hh
      exact hh.trans (by exact_mod_cast exactRank_copies_le (power A.val n) (a n))
    have hupper : tensorAsymptoticRank B ^ n ≤ (a n : ℝ) * (C * r ^ n) :=
      hpow.trans (mul_le_mul_of_nonneg_left (hbound n) hapos.le)
    have hl := Real.log_le_log (pow_pos hBpos n) hupper
    rw [Real.log_pow, Real.log_mul hapos.ne' (mul_pos hC (pow_pos hrpos n)).ne',
      Real.log_mul hC.ne' (pow_pos hrpos n).ne', Real.log_pow] at hl
    have hd := div_le_div_of_nonneg_right hl hnpos.le
    convert hd using 1 <;> field_simp [ne_of_gt hnpos] <;> ring
  have hclim : Tendsto (fun n : ℕ => Real.log C / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => Real.log (a n : ℝ) / (n : ℝ) +
      Real.log C / (n : ℝ) + Real.log r) atTop (𝓝 (Real.log r)) := by
    simpa only [zero_add] using (halim.add hclim).add_const (Real.log r)
  exact (Real.log_le_log_iff hBpos hrpos).mp
    (le_of_tendsto_of_tendsto tendsto_const_nhds hlim hlog)

/-- Tensoring genuine finite decompositions bounds the product asymptotic rank. -/
theorem tensorAsymptoticRank_product_le (A B : NonzeroTensor K) :
    tensorAsymptoticRank (A.product B) ≤ tensorAsymptoticRank A * tensorAsymptoticRank B := by
  have hrate (r s : ℝ) (hr : tensorAsymptoticRank A < r)
      (hs : tensorAsymptoticRank B < s) :
      tensorAsymptoticRank (A.product B) ≤ r * s := by
    obtain ⟨C, hC, hboundA⟩ := exists_exact_power_rank_bound A hr
    obtain ⟨D, hD, hboundB⟩ := exists_exact_power_rank_bound B hs
    have hrpos : 0 < r := lt_trans
      (lt_of_lt_of_le zero_lt_one (one_le_tensorAsymptoticRank A)) hr
    have hspos : 0 < s := lt_trans
      (lt_of_lt_of_le zero_lt_one (one_le_tensorAsymptoticRank B)) hs
    apply tensorAsymptoticRank_le_of_uniform_bound (A.product B)
      (mul_pos hC hD) (mul_pos hrpos hspos)
    intro n
    change (exactRank (power (product A.val B.val) n).coeff : ℝ) ≤ _
    calc
      _ ≤ (exactRank (power A.val n).coeff : ℝ) *
          (exactRank (power B.val n).coeff : ℝ) := by
        exact_mod_cast exactRank_power_product_le A.val B.val n
      _ ≤ (C * r ^ n) * (D * s ^ n) :=
        mul_le_mul (hboundA n) (hboundB n) (Nat.cast_nonneg _)
          (mul_nonneg hC.le (pow_nonneg hrpos.le _))
      _ = (C * D) * (r * s) ^ n := by rw [mul_pow]; ring
  have hfixed (r : ℝ) (hr : tensorAsymptoticRank A < r) :
      tensorAsymptoticRank (A.product B) ≤ r * tensorAsymptoticRank B := by
    have hlim : Tendsto (fun s : ℝ => r * s) (𝓝[>] tensorAsymptoticRank B)
        (𝓝 (r * tensorAsymptoticRank B)) :=
      (continuous_const.mul continuous_id).continuousAt.tendsto.mono_left inf_le_left
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hrate r s hr hs
  have hlim : Tendsto (fun r : ℝ => r * tensorAsymptoticRank B)
      (𝓝[>] tensorAsymptoticRank A)
      (𝓝 (tensorAsymptoticRank A * tensorAsymptoticRank B)) :=
    (continuous_id.mul continuous_const).continuousAt.tendsto.mono_left inf_le_left
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hfixed r hr

end BlockIdentities.Rectangular
