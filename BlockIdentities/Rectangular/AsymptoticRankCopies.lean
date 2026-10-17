/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.AsymptoticRankMonotonicity

/-! Literal independent-copy multiplicities in asymptotic rank. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped Topology
variable {K : Type*} [Field K]

/-- Finite mutual restriction identifies each exact power rank. -/
theorem tensorAsymptoticRank_eq_of_tensorClass_eq (A B : NonzeroTensor K)
    (h : tensorClass A.val = tensorClass B.val) :
    tensorAsymptoticRank A = tensorAsymptoticRank B := by
  have hRank (n : ℕ) : exactRank (power A.val n).coeff = exactRank (power B.val n).coeff := by
    change rank (tensorClass (power A.val n)) = rank (tensorClass (power B.val n))
    rw [tensorClass_power_eq, tensorClass_power_eq, h]
  unfold tensorAsymptoticRank
  congr 1
  ext r
  simp only [hRank]

/-- Copies tensor independently, so an n-th power has a^n full copies.
The rank inequality uses only actual tensor-class multiplication. -/
theorem exactRank_power_copies_le (T : BlockIdentities.FiniteTensor K) (a n : ℕ) :
    exactRank (power (copies a T) n).coeff ≤ a ^ n * exactRank (power T n).coeff := by
  change rank (tensorClass (power (copies a T) n)) ≤ a ^ n * rank (tensorClass (power T n))
  rw [tensorClass_power_eq, tensorClass_copies_eq, tensorClass_power_eq, mul_pow]
  have hscalar : rank ((a : TensorClass K) ^ n) ≤ a ^ n := by
    rw [← Nat.cast_pow]
    exact Square.rank_natCast_le (a ^ n)
  exact (rank_mul_le ((a : TensorClass K) ^ n) (tensorClass T ^ n)).trans
    (Nat.mul_le_mul_right _ hscalar)

/-- The copy count is fixed before all tensor powers and size constants. -/
theorem tensorAsymptoticRank_copies_le (T : NonzeroTensor K) (a : ℕ) (ha : 1 ≤ a) :
    tensorAsymptoticRank (T.copies a ha) ≤ (a : ℝ) * tensorAsymptoticRank T := by
  have hapos : 0 < (a : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ha)
  have hrate (r : ℝ) (hr : tensorAsymptoticRank T < r) :
      tensorAsymptoticRank (T.copies a ha) ≤ (a : ℝ) * r := by
    obtain ⟨C, hC, hbound⟩ := exists_exact_power_rank_bound T hr
    have hrpos : 0 < r := lt_trans
      (lt_of_lt_of_le zero_lt_one (one_le_tensorAsymptoticRank T)) hr
    apply tensorAsymptoticRank_le_of_uniform_bound (T.copies a ha) hC (mul_pos hapos hrpos)
    intro n
    change (exactRank (power (copies a T.val) n).coeff : ℝ) ≤ _
    calc
      _ ≤ (a : ℝ) ^ n * (exactRank (power T.val n).coeff : ℝ) := by
        exact_mod_cast exactRank_power_copies_le T.val a n
      _ ≤ (a : ℝ) ^ n * (C * r ^ n) :=
        mul_le_mul_of_nonneg_left (hbound n) (pow_nonneg hapos.le _)
      _ = C * ((a : ℝ) * r) ^ n := by rw [mul_pow]; ring
  have hlim : Tendsto (fun r : ℝ => (a : ℝ) * r) (𝓝[>] tensorAsymptoticRank T)
      (𝓝 ((a : ℝ) * tensorAsymptoticRank T)) :=
    (continuous_const.mul continuous_id).continuousAt.tendsto.mono_left inf_le_left
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hrate r hr

end BlockIdentities.Rectangular
