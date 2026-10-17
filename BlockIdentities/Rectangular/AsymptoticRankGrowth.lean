/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.AsymptoticRankBasics
public import Mathlib.Algebra.BigOperators.Fin

/-! All-power bounds from one genuine rank root. Division with remainder keeps
the finite remainder constant fixed before the power varies. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators
variable {K : Type*} [Field K]

/-- The actual coefficient power at n+m is a pullback of the product of the
powers at n and m, by splitting each independent word into its two pieces. -/
theorem exactRank_power_add_le (T : BlockIdentities.FiniteTensor K) (n m : ℕ) :
    exactRank (power T (n + m)).coeff ≤
      exactRank (power T n).coeff * exactRank (power T m).coeff := by
  let split (d : ℕ) (x : Fin (n + m) → Fin d) :
      (Fin n → Fin d) × (Fin m → Fin d) :=
    (fun i => x (Fin.castAdd m i), fun j => x (Fin.natAdd n j))
  have hp := ((exactRank_spec (Tensor.power T.coeff n)).product
    (exactRank_spec (Tensor.power T.coeff m))).pullback
    (split T.nx) (split T.ny) (split T.nz)
  have heq : Tensor.pullback (split T.nx) (split T.ny) (split T.nz)
      (Tensor.product (Tensor.power T.coeff n) (Tensor.power T.coeff m)) =
      Tensor.power T.coeff (n + m) := by
    funext x y z
    simp only [Tensor.pullback, Tensor.product, Tensor.power, split, Fin.prod_univ_add]
  rw [heq] at hp
  simpa only [exactRank_power_coeff] using exactRank_le hp

/-- Repeating one fixed block is a genuine finite tensor-rank construction. -/
theorem exactRank_power_mul_le (T : BlockIdentities.FiniteTensor K) (k q : ℕ) :
    exactRank (power T (k * q)).coeff ≤ (exactRank (power T k).coeff) ^ q := by
  induction q with
  | zero =>
    have hr := (exactRank_spec T.coeff).power 0
    have hh := exactRank_le hr
    rw [Nat.mul_zero, pow_zero, exactRank_power_coeff]
    simpa only [pow_zero] using hh
  | succ q ih =>
    rw [Nat.mul_succ, pow_succ]
    exact (exactRank_power_add_le T (k * q) k).trans (Nat.mul_le_mul_right _ ih)

/-- Any rate strictly above the literal infimum of finite rank roots controls
all powers with one constant. No limiting characterization is assumed. -/
theorem exists_exact_power_rank_bound (T : NonzeroTensor K) {r : ℝ}
    (hr : tensorAsymptoticRank T < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (exactRank (power T.val n).coeff : ℝ) ≤ C * r ^ n := by
  have hrone : 1 < r := (one_le_tensorAsymptoticRank T).trans_lt hr
  have hrpos : 0 < r := lt_trans zero_lt_one hrone
  obtain ⟨x, hx, hxr⟩ := exists_lt_of_csInf_lt (tensorRankRoots_nonempty T) hr
  obtain ⟨k, hk, rfl⟩ := hx
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hblock : (exactRank (power T.val k).coeff : ℝ) ≤ r ^ k := by
    have hh := (Real.rpow_inv_lt_iff_of_pos (Nat.cast_nonneg _) hrpos.le hkreal).mp
      (show (exactRank (power T.val k).coeff : ℝ) ^ (k : ℝ)⁻¹ < r by
        simpa only [one_div] using hxr)
    simpa only [Real.rpow_natCast] using hh.le
  let B : ℕ := ∑ s ∈ Finset.range k, exactRank (power T.val s).coeff
  refine ⟨((B + 1 : ℕ) : ℝ), by positivity, ?_⟩
  intro n
  have hrem : n % k ∈ Finset.range k := Finset.mem_range.mpr (Nat.mod_lt n hkpos)
  have hremainder : exactRank (power T.val (n % k)).coeff ≤ B := by
    dsimp only [B]
    exact Finset.single_le_sum
      (f := fun s => exactRank (power T.val s).coeff) (fun _ _ => Nat.zero_le _) hrem
  have hn : k * (n / k) + n % k = n := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod n k
  have hfinite : exactRank (power T.val n).coeff ≤
      (exactRank (power T.val k).coeff) ^ (n / k) * B := by
    calc
      _ = exactRank (power T.val (k * (n / k) + n % k)).coeff := by rw [hn]
      _ ≤ exactRank (power T.val (k * (n / k))).coeff *
          exactRank (power T.val (n % k)).coeff := exactRank_power_add_le _ _ _
      _ ≤ _ := Nat.mul_le_mul (exactRank_power_mul_le _ _ _) hremainder
  calc
    (exactRank (power T.val n).coeff : ℝ) ≤
        (exactRank (power T.val k).coeff : ℝ) ^ (n / k) * (B : ℝ) := by
      exact_mod_cast hfinite
    _ ≤ (r ^ k) ^ (n / k) * (B : ℝ) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hblock _)
        (Nat.cast_nonneg _)
    _ ≤ r ^ n * (B : ℝ) := by
      rw [← pow_mul]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hrone.le (by omega : k * (n / k) ≤ n)) (Nat.cast_nonneg _)
    _ ≤ ((B + 1 : ℕ) : ℝ) * r ^ n := by
      rw [mul_comm (r ^ n)]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.le_succ B))
        (pow_nonneg hrpos.le _)

end BlockIdentities.Rectangular
