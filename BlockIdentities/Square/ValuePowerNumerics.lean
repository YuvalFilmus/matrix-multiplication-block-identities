/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Literal ordinary-value gain identities for repeating finite extractions. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square

private theorem gain_eq_exp (n h m : ℕ) (hh : 1 ≤ h) (hm : 1 ≤ m) (ρ : ℝ) :
    ((h : ℝ) * (m : ℝ) ^ ρ) ^ (1 / (3 * (n : ℝ))) =
      Real.exp ((Real.log (h : ℝ) + ρ * Real.log (m : ℝ)) / (3 * (n : ℝ))) := by
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  rw [Real.rpow_def_of_pos (mul_pos hhpos (Real.rpow_pos_of_pos hmpos ρ)),
    Real.log_mul (ne_of_gt hhpos) (ne_of_gt (Real.rpow_pos_of_pos hmpos ρ)),
    Real.log_rpow hmpos]
  congr 1
  ring

/-- Repeating an extraction k times leaves its normalized gain unchanged. -/
theorem matrixValueGain_repeat (n : ℕ) (hn : 1 ≤ n)
    (h : ℕ) (hh : 1 ≤ h) (m : ℕ) (hm : 1 ≤ m)
    (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ) :
    (((h ^ k : ℕ) : ℝ) * ((m ^ k : ℕ) : ℝ) ^ ρ) ^
        (1 / (3 * ((n * k : ℕ) : ℝ))) =
      ((h : ℝ) * (m : ℝ) ^ ρ) ^ (1 / (3 * (n : ℝ))) := by
  rw [gain_eq_exp (n * k) (h ^ k) (m ^ k) (Nat.one_le_pow _ _ hh)
      (Nat.one_le_pow _ _ hm), gain_eq_exp n h m hh hm]
  simp only [Nat.cast_pow, Nat.cast_mul, Real.log_pow]
  congr 1
  have hnz : (n : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn))
  have hkz : (k : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk))
  field_simp [hnz, hkz] <;> ring

/-- Changing the source normalization by a fixed factor divides its gain
exponent by that factor. The outer power here is a natural power. -/
theorem matrixValueGain_reindex_power (n : ℕ) (hn : 1 ≤ n)
    (h : ℕ) (hh : 1 ≤ h) (m : ℕ) (hm : 1 ≤ m)
    (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ) :
    ((h : ℝ) * (m : ℝ) ^ ρ) ^ (1 / (3 * (n : ℝ))) =
      (((h : ℝ) * (m : ℝ) ^ ρ) ^ (1 / (3 * ((k * n : ℕ) : ℝ)))) ^ k := by
  rw [gain_eq_exp n h m hh hm, gain_eq_exp (k * n) h m hh hm,
    ← Real.exp_nat_mul]
  simp only [Nat.cast_mul]
  congr 1
  have hnz : (n : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn))
  have hkz : (k : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk))
  field_simp [hnz, hkz] <;> ring

/-- Raising both independent-copy count and square dimension to k raises the
literal gain to the same natural power. -/
theorem matrixValueGain_pow_dimensions (n : ℕ) (hn : 1 ≤ n)
    (h : ℕ) (hh : 1 ≤ h) (m : ℕ) (hm : 1 ≤ m)
    (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ) :
    (((h ^ k : ℕ) : ℝ) * ((m ^ k : ℕ) : ℝ) ^ ρ) ^ (1 / (3 * (n : ℝ))) =
      (((h : ℝ) * (m : ℝ) ^ ρ) ^ (1 / (3 * (n : ℝ)))) ^ k := by
  rw [gain_eq_exp n (h ^ k) (m ^ k) (Nat.one_le_pow _ _ hh)
      (Nat.one_le_pow _ _ hm), gain_eq_exp n h m hh hm, ← Real.exp_nat_mul]
  simp only [Nat.cast_pow, Real.log_pow]
  congr 1
  ring

/-- Multiplying the extraction copy count by b^(3n) multiplies its gain by b. -/
theorem matrixValueGain_scale_copies (n : ℕ) (hn : 1 ≤ n)
    (h : ℕ) (hh : 1 ≤ h) (m : ℕ) (hm : 1 ≤ m)
    (b : ℕ) (hb : 1 ≤ b) (ρ : ℝ) :
    ((((b ^ (3 * n) * h : ℕ) : ℝ)) * (m : ℝ) ^ ρ) ^ (1 / (3 * (n : ℝ))) =
      (b : ℝ) * (((h : ℝ) * (m : ℝ) ^ ρ) ^ (1 / (3 * (n : ℝ)))) := by
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hb)
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hcopies : 1 ≤ b ^ (3 * n) * h :=
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ b ^ (3 * n) * h := Nat.mul_le_mul (Nat.one_le_pow _ _ hb) hh
  rw [gain_eq_exp n (b ^ (3 * n) * h) m hcopies hm, gain_eq_exp n h m hh hm]
  conv_rhs => rw [← Real.exp_log hbpos, ← Real.exp_add]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_mul (ne_of_gt (pow_pos hbpos (3 * n))) (ne_of_gt hhpos), Real.log_pow]
  congr 1
  have hnz : (n : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn))
  push_cast
  field_simp [hnz] <;> ring

end BlockIdentities.Square
