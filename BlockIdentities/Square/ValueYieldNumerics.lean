/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Square.MatrixRateLimits
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Internal real algebra converting genuine extraction-rate bounds to gains. -/

@[expose] public section
noncomputable section
namespace BlockIdentities.Square

/-- Internal numerical endpoint argument. Its rate premise must be supplied by
an actual matrix extraction argument, not by an assumed value characterization. -/
theorem matrixValueGain_le_of_rate_upper (ν : ℝ) (hν : 0 < ν)
    (k : ℕ) (hk : 1 ≤ k) (h : ℕ) (hh : 1 ≤ h) (m : ℕ) (hm : 1 ≤ m)
    (R : ℝ) (hR : 1 ≤ R)
    (hbound : ∀ ε : ℝ, 0 < ε → ∀ r : ℝ, 1 ≤ r →
      Real.log r < (Real.log (h : ℝ) / (ν + ε) + Real.log (m : ℝ)) / (k : ℝ) →
      r ≤ R) :
    ((h : ℝ) * (m : ℝ) ^ ν) ^ (1 / (k : ℝ)) ≤ R ^ ν := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hlogh : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast hh)
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hend (ε : ℝ) (hε : 0 < ε) :
      (Real.log (h : ℝ) / (ν + ε) + Real.log (m : ℝ)) / (k : ℝ) ≤
        Real.log R := by
    by_contra hn
    have hlt : Real.log R <
        (Real.log (h : ℝ) / (ν + ε) + Real.log (m : ℝ)) / (k : ℝ) := lt_of_not_ge hn
    let L := (Real.log (h : ℝ) / (ν + ε) + Real.log (m : ℝ)) / (k : ℝ)
    let t := (L + Real.log R) / 2
    have ht : 0 ≤ t := by dsimp [t]; change Real.log R < L at hlt; linarith
    have hr := hbound ε hε (Real.exp t) (Real.one_le_exp_iff.mpr ht) (by
      rw [Real.log_exp]
      change t < L
      dsimp [t]
      change Real.log R < L at hlt
      linarith)
    have hlogs := Real.log_le_log (Real.exp_pos t) hr
    rw [Real.log_exp] at hlogs
    dsimp [t] at hlogs
    change Real.log R < L at hlt
    linarith
  let B := (k : ℝ) * Real.log R - Real.log (m : ℝ)
  have heps (ε : ℝ) (hε : 0 < ε) : Real.log (h : ℝ) ≤ (ν + ε) * B := by
    have he := (div_le_iff₀ hkpos).1 (hend ε hε)
    have he' : Real.log (h : ℝ) / (ν + ε) ≤ B := by dsimp [B]; nlinarith [he]
    have hden : 0 < ν + ε := by linarith
    have he'' := (div_le_iff₀ hden).1 he'
    nlinarith
  have hB : 0 ≤ B := by
    have he := heps 1 (by norm_num)
    by_contra hn
    have hbneg : B < 0 := lt_of_not_ge hn
    have : (ν + 1) * B < 0 := mul_neg_of_pos_of_neg (by linarith) hbneg
    linarith
  have hlim : Real.log (h : ℝ) ≤ ν * B := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hden : 0 < B + 1 := by linarith
    have hε : 0 < δ / (B + 1) := div_pos hδ hden
    have he := heps (δ / (B + 1)) hε
    have hid : δ / (B + 1) * (B + 1) = δ :=
      div_mul_cancel₀ δ (ne_of_gt hden)
    nlinarith
  rw [Real.rpow_def_of_pos (mul_pos hhpos (Real.rpow_pos_of_pos hmpos ν)),
    Real.rpow_def_of_pos hRpos, Real.log_mul (ne_of_gt hhpos)
      (ne_of_gt (Real.rpow_pos_of_pos hmpos ν)), Real.log_rpow hmpos]
  apply Real.exp_le_exp.mpr
  simp only [one_div]
  change (Real.log (h : ℝ) + ν * Real.log (m : ℝ)) / (k : ℝ) ≤ Real.log R * ν
  apply (div_le_iff₀ hkpos).2
  dsimp [B] at hlim
  nlinarith

end BlockIdentities.Square
