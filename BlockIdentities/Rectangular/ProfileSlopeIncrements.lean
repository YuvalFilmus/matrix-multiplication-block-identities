/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.ProfileSlopes
public import BlockIdentities.Rectangular.ProfileIncrements

/-! The common-slope output gives the actual coordinate increment estimate.
These scalar consumers keep all slope and positivity requirements explicit. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular

/-- An affine upper bound and a lower increment with the same positive slope
force a multiplicative increment. -/
theorem ratio_ge_of_common_slope {P : ℝ → ℝ} {L c s t : ℝ}
    (hL : 0 < L) (hc : 0 ≤ c) (hs : 0 < s) (ht : 0 < t)
    (hP : 0 < P s) (hupper : P s ≤ L * (s + c))
    (hinc : L * t ≤ P (s + t) - P s) :
    1 + t / (s + c) ≤ P (s + t) / P s := by
  have hden : 0 < s + c := add_pos_of_pos_of_nonneg hs hc
  apply (le_div_iff₀ hP).mpr
  have hsmall : t / (s + c) * P s ≤ L * t := by
    have h := mul_le_mul_of_nonneg_left hupper (div_pos ht hden).le
    have he : t / (s + c) * (L * (s + c)) = L * t := by
      field_simp [hden.ne']
    exact h.trans_eq he
  nlinarith only [hsmall, hinc]

/-- Raising the genuine powered-profile increment to p recovers the profile
ratio. The strict support-coordinate premise is used only here. -/
theorem profile_ratio_ge_of_powered_slope {g : ℝ → ℝ} {p L c s t : ℝ}
    (hp : 0 < p) (hL : 0 < L) (hc : 0 ≤ c) (hs : 0 < s) (ht : 0 < t)
    (hg : ∀ x : ℝ, 0 < x → 0 < g x)
    (hupper : g s ^ (1 / p) ≤ L * (s + c))
    (hinc : L * t ≤ g (s + t) ^ (1 / p) - g s ^ (1 / p)) :
    (1 + t / (s + c)) ^ p ≤ g (s + t) / g s := by
  have hgs := hg s hs
  have hgplus := hg (s + t) (add_pos hs ht)
  have hbase : 0 < 1 + t / (s + c) := by positivity
  have hratio := ratio_ge_of_common_slope (P := fun x => g x ^ (1 / p)) hL hc hs ht
    (Real.rpow_pos_of_pos hgs _) hupper hinc
  have hpow := Real.rpow_le_rpow hbase.le hratio hp.le
  have heq : (g (s + t) ^ (1 / p) / g s ^ (1 / p)) ^ p = g (s + t) / g s := by
    rw [Real.div_rpow (Real.rpow_pos_of_pos hgplus _).le (Real.rpow_pos_of_pos hgs _).le,
      ← Real.rpow_mul hgplus.le, ← Real.rpow_mul hgs.le]
    simp only [one_div_mul_cancel hp.ne', Real.rpow_one]
  rwa [heq] at hpow

/-- Homogeneity transports the normalized slice estimate to the whole
positive quadrant, with the source affine denominator s+c*r. -/
theorem profile_second_increment_of_slope (g : ℝ → ℝ → ℝ)
    {p L c : ℝ} (hp : 0 < p) (hL : 0 < L) (hc : 0 ≤ c)
    (hg : ∀ r s : ℝ, 0 < r → 0 < s → 0 < g r s)
    (hhom : ∀ t r s : ℝ, 0 < t → 0 < r → 0 < s → g (t*r) (t*s) = t*g r s)
    (hupper : ∀ s : ℝ, 0 < s → g 1 s ^ (1/p) ≤ L*(s+c))
    (hinc : ∀ u v : ℝ, 0 < u → u < v →
      L*(v-u) ≤ g 1 v ^ (1/p) - g 1 u ^ (1/p))
    (r s t : ℝ) (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    (1+t/(s+c*r)) ^ p ≤ g r (s+t) / g r s := by
  have hsr : 0 < s/r := div_pos hs hr
  have htr : 0 < t/r := div_pos ht hr
  have hraw := profile_ratio_ge_of_powered_slope hp hL hc hsr htr
    (fun x hx => hg 1 x zero_lt_one hx) (hupper _ hsr)
    (by have h := hinc (s/r) (s/r+t/r) hsr (lt_add_of_pos_right _ htr)
        simpa only [add_sub_cancel_left] using h)
  have heq (x : ℝ) (hx : 0 < x) : g r x = r*g 1 (x/r) := by
    have h := hhom r 1 (x/r) hr zero_lt_one (div_pos hx hr)
    simpa only [mul_one, mul_div_cancel₀ x hr.ne'] using h
  have hden : 0 < s+c*r := add_pos_of_pos_of_nonneg hs (mul_nonneg hc hr.le)
  have hbase : 1+(t/r)/(s/r+c) = 1+t/(s+c*r) := by
    field_simp [hr.ne', hden.ne']
    <;> ring
  rw [hbase, ← add_div] at hraw
  have hratio : g 1 ((s+t)/r) / g 1 (s/r) = g r (s+t)/g r s := by
    rw [heq (s+t) (add_pos hs ht), heq s hs]
    field_simp [hr.ne']
  rwa [hratio] at hraw

/-- Interchanging the two actual coordinate presentations supplies the first
increment and therefore the pair quadratic. -/
theorem profile_pair_quadratic_of_second_increments (g h : ℝ → ℝ → ℝ)
    {p q c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hg : ∀ r s : ℝ, 0 < r → 0 < s → 0 < g r s)
    (hhom : ∀ t r s : ℝ, 0 < t → 0 < r → 0 < s → g (t*r) (t*s) = t*g r s)
    (hswap : ∀ r s : ℝ, 0 < r → 0 < s → h s r = g r s)
    (hsecond : ∀ r s t : ℝ, 0 < r → 0 < s → 0 < t →
      (1+t/(s+c*r)) ^ p ≤ g r (s+t)/g r s)
    (hsecond' : ∀ r s t : ℝ, 0 < r → 0 < s → 0 < t →
      (1+t/(s+d*r)) ^ q ≤ h r (s+t)/h r s) :
    ∀ t : ℝ, 0 < t →
      0 ≤ (1-q)*c*t^2 + (1-p-q+c*d)*t + (1-p)*d := by
  apply offset_quadratic_of_ratio hc hd
  intro t ht
  have hfirst (r s u : ℝ) (hr : 0 < r) (hs : 0 < s) (hu : 0 < u) :
      (1+u/(r+d*s)) ^ q ≤ g (r+u) s/g r s := by
    have h := hsecond' s r u hs hr hu
    rwa [hswap (r+u) s (add_pos hr hu) hs, hswap r s hr hs] at h
  have h := profile_ratio_of_coordinate_increments g hc hd hg hhom hfirst hsecond ht zero_lt_one
  simpa only [mul_one, div_one] using h

end BlockIdentities.Rectangular
