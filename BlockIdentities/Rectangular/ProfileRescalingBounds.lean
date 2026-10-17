/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.ProfileRescaling

/-! Genuine lower bounds and scale comparisons for the rational profile. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular

/-- The diagonal replication and actual monotonicity produce the discrete
minimum bound from the single scalar endpoint f(1,1)>=1. -/
theorem discrete_profile_min_lower (f : ℕ+ → ℕ+ → ℝ)
    (h₁ : 1 ≤ f 1 1)
    (hrep : ∀ k R S : ℕ+, (k : ℝ) * f R S ≤ f (k * R) (k * S))
    (hmono : ∀ R S R' S' : ℕ+, (R : ℕ) ≤ R' → (S : ℕ) ≤ S' → f R S ≤ f R' S')
    (R S : ℕ+) : min (R : ℝ) (S : ℝ) ≤ f R S := by
  let k := min R S
  have hdiag := hrep k 1 1
  simp only [mul_one] at hdiag
  have hfirst : (k : ℝ) ≤ (k : ℝ) * f 1 1 := by
    have h := mul_le_mul_of_nonneg_left h₁ (show (0 : ℝ) ≤ k by exact_mod_cast k.property.le)
    simpa only [mul_one] using h
  have hm := hmono k k R S (show (k : ℕ) ≤ R from min_le_left _ _)
    (show (k : ℕ) ≤ S from min_le_right _ _)
  have hk : (k : ℝ) = min (R : ℝ) (S : ℝ) := by
    rcases le_total R S with h | h
    · rw [show k = R from min_eq_left h, min_eq_left (by exact_mod_cast h)]
    · rw [show k = S from min_eq_right h, min_eq_right (by exact_mod_cast h)]
  rw [← hk]
  exact hfirst.trans (hdiag.trans hm)

/-- The literal sample supremum is bounded below by the positive minimum of
its two rational lengths, using actual positive discrete lengths. -/
theorem rationalProfile_min_lower (f : ℕ+ → ℕ+ → ℝ)
    (hbound : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (hmin : ∀ R S : ℕ+, min (R : ℝ) (S : ℝ) ≤ f R S)
    (r s : {x : ℚ // 0 < x}) : min (r.val : ℝ) (s.val : ℝ) ≤ rationalProfile f r s := by
  obtain ⟨v, hv⟩ := rationalProfileSamples_nonempty f r s
  obtain ⟨q, hq, R, S, hr, hs, rfl⟩ := hv
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrr : (q : ℝ) * (r.val : ℝ) = (R : ℝ) := by exact_mod_cast hr
  have hss : (q : ℝ) * (s.val : ℝ) = (S : ℝ) := by exact_mod_cast hs
  have hsample : f R S / (q : ℝ) ∈ rationalProfileSamples f r s :=
    ⟨q, hq, R, S, hr, hs, rfl⟩
  have hupper : f R S / (q : ℝ) ≤ rationalProfile f r s :=
    le_csSup (rationalProfileSamples_bddAbove f hbound r s) hsample
  have hminscaled := div_le_div_of_nonneg_right (hmin R S) hqr.le
  have he : min (R : ℝ) (S : ℝ) / (q : ℝ) = min (r.val : ℝ) (s.val : ℝ) := by
    rw [← hrr, ← hss]
    rcases le_total (r.val : ℝ) (s.val : ℝ) with h | h
    · rw [min_eq_left (mul_le_mul_of_nonneg_left h hqr.le), min_eq_left h]
      field_simp [hqr.ne']
    · rw [min_eq_right (mul_le_mul_of_nonneg_left h hqr.le), min_eq_right h]
      field_simp [hqr.ne']
  rw [he] at hminscaled
  exact hminscaled.trans hupper

theorem rationalProfile_pos (f : ℕ+ → ℕ+ → ℝ)
    (hbound : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (hmin : ∀ R S : ℕ+, min (R : ℝ) (S : ℝ) ≤ f R S)
    (r s : {x : ℚ // 0 < x}) : 0 < rationalProfile f r s := by
  have hr : 0 < (r.val : ℝ) := by exact_mod_cast r.property
  have hs : 0 < (s.val : ℝ) := by exact_mod_cast s.property
  exact (lt_min hr hs).trans_le (rationalProfile_min_lower f hbound hmin r s)

/-- The source min/max ratio squeeze on two positive rational pairs. -/
theorem rationalProfile_scale_compare (f : ℕ+ → ℕ+ → ℝ)
    (hbound : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (hrep : ∀ k R S : ℕ+, (k : ℝ) * f R S ≤ f (k * R) (k * S))
    (hmono : ∀ R S R' S' : ℕ+, (R : ℕ) ≤ R' → (S : ℕ) ≤ S' → f R S ≤ f R' S')
    (r s r' s' : {x : ℚ // 0 < x}) :
    ((min (r'.val / r.val) (s'.val / s.val) : ℚ) : ℝ) * rationalProfile f r s ≤ rationalProfile f r' s' ∧
      rationalProfile f r' s' ≤ ((max (r'.val / r.val) (s'.val / s.val) : ℚ) : ℝ) * rationalProfile f r s := by
  let a : {x : ℚ // 0 < x} := ⟨min (r'.val / r.val) (s'.val / s.val),
    lt_min (div_pos r'.property r.property) (div_pos s'.property s.property)⟩
  let b : {x : ℚ // 0 < x} := ⟨max (r'.val / r.val) (s'.val / s.val),
    (div_pos r'.property r.property).trans_le (le_max_left _ _)⟩
  have har : a.val * r.val ≤ r'.val := (le_div_iff₀ r.property).mp (min_le_left _ _)
  have has : a.val * s.val ≤ s'.val := (le_div_iff₀ s.property).mp (min_le_right _ _)
  have hbr : r'.val ≤ b.val * r.val := (div_le_iff₀ r.property).mp (le_max_left _ _)
  have hbs : s'.val ≤ b.val * s.val := (div_le_iff₀ s.property).mp (le_max_right _ _)
  have hlower := rationalProfile_mono f hbound hrep hmono
    ⟨a.val * r.val, mul_pos a.property r.property⟩
    ⟨a.val * s.val, mul_pos a.property s.property⟩ r' s' har has
  have hupper := rationalProfile_mono f hbound hrep hmono r' s'
    ⟨b.val * r.val, mul_pos b.property r.property⟩
    ⟨b.val * s.val, mul_pos b.property s.property⟩ hbr hbs
  rw [rationalProfile_homogeneous f hbound r s a] at hlower
  rw [rationalProfile_homogeneous f hbound r s b] at hupper
  exact ⟨hlower, hupper⟩

private theorem ratio_squeeze_abs {x y x' y' v v' : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hv : 0 ≤ v) (hbound : v ≤ x + y)
    (hlo : min (x' / x) (y' / y) * v ≤ v')
    (hhi : v' ≤ max (x' / x) (y' / y) * v) :
    |v' - v| ≤ (x + y) / min x y * max |x' - x| |y' - y| := by
  let δ := max |x' - x| |y' - y|
  let d := min x y
  have hd : 0 < d := lt_min hx hy
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (le_max_left _ _)
  have hrat {z z' : ℝ} (hz : 0 < z) (hdz : d ≤ z) (hzδ : |z' - z| ≤ δ) :
      1 - δ / d ≤ z' / z ∧ z' / z ≤ 1 + δ / d := by
    have hdivide : δ / z ≤ δ / d := (div_le_div_iff₀ hz hd).mpr
      (mul_le_mul_of_nonneg_left hdz hδ)
    have hzlower : 1 - δ / z ≤ z' / z := by
      apply (le_div_iff₀ hz).mpr
      have hcancel : (δ / z) * z = δ := div_mul_cancel₀ δ hz.ne'
      have h := (abs_le.mp hzδ).1
      nlinarith only [hcancel, h]
    have hzupper : z' / z ≤ 1 + δ / z := by
      apply (div_le_iff₀ hz).mpr
      have hcancel : (δ / z) * z = δ := div_mul_cancel₀ δ hz.ne'
      have h := (abs_le.mp hzδ).2
      nlinarith only [hcancel, h]
    exact ⟨by linarith only [hzlower, hdivide], by linarith only [hzupper, hdivide]⟩
  have hratx := hrat hx (min_le_left x y) (le_max_left |x' - x| |y' - y|)
  have hraty := hrat hy (min_le_right x y) (le_max_right |x' - x| |y' - y|)
  have ha : 1 - δ / d ≤ min (x' / x) (y' / y) := le_min hratx.1 hraty.1
  have hb : max (x' / x) (y' / y) ≤ 1 + δ / d := max_le hratx.2 hraty.2
  have hal := mul_le_mul_of_nonneg_right ha hv
  have hbu := mul_le_mul_of_nonneg_right hb hv
  have hgrowth := mul_le_mul_of_nonneg_left hbound (div_nonneg hδ hd.le)
  have habs : |v' - v| ≤ δ / d * (x + y) := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hlo, hhi, hal, hbu, hgrowth]
  have he : δ / d * (x + y) = (x + y) / d * δ := by ring
  rwa [he] at habs

/-- The source local Lipschitz estimate follows from the actual homogeneous
monotone rational profile. Its coefficient is bounded away from the axes. -/
theorem rationalProfile_local_lipschitz (f : ℕ+ → ℕ+ → ℝ)
    (hbound : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (hmin : ∀ R S : ℕ+, min (R : ℝ) (S : ℝ) ≤ f R S)
    (hrep : ∀ k R S : ℕ+, (k : ℝ) * f R S ≤ f (k * R) (k * S))
    (hmono : ∀ R S R' S' : ℕ+, (R : ℕ) ≤ R' → (S : ℕ) ≤ S' → f R S ≤ f R' S')
    (r s r' s' : {x : ℚ // 0 < x}) :
    |rationalProfile f r' s' - rationalProfile f r s| ≤
      ((r.val : ℝ) + s.val) / min (r.val : ℝ) (s.val : ℝ) *
        max |(r'.val : ℝ) - r.val| |(s'.val : ℝ) - s.val| := by
  have hcompare := rationalProfile_scale_compare f hbound hrep hmono r s r' s'
  simp only [Rat.cast_min, Rat.cast_max, Rat.cast_div] at hcompare
  exact ratio_squeeze_abs (by exact_mod_cast r.property) (by exact_mod_cast s.property)
    (rationalProfile_pos f hbound hmin r s).le (rationalProfile_le f hbound r s)
    hcompare.1 hcompare.2

end BlockIdentities.Rectangular
