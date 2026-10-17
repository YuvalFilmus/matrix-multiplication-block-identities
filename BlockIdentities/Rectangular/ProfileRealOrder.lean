/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.ProfileRealLaws

/-! Coordinate order and interchange of actual profile extensions. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular

/-- The rational ratio bound extends without any ordered-density assumption. -/
theorem continuous_profile_scale_upper (f : ℕ+ → ℕ+ → ℝ)
    (hbound : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (hrep : ∀ k R S : ℕ+, (k : ℝ) * f R S ≤ f (k * R) (k * S))
    (hmono : ∀ R S R' S' : ℕ+, (R : ℕ) ≤ R' → (S : ℕ) ≤ S' → f R S ≤ f R' S')
    (g : ({x : ℝ // 0 < x} × {x : ℝ // 0 < x}) → ℝ) (hg : Continuous g)
    (hag : ∀ r s : {x : ℚ // 0 < x},
      g (⟨(r.val : ℝ), by exact_mod_cast r.property⟩,
        ⟨(s.val : ℝ), by exact_mod_cast s.property⟩) = rationalProfile f r s)
    (r s r' s' : {x : ℝ // 0 < x}) :
    g (r',s') ≤ max (r'.val/r.val) (s'.val/s.val)*g (r,s) := by
  have hd := positive_rat_cast_dense.prodMap positive_rat_cast_dense
  apply hd.induction_on₂ (p := fun u v =>
    g v ≤ max (v.1.val/u.1.val) (v.2.val/u.2.val)*g u) _ _ (r,s) (r',s')
  · have hd₁ : Continuous (fun z :
        ({x : ℝ // 0 < x} × {x : ℝ // 0 < x}) ×
        ({x : ℝ // 0 < x} × {x : ℝ // 0 < x}) => z.2.1.val/z.1.1.val) :=
        (by fun_prop : Continuous (fun z :
          ({x : ℝ // 0 < x} × {x : ℝ // 0 < x}) ×
          ({x : ℝ // 0 < x} × {x : ℝ // 0 < x}) => z.2.1.val)).div
          (by fun_prop) (fun z => z.1.1.property.ne')
    have hd₂ : Continuous (fun z :
        ({x : ℝ // 0 < x} × {x : ℝ // 0 < x}) ×
        ({x : ℝ // 0 < x} × {x : ℝ // 0 < x}) => z.2.2.val/z.1.2.val) :=
        (by fun_prop : Continuous (fun z :
          ({x : ℝ // 0 < x} × {x : ℝ // 0 < x}) ×
          ({x : ℝ // 0 < x} × {x : ℝ // 0 < x}) => z.2.2.val)).div
          (by fun_prop) (fun z => z.1.2.property.ne')
    exact isClosed_le (hg.comp continuous_snd)
      ((hd₁.max hd₂).mul (hg.comp continuous_fst))
  · rintro ⟨r,s⟩ ⟨r',s'⟩
    dsimp only [Prod.map]
    rw [hag,hag]
    simpa only [Rat.cast_max, Rat.cast_div] using
      (rationalProfile_scale_compare f hbound hrep hmono r s r' s').2

/-- Monotonicity follows from the actual ratio bound and positive growth bound. -/
theorem continuous_profile_mono (f : ℕ+ → ℕ+ → ℝ)
    (hbound : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (hmin : ∀ R S : ℕ+, min (R : ℝ) (S : ℝ) ≤ f R S)
    (hrep : ∀ k R S : ℕ+, (k : ℝ) * f R S ≤ f (k * R) (k * S))
    (hmono : ∀ R S R' S' : ℕ+, (R : ℕ) ≤ R' → (S : ℕ) ≤ S' → f R S ≤ f R' S')
    (g : ({x : ℝ // 0 < x} × {x : ℝ // 0 < x}) → ℝ) (hg : Continuous g)
    (hag : ∀ r s : {x : ℚ // 0 < x},
      g (⟨(r.val : ℝ), by exact_mod_cast r.property⟩,
        ⟨(s.val : ℝ), by exact_mod_cast s.property⟩) = rationalProfile f r s)
    (r s r' s' : {x : ℝ // 0 < x}) (hr : r.val ≤ r'.val) (hs : s.val ≤ s'.val) :
    g (r,s) ≤ g (r',s') := by
  have hh := continuous_profile_scale_upper f hbound hrep hmono g hg hag r' s' r s
  have hnonneg : 0 ≤ g (r',s') := (lt_min r'.property s'.property).le.trans
    (continuous_profile_bounds f hbound hmin g hg hag r' s').1
  have hc : max (r.val/r'.val) (s.val/s'.val) ≤ 1 := max_le
    ((div_le_one r'.property).mpr hr) ((div_le_one s'.property).mpr hs)
  exact hh.trans ((mul_le_mul_of_nonneg_right hc hnonneg).trans_eq (one_mul _))

/-- Swapping the two integer inputs swaps the literal rational rescaling. -/
theorem rationalProfile_interchange (f h : ℕ+ → ℕ+ → ℝ)
    (hswap : ∀ R S, f R S = h S R) (r s : {x : ℚ // 0 < x}) :
    rationalProfile f r s = rationalProfile h s r := by
  unfold rationalProfile
  congr 1
  ext v
  constructor
  · rintro ⟨q,hq,R,S,hr,hs,hv⟩
    exact ⟨q,hq,S,R,hs,hr,by simpa only [hswap R S] using hv⟩
  · rintro ⟨q,hq,S,R,hs,hr,hv⟩
    exact ⟨q,hq,R,S,hr,hs,by simpa only [hswap R S] using hv⟩

/-- Interchange extends by density, without identifying unrelated orientations. -/
theorem continuous_profile_interchange (f h : ℕ+ → ℕ+ → ℝ)
    (hswap : ∀ R S, f R S = h S R)
    (g v : ({x : ℝ // 0 < x} × {x : ℝ // 0 < x}) → ℝ)
    (hg : Continuous g) (hv : Continuous v)
    (hag : ∀ r s : {x : ℚ // 0 < x},
      g (⟨(r.val : ℝ), by exact_mod_cast r.property⟩,
        ⟨(s.val : ℝ), by exact_mod_cast s.property⟩) = rationalProfile f r s)
    (hav : ∀ r s : {x : ℚ // 0 < x},
      v (⟨(r.val : ℝ), by exact_mod_cast r.property⟩,
        ⟨(s.val : ℝ), by exact_mod_cast s.property⟩) = rationalProfile h r s)
    (r s : {x : ℝ // 0 < x}) : g (r,s)=v (s,r) := by
  apply positive_rat_cast_dense.induction_on₂ (p := fun r s => g (r,s)=v (s,r)) _ _ r s
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro r s
    rw [hag,hav]
    exact rationalProfile_interchange f h hswap r s

end BlockIdentities.Rectangular
