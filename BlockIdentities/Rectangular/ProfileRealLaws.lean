/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.ProfileRealExtension
public import BlockIdentities.Rectangular.ProfileRescalingTripling
public import Mathlib.Tactic.FunProp

/-! Laws of an actual continuous extension, transferred by density. All
agreements refer to the literal rational supremum; no extension is postulated. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular

/-- Positive rationals are dense in positive reals, with their actual cast. -/
theorem positive_rat_cast_dense : DenseRange
    (fun q : {x : ℚ // 0 < x} => (⟨(q.val : ℝ), by exact_mod_cast q.property⟩ : {x : ℝ // 0 < x})) := by
  apply Metric.denseRange_iff.mpr
  intro x ε hε
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn
    (show max 0 (x.val - ε) < x.val from max_lt x.property (by linarith))
  have hqp : 0 < (q : ℝ) := (le_max_left 0 (x.val - ε)).trans_lt hqlo
  have hq : 0 < q := by exact_mod_cast hqp
  refine ⟨⟨q, hq⟩, ?_⟩
  change dist x.val (q : ℝ) < ε
  rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hqhi)]
  have hh := (le_max_right 0 (x.val - ε)).trans_lt hqlo
  linarith only [hh]

/-- Both literal growth bounds survive the actual continuous extension. -/
theorem continuous_profile_bounds (f : ℕ+ → ℕ+ → ℝ)
    (hbound : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (hmin : ∀ R S : ℕ+, min (R : ℝ) (S : ℝ) ≤ f R S)
    (g : ({x : ℝ // 0 < x} × {x : ℝ // 0 < x}) → ℝ) (hg : Continuous g)
    (hagree : ∀ r s : {x : ℚ // 0 < x},
      g (⟨(r.val : ℝ), by exact_mod_cast r.property⟩,
        ⟨(s.val : ℝ), by exact_mod_cast s.property⟩) = rationalProfile f r s)
    (r s : {x : ℝ // 0 < x}) :
    min r.val s.val ≤ g (r,s) ∧ g (r,s) ≤ r.val + s.val := by
  apply positive_rat_cast_dense.induction_on₂ (p := fun r s =>
    min r.val s.val ≤ g (r,s) ∧ g (r,s) ≤ r.val + s.val) _ _ r s
  · have hlo : IsClosed {z : {x : ℝ // 0 < x} × {x : ℝ // 0 < x} |
        min z.1.val z.2.val ≤ g z} := isClosed_le (by fun_prop) hg
    have hhi : IsClosed {z : {x : ℝ // 0 < x} × {x : ℝ // 0 < x} |
        g z ≤ z.1.val + z.2.val} := isClosed_le hg (by fun_prop)
    exact hlo.inter hhi
  · intro r s
    rw [hagree]
    exact ⟨rationalProfile_min_lower f hbound hmin r s, rationalProfile_le f hbound r s⟩

/-- Degree-one homogeneity transfers from the actual rational rescaling. -/
theorem continuous_profile_homogeneous (f : ℕ+ → ℕ+ → ℝ)
    (hbound : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (g : ({x : ℝ // 0 < x} × {x : ℝ // 0 < x}) → ℝ) (hg : Continuous g)
    (hagree : ∀ r s : {x : ℚ // 0 < x},
      g (⟨(r.val : ℝ), by exact_mod_cast r.property⟩,
        ⟨(s.val : ℝ), by exact_mod_cast s.property⟩) = rationalProfile f r s)
    (t r s : {x : ℝ // 0 < x}) :
    g (⟨t.val*r.val, mul_pos t.property r.property⟩,
      ⟨t.val*s.val, mul_pos t.property s.property⟩) = t.val * g (r,s) := by
  apply positive_rat_cast_dense.induction_on₃ (p := fun t r s =>
    g (⟨t.val*r.val, mul_pos t.property r.property⟩,
      ⟨t.val*s.val, mul_pos t.property s.property⟩) = t.val * g (r,s)) _ _ t r s
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro t r s
    have he := hagree ⟨t.val*r.val, mul_pos t.property r.property⟩
      ⟨t.val*s.val, mul_pos t.property s.property⟩
    simp only [Rat.cast_mul] at he
    rw [he, hagree]
    exact rationalProfile_homogeneous f hbound r s t

/-- A proved rational tripling inequality extends to every positive real pair.
The premise is a finite-dimensional rational law, not the real conclusion. -/
theorem continuous_profile_tripling_of_rational
    (f h : ℕ+ → ℕ+ → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (g v : ({x : ℝ // 0 < x} × {x : ℝ // 0 < x}) → ℝ)
    (hg : Continuous g) (hv : Continuous v)
    (hag : ∀ r s : {x : ℚ // 0 < x},
      g (⟨(r.val : ℝ), by exact_mod_cast r.property⟩,
        ⟨(s.val : ℝ), by exact_mod_cast s.property⟩) = rationalProfile f r s)
    (hav : ∀ r s : {x : ℚ // 0 < x},
      v (⟨(r.val : ℝ), by exact_mod_cast r.property⟩,
        ⟨(s.val : ℝ), by exact_mod_cast s.property⟩) = rationalProfile h r s)
    (htri : ∀ r s : {x : ℚ // 0 < x},
      2 * rationalProfile f r s ^ ρ + rationalProfile h r s ^ ρ ≤
        rationalProfile f r ⟨3*s.val+r.val, add_pos (mul_pos (by norm_num) s.property) r.property⟩ ^ ρ)
    (r s : {x : ℝ // 0 < x}) :
    2 * g (r,s) ^ ρ + v (r,s) ^ ρ ≤
      g (r, ⟨3*s.val+r.val, add_pos (mul_pos (by norm_num) s.property) r.property⟩) ^ ρ := by
  have hc : Continuous (fun x : ℝ => x ^ ρ) := Real.continuous_rpow_const hρ
  apply positive_rat_cast_dense.induction_on₂ (p := fun r s =>
    2 * g (r,s) ^ ρ + v (r,s) ^ ρ ≤
      g (r, ⟨3*s.val+r.val, add_pos (mul_pos (by norm_num) s.property) r.property⟩) ^ ρ) _ _ r s
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro r s
    have he := hag r ⟨3*s.val+r.val, add_pos (mul_pos (by norm_num) s.property) r.property⟩
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat] at he
    rw [hag, hav, he]
    exact htri r s

end BlockIdentities.Rectangular
