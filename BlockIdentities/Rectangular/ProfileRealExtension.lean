/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.ProfileCompletion
public import Mathlib.Topology.Instances.Real.Lemmas

/-! Existence and uniqueness of the actual continuous positive-real profile
extension, derived from the rational local Lipschitz theorem. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular

private def positiveRatToReal (x : {q : ℚ // 0 < q}) : {r : ℝ // 0 < r} :=
  ⟨(x.val : ℝ), by exact_mod_cast x.property⟩

private theorem positiveRatToReal_isometry : Isometry positiveRatToReal := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  change dist (x.val : ℝ) (y.val : ℝ) = dist x.val y.val
  simp only [Real.dist_eq, Rat.dist_eq]

private theorem positiveRatToReal_dense : DenseRange positiveRatToReal := by
  apply Metric.denseRange_iff.mpr
  intro x ε hε
  have hinterval : max 0 (x.val - ε) < x.val := max_lt x.property (by linarith)
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn hinterval
  have hqp : 0 < (q : ℝ) := (le_max_left 0 (x.val - ε)).trans_lt hqlo
  have hq : 0 < q := by exact_mod_cast hqp
  refine ⟨⟨q, hq⟩, ?_⟩
  change dist x.val (q : ℝ) < ε
  rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hqhi)]
  have hh := (le_max_right 0 (x.val - ε)).trans_lt hqlo
  linarith only [hh]

/-- The extension is an actual uniquely existing continuous function on the
positive real quadrant, characterized by agreement with the literal rational
supremum. No off-domain defaults or promised real profile definitions occur. -/
theorem rationalProfile_exists_unique_continuous_extension (f : ℕ+ → ℕ+ → ℝ)
    (hbound : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (hmin : ∀ R S : ℕ+, min (R : ℝ) (S : ℝ) ≤ f R S)
    (hrep : ∀ k R S : ℕ+, (k : ℝ) * f R S ≤ f (k * R) (k * S))
    (hmono : ∀ R S R' S' : ℕ+, (R : ℕ) ≤ R' → (S : ℕ) ≤ S' → f R S ≤ f R' S') :
    ∃! g : ({r : ℝ // 0 < r} × {s : ℝ // 0 < s}) → ℝ,
      Continuous g ∧ ∀ r s : {q : ℚ // 0 < q},
        g (⟨(r.val : ℝ), by exact_mod_cast r.property⟩,
          ⟨(s.val : ℝ), by exact_mod_cast s.property⟩) = rationalProfile f r s := by
  let i : ({q : ℚ // 0 < q} × {q : ℚ // 0 < q}) →
      ({r : ℝ // 0 < r} × {r : ℝ // 0 < r}) :=
    fun x => (positiveRatToReal x.1, positiveRatToReal x.2)
  have hi : Isometry i := positiveRatToReal_isometry.prodMap positiveRatToReal_isometry
  have hdense : DenseRange i := positiveRatToReal_dense.prodMap positiveRatToReal_dense
  have hlocal (b : {r : ℝ // 0 < r} × {r : ℝ // 0 < r}) :
      ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧
      ∀ x y : {q : ℚ // 0 < q} × {q : ℚ // 0 < q},
        dist (i x) b < ρ → dist (i y) b < ρ →
        dist (rationalProfile f x.1 x.2) (rationalProfile f y.1 y.2) ≤ K * dist (i x) (i y) := by
    let ρ : ℝ := min b.1.val b.2.val / 2
    let K : ℝ := (b.1.val + b.2.val + 2 * ρ) / ρ
    have hb₁ : 0 < b.1.val := b.1.property
    have hb₂ : 0 < b.2.val := b.2.property
    have hρ : 0 < ρ := div_pos (lt_min b.1.property b.2.property) (by norm_num)
    have hK : 0 ≤ K := div_nonneg (by positivity) hρ.le
    refine ⟨ρ, K, hρ, hK, ?_⟩
    intro x y hx hy
    have hx' : max |(x.1.val : ℝ) - b.1.val| |(x.2.val : ℝ) - b.2.val| < ρ := by
      simpa only [i, positiveRatToReal, Prod.dist_eq, Subtype.dist_eq, Real.dist_eq] using hx
    have hx₁ := abs_lt.mp ((le_max_left _ _).trans_lt hx')
    have hx₂ := abs_lt.mp ((le_max_right _ _).trans_lt hx')
    have hρ₁ : 2 * ρ ≤ b.1.val := by dsimp only [ρ]; linarith [min_le_left b.1.val b.2.val]
    have hρ₂ : 2 * ρ ≤ b.2.val := by dsimp only [ρ]; linarith [min_le_right b.1.val b.2.val]
    have hden : ρ ≤ min (x.1.val : ℝ) (x.2.val : ℝ) := le_min (by linarith) (by linarith)
    have hnum : (x.1.val : ℝ) + x.2.val ≤ b.1.val + b.2.val + 2 * ρ := by linarith
    have hminpos : 0 < min (x.1.val : ℝ) (x.2.val : ℝ) := hρ.trans_le hden
    have hcoeff : ((x.1.val : ℝ) + x.2.val) / min (x.1.val : ℝ) (x.2.val : ℝ) ≤ K := by
      exact (div_le_div_of_nonneg_right hnum hminpos.le).trans
        (div_le_div_of_nonneg_left (by positivity) hρ hden)
    have hlip := rationalProfile_local_lipschitz f hbound hmin hrep hmono x.1 x.2 y.1 y.2
    have hδ : 0 ≤ max |(y.1.val : ℝ) - x.1.val| |(y.2.val : ℝ) - x.2.val| :=
      (abs_nonneg _).trans (le_max_left _ _)
    have h := hlip.trans (mul_le_mul_of_nonneg_right hcoeff hδ)
    simpa only [i, positiveRatToReal, Prod.dist_eq, Subtype.dist_eq, Real.dist_eq, abs_sub_comm] using h
  obtain ⟨g, hg, huniq⟩ := exists_unique_continuous_extension_of_local_bounds i hi hdense
    (fun x => rationalProfile f x.1 x.2) hlocal
  refine ⟨g, ⟨hg.1, fun r s => hg.2 (r, s)⟩, ?_⟩
  intro g' hg'
  exact huniq g' ⟨hg'.1, fun x => hg'.2 x.1 x.2⟩

end BlockIdentities.Rectangular
