/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedProfileRows
public import BlockIdentities.Rectangular.ProfileRealConcavity
public import BlockIdentities.Rectangular.ProfileRescalingConcavity
public import BlockIdentities.Rectangular.ProfileRealOrder

/-! Actual six-profile completion from the literal convolution values.
Off-quadrant values are chosen only locally inside an existence proof. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open scoped Topology
variable {F : Type*} [Field F]

/-- Each genuine discrete convolution profile has its unique continuous
positive-quadrant extension, agreeing with the literal rational supremum. -/
theorem exists_oriented_convolution_continuous_profiles (S : InteriorSupport F) :
    ∃ G : LegPermutation → ({x : ℝ // 0 < x} × {x : ℝ // 0 < x}) → ℝ,
      (∀ π, Continuous (G π)) ∧
      ∀ π (r s : {x : ℚ // 0 < x}),
        G π (⟨(r.val : ℝ), by exact_mod_cast r.property⟩,
          ⟨(s.val : ℝ), by exact_mod_cast s.property⟩) =
          rationalProfile (convolutionProfile S π) r s := by
  have hex (π : LegPermutation) :=
    (rationalProfile_exists_unique_continuous_extension (convolutionProfile S π)
      (convolutionProfile_le_add S π) (min_le_convolutionProfile S π)
      (convolutionProfile_replication S π)
      (fun R b R' b' hr hs => convolutionProfile_mono S π hr hs)).exists
  choose G hc ha using hex
  exact ⟨G, hc, ha⟩

/-- All six real profile laws consumed by the numerical angular argument are
produced from actual convolution tensors. Positive support weights are used
only for the powered concavity/monotonicity/tripling branch. -/
theorem exists_oriented_convolution_profile_laws (S : InteriorSupport F)
    (hpositive : ∀ i, 0 < S.weight i) :
    ∃ g : LegPermutation → ℝ → ℝ → ℝ,
      (∀ π, Continuous (fun z : {x : ℝ // 0 < x} × {x : ℝ // 0 < x} => g π z.1.val z.2.val)) ∧
      (∀ π r s, 0 < r → 0 < s → min r s ≤ g π r s ∧ g π r s ≤ r + s) ∧
      (∀ π r s, 0 < r → 0 < s → 0 < g π r s) ∧
      (∀ π t r s, 0 < t → 0 < r → 0 < s → g π (t*r) (t*s) = t*g π r s) ∧
      (∀ π r s, 0 < r → 0 < s → g (convolutionSwapInputs π) s r = g π r s) ∧
      (∀ π r s r' s', 0 < r → 0 < s → 0 < r' → 0 < s' → r ≤ r' → s ≤ s' →
        g π r s ≤ g π r' s') ∧
      (∀ π, ConcaveOn ℝ (Set.Ioi 0) (fun s => g π 1 s ^ (1 / S.weight (convolutionLeftAxis π)))) ∧
      (∀ π, MonotoneOn (fun s => g π 1 s ^ (1 / S.weight (convolutionLeftAxis π))) (Set.Ioi 0)) ∧
      (∀ π s, 0 < s →
        2*g π 1 s ^ (1 / S.weight (convolutionLeftAxis π)) +
          g (convolutionSwapSides π) 1 s ^ (1 / S.weight (convolutionLeftAxis π)) ≤
          g π 1 (3*s+1) ^ (1 / S.weight (convolutionLeftAxis π))) := by
  classical
  obtain ⟨G, hGc, hGa⟩ := exists_oriented_convolution_continuous_profiles S
  let g : LegPermutation → ℝ → ℝ → ℝ := fun π r s =>
    if hr : 0 < r then if hs : 0 < s then G π (⟨r, hr⟩, ⟨s, hs⟩) else 0 else 0
  have hbound π := convolutionProfile_le_add S π
  have hmin π := min_le_convolutionProfile S π
  have hrep π := convolutionProfile_replication S π
  have hmono π := fun R b R' b' hr hs => convolutionProfile_mono S π (r := R) (s := b)
    (R := R') (b := b') hr hs
  have hbounds (π : LegPermutation) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
      min r s ≤ g π r s ∧ g π r s ≤ r + s := by
    simp only [g, dif_pos hr, dif_pos hs]
    exact continuous_profile_bounds (convolutionProfile S π) (hbound π) (hmin π)
      (G π) (hGc π) (hGa π) ⟨r, hr⟩ ⟨s, hs⟩
  have hgpos (π : LegPermutation) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) : 0 < g π r s :=
    (lt_min hr hs).trans_le (hbounds π r s hr hs).1
  have hgrid (π : LegPermutation) (r s r' s' : ℝ)
      (hr : 0 < r) (hs : 0 < s) (hr' : 0 < r') (hs' : 0 < s') (hrr : r ≤ r') (hss : s ≤ s') :
      g π r s ≤ g π r' s' := by
    simp only [g, dif_pos hr, dif_pos hs, dif_pos hr', dif_pos hs']
    exact continuous_profile_mono (convolutionProfile S π) (hbound π) (hmin π) (hrep π) (hmono π)
      (G π) (hGc π) (hGa π) ⟨r, hr⟩ ⟨s, hs⟩ ⟨r', hr'⟩ ⟨s', hs'⟩ hrr hss
  have hrationalConcave (π : LegPermutation) := rationalProfile_powered_concave
    (convolutionProfile S π) (1 / S.weight (convolutionLeftAxis π))
    (div_nonneg zero_le_one (hpositive _).le)
    (fun R b => (le_trans zero_le_one (one_le_convolutionProfile S π R b)))
    (hbound π) (hrep π) (by
      intro R n
      have hc := convolutionProfile_neighbor_powered S π R ⟨n + 2, by omega⟩ (by change 2 ≤ n + 2; omega) (hpositive _)
      have he₁ : (⟨(n + 2) - 1, by omega⟩ : ℕ+) = ⟨n + 1, by omega⟩ := by
        apply Subtype.ext
        change (n + 2) - 1 = n + 1
        omega
      have he₂ : (⟨(n + 2) + 1, by omega⟩ : ℕ+) = ⟨n + 3, by omega⟩ := by
        apply Subtype.ext
        change (n + 2) + 1 = n + 3
        omega
      change convolutionProfile S π R ⟨(n + 2) - 1, by omega⟩ ^
          (1 / S.weight (convolutionLeftAxis π)) +
        convolutionProfile S π R ⟨(n + 2) + 1, by omega⟩ ^
          (1 / S.weight (convolutionLeftAxis π)) ≤
        2 * convolutionProfile S π R ⟨n + 2, by omega⟩ ^
          (1 / S.weight (convolutionLeftAxis π)) at hc
      rw [he₁, he₂] at hc
      exact hc)
  have hrationalTri (π : LegPermutation) := rationalProfile_coupled_tripling
    (convolutionProfile S π) (convolutionProfile S (convolutionSwapSides π))
    (1 / S.weight (convolutionLeftAxis π)) (div_nonneg zero_le_one (hpositive _).le)
    (fun R b => le_trans zero_le_one (one_le_convolutionProfile S π R b))
    (fun R b => le_trans zero_le_one (one_le_convolutionProfile S (convolutionSwapSides π) R b))
    (hbound π) (hbound (convolutionSwapSides π)) (hrep π) (hrep (convolutionSwapSides π))
    (hmono π) (fun R b => convolutionProfile_tripling_powered S π R b (hpositive _))
  refine ⟨g, ?_, hbounds, hgpos, ?_, ?_, hgrid, ?_, ?_, ?_⟩
  · intro π
    have he : (fun z : {x : ℝ // 0 < x} × {x : ℝ // 0 < x} => g π z.1.val z.2.val) = G π := by
      funext z
      simp only [g, dif_pos z.1.property, dif_pos z.2.property]
    rw [he]
    exact hGc π
  · intro π t r s ht hr hs
    simp only [g, dif_pos hr, dif_pos hs, dif_pos (mul_pos ht hr), dif_pos (mul_pos ht hs)]
    exact continuous_profile_homogeneous (convolutionProfile S π) (hbound π)
      (G π) (hGc π) (hGa π) ⟨t, ht⟩ ⟨r, hr⟩ ⟨s, hs⟩
  · intro π r s hr hs
    simp only [g, dif_pos hr, dif_pos hs]
    exact (continuous_profile_interchange (convolutionProfile S π)
      (convolutionProfile S (convolutionSwapInputs π))
      (fun R b => convolutionProfile_input_swap S π R b)
      (G π) (G (convolutionSwapInputs π)) (hGc π) (hGc _) (hGa π) (hGa _)
      ⟨r, hr⟩ ⟨s, hs⟩).symm
  · intro π
    refine ⟨convex_Ioi 0, ?_⟩
    intro x hx y hy a b ha hb hab
    have hxpos : (0 : ℝ) < x := hx
    have hypos : (0 : ℝ) < y := hy
    have hm : 0 < a*x+b*y := (convex_Ioi (0 : ℝ)) hx hy ha hb hab
    have hc := continuous_profile_powered_concave (convolutionProfile S π)
      (1 / S.weight (convolutionLeftAxis π)) (div_nonneg zero_le_one (hpositive _).le)
      (G π) (hGc π) (hGa π) (hrationalConcave π) ⟨1, zero_lt_one⟩ ⟨x, hx⟩ ⟨y, hy⟩
      a ⟨ha, by linarith⟩ ⟨a*x+b*y, hm⟩ (by
        change a*x+b*y = a*x+(1-a)*y
        rw [show b=1-a from by linarith only [hab]])
    change a * (g π 1 x) ^ (1 / S.weight (convolutionLeftAxis π)) +
      b * (g π 1 y) ^ (1 / S.weight (convolutionLeftAxis π)) ≤
      (g π 1 (a*x+b*y)) ^ (1 / S.weight (convolutionLeftAxis π))
    simp only [g, dif_pos zero_lt_one, dif_pos hxpos, dif_pos hypos, dif_pos hm]
    simpa only [show 1-a=b from by linarith only [hab]] using hc
  · intro π x hx y hy hxy
    exact Real.rpow_le_rpow (hgpos π 1 x zero_lt_one hx).le
      (hgrid π 1 x 1 y zero_lt_one hx zero_lt_one hy le_rfl hxy)
      (div_nonneg zero_le_one (hpositive _).le)
  · intro π s hs
    have h3 : 0 < 3*s+1 := by positivity
    have hc := continuous_profile_tripling_of_rational (convolutionProfile S π)
      (convolutionProfile S (convolutionSwapSides π))
      (1 / S.weight (convolutionLeftAxis π)) (div_nonneg zero_le_one (hpositive _).le)
      (G π) (G (convolutionSwapSides π)) (hGc π) (hGc _) (hGa π) (hGa _)
      (hrationalTri π) ⟨1, zero_lt_one⟩ ⟨s, hs⟩
    simpa only [g, dif_pos zero_lt_one, dif_pos hs, dif_pos h3] using hc

end BlockIdentities.Rectangular
