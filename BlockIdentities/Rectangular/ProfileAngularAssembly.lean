/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.ProfileSlopeIncrements
public import BlockIdentities.Rectangular.AngularParameters
public import BlockIdentities.Rectangular.OrientedProfileRows

/-! Numerical assembly of the actual six-profile laws. No slopes, offsets,
quadratics, character parameters, or angular conclusions are assumed. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open scoped BigOperators

/-- The six source profile laws force the angular constraint. Functions are
used only on the positive quadrant; their values elsewhere are immaterial. -/
theorem angular_of_six_profile_laws (p : Axis → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc 0 1) (hpositive : ∀ i, 0 < p i)
    (g : LegPermutation → ℝ → ℝ → ℝ)
    (hg : ∀ π r s, 0 < r → 0 < s → 0 < g π r s)
    (hhom : ∀ π t r s, 0 < t → 0 < r → 0 < s →
      g π (t*r) (t*s) = t*g π r s)
    (hswap : ∀ π r s, 0 < r → 0 < s →
      g (convolutionSwapInputs π) s r = g π r s)
    (hconc : ∀ π, ConcaveOn ℝ (Set.Ioi 0)
      (fun s => g π 1 s ^ (1/p (convolutionLeftAxis π))))
    (hmono : ∀ π, MonotoneOn
      (fun s => g π 1 s ^ (1/p (convolutionLeftAxis π))) (Set.Ioi 0))
    (htri : ∀ π s, 0 < s →
      2*g π 1 s ^ (1/p (convolutionLeftAxis π)) +
        g (convolutionSwapSides π) 1 s ^ (1/p (convolutionLeftAxis π)) ≤
      g π 1 (3*s+1) ^ (1/p (convolutionLeftAxis π))) :
    Real.pi/2 ≤ ∑ i, Real.arccos (Real.sqrt (p i)) := by
  obtain ⟨L0, c01, c02, hL0, hc01, hc02, hb0, hu0, hi0⟩ :=
    common_positive_slope_offsets
      (fun s => g .xyz 1 s ^ (1/p 0)) (fun s => g .xzy 1 s ^ (1/p 0))
      (hconc .xyz) (hconc .xzy) (hmono .xyz) (hmono .xzy)
      (fun s hs => Real.rpow_pos_of_pos (hg .xyz 1 s zero_lt_one hs) _)
      (fun s hs => Real.rpow_pos_of_pos (hg .xzy 1 s zero_lt_one hs) _)
      (fun s hs => by simpa only [convolutionLeftAxis, convolutionSwapSides] using htri .xyz s hs)
      (fun s hs => by simpa only [convolutionLeftAxis, convolutionSwapSides] using htri .xzy s hs)
  obtain ⟨L1, c10, c12, hL1, hc10, hc12, hb1, hu1, hi1⟩ :=
    common_positive_slope_offsets
      (fun s => g .yxz 1 s ^ (1/p 1)) (fun s => g .zxy 1 s ^ (1/p 1))
      (hconc .yxz) (hconc .zxy) (hmono .yxz) (hmono .zxy)
      (fun s hs => Real.rpow_pos_of_pos (hg .yxz 1 s zero_lt_one hs) _)
      (fun s hs => Real.rpow_pos_of_pos (hg .zxy 1 s zero_lt_one hs) _)
      (fun s hs => by simpa only [convolutionLeftAxis, convolutionSwapSides] using htri .yxz s hs)
      (fun s hs => by simpa only [convolutionLeftAxis, convolutionSwapSides] using htri .zxy s hs)
  obtain ⟨L2, c20, c21, hL2, hc20, hc21, hb2, hu2, hi2⟩ :=
    common_positive_slope_offsets
      (fun s => g .yzx 1 s ^ (1/p 2)) (fun s => g .zyx 1 s ^ (1/p 2))
      (hconc .yzx) (hconc .zyx) (hmono .yzx) (hmono .zyx)
      (fun s hs => Real.rpow_pos_of_pos (hg .yzx 1 s zero_lt_one hs) _)
      (fun s hs => Real.rpow_pos_of_pos (hg .zyx 1 s zero_lt_one hs) _)
      (fun s hs => by simpa only [convolutionLeftAxis, convolutionSwapSides] using htri .yzx s hs)
      (fun s hs => by simpa only [convolutionLeftAxis, convolutionSwapSides] using htri .zyx s hs)
  have hs01 := profile_second_increment_of_slope (g .xyz)
    (hpositive 0) hL0 hc01 (hg .xyz) (hhom .xyz)
    (fun s hs => (hu0 s hs).1)
    (fun u v hu huv => (hi0 u v hu huv).1)
  have hs02 := profile_second_increment_of_slope (g .xzy)
    (hpositive 0) hL0 hc02 (hg .xzy) (hhom .xzy)
    (fun s hs => (hu0 s hs).2)
    (fun u v hu huv => (hi0 u v hu huv).2)
  have hs10 := profile_second_increment_of_slope (g .yxz)
    (hpositive 1) hL1 hc10 (hg .yxz) (hhom .yxz)
    (fun s hs => (hu1 s hs).1)
    (fun u v hu huv => (hi1 u v hu huv).1)
  have hs12 := profile_second_increment_of_slope (g .zxy)
    (hpositive 1) hL1 hc12 (hg .zxy) (hhom .zxy)
    (fun s hs => (hu1 s hs).2)
    (fun u v hu huv => (hi1 u v hu huv).2)
  have hs20 := profile_second_increment_of_slope (g .yzx)
    (hpositive 2) hL2 hc20 (hg .yzx) (hhom .yzx)
    (fun s hs => (hu2 s hs).1)
    (fun u v hu huv => (hi2 u v hu huv).1)
  have hs21 := profile_second_increment_of_slope (g .zyx)
    (hpositive 2) hL2 hc21 (hg .zyx) (hhom .zyx)
    (fun s hs => (hu2 s hs).2)
    (fun u v hu huv => (hi2 u v hu huv).2)
  have hQ01 := profile_pair_quadratic_of_second_increments (g .xyz) (g .yxz)
    hc01 hc10 (hg .xyz) (hhom .xyz) (hswap .xyz) hs01 hs10
  have hQ02 := profile_pair_quadratic_of_second_increments (g .xzy) (g .yzx)
    hc02 hc20 (hg .xzy) (hhom .xzy) (hswap .xzy) hs02 hs20
  have hQ12 := profile_pair_quadratic_of_second_increments (g .zxy) (g .zyx)
    hc12 hc21 (hg .zxy) (hhom .zxy) (hswap .zxy) hs12 hs21
  have h := angular_parameters_of_offset_quadratics (hp 0) (hp 1) (hp 2)
    hc01 hc02 hc10 hc12 hc20 hc21 hb0 hb1 hb2 hQ01 hQ02 hQ12
  have heq : (∑ i, Real.arccos (Real.sqrt (p i))) =
      Real.arccos (Real.sqrt (p 0)) + Real.arccos (Real.sqrt (p 1)) +
        Real.arccos (Real.sqrt (p 2)) := by
    rw [Fin.sum_univ_three]
  rwa [heq]

end BlockIdentities.Rectangular
