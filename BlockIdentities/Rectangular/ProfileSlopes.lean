/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Genuine slopes of concave monotone functions on the positive half-line.
These scalar lemmas do not define a tensor profile or assume a common slope. -/
@[expose] public section
noncomputable section
open Filter Topology
namespace BlockIdentities.Rectangular

/-- Every nondecreasing concave positive-axis function has an actual finite
nonnegative asymptotic ratio slope. -/
theorem concave_monotone_ratio_limit (P : ℝ → ℝ)
    (hconc : ConcaveOn ℝ (Set.Ioi 0) P) (hmono : MonotoneOn P (Set.Ioi 0)) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto (fun x : ℝ => P x / x) atTop (𝓝 L) := by
  let f : ℝ → ℝ := fun x => slope P 1 (max x 2)
  have hanti : Antitone f := by
    intro x y hxy
    exact hconc.antitoneOn_slope_gt (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
      ⟨(show 0 < max x 2 by linarith [le_max_right x 2]), by linarith [le_max_right x 2]⟩
      ⟨(show 0 < max y 2 by linarith [le_max_right y 2]), by linarith [le_max_right y 2]⟩
      (max_le_max_right 2 hxy)
  have hnonneg (x : ℝ) : 0 ≤ f x := by
    change 0 ≤ slope P 1 (max x 2)
    rw [slope_def_field]
    exact div_nonneg (sub_nonneg.mpr (hmono (by norm_num)
      (show 0 < max x 2 by linarith [le_max_right x 2]) (by linarith [le_max_right x 2])))
      (by linarith [le_max_right x 2])
  have hbdd : BddBelow (Set.range f) := ⟨0, by rintro y ⟨x, rfl⟩; exact hnonneg x⟩
  let L := iInf f
  have hlim : Tendsto f atTop (𝓝 L) := tendsto_atTop_ciInf hanti hbdd
  have hL : 0 ≤ L := ge_of_tendsto hlim (Filter.Eventually.of_forall hnonneg)
  have hslope : Tendsto (fun x : ℝ => slope P 1 x) atTop (𝓝 L) := by
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    dsimp only [f]
    rw [max_eq_left hx]
  have hdiv₁ : Tendsto (fun x : ℝ => (1 : ℝ) / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hdivP : Tendsto (fun x : ℝ => P 1 / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hratio : Tendsto (fun x : ℝ => slope P 1 x * (1 - 1 / x) + P 1 / x)
      atTop (𝓝 L) := by
    simpa only [sub_zero, mul_one, add_zero] using
      (hslope.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hdiv₁)).add hdivP
  refine ⟨L, hL, hratio.congr' ?_⟩
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
  rw [slope_def_field]
  field_simp [show x ≠ 0 by linarith, show x - 1 ≠ 0 by linarith]
  <;> ring

/-- Any fixed anchor has the same asymptotic secant slope as the ratio limit. -/
theorem slope_tendsto_of_ratio {P : ℝ → ℝ} {L : ℝ}
    (hlim : Tendsto (fun x : ℝ => P x / x) atTop (𝓝 L)) (u : ℝ) :
    Tendsto (fun x : ℝ => slope P u x) atTop (𝓝 L) := by
  have hdivu : Tendsto (fun x : ℝ => u / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hdivP : Tendsto (fun x : ℝ => P u / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h : Tendsto (fun x : ℝ => (P x / x - P u / x) / (1 - u / x))
      atTop (𝓝 L) := by
    have hraw := (hlim.sub hdivP).div
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hdivu) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    simp only [sub_zero, div_one] at hraw
    convert hraw using 1
  apply h.congr'
  filter_upwards [eventually_gt_atTop (max u 0)] with x hx
  rw [slope_def_field]
  have hx0 : x ≠ 0 := by have := le_max_right u 0; linarith
  have hxu : x - u ≠ 0 := by have := le_max_left u 0; linarith
  field_simp [hx0, hxu]
  <;> ring

/-- The actual asymptotic slope is a lower bound on every positive secant. -/
theorem concave_increment_ge_ratio_slope {P : ℝ → ℝ} {L : ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0) P)
    (hlim : Tendsto (fun x : ℝ => P x / x) atTop (𝓝 L))
    {u v : ℝ} (hu : 0 < u) (huv : u < v) : L * (v - u) ≤ P v - P u := by
  have hs := slope_tendsto_of_ratio hlim v
  have hbound : ∀ᶠ z : ℝ in atTop, slope P v z ≤ (P v - P u) / (v - u) := by
    filter_upwards [eventually_gt_atTop v] with z hz
    rw [slope_def_field]
    exact hconc.slope_anti_adjacent hu (show 0 < z by linarith) huv hz
  have h := le_of_tendsto hs hbound
  exact (le_div_iff₀ (sub_pos.mpr huv)).mp h

/-- Nonnegative positive-axis values dominate their actual asymptotic line;
no value or continuity at zero is needed. -/
theorem profile_ge_ratio_line {P : ℝ → ℝ} {L : ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0) P)
    (hpos : ∀ x : ℝ, 0 < x → 0 ≤ P x)
    (hlim : Tendsto (fun x : ℝ => P x / x) atTop (𝓝 L)) {v : ℝ} (hv : 0 < v) :
    L * v ≤ P v := by
  have hdiv : Tendsto (fun x : ℝ => v / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hleft : Tendsto (fun x : ℝ => L * (v - v / x)) atTop (𝓝 (L * v)) := by
    simpa only [sub_zero] using tendsto_const_nhds.mul (tendsto_const_nhds.sub hdiv)
  apply le_of_tendsto hleft
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hxpos : 0 < x := by linarith
  have hu : 0 < v / x := div_pos hv hxpos
  have huv : v / x < v := (div_lt_iff₀ hxpos).mpr (by nlinarith)
  have h := concave_increment_ge_ratio_slope hconc hlim hu huv
  linarith only [h, hpos (v / x) hu]

private theorem tripling_ratio_limit {P : ℝ → ℝ} {L : ℝ}
    (hlim : Tendsto (fun x : ℝ => P x / x) atTop (𝓝 L)) :
    Tendsto (fun x : ℝ => P (3 * x + 1) / x) atTop (𝓝 (3 * L)) := by
  have hscale : Tendsto (fun x : ℝ => 3 * x + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (max b 0)] with x hx
    have hx₁ := (le_max_left b 0).trans hx
    have hx₂ := (le_max_right b 0).trans hx
    linarith
  have hdiv : Tendsto (fun x : ℝ => (1 : ℝ) / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h : Tendsto (fun x : ℝ => (P (3 * x + 1) / (3 * x + 1)) * (3 + 1 / x))
      atTop (𝓝 (3 * L)) := by
    simpa only [Function.comp_apply, add_zero, mul_comm L 3] using
      (hlim.comp hscale).mul ((tendsto_const_nhds (x := (3 : ℝ))).add hdiv)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  field_simp [show x ≠ 0 by linarith, show 3 * x + 1 ≠ 0 by linarith]
  <;> ring

/-- Coupled tripling forces equality of the independently constructed slopes. -/
theorem common_ratio_slope_of_tripling {P Q : ℝ → ℝ} {LP LQ : ℝ}
    (hP : Tendsto (fun x : ℝ => P x / x) atTop (𝓝 LP))
    (hQ : Tendsto (fun x : ℝ => Q x / x) atTop (𝓝 LQ))
    (hPQ : ∀ x : ℝ, 0 < x → 2 * P x + Q x ≤ P (3 * x + 1))
    (hQP : ∀ x : ℝ, 0 < x → 2 * Q x + P x ≤ Q (3 * x + 1)) : LP = LQ := by
  have hbound {f g : ℝ → ℝ} {A B : ℝ}
      (hf : Tendsto (fun x : ℝ => f x / x) atTop (𝓝 A))
      (hg : Tendsto (fun x : ℝ => g x / x) atTop (𝓝 B))
      (hfg : ∀ x : ℝ, 0 < x → 2 * f x + g x ≤ f (3 * x + 1)) : B ≤ A := by
    have hleft : Tendsto (fun x : ℝ => 2 * (f x / x) + g x / x)
        atTop (𝓝 (2 * A + B)) := (tendsto_const_nhds.mul hf).add hg
    have hright := tripling_ratio_limit hf
    have h := le_of_tendsto_of_tendsto hleft hright (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hh := div_le_div_of_nonneg_right (hfg x hx) hx.le
      simpa only [add_div, mul_div_assoc] using hh)
    linarith only [h]
  exact le_antisymm (hbound hQ hP hQP) (hbound hP hQ hPQ)

/-- Iterating the actual affine tripling step gives the source sum-majorant.
The ratio limit is consumed here only after it has been constructed above. -/
theorem tripling_sum_majorant {R : ℝ → ℝ} {M : ℝ}
    (hlim : Tendsto (fun x : ℝ => R x / x) atTop (𝓝 M))
    (hstep : ∀ x : ℝ, 0 < x → 3 * R x ≤ R (3 * x + 1))
    {s : ℝ} (hs : 0 < s) : R s ≤ M * (s + 1 / 2) := by
  let sn : ℕ → ℝ := fun n => (3 : ℝ) ^ n * (s + 1 / 2) - 1 / 2
  have hsnpos (n : ℕ) : 0 < sn n := by
    have hpow := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3) (n := n)
    dsimp only [sn]
    nlinarith
  have hsnstep (n : ℕ) : sn (n + 1) = 3 * sn n + 1 := by
    dsimp only [sn]
    rw [pow_succ]
    ring
  have hlower (n : ℕ) : (3 : ℝ) ^ n * R s ≤ R (sn n) := by
    induction n with
    | zero => simp only [sn, pow_zero, one_mul, add_sub_cancel_right, le_refl]
    | succ n ih =>
      rw [hsnstep, pow_succ]
      have h := hstep (sn n) (hsnpos n)
      nlinarith only [h, ih]
  have hpow : Tendsto (fun n : ℕ => (3 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hsn : Tendsto sn atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    have hsp : 0 < s + (1 : ℝ) / 2 := by linarith
    filter_upwards [hpow.eventually (eventually_ge_atTop ((b + 1 / 2) / (s + 1 / 2)))] with n hn
    have h := (div_le_iff₀ hsp).mp hn
    dsimp only [sn]
    linarith only [h]
  have hdiv : Tendsto (fun n : ℕ => (1 / 2 : ℝ) / (3 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpow
  have hscaled : Tendsto (fun n : ℕ => R (sn n) / (3 : ℝ) ^ n)
      atTop (𝓝 (M * (s + 1 / 2))) := by
    have h := (hlim.comp hsn).mul ((tendsto_const_nhds (x := s + 1 / 2)).sub hdiv)
    simp only [sub_zero] at h
    apply h.congr'
    exact Filter.Eventually.of_forall (fun n => by
      have hp : (3 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      have hn : sn n ≠ 0 := (hsnpos n).ne'
      change R (sn n) / sn n * (s + 1 / 2 - 1 / 2 / (3 : ℝ) ^ n) =
        R (sn n) / (3 : ℝ) ^ n
      have he : s + 1 / 2 - 1 / 2 / (3 : ℝ) ^ n = sn n / (3 : ℝ) ^ n := by
        dsimp only [sn]
        field_simp [hp]
        <;> ring
      rw [he]
      field_simp [hp, hn])
  apply ge_of_tendsto hscaled
  exact Filter.Eventually.of_forall (fun n =>
    (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 3) n)).mpr
      (by simpa only [mul_comm] using hlower n))

private theorem residual_offsets (f g : ℝ → ℝ)
    (hf : MonotoneOn f (Set.Ioi 0)) (hg : MonotoneOn g (Set.Ioi 0))
    (hf0 : ∀ s, 0 < s → 0 ≤ f s) (hg0 : ∀ s, 0 < s → 0 ≤ g s)
    (hbudget : ∀ s, 0 < s → f s + g s ≤ 1) :
    ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ c + d ≤ 1 ∧
      (∀ s, 0 < s → f s ≤ c) ∧ (∀ s, 0 < s → g s ≤ d) := by
  let rf := Set.range (fun s : Set.Ioi (0 : ℝ) => f s)
  let rg := Set.range (fun s : Set.Ioi (0 : ℝ) => g s)
  have hrf : rf.Nonempty := ⟨f 1, ⟨⟨1, by norm_num⟩, rfl⟩⟩
  have hrg : rg.Nonempty := ⟨g 1, ⟨⟨1, by norm_num⟩, rfl⟩⟩
  have hfbdd : BddAbove rf := ⟨1, by
    rintro y ⟨s, rfl⟩
    linarith only [hbudget s s.property, hg0 s s.property]⟩
  have hgbdd : BddAbove rg := ⟨1, by
    rintro y ⟨s, rfl⟩
    linarith only [hbudget s s.property, hf0 s s.property]⟩
  let c := sSup rf
  let d := sSup rg
  have hfc (s : ℝ) (hs : 0 < s) : f s ≤ c := le_csSup hfbdd ⟨⟨s, hs⟩, rfl⟩
  have hgd (s : ℝ) (hs : 0 < s) : g s ≤ d := le_csSup hgbdd ⟨⟨s, hs⟩, rfl⟩
  have hcross (s t : ℝ) (hs : 0 < s) (ht : 0 < t) : f s + g t ≤ 1 := by
    have hm : 0 < max s t := hs.trans_le (le_max_left _ _)
    have hfs := hf hs hm (le_max_left s t)
    have hgt := hg ht hm (le_max_right s t)
    linarith only [hfs, hgt, hbudget (max s t) hm]
  have hcbound (t : ℝ) (ht : 0 < t) : c ≤ 1 - g t := by
    apply csSup_le hrf
    rintro y ⟨s, rfl⟩
    linarith only [hcross s t s.property ht]
  have hdbound : d ≤ 1 - c := by
    apply csSup_le hrg
    rintro y ⟨t, rfl⟩
    linarith only [hcbound t t.property]
  exact ⟨c, d, (hf0 1 (by norm_num)).trans (hfc 1 (by norm_num)),
    (hg0 1 (by norm_num)).trans (hgd 1 (by norm_num)), by linarith only [hdbound], hfc, hgd⟩

/-- The source common positive slope and bounded offsets are actual consequences
of concavity, monotonicity, strict positivity and the two coupled tripling laws.
No common slope, affine majorant, offset or asymptotic limit is assumed. -/
theorem common_positive_slope_offsets (P Q : ℝ → ℝ)
    (hPc : ConcaveOn ℝ (Set.Ioi 0) P) (hQc : ConcaveOn ℝ (Set.Ioi 0) Q)
    (hPm : MonotoneOn P (Set.Ioi 0)) (hQm : MonotoneOn Q (Set.Ioi 0))
    (hPpos : ∀ s : ℝ, 0 < s → 0 < P s) (hQpos : ∀ s : ℝ, 0 < s → 0 < Q s)
    (hPQ : ∀ s : ℝ, 0 < s → 2 * P s + Q s ≤ P (3 * s + 1))
    (hQP : ∀ s : ℝ, 0 < s → 2 * Q s + P s ≤ Q (3 * s + 1)) :
    ∃ L c d : ℝ, 0 < L ∧ 0 ≤ c ∧ 0 ≤ d ∧ c + d ≤ 1 ∧
      (∀ s : ℝ, 0 < s → P s ≤ L * (s + c) ∧ Q s ≤ L * (s + d)) ∧
      (∀ u v : ℝ, 0 < u → u < v →
        L * (v - u) ≤ P v - P u ∧ L * (v - u) ≤ Q v - Q u) := by
  obtain ⟨L, hL0, hPlim⟩ := concave_monotone_ratio_limit P hPc hPm
  obtain ⟨M, hM0, hQlim⟩ := concave_monotone_ratio_limit Q hQc hQm
  have hLM := common_ratio_slope_of_tripling hPlim hQlim hPQ hQP
  subst M
  have hsumlim : Tendsto (fun x : ℝ => (P x + Q x) / x) atTop (𝓝 (2 * L)) := by
    simpa only [add_div, two_mul] using hPlim.add hQlim
  have hmajor (s : ℝ) (hs : 0 < s) : P s + Q s ≤ L * (2 * s + 1) := by
    have h := tripling_sum_majorant hsumlim (fun x hx => by
      have h₁ := hPQ x hx
      have h₂ := hQP x hx
      linarith only [h₁, h₂]) hs
    convert h using 1 <;> ring
  have hL : 0 < L := by
    have h := hmajor 1 (by norm_num)
    have hp := hPpos 1 (by norm_num)
    have hq := hQpos 1 (by norm_num)
    linarith
  let f : ℝ → ℝ := fun s => P s / L - s
  let g : ℝ → ℝ := fun s => Q s / L - s
  have hres {H : ℝ → ℝ} (hconc : ConcaveOn ℝ (Set.Ioi 0) H)
      (hpos : ∀ s, 0 < s → 0 < H s)
      (hlim : Tendsto (fun x : ℝ => H x / x) atTop (𝓝 L)) :
      MonotoneOn (fun s => H s / L - s) (Set.Ioi 0) ∧
      (∀ s, 0 < s → 0 ≤ H s / L - s) := by
    constructor
    · intro u hu v hv huv
      rcases eq_or_lt_of_le huv with rfl | huv
      · exact le_rfl
      have h := concave_increment_ge_ratio_slope hconc hlim hu huv
      have he : v - u ≤ (H v - H u) / L :=
        (le_div_iff₀ hL).mpr (by simpa only [mul_comm] using h)
      rw [sub_div] at he
      linarith only [he]
    · intro s hs
      have h := profile_ge_ratio_line hconc (fun s hs => (hpos s hs).le) hlim hs
      have hd : s ≤ H s / L := (le_div_iff₀ hL).mpr (by simpa only [mul_comm] using h)
      linarith only [hd]
  obtain ⟨hfm, hf0⟩ := hres hPc hPpos hPlim
  obtain ⟨hgm, hg0⟩ := hres hQc hQpos hQlim
  have hbudget (s : ℝ) (hs : 0 < s) : f s + g s ≤ 1 := by
    have h := (div_le_div_of_nonneg_right (hmajor s hs) hL.le)
    have he : (L * (2 * s + 1)) / L = 2 * s + 1 := by field_simp [hL.ne']
    rw [he, add_div] at h
    dsimp only [f, g]
    linarith only [h]
  obtain ⟨c, d, hc, hd, hcd, hfc, hgd⟩ := residual_offsets f g hfm hgm hf0 hg0 hbudget
  refine ⟨L, c, d, hL, hc, hd, hcd, ?_, ?_⟩
  · intro s hs
    have hp := hfc s hs
    have hq := hgd s hs
    dsimp only [f] at hp
    dsimp only [g] at hq
    constructor
    · have hh : P s ≤ (s + c) * L := (div_le_iff₀ hL).mp (by linarith only [hp])
      nlinarith only [hh]
    · have hh : Q s ≤ (s + d) * L := (div_le_iff₀ hL).mp (by linarith only [hq])
      nlinarith only [hh]
  · intro u v hu huv
    exact ⟨concave_increment_ge_ratio_slope hPc hPlim hu huv,
      concave_increment_ge_ratio_slope hQc hQlim hu huv⟩

end BlockIdentities.Rectangular
