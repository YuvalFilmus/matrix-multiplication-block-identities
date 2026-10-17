/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.ShapeCoordinateBound
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-! Actual coordinate cost bounds give joint continuity, including boundary shapes. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Arithmetic
open Filter
open scoped NNReal Topology
variable {F : Type*} [Field F]

private theorem formalShapeOmega_le_add_abs (a b c A B C : ℝ≥0) :
    formalShapeOmega F a b c ≤ formalShapeOmega F A B C +
      |(a : ℝ) - A| + |(b : ℝ) - B| + |(c : ℝ) - C| := by
  let da : ℝ≥0 := ⟨|(a : ℝ) - A|, abs_nonneg _⟩
  let db : ℝ≥0 := ⟨|(b : ℝ) - B|, abs_nonneg _⟩
  let dc : ℝ≥0 := ⟨|(c : ℝ) - C|, abs_nonneg _⟩
  have ha : a ≤ A + da := by
    change (a : ℝ) ≤ (A : ℝ) + |(a : ℝ) - A|
    linarith [le_abs_self ((a : ℝ) - A)]
  have hb : b ≤ B + db := by
    change (b : ℝ) ≤ (B : ℝ) + |(b : ℝ) - B|
    linarith [le_abs_self ((b : ℝ) - B)]
  have hc : c ≤ C + dc := by
    change (c : ℝ) ≤ (C : ℝ) + |(c : ℝ) - C|
    linarith [le_abs_self ((c : ℝ) - C)]
  have hm := formalShapeOmega_mono (F := F) ha hb hc
  have h1 := formalShapeOmega_add_first_le (F := F) A B C da
  have h2 := formalShapeOmega_add_second_le (F := F) (A + da) B C db
  have h3 := formalShapeOmega_add_third_le (F := F) (A + da) (B + db) C dc
  change formalShapeOmega F (A + da) B C ≤ formalShapeOmega F A B C + |(a : ℝ) - A| at h1
  change formalShapeOmega F (A + da) (B + db) C ≤
    formalShapeOmega F (A + da) B C + |(b : ℝ) - B| at h2
  change formalShapeOmega F (A + da) (B + db) (C + dc) ≤
    formalShapeOmega F (A + da) (B + db) C + |(c : ℝ) - C| at h3
  linarith

/-- A global coordinatewise Lipschitz estimate for the literal formal exponent. -/
theorem abs_formalShapeOmega_sub_le (a b c A B C : ℝ≥0) :
    |formalShapeOmega F a b c - formalShapeOmega F A B C| ≤
      |(a : ℝ) - A| + |(b : ℝ) - B| + |(c : ℝ) - C| := by
  have h1 := formalShapeOmega_le_add_abs (F := F) a b c A B C
  have h2 := formalShapeOmega_le_add_abs (F := F) A B C a b c
  rw [abs_sub_comm (A : ℝ) (a : ℝ), abs_sub_comm (B : ℝ) (b : ℝ),
    abs_sub_comm (C : ℝ) (c : ℝ)] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Joint convergence from coordinate convergence in real coercions, including
zero coordinates. No interior condition is used for this geometry theorem. -/
theorem tendsto_formalShapeOmega {ι : Type*} {l : Filter ι}
    {a b c : ι → ℝ≥0} {A B C : ℝ≥0}
    (ha : Tendsto (fun i => (a i : ℝ)) l (𝓝 (A : ℝ)))
    (hb : Tendsto (fun i => (b i : ℝ)) l (𝓝 (B : ℝ)))
    (hc : Tendsto (fun i => (c i : ℝ)) l (𝓝 (C : ℝ))) :
    Tendsto (fun i => formalShapeOmega F (a i) (b i) (c i)) l
      (𝓝 (formalShapeOmega F A B C)) := by
  have hsum : Tendsto (fun i => |(a i : ℝ) - A| + |(b i : ℝ) - B| + |(c i : ℝ) - C|)
      l (𝓝 0) := by
    simpa only [sub_self, abs_zero, add_zero] using
      ((ha.sub (tendsto_const_nhds : Tendsto (fun _ : ι => (A : ℝ)) l (𝓝 (A : ℝ)))).abs.add (hb.sub (tendsto_const_nhds : Tendsto (fun _ : ι => (B : ℝ)) l (𝓝 (B : ℝ)))).abs).add
        (hc.sub (tendsto_const_nhds : Tendsto (fun _ : ι => (C : ℝ)) l (𝓝 (C : ℝ)))).abs
  have hzero : Tendsto (fun i => |formalShapeOmega F (a i) (b i) (c i) -
      formalShapeOmega F A B C|) l (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) (fun i => abs_formalShapeOmega_sub_le _ _ _ _ _ _) hsum
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Real.dist_eq] using hzero

/-- Continuity on the complete nonnegative shape domain. -/
theorem continuous_formalShapeOmega :
    Continuous (fun p : ℝ≥0 × ℝ≥0 × ℝ≥0 => formalShapeOmega F p.1 p.2.1 p.2.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_formalShapeOmega
  · exact (NNReal.continuous_coe.comp continuous_fst).continuousAt
  · exact (NNReal.continuous_coe.comp (continuous_fst.comp continuous_snd)).continuousAt
  · exact (NNReal.continuous_coe.comp (continuous_snd.comp continuous_snd)).continuousAt
end BlockIdentities.Arithmetic
