/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.ProfileRescalingBounds
public import Mathlib.Topology.UniformSpace.CompleteSeparated
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.Instances.Rat

/-! Actual continuous extension from dense metric data with locally bounded
Lipschitz constants. The extension is asserted only after proving existence. -/
@[expose] public section
noncomputable section
open Filter Topology
namespace BlockIdentities.Rectangular

/-- A dense isometric domain and genuine local Lipschitz bounds give a unique
continuous extension, by Cauchy filters in the complete real codomain. -/
theorem exists_unique_continuous_extension_of_local_bounds
    {α β : Type*} [MetricSpace α] [MetricSpace β]
    (i : α → β) (hi : Isometry i) (hdense : DenseRange i) (f : α → ℝ)
    (hlocal : ∀ b : β, ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧
      ∀ x y : α, dist (i x) b < ρ → dist (i y) b < ρ →
        dist (f x) (f y) ≤ K * dist (i x) (i y)) :
    ∃! g : β → ℝ, Continuous g ∧ ∀ x, g (i x) = f x := by
  let di : IsDenseInducing i := ⟨hi.isEmbedding.isInducing, hdense⟩
  have hcauchy (b : β) : Cauchy (map f (comap i (𝓝 b))) := by
    haveI : NeBot (comap i (𝓝 b)) := di.comap_nhds_neBot b
    refine Metric.cauchy_iff.mpr ⟨by infer_instance, ?_⟩
    intro ε hε
    obtain ⟨ρ, K, hρ, hK, hbound⟩ := hlocal b
    let δ := min ρ (ε / (2 * (K + 1)))
    have hδ : 0 < δ := lt_min hρ (div_pos hε (by positivity))
    let u := i ⁻¹' Metric.ball b δ
    refine ⟨f '' u, ?_, ?_⟩
    · apply Filter.mem_map.mpr
      apply Filter.mem_of_superset (Filter.preimage_mem_comap (Metric.ball_mem_nhds b hδ))
      intro x hx
      exact ⟨x, hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have hxδ : dist (i x) b < δ := hx
      have hyδ : dist (i y) b < δ := hy
      have hxρ : dist (i x) b < ρ := hxδ.trans_le (min_le_left _ _)
      have hyρ : dist (i y) b < ρ := hyδ.trans_le (min_le_left _ _)
      have hdist : dist (i x) (i y) < 2 * δ := by
        have htri := dist_triangle (i x) b (i y)
        rw [dist_comm b (i y)] at htri
        linarith only [htri, hxδ, hyδ]
      have hδle : 2 * δ ≤ ε / (K + 1) := by
        have hh : δ ≤ ε / (2 * (K + 1)) := min_le_right _ _
        have hh' := (le_div_iff₀ (show 0 < 2 * (K + 1) by positivity)).mp hh
        apply (le_div_iff₀ (show 0 < K + 1 by linarith)).mpr
        nlinarith only [hh']
      have hsmall := (lt_div_iff₀ (show 0 < K + 1 by linarith)).mp (hdist.trans_le hδle)
      have h := hbound x y hxρ hyρ
      nlinarith only [h, hsmall, (show 0 ≤ dist (i x) (i y) from dist_nonneg)]
  have hcontinuous : Continuous (di.extend f) := di.continuous_extend_of_cauchy hcauchy
  have hagree (x : α) : di.extend f (i x) = f x := by
    obtain ⟨c, hc⟩ := CompleteSpace.complete (hcauchy (i x))
    have hp : pure x ≤ comap i (𝓝 (i x)) := by
      apply Filter.map_le_iff_le_comap.mp
      simpa only [Filter.map_pure] using pure_le_nhds (i x)
    have hpf : pure (f x) ≤ map f (comap i (𝓝 (i x))) := by
      simpa only [Filter.map_pure] using Filter.map_mono hp
    have he : f x = c := pure_le_nhds_iff.mp (hpf.trans hc)
    exact (di.extend_eq_of_tendsto hc).trans he.symm
  refine ⟨di.extend f, ⟨hcontinuous, hagree⟩, ?_⟩
  intro g hg
  exact (di.extend_unique hg.2 hg.1).symm

end BlockIdentities.Rectangular
