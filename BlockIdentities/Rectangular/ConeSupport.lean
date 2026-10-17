/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.LinearAlgebra.Pi

/-! Supporting weights for a monotone sublinear function on a nonnegative cone.
The function is explicit input to this general convexity lemma. Applying it to
the actual matrix exponent requires proving its laws, not assuming a bound. -/
@[expose] public section
noncomputable section
open scoped BigOperators NNReal
namespace BlockIdentities.Rectangular

private def positiveCoordinates {ι : Type*} (x : ι → ℝ) : ι → ℝ≥0 :=
  fun i => Real.toNNReal (x i)

private theorem positiveCoordinates_coe {ι : Type*} (u : ι → ℝ≥0) :
    positiveCoordinates (fun i => (u i : ℝ)) = u := by
  funext i
  simp only [positiveCoordinates, Real.toNNReal_coe]

private theorem positiveCoordinates_smul {ι : Type*} {t : ℝ} (ht : 0 ≤ t)
    (x : ι → ℝ) :
    positiveCoordinates (t • x) = Real.toNNReal t • positiveCoordinates x := by
  funext i
  exact Real.toNNReal_mul ht

/-- A genuine Hahn--Banach support at a nonzero nonnegative direction. All
sublinearity hypotheses belong to the arbitrary input function of this lemma. -/
theorem exists_support_weights_of_sublinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : (ι → ℝ≥0) → ℝ) (hzero : w 0 = 0)
    (hadd : ∀ u v, w (u + v) ≤ w u + w v)
    (hhom : ∀ (t : ℝ≥0) u, w (t • u) = (t : ℝ) * w u)
    (hmono : ∀ u v, (∀ i, u i ≤ v i) → w u ≤ w v)
    (v : ι → ℝ≥0) (hv : v ≠ 0) :
    ∃ p : ι → ℝ, (∀ u : ι → ℝ≥0, (∑ i, p i * (u i : ℝ)) ≤ w u) ∧
      (∑ i, p i * (v i : ℝ)) = w v := by
  classical
  let vr : ι → ℝ := fun i => (v i : ℝ)
  have hvr : vr ≠ 0 := by
    intro he
    apply hv
    funext i
    apply NNReal.coe_injective
    simpa only [vr, Pi.zero_apply, NNReal.coe_zero] using congrFun he i
  have hnonneg (u : ι → ℝ≥0) : 0 ≤ w u := by
    rw [← hzero]
    exact hmono 0 u (fun i => bot_le)
  let N : (ι → ℝ) → ℝ := fun x => w (positiveCoordinates x)
  have hNh : ∀ t : ℝ, 0 < t → ∀ x, N (t • x) = t * N x := by
    intro t ht x
    dsimp only [N]
    rw [positiveCoordinates_smul ht.le, hhom, Real.coe_toNNReal _ ht.le]
  have hNa : ∀ x y, N (x + y) ≤ N x + N y := by
    intro x y
    exact (hmono _ _ (fun i => Real.toNNReal_add_le)).trans (hadd _ _)
  have hvanish : ∀ c : ℝ, c • vr = 0 → c • w v = 0 := by
    intro c hc
    have hc0 : c = 0 := (smul_eq_zero.mp hc).resolve_right hvr
    rw [hc0, zero_smul]
  let f : (ι → ℝ) →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' vr (w v) hvanish
  have hf : ∀ x : f.domain, f x ≤ N x := by
    intro x
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (show (x : ι → ℝ) ∈ Submodule.span ℝ {vr} from x.property)
    let y : f.domain := ⟨c • vr, by
      change c • vr ∈ Submodule.span ℝ {vr}
      exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩⟩
    have hxy : x = y := Subtype.ext hc.symm
    rw [hxy]
    change f y ≤ N (c • vr)
    have hfeq : f y = c * w v := by
      exact LinearPMap.mkSpanSingleton'_apply vr (w v) hvanish c y.property
    rw [hfeq]
    by_cases hc : 0 ≤ c
    · have he : positiveCoordinates (c • vr) = Real.toNNReal c • v := by
        rw [positiveCoordinates_smul hc]
        exact congrArg (fun z => Real.toNNReal c • z) (positiveCoordinates_coe v)
      dsimp only [N]
      rw [he, hhom, Real.coe_toNNReal _ hc]
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) (hnonneg v)).trans
        (hnonneg _)
  obtain ⟨g, hgf, hgN⟩ := exists_extension_of_le_sublinear f N hNh hNa hf
  have hgv : g vr = w v := by
    have h := hgf ⟨vr, Submodule.mem_span_singleton_self vr⟩
    exact h.trans (LinearPMap.mkSpanSingleton'_apply_self vr (w v) hvanish _)
  let p : ι → ℝ := fun i => g (Pi.single i 1)
  have hexpand (x : ι → ℝ) : g x = ∑ i, p i * x i := by
    have he : x = ∑ i, x i • Pi.single i (1 : ℝ) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      simp
    calc
      g x = g (∑ i, x i • Pi.single i (1 : ℝ)) := congrArg g he
      _ = ∑ i, g (x i • Pi.single i (1 : ℝ)) := map_sum g _ _
      _ = ∑ i, p i * x i := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [map_smul, smul_eq_mul, p]
        exact mul_comm _ _
  refine ⟨p, ?_, ?_⟩
  · intro u
    rw [← hexpand]
    have h := hgN (fun i => (u i : ℝ))
    simpa only [N, positiveCoordinates_coe] using h
  · rw [← hexpand]
    exact hgv

end BlockIdentities.Rectangular
