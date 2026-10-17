/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.ConeSupport
public import Mathlib.Tactic.Linarith

/-! Coordinate bounds for a supporting functional of a monotone function with
coordinate increments at most their length. -/
@[expose] public section
noncomputable section
open scoped BigOperators NNReal
namespace BlockIdentities.Rectangular

theorem support_weights_mem_Icc {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : (ι → ℝ≥0) → ℝ) (v : ι → ℝ≥0) (hv : ∀ i, 0 < v i)
    (p : ι → ℝ)
    (hs : ∀ u : ι → ℝ≥0, (∑ i, p i * (u i : ℝ)) ≤ w u)
    (ht : (∑ i, p i * (v i : ℝ)) = w v)
    (hm : ∀ u z, (∀ i, u i ≤ z i) → w u ≤ w z)
    (hi : ∀ u i, w (u + Pi.single i 1) ≤ w u + 1) :
    ∀ i, p i ∈ Set.Icc (0 : ℝ) 1 := by
  intro i
  have hsum (u : ι → ℝ≥0) (t : ℝ≥0) :
      (∑ j, p j * (((u + Pi.single i t : ι → ℝ≥0) j) : ℝ)) =
        (∑ j, p j * (u j : ℝ)) + p i * (t : ℝ) := by
    simp only [Pi.add_apply, NNReal.coe_add, mul_add, Finset.sum_add_distrib]
    congr 1
    simp [Pi.single_apply, apply_ite]
  have hup := (hs (v + Pi.single i 1)).trans (hi v i)
  rw [hsum, ht, NNReal.coe_one, mul_one] at hup
  let u : ι → ℝ≥0 := Function.update v i 0
  have hu : u + Pi.single i (v i) = v := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [u]
    · simp [u, hji, Pi.single_apply]
  have hum : w u ≤ w v := hm u v (by
    intro j
    by_cases hji : j = i
    · subst j
      simp [u]
    · simp [u, hji])
  have hlow := (hs u).trans hum
  have hcontact : (∑ j, p j * (u j : ℝ)) + p i * (v i : ℝ) = w v := by
    rw [← hsum, hu, ht]
  have hprod : 0 ≤ p i * (v i : ℝ) := by linarith
  have hvi : 0 < (v i : ℝ) := by exact_mod_cast hv i
  exact ⟨(mul_nonneg_iff_of_pos_right hvi).mp hprod, by linarith⟩

end BlockIdentities.Rectangular
