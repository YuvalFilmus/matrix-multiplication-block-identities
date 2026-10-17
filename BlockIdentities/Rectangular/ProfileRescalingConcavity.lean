/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.ProfileRescaling
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Fin.VecNotation

/-! Powered rational profile concavity from actual discrete neighboring
concavity and simultaneous supremum approximation. -/
@[expose] public section
noncomputable section
open Filter Topology
namespace BlockIdentities.Rectangular

private theorem positive_discrete_powered_jensen (f : ℕ+ → ℕ+ → ℝ) (ρ : ℝ)
    (hconc : ∀ R : ℕ+, ∀ n : ℕ,
      (f R ⟨n + 1, by omega⟩) ^ ρ + (f R ⟨n + 3, by omega⟩) ^ ρ ≤
        2 * (f R ⟨n + 2, by omega⟩) ^ ρ)
    (R S₁ S₂ S₃ : ℕ+) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hmix : (S₃ : ℝ) = t * (S₁ : ℝ) + (1 - t) * (S₂ : ℝ)) :
    t * (f R S₁) ^ ρ + (1 - t) * (f R S₂) ^ ρ ≤ (f R S₃) ^ ρ := by
  let y : ℕ → ℝ := fun n => (f R ⟨n + 1, by omega⟩) ^ ρ
  have hy : ∀ n, y n + y (n + 2) ≤ 2 * y (n + 1) := by
    intro n
    simpa only [y, Nat.add_assoc] using hconc R n
  let a := (S₁ : ℕ) - 1
  let b := (S₃ : ℕ) - 1
  let c := (S₂ : ℕ) - 1
  have hcast (S : ℕ+) : (((S : ℕ) - 1 : ℕ) : ℝ) = (S : ℝ) - 1 := by
    have he : (((S : ℕ) - 1 : ℕ) : ℝ) + 1 = (S : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel S.property)
    linarith only [he]
  have he : (b : ℝ) = t * (a : ℝ) + (1 - t) * (c : ℝ) := by
    dsimp only [a, b, c]
    rw [hcast, hcast, hcast]
    nlinarith only [hmix]
  have h := discrete_concave_jensen y hy ht he
  let idx (S : ℕ+) : ℕ+ := ⟨(S : ℕ) - 1 + 1, by omega⟩
  have hidx (S : ℕ+) : idx S = S := by
    apply Subtype.ext
    exact Nat.sub_add_cancel S.property
  change t * (f R (idx S₁)) ^ ρ + (1 - t) * (f R (idx S₂)) ^ ρ ≤ (f R (idx S₃)) ^ ρ at h
  simpa only [hidx] using h

/-- Every finite family of normalized samples can be chosen to converge to the
actual rational suprema, with one common integer scale at each stage. -/
theorem rationalProfile_simultaneous_limits {ι : Type*} [Fintype ι]
    (f : ℕ+ → ℕ+ → ℝ)
    (hbound : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (hrep : ∀ k R S : ℕ+, (k : ℝ) * f R S ≤ f (k * R) (k * S))
    (r s : ι → {x : ℚ // 0 < x}) :
    ∃ Q : ℕ → ℕ+, ∃ R S : ℕ → ι → ℕ+,
      (∀ n i, (Q n : ℚ) * (r i).val = (R n i : ℚ) ∧
        (Q n : ℚ) * (s i).val = (S n i : ℚ)) ∧
      (∀ i, Tendsto (fun n => f (R n i) (S n i) / (Q n : ℝ)) atTop
        (𝓝 (rationalProfile f (r i) (s i)))) := by
  classical
  have hchoices (n : ℕ) := rationalProfile_common_approximation f hrep r s
    (1 / ((n : ℝ) + 1)) (by positivity)
  choose Q R S h using hchoices
  refine ⟨Q, R, S, (fun n i => ⟨(h n i).1, (h n i).2.1⟩), ?_⟩
  intro i
  have hlower : Tendsto (fun n : ℕ => rationalProfile f (r i) (s i) - 1 / ((n : ℝ) + 1))
      atTop (𝓝 (rationalProfile f (r i) (s i))) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · exact Filter.Eventually.of_forall (fun n => (h n i).2.2.le)
  · apply Filter.Eventually.of_forall
    intro n
    apply le_csSup (rationalProfileSamples_bddAbove f hbound (r i) (s i))
    exact ⟨(Q n : ℚ), by exact_mod_cast (Q n).property, R n i, S n i,
      (h n i).1, (h n i).2.1, rfl⟩

/-- Actual discrete powered concavity passes to the rational rescaled profile.
The common-scale integer Jensen inequality is proved above and the three
normalized samples converge to the literal suprema. -/
theorem rationalProfile_powered_concave (f : ℕ+ → ℕ+ → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hf : ∀ R S : ℕ+, 0 ≤ f R S)
    (hbound : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (hrep : ∀ k R S : ℕ+, (k : ℝ) * f R S ≤ f (k * R) (k * S))
    (hconc : ∀ R : ℕ+, ∀ n : ℕ,
      (f R ⟨n + 1, by omega⟩) ^ ρ + (f R ⟨n + 3, by omega⟩) ^ ρ ≤
        2 * (f R ⟨n + 2, by omega⟩) ^ ρ)
    (r s₁ s₂ : {x : ℚ // 0 < x}) (t : ℚ) (ht : t ∈ Set.Icc 0 1)
    (s₃ : {x : ℚ // 0 < x}) (hmix : s₃.val = t * s₁.val + (1 - t) * s₂.val) :
    (t : ℝ) * rationalProfile f r s₁ ^ ρ +
      (1 - (t : ℝ)) * rationalProfile f r s₂ ^ ρ ≤ rationalProfile f r s₃ ^ ρ := by
  let ss : Fin 3 → {x : ℚ // 0 < x} := ![s₁, s₂, s₃]
  obtain ⟨Q, R, S, hcoords, hlim⟩ := rationalProfile_simultaneous_limits f hbound hrep
    (fun _ : Fin 3 => r) ss
  have hlim₀ := (Real.continuous_rpow_const hρ).continuousAt.tendsto.comp (hlim 0)
  have hlim₁ := (Real.continuous_rpow_const hρ).continuousAt.tendsto.comp (hlim 1)
  have hlim₂ := (Real.continuous_rpow_const hρ).continuousAt.tendsto.comp (hlim 2)
  have hlhs := ((tendsto_const_nhds (x := (t : ℝ))).mul hlim₀).add
    ((tendsto_const_nhds (x := 1 - (t : ℝ))).mul hlim₁)
  have htr : (t : ℝ) ∈ Set.Icc 0 1 := by
    constructor
    · exact_mod_cast ht.1
    · exact_mod_cast ht.2
  apply le_of_tendsto_of_tendsto hlhs hlim₂
  apply Filter.Eventually.of_forall
  intro n
  have hR (i : Fin 3) : R n i = R n 0 := by
    apply PNat.coe_injective
    have he : (R n i : ℚ) = (R n 0 : ℚ) := (hcoords n i).1.symm.trans (hcoords n 0).1
    exact_mod_cast he
  have hm : (S n 2 : ℝ) = (t : ℝ) * (S n 0 : ℝ) + (1 - (t : ℝ)) * (S n 1 : ℝ) := by
    have he : (S n 2 : ℚ) = t * (S n 0 : ℚ) + (1 - t) * (S n 1 : ℚ) := by
      rw [← (hcoords n 2).2, ← (hcoords n 0).2, ← (hcoords n 1).2]
      change (Q n : ℚ) * s₃.val = t * ((Q n : ℚ) * s₁.val) + (1 - t) * ((Q n : ℚ) * s₂.val)
      rw [hmix]
      ring
    exact_mod_cast he
  have hJ := positive_discrete_powered_jensen f ρ hconc (R n 0) (S n 0) (S n 1) (S n 2) htr hm
  have hQpos : 0 < (Q n : ℝ) := by exact_mod_cast (Q n).property
  have hdiv := div_le_div_of_nonneg_right hJ (Real.rpow_nonneg hQpos.le ρ)
  rw [add_div, mul_div_assoc, mul_div_assoc] at hdiv
  change (t : ℝ) * (f (R n 0) (S n 0) / (Q n : ℝ)) ^ ρ +
    (1 - (t : ℝ)) * (f (R n 1) (S n 1) / (Q n : ℝ)) ^ ρ ≤
    (f (R n 2) (S n 2) / (Q n : ℝ)) ^ ρ
  rw [hR 1, hR 2,
    Real.div_rpow (hf (R n 0) (S n 0)) hQpos.le ρ,
    Real.div_rpow (hf (R n 0) (S n 1)) hQpos.le ρ,
    Real.div_rpow (hf (R n 0) (S n 2)) hQpos.le ρ]
  exact hdiv

end BlockIdentities.Rectangular
