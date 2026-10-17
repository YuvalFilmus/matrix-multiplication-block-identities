/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.ProfileRescalingFamily

/-! Coupled tripling for the actual rational sample suprema. Different profiles
are approximated at one scale using their individual replication laws. -/
@[expose] public section
noncomputable section
open Filter Topology
namespace BlockIdentities.Rectangular

/-- Discrete source length 3S+R-1 is enlarged monotonically to 3S+R before
rescaling. The two right profiles are genuinely different function arguments. -/
theorem rationalProfile_coupled_tripling (f h : ℕ+ → ℕ+ → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hf : ∀ R S : ℕ+, 0 ≤ f R S) (hh : ∀ R S : ℕ+, 0 ≤ h R S)
    (hbf : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (hbh : ∀ R S : ℕ+, h R S ≤ (R : ℝ) + S)
    (hrf : ∀ k R S : ℕ+, (k : ℝ) * f R S ≤ f (k * R) (k * S))
    (hrh : ∀ k R S : ℕ+, (k : ℝ) * h R S ≤ h (k * R) (k * S))
    (hmf : ∀ R S R' S' : ℕ+, (R : ℕ) ≤ R' → (S : ℕ) ≤ S' → f R S ≤ f R' S')
    (htri : ∀ R S : ℕ+, 2 * (f R S) ^ ρ + (h R S) ^ ρ ≤
      (f R ⟨3 * (S : ℕ) + (R : ℕ) - 1, by
        have hR : 0 < (R : ℕ) := R.property
        have hS : 0 < (S : ℕ) := S.property
        change 0 < 3 * (S : ℕ) + (R : ℕ) - 1
        omega⟩) ^ ρ)
    (r s : {x : ℚ // 0 < x}) :
    2 * rationalProfile f r s ^ ρ + rationalProfile h r s ^ ρ ≤
      rationalProfile f r ⟨3 * s.val + r.val, add_pos (mul_pos (by norm_num) s.property) r.property⟩ ^ ρ := by
  let ff : Bool → ℕ+ → ℕ+ → ℝ := fun b => if b then h else f
  have hbound : ∀ b, ∀ R S : ℕ+, ff b R S ≤ (R : ℝ) + S := by
    intro b
    cases b
    · exact hbf
    · exact hbh
  have hrep : ∀ b, ∀ k R S : ℕ+, (k : ℝ) * ff b R S ≤ ff b (k * R) (k * S) := by
    intro b
    cases b
    · exact hrf
    · exact hrh
  obtain ⟨Q, R, S, hcoords, hlim⟩ := rationalProfile_family_simultaneous_limits ff hbound hrep
    (fun _ => r) (fun _ => s)
  have hlimf : Tendsto (fun n => (f (R n false) (S n false) / (Q n : ℝ)) ^ ρ)
      atTop (𝓝 (rationalProfile f r s ^ ρ)) := by
    exact (Real.continuous_rpow_const hρ).continuousAt.tendsto.comp (hlim false)
  have hlimh : Tendsto (fun n => (h (R n true) (S n true) / (Q n : ℝ)) ^ ρ)
      atTop (𝓝 (rationalProfile h r s ^ ρ)) := by
    exact (Real.continuous_rpow_const hρ).continuousAt.tendsto.comp (hlim true)
  have hlhs := ((tendsto_const_nhds (x := (2 : ℝ))).mul hlimf).add hlimh
  apply le_of_tendsto hlhs
  apply Filter.Eventually.of_forall
  intro n
  have hR : R n true = R n false := by
    apply PNat.coe_injective
    have he : (R n true : ℚ) = (R n false : ℚ) := (hcoords n true).1.symm.trans (hcoords n false).1
    exact_mod_cast he
  have hS : S n true = S n false := by
    apply PNat.coe_injective
    have he : (S n true : ℚ) = (S n false : ℚ) := (hcoords n true).2.symm.trans (hcoords n false).2
    exact_mod_cast he
  rw [hR, hS]
  let U : ℕ+ := ⟨3 * (S n false : ℕ) + (R n false : ℕ) - 1, by
    have hr : 0 < (R n false : ℕ) := (R n false).property
    have hs : 0 < (S n false : ℕ) := (S n false).property
    change 0 < 3 * (S n false : ℕ) + (R n false : ℕ) - 1
    omega⟩
  let T : ℕ+ := ⟨3 * (S n false : ℕ) + (R n false : ℕ), by
    have hr : 0 < (R n false : ℕ) := (R n false).property
    change 0 < 3 * (S n false : ℕ) + (R n false : ℕ)
    omega⟩
  have hQpos : 0 < (Q n : ℝ) := by exact_mod_cast (Q n).property
  have hdiv := div_le_div_of_nonneg_right (htri (R n false) (S n false))
    (Real.rpow_nonneg hQpos.le ρ)
  rw [add_div, mul_div_assoc] at hdiv
  have hnorm : 2 * (f (R n false) (S n false) / (Q n : ℝ)) ^ ρ +
      (h (R n false) (S n false) / (Q n : ℝ)) ^ ρ ≤
      (f (R n false) U / (Q n : ℝ)) ^ ρ := by
    rw [Real.div_rpow (hf _ _) hQpos.le ρ, Real.div_rpow (hh _ _) hQpos.le ρ,
      Real.div_rpow (hf _ _) hQpos.le ρ]
    simpa only [U] using hdiv
  have hUT : (U : ℕ) ≤ T := by
    change 3 * (S n false : ℕ) + (R n false : ℕ) - 1 ≤
      3 * (S n false : ℕ) + (R n false : ℕ)
    exact Nat.sub_le _ _
  have hmon := div_le_div_of_nonneg_right (hmf (R n false) U (R n false) T le_rfl hUT) hQpos.le
  have hpow := Real.rpow_le_rpow (div_nonneg (hf (R n false) U) hQpos.le) hmon hρ
  have hTcoord : (Q n : ℚ) * (3 * s.val + r.val) = (T : ℚ) := by
    change (Q n : ℚ) * (3 * s.val + r.val) =
      ((3 * (S n false : ℕ) + (R n false : ℕ) : ℕ) : ℚ)
    push_cast
    rw [← (hcoords n false).1, ← (hcoords n false).2]
    ring
  have hsample : f (R n false) T / (Q n : ℝ) ∈ rationalProfileSamples f r
      ⟨3 * s.val + r.val, add_pos (mul_pos (by norm_num) s.property) r.property⟩ :=
    ⟨(Q n : ℚ), by exact_mod_cast (Q n).property, R n false, T,
      (hcoords n false).1, hTcoord, rfl⟩
  have hupper : f (R n false) T / (Q n : ℝ) ≤
      rationalProfile f r ⟨3 * s.val + r.val, add_pos (mul_pos (by norm_num) s.property) r.property⟩ :=
    le_csSup (rationalProfileSamples_bddAbove f hbf r _) hsample
  have hlast := Real.rpow_le_rpow (div_nonneg (hf (R n false) T) hQpos.le) hupper hρ
  exact hnorm.trans (hpow.trans hlast)

end BlockIdentities.Rectangular
