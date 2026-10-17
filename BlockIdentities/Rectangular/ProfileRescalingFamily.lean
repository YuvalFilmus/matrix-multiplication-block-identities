/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.ProfileRescalingConcavity

/-! Common-scale approximation for genuinely different discrete profiles.
This is needed for coupled tripling, not merely single-profile concavity. -/
@[expose] public section
noncomputable section
open Filter Topology
namespace BlockIdentities.Rectangular

/-- Every member of a finite family has its own literal supremum and discrete
replication law; all chosen samples are raised to one actual integer scale. -/
theorem rationalProfile_family_common_approximation {ι : Type*} [Fintype ι]
    (f : ι → ℕ+ → ℕ+ → ℝ)
    (hrep : ∀ i, ∀ k R S : ℕ+, (k : ℝ) * f i R S ≤ f i (k * R) (k * S))
    (r s : ι → {x : ℚ // 0 < x}) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ+, ∃ R S : ι → ℕ+, ∀ i,
      (Q : ℚ) * (r i).val = (R i : ℚ) ∧
      (Q : ℚ) * (s i).val = (S i : ℚ) ∧
      rationalProfile (f i) (r i) (s i) - ε < f i (R i) (S i) / (Q : ℝ) := by
  classical
  have hsample (i : ι) : ∃ q : ℚ, 0 < q ∧ ∃ R S : ℕ+,
      q * (r i).val = (R : ℚ) ∧ q * (s i).val = (S : ℚ) ∧
      rationalProfile (f i) (r i) (s i) - ε < f i R S / (q : ℝ) := by
    obtain ⟨v, hv, hlt⟩ := exists_lt_of_lt_csSup
      (rationalProfileSamples_nonempty (f i) (r i) (s i))
      (show rationalProfile (f i) (r i) (s i) - ε <
        sSup (rationalProfileSamples (f i) (r i) (s i)) by
          change rationalProfile (f i) (r i) (s i) - ε < rationalProfile (f i) (r i) (s i)
          linarith only [hε])
    obtain ⟨q, hq, R, S, hr, hs, rfl⟩ := hv
    exact ⟨q, hq, R, S, hr, hs, hlt⟩
  choose q hq R S hr hs hval using hsample
  obtain ⟨Q, k, hk⟩ := positive_rat_common_integer_scale q hq
  refine ⟨Q, (fun i => k i * R i), (fun i => k i * S i), ?_⟩
  intro i
  have hkr : 0 < (k i : ℝ) := by exact_mod_cast (k i).property
  have hqr : 0 < (q i : ℝ) := by exact_mod_cast hq i
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast Q.property
  have hkreal : (k i : ℝ) * (q i : ℝ) = (Q : ℝ) := by exact_mod_cast hk i
  refine ⟨?_, ?_, (hval i).trans_le ?_⟩
  · simp only [PNat.mul_coe, Nat.cast_mul]
    rw [← hk i, mul_assoc, hr i]
  · simp only [PNat.mul_coe, Nat.cast_mul]
    rw [← hk i, mul_assoc, hs i]
  · calc
      f i (R i) (S i) / (q i : ℝ) = ((k i : ℝ) * f i (R i) (S i)) / (Q : ℝ) := by
        rw [← hkreal]
        field_simp [hkr.ne', hqr.ne'] <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right (hrep i (k i) (R i) (S i)) hQr.le

/-- Actual simultaneous sample limits, now allowing a different profile at
each index. Bounds ensure the source suprema are genuine finite values. -/
theorem rationalProfile_family_simultaneous_limits {ι : Type*} [Fintype ι]
    (f : ι → ℕ+ → ℕ+ → ℝ)
    (hbound : ∀ i, ∀ R S : ℕ+, f i R S ≤ (R : ℝ) + S)
    (hrep : ∀ i, ∀ k R S : ℕ+, (k : ℝ) * f i R S ≤ f i (k * R) (k * S))
    (r s : ι → {x : ℚ // 0 < x}) :
    ∃ Q : ℕ → ℕ+, ∃ R S : ℕ → ι → ℕ+,
      (∀ n i, (Q n : ℚ) * (r i).val = (R n i : ℚ) ∧
        (Q n : ℚ) * (s i).val = (S n i : ℚ)) ∧
      (∀ i, Tendsto (fun n => f i (R n i) (S n i) / (Q n : ℝ)) atTop
        (𝓝 (rationalProfile (f i) (r i) (s i)))) := by
  classical
  have hchoices (n : ℕ) := rationalProfile_family_common_approximation f hrep r s
    (1 / ((n : ℝ) + 1)) (by positivity)
  choose Q R S h using hchoices
  refine ⟨Q, R, S, (fun n i => ⟨(h n i).1, (h n i).2.1⟩), ?_⟩
  intro i
  have hlower : Tendsto (fun n : ℕ => rationalProfile (f i) (r i) (s i) - 1 / ((n : ℝ) + 1))
      atTop (𝓝 (rationalProfile (f i) (r i) (s i))) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · exact Filter.Eventually.of_forall (fun n => (h n i).2.2.le)
  · apply Filter.Eventually.of_forall
    intro n
    apply le_csSup (rationalProfileSamples_bddAbove (f i) (hbound i) (r i) (s i))
    exact ⟨(Q n : ℚ), by exact_mod_cast (Q n).property, R n i, S n i,
      (h n i).1, (h n i).2.1, rfl⟩

end BlockIdentities.Rectangular
