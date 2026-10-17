/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.PNat.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Choose
public import Mathlib.Order.Monotone.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Literal rational positive-length rescaling by the source supremum.
No real extension or profile asymptotic theorem is defined by promise. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace BlockIdentities.Rectangular

/-- Actual normalized discrete samples at all admissible positive rational scales. -/
def rationalProfileSamples (f : ℕ+ → ℕ+ → ℝ)
    (r s : {x : ℚ // 0 < x}) : Set ℝ :=
  {v | ∃ q : ℚ, 0 < q ∧ ∃ R S : ℕ+,
    q * r.val = (R : ℚ) ∧ q * s.val = (S : ℚ) ∧ v = f R S / (q : ℝ)}

/-- The literal source supremum, on positive rational lengths only. -/
def rationalProfile (f : ℕ+ → ℕ+ → ℝ) (r s : {x : ℚ // 0 < x}) : ℝ :=
  sSup (rationalProfileSamples f r s)

private theorem positive_rat_integer_scale (x : ℚ) (hx : 0 < x) :
    ∃ d n : ℕ+, (d : ℚ) * x = (n : ℚ) := by
  have hnum : 0 < x.num := Rat.num_pos.mpr hx
  let d : ℕ+ := ⟨x.den, x.den_pos⟩
  let n : ℕ+ := ⟨x.num.toNat, Int.pos_iff_toNat_pos.mp hnum⟩
  refine ⟨d, n, ?_⟩
  change (x.den : ℚ) * x = (x.num.toNat : ℚ)
  rw [Rat.den_mul_eq_num]
  exact_mod_cast (Int.toNat_of_nonneg hnum.le).symm

/-- The sample set is nonempty by an actual common integer denominator. -/
theorem rationalProfileSamples_nonempty (f : ℕ+ → ℕ+ → ℝ)
    (r s : {x : ℚ // 0 < x}) : (rationalProfileSamples f r s).Nonempty := by
  obtain ⟨d, n, hd⟩ := positive_rat_integer_scale r.val r.property
  obtain ⟨e, k, he⟩ := positive_rat_integer_scale s.val s.property
  let q : ℚ := (d : ℚ) * (e : ℚ)
  have hq : 0 < q := mul_pos (by exact_mod_cast d.property) (by exact_mod_cast e.property)
  refine ⟨f (n * e) (k * d) / (q : ℝ), q, hq, n * e, k * d, ?_, ?_, rfl⟩
  · change ((d : ℚ) * e) * r.val = ((n * e : ℕ+) : ℚ)
    rw [show ((n * e : ℕ+) : ℚ) = (n : ℚ) * e by simp only [PNat.mul_coe, Nat.cast_mul], ← hd]
    ring
  · change ((d : ℚ) * e) * s.val = ((k * d : ℕ+) : ℚ)
    rw [show ((k * d : ℕ+) : ℚ) = (k : ℚ) * d by simp only [PNat.mul_coe, Nat.cast_mul], ← he]
    ring

/-- The actual discrete linear bound bounds every sample at r+s. -/
theorem rationalProfileSamples_le (f : ℕ+ → ℕ+ → ℝ)
    (hbound : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (r s : {x : ℚ // 0 < x}) {v : ℝ} (hv : v ∈ rationalProfileSamples f r s) :
    v ≤ (r.val : ℝ) + s.val := by
  obtain ⟨q, hq, R, S, hr, hs, rfl⟩ := hv
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrreal : (q : ℝ) * (r.val : ℝ) = (R : ℝ) := by exact_mod_cast hr
  have hsreal : (q : ℝ) * (s.val : ℝ) = (S : ℝ) := by exact_mod_cast hs
  calc
    f R S / (q : ℝ) ≤ ((R : ℝ) + S) / (q : ℝ) :=
      div_le_div_of_nonneg_right (hbound R S) hqr.le
    _ = (r.val : ℝ) + s.val := by
      rw [← hrreal, ← hsreal]
      field_simp [hqr.ne']
      <;> ring

theorem rationalProfileSamples_bddAbove (f : ℕ+ → ℕ+ → ℝ)
    (hbound : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (r s : {x : ℚ // 0 < x}) : BddAbove (rationalProfileSamples f r s) :=
  ⟨(r.val : ℝ) + s.val, fun _ hv => rationalProfileSamples_le f hbound r s hv⟩

theorem rationalProfile_le (f : ℕ+ → ℕ+ → ℝ)
    (hbound : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (r s : {x : ℚ // 0 < x}) : rationalProfile f r s ≤ (r.val : ℝ) + s.val :=
  csSup_le (rationalProfileSamples_nonempty f r s) (fun _ hv => rationalProfileSamples_le f hbound r s hv)

/-- Finitely many positive rational scales have a genuine common positive
integer multiple. This includes an empty family, whose common scale is one. -/
theorem positive_rat_common_integer_scale {ι : Type*} [Fintype ι]
    (q : ι → ℚ) (hq : ∀ i, 0 < q i) :
    ∃ Q : ℕ+, ∃ k : ι → ℕ+, ∀ i, (k i : ℚ) * q i = (Q : ℚ) := by
  classical
  choose d n hdn using (fun i => positive_rat_integer_scale (q i)⁻¹ (inv_pos.mpr (hq i)))
  let Q : ℕ+ := ∏ i, d i
  let k : ι → ℕ+ := fun i => n i * ∏ j ∈ Finset.univ.erase i, d j
  refine ⟨Q, k, ?_⟩
  intro i
  have he : (n i : ℚ) * q i = (d i : ℚ) := by
    have hh : (d i : ℚ) / q i = (n i : ℚ) := by
      simpa only [div_eq_mul_inv] using hdn i
    exact ((div_eq_iff (hq i).ne').mp hh).symm
  have hp := congrArg (fun z : ℕ+ => (z : ℚ))
    (Finset.prod_erase_mul Finset.univ d (Finset.mem_univ i))
  calc
    (k i : ℚ) * q i = ((∏ j ∈ Finset.univ.erase i, d j : ℕ+) : ℚ) *
        ((n i : ℚ) * q i) := by
      dsimp only [k]
      simp only [PNat.mul_coe, Nat.cast_mul]
      ring
    _ = ((∏ j ∈ Finset.univ.erase i, d j : ℕ+) : ℚ) * (d i : ℚ) := by rw [he]
    _ = (Q : ℚ) := by
      simpa only [PNat.mul_coe, Nat.cast_mul] using hp

private theorem rationalProfile_scale_le (f : ℕ+ → ℕ+ → ℝ)
    (hbound : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (r s t : {x : ℚ // 0 < x}) :
    rationalProfile f ⟨t.val * r.val, mul_pos t.property r.property⟩
      ⟨t.val * s.val, mul_pos t.property s.property⟩ ≤ (t.val : ℝ) * rationalProfile f r s := by
  apply csSup_le (rationalProfileSamples_nonempty f _ _)
  rintro v ⟨q, hq, R, S, hr, hs, rfl⟩
  have hqt : 0 < q * t.val := mul_pos hq t.property
  have hsample : f R S / ((q * t.val : ℚ) : ℝ) ∈ rationalProfileSamples f r s := by
    refine ⟨q * t.val, hqt, R, S, ?_, ?_, rfl⟩
    · simpa only [mul_assoc] using hr
    · simpa only [mul_assoc] using hs
  have hle := le_csSup (rationalProfileSamples_bddAbove f hbound r s) hsample
  have ht : 0 < (t.val : ℝ) := by exact_mod_cast t.property
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  calc
    f R S / (q : ℝ) = (t.val : ℝ) * (f R S / ((q * t.val : ℚ) : ℝ)) := by
      rw [Rat.cast_mul]
      field_simp [ht.ne', hqr]
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hle ht.le

/-- Exact rational homogeneity follows by changing the admissible scale q to
q*t, then applying the same proved inequality at inverse t. -/
theorem rationalProfile_homogeneous (f : ℕ+ → ℕ+ → ℝ)
    (hbound : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (r s t : {x : ℚ // 0 < x}) :
    rationalProfile f ⟨t.val * r.val, mul_pos t.property r.property⟩
      ⟨t.val * s.val, mul_pos t.property s.property⟩ = (t.val : ℝ) * rationalProfile f r s := by
  apply le_antisymm (rationalProfile_scale_le f hbound r s t)
  let tr : {x : ℚ // 0 < x} := ⟨t.val * r.val, mul_pos t.property r.property⟩
  let ts : {x : ℚ // 0 < x} := ⟨t.val * s.val, mul_pos t.property s.property⟩
  let ti : {x : ℚ // 0 < x} := ⟨t.val⁻¹, inv_pos.mpr t.property⟩
  have he₁ : (⟨ti.val * tr.val, mul_pos ti.property tr.property⟩ : {x : ℚ // 0 < x}) = r := by
    apply Subtype.ext
    dsimp only [ti, tr]
    rw [← mul_assoc, inv_mul_cancel₀ t.property.ne', one_mul]
  have he₂ : (⟨ti.val * ts.val, mul_pos ti.property ts.property⟩ : {x : ℚ // 0 < x}) = s := by
    apply Subtype.ext
    dsimp only [ti, ts]
    rw [← mul_assoc, inv_mul_cancel₀ t.property.ne', one_mul]
  have h := rationalProfile_scale_le f hbound tr ts ti
  rw [he₁, he₂] at h
  have ht : 0 < (t.val : ℝ) := by exact_mod_cast t.property
  have hm := mul_le_mul_of_nonneg_left h ht.le
  simpa only [ti, Rat.cast_inv, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] using hm

/-- Replication raises any finite family of actual samples to one common
integer scale, preserving or improving every normalized value simultaneously. -/
theorem rationalProfile_common_samples {ι : Type*} [Fintype ι]
    (f : ℕ+ → ℕ+ → ℝ)
    (hrep : ∀ k R S : ℕ+, (k : ℝ) * f R S ≤ f (k * R) (k * S))
    (r s : ι → {x : ℚ // 0 < x}) (q : ι → ℚ) (hq : ∀ i, 0 < q i)
    (R S : ι → ℕ+) (hr : ∀ i, q i * (r i).val = (R i : ℚ))
    (hs : ∀ i, q i * (s i).val = (S i : ℚ)) :
    ∃ Q : ℕ+, ∃ R' S' : ι → ℕ+, ∀ i,
      (Q : ℚ) * (r i).val = (R' i : ℚ) ∧
      (Q : ℚ) * (s i).val = (S' i : ℚ) ∧
      f (R i) (S i) / (q i : ℝ) ≤ f (R' i) (S' i) / (Q : ℝ) := by
  obtain ⟨Q, k, hk⟩ := positive_rat_common_integer_scale q hq
  refine ⟨Q, (fun i => k i * R i), (fun i => k i * S i), ?_⟩
  intro i
  have hkr : 0 < (k i : ℝ) := by exact_mod_cast (k i).property
  have hqr : 0 < (q i : ℝ) := by exact_mod_cast hq i
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast Q.property
  have hkreal : (k i : ℝ) * (q i : ℝ) = (Q : ℝ) := by exact_mod_cast hk i
  refine ⟨?_, ?_, ?_⟩
  · simp only [PNat.mul_coe, Nat.cast_mul]
    rw [← hk i, mul_assoc, hr i]
  · simp only [PNat.mul_coe, Nat.cast_mul]
    rw [← hk i, mul_assoc, hs i]
  · calc
      f (R i) (S i) / (q i : ℝ) = ((k i : ℝ) * f (R i) (S i)) / (Q : ℝ) := by
        rw [← hkreal]
        field_simp [hkr.ne', hqr.ne']
        <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right (hrep (k i) (R i) (S i)) hQr.le

/-- Finitely many actual suprema are approached at one common integer scale.
All discrete lengths and the scale are constructed, not posited as a limit. -/
theorem rationalProfile_common_approximation {ι : Type*} [Fintype ι]
    (f : ℕ+ → ℕ+ → ℝ)
    (hrep : ∀ k R S : ℕ+, (k : ℝ) * f R S ≤ f (k * R) (k * S))
    (r s : ι → {x : ℚ // 0 < x}) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ+, ∃ R S : ι → ℕ+, ∀ i,
      (Q : ℚ) * (r i).val = (R i : ℚ) ∧
      (Q : ℚ) * (s i).val = (S i : ℚ) ∧
      rationalProfile f (r i) (s i) - ε < f (R i) (S i) / (Q : ℝ) := by
  classical
  have hsample (i : ι) : ∃ q : ℚ, 0 < q ∧ ∃ R S : ℕ+,
      q * (r i).val = (R : ℚ) ∧ q * (s i).val = (S : ℚ) ∧
      rationalProfile f (r i) (s i) - ε < f R S / (q : ℝ) := by
    obtain ⟨v, hv, hlt⟩ := exists_lt_of_lt_csSup (rationalProfileSamples_nonempty f (r i) (s i))
      (show rationalProfile f (r i) (s i) - ε < sSup (rationalProfileSamples f (r i) (s i)) by
        change rationalProfile f (r i) (s i) - ε < rationalProfile f (r i) (s i)
        linarith only [hε])
    obtain ⟨q, hq, R, S, hr, hs, rfl⟩ := hv
    exact ⟨q, hq, R, S, hr, hs, hlt⟩
  choose q hq R S hr hs hval using hsample
  obtain ⟨Q, R', S', hcommon⟩ := rationalProfile_common_samples f hrep r s q hq R S hr hs
  refine ⟨Q, R', S', ?_⟩
  intro i
  exact ⟨(hcommon i).1, (hcommon i).2.1, (hval i).trans_le (hcommon i).2.2⟩

/-- Actual discrete monotonicity passes to the rational supremum by a common
integer scale; two separately chosen incompatible scales are never compared. -/
theorem rationalProfile_mono (f : ℕ+ → ℕ+ → ℝ)
    (hbound : ∀ R S : ℕ+, f R S ≤ (R : ℝ) + S)
    (hrep : ∀ k R S : ℕ+, (k : ℝ) * f R S ≤ f (k * R) (k * S))
    (hmono : ∀ R S R' S' : ℕ+, (R : ℕ) ≤ R' → (S : ℕ) ≤ S' → f R S ≤ f R' S')
    (r s r' s' : {x : ℚ // 0 < x}) (hr : r.val ≤ r'.val) (hs : s.val ≤ s'.val) :
    rationalProfile f r s ≤ rationalProfile f r' s' := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let rr : Bool → {x : ℚ // 0 < x} := fun b => if b then r' else r
  let ss : Bool → {x : ℚ // 0 < x} := fun b => if b then s' else s
  obtain ⟨Q, R, S, h⟩ := rationalProfile_common_approximation f hrep rr ss ε hε
  have hQr : 0 < (Q : ℚ) := by exact_mod_cast Q.property
  have hR : (R false : ℚ) ≤ (R true : ℚ) := by
    rw [← (h false).1, ← (h true).1]
    exact mul_le_mul_of_nonneg_left hr hQr.le
  have hS : (S false : ℚ) ≤ (S true : ℚ) := by
    rw [← (h false).2.1, ← (h true).2.1]
    exact mul_le_mul_of_nonneg_left hs hQr.le
  have hRnat : (R false : ℕ) ≤ R true := by exact_mod_cast hR
  have hSnat : (S false : ℕ) ≤ S true := by exact_mod_cast hS
  have hm := div_le_div_of_nonneg_right (hmono _ _ _ _ hRnat hSnat)
    (show (0 : ℝ) ≤ Q by exact_mod_cast Q.property.le)
  have hv : f (R true) (S true) / (Q : ℝ) ∈ rationalProfileSamples f r' s' :=
    ⟨(Q : ℚ), hQr, R true, S true, (h true).1, (h true).2.1, rfl⟩
  have hupper := le_csSup (rationalProfileSamples_bddAbove f hbound r' s') hv
  change f (R true) (S true) / (Q : ℝ) ≤ rationalProfile f r' s' at hupper
  have hlower := (h false).2.2
  change rationalProfile f r s - ε < f (R false) (S false) / (Q : ℝ) at hlower
  linarith only [hlower, hm, hupper]

/-- Discrete midpoint concavity implies the full integer chord inequality.
This supplies the actual finite Jensen ingredient rather than assuming it. -/
theorem discrete_concave_chord (y : ℕ → ℝ)
    (hconc : ∀ n : ℕ, y n + y (n + 2) ≤ 2 * y (n + 1))
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ((c - b : ℕ) : ℝ) * y a + ((b - a : ℕ) : ℝ) * y c ≤
      ((c - a : ℕ) : ℝ) * y b := by
  let δ : ℕ → ℝ := fun n => y (n + 1) - y n
  have hanti : Antitone δ := antitone_nat_of_succ_le (fun n => by
    dsimp only [δ]
    have h := hconc n
    have he : n + 1 + 1 = n + 2 := by omega
    rw [he]
    linarith only [h])
  have htelescope (u k : ℕ) : (∑ i ∈ Finset.range k, δ (u + i)) = y (u + k) - y u := by
    dsimp only [δ]
    simpa only [Nat.add_assoc, Nat.add_zero] using
      Finset.sum_range_sub (fun i => y (u + i)) k
  have hleft : ((b - a : ℕ) : ℝ) * δ b ≤ y b - y a := by
    calc
      _ = ∑ i ∈ Finset.range (b - a), δ b := by simp
      _ ≤ ∑ i ∈ Finset.range (b - a), δ (a + i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hanti (by have hh := Finset.mem_range.mp hi; omega)
      _ = _ := by rw [htelescope, Nat.add_sub_of_le hab]
  have hright : y c - y b ≤ ((c - b : ℕ) : ℝ) * δ b := by
    calc
      _ = ∑ i ∈ Finset.range (c - b), δ (b + i) := by rw [htelescope, Nat.add_sub_of_le hbc]
      _ ≤ ∑ i ∈ Finset.range (c - b), δ b := by
        apply Finset.sum_le_sum
        intro i _
        exact hanti (Nat.le_add_right b i)
      _ = _ := by simp
  have h₁ := mul_le_mul_of_nonneg_left hleft (Nat.cast_nonneg (c - b) : (0 : ℝ) ≤ _)
  have h₂ := mul_le_mul_of_nonneg_left hright (Nat.cast_nonneg (b - a) : (0 : ℝ) ≤ _)
  have he₁ : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := Nat.cast_sub hab
  have he₂ : ((c - b : ℕ) : ℝ) = (c : ℝ) - b := Nat.cast_sub hbc
  have he₃ : ((c - a : ℕ) : ℝ) = (c : ℝ) - a := Nat.cast_sub (hab.trans hbc)
  rw [he₁, he₂] at h₁ h₂
  rw [he₁, he₂, he₃]
  nlinarith only [h₁, h₂]

private theorem discrete_concave_jensen_ordered (y : ℕ → ℝ)
    (hconc : ∀ n : ℕ, y n + y (n + 2) ≤ 2 * y (n + 1))
    {a b c : ℕ} {t : ℝ} (ht : t ∈ Set.Icc 0 1) (hac : a ≤ c)
    (he : (b : ℝ) = t * a + (1 - t) * c) : t * y a + (1 - t) * y c ≤ y b := by
  by_cases hz : a = c
  · subst c
    have hb : b = a := by
      have hb' : (b : ℝ) = a := by nlinarith only [he]
      exact_mod_cast hb'
    subst b
    nlinarith
  have hac' : a < c := lt_of_le_of_ne hac hz
  have hdiff : 0 < (c : ℝ) - a := sub_pos.mpr (by exact_mod_cast hac')
  have hba : (a : ℝ) ≤ b := by
    have hh := mul_nonneg (sub_nonneg.mpr ht.2) hdiff.le
    nlinarith only [hh, he]
  have hcb : (b : ℝ) ≤ c := by
    have hh := mul_nonneg ht.1 hdiff.le
    nlinarith only [hh, he]
  have hab : a ≤ b := by exact_mod_cast hba
  have hbc : b ≤ c := by exact_mod_cast hcb
  have hchord := discrete_concave_chord y hconc hab hbc
  rw [Nat.cast_sub hab, Nat.cast_sub hbc, Nat.cast_sub hac] at hchord
  have h₁ : (c : ℝ) - b = t * ((c : ℝ) - a) := by nlinarith only [he]
  have h₂ : (b : ℝ) - a = (1 - t) * ((c : ℝ) - a) := by nlinarith only [he]
  rw [h₁, h₂] at hchord
  have hscaled : ((c : ℝ) - a) * (t * y a + (1 - t) * y c) ≤ ((c : ℝ) - a) * y b := by
    nlinarith only [hchord]
  exact le_of_mul_le_mul_left hscaled hdiff

/-- Actual discrete midpoint concavity gives all real convex combinations whose
three locations are integers. Thus rational mixing at a common scale is valid. -/
theorem discrete_concave_jensen (y : ℕ → ℝ)
    (hconc : ∀ n : ℕ, y n + y (n + 2) ≤ 2 * y (n + 1))
    {a b c : ℕ} {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (he : (b : ℝ) = t * a + (1 - t) * c) : t * y a + (1 - t) * y c ≤ y b := by
  rcases le_total a c with hac | hca
  · exact discrete_concave_jensen_ordered y hconc ht hac he
  · have ht' : 1 - t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have he' : (b : ℝ) = (1 - t) * c + (1 - (1 - t)) * a := by nlinarith only [he]
    have h := discrete_concave_jensen_ordered y hconc ht' hca he'
    nlinarith only [h]

end BlockIdentities.Rectangular
