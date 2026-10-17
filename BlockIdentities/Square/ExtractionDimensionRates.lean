/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Square.TypeCountSchedules

/-! Actual input and output matrix dimensions of fixed-type extraction. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open Filter
open scoped BigOperators Topology

def extractionInputDimension {ι : Type*} [Fintype ι] (c : ℕ) (counts : ι → ℕ) : ℕ :=
  c ^ (∑ i, counts i)

def extractionOutputDimension {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι → ℕ) (counts : ι → ℕ) : ℕ :=
  Fintype.card (ExactWords counts) * ∏ i, k i ^ counts i

theorem extractionInputDimension_pos {ι : Type*} [Fintype ι]
    (c : ℕ) (hc : 1 ≤ c) (counts : ι → ℕ) : 0 < extractionInputDimension c counts :=
  pow_pos (lt_of_lt_of_le Nat.zero_lt_one hc) _

theorem extractionOutputDimension_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i) (counts : ι → ℕ) :
    0 < extractionOutputDimension k counts :=
  Nat.mul_pos (exactWords_card_pos counts)
    (Finset.prod_pos (fun i _ => pow_pos (lt_of_lt_of_le Nat.zero_lt_one (hk i)) _))

/-- Literal positive dimensions have the advertised finite logarithm. -/
theorem extractionDimension_log_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (counts : ι → ℕ) (hn : 1 ≤ ∑ i, counts i)
    (c : ℕ) (hc : 1 ≤ c) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i) :
    Real.log ((extractionOutputDimension k counts : ℝ) /
        (extractionInputDimension c counts : ℝ)) / (3 * (∑ i, counts i : ℕ)) =
      (Real.log (Fintype.card (ExactWords counts) : ℝ) / (∑ i, counts i : ℕ) +
        (∑ i, ((counts i : ℝ) / (∑ l, counts l : ℕ)) * Real.log (k i : ℝ)) -
        Real.log (c : ℝ)) / 3 := by
  have hcpos : 0 < (c : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hc)
  have hkpos (i : ι) : 0 < (k i : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hk i))
  have hM : 0 < (Fintype.card (ExactWords counts) : ℝ) := by
    exact_mod_cast exactWords_card_pos counts
  have hp : 0 < ∏ i, (k i : ℝ) ^ counts i :=
    Finset.prod_pos fun i _ => pow_pos (hkpos i) _
  have ha : 0 < (extractionInputDimension c counts : ℝ) := by
    simpa only [extractionInputDimension, Nat.cast_pow] using pow_pos hcpos (∑ i, counts i)
  have hb : 0 < (extractionOutputDimension k counts : ℝ) := by
    simpa only [extractionOutputDimension, Nat.cast_mul, Nat.cast_prod, Nat.cast_pow]
      using mul_pos hM hp
  have hlogA : Real.log (extractionInputDimension c counts : ℝ) =
      (∑ i, counts i : ℕ) * Real.log (c : ℝ) := by
    rw [extractionInputDimension, Nat.cast_pow, Real.log_pow]
  have hlogB : Real.log (extractionOutputDimension k counts : ℝ) =
      Real.log (Fintype.card (ExactWords counts) : ℝ) +
        ∑ i, (counts i : ℝ) * Real.log (k i : ℝ) := by
    simp only [extractionOutputDimension, Nat.cast_mul, Nat.cast_prod, Nat.cast_pow]
    rw [Real.log_mul (ne_of_gt hM) (ne_of_gt hp),
      Real.log_prod (fun i _ => ne_of_gt (pow_pos (hkpos i) _))]
    simp only [Real.log_pow]
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha), hlogB, hlogA]
  have hsum : (∑ i, ((counts i : ℝ) / (∑ l, counts l : ℕ)) * Real.log (k i : ℝ)) =
      (∑ i, (counts i : ℝ) * Real.log (k i : ℝ)) / (∑ l, counts l : ℕ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  have hnz : ((∑ i, counts i : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
  field_simp [hnz] <;> ring

/-- Genuine entropy and empirical limits produce the source dimension gain. -/
theorem extractionDimension_rate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (counts : ℕ → ι → ℕ) (hn : ∀ j, 1 ≤ ∑ i, counts j i)
    (p : ι → ℝ)
    (hemp : ∀ i, Tendsto (fun j => (counts j i : ℝ) / (∑ l, counts j l : ℕ))
      atTop (𝓝 (p i)))
    (hwords : Tendsto (fun j => Real.log (Fintype.card (ExactWords (counts j)) : ℝ) /
      (∑ i, counts j i : ℕ)) atTop (𝓝 (finiteEntropy p)))
    (c : ℕ) (hc : 1 ≤ c) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i) :
    Tendsto (fun j => Real.log ((extractionOutputDimension k (counts j) : ℝ) /
      (extractionInputDimension c (counts j) : ℝ)) / (3 * (∑ i, counts j i : ℕ)))
      atTop (𝓝 ((finiteEntropy p + ∑ i, p i * Real.log (k i : ℝ) - Real.log (c : ℝ)) / 3)) := by
  have hs := tendsto_finsetSum Finset.univ (fun i _ => (hemp i).mul_const (Real.log (k i : ℝ)))
  have ht := ((hwords.add hs).sub_const (Real.log (c : ℝ))).div_const 3
  apply ht.congr
  intro j
  exact (extractionDimension_log_ratio (counts j) (hn j) c hc k hk).symm

/-- Any fixed positive source multiplicity has zero logarithmic overhead. -/
theorem constant_overhead_log_rate (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (u : ℕ) :
    Tendsto (fun j => Real.log (u : ℝ) / (n j : ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hn)

end BlockIdentities.Square
