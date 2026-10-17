/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Square.AbsorptionRounding
public import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexTypeEntropy
public import Lean.Elab.Tactic.Omega

/-! Actual fixed-offset floor schedules for probability types and their entropy. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open Filter
open scoped BigOperators Topology

/-- The offset is fixed once, before all schedule indices. -/
def floorTypeCounts {ι : Type*} (p : ι → ℝ) (N j : ℕ) (i : ι) : ℕ :=
  Nat.floor (p i * ((j + N : ℕ) : ℝ))

/-- Every finite real probability law has genuine nonempty integral types with
its empirical probabilities and exact-word entropy rate. -/
theorem exists_floorTypeCounts_schedule {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∃ N : ℕ,
      (∀ j, 1 ≤ ∑ i, floorTypeCounts p N j i) ∧
      Tendsto (fun j => ∑ i, floorTypeCounts p N j i) atTop atTop ∧
      (∀ i, Tendsto (fun j => (floorTypeCounts p N j i : ℝ) /
        (∑ l, floorTypeCounts p N j l : ℕ)) atTop (𝓝 (p i))) ∧
      Tendsto (fun j => Real.log (Fintype.card (ExactWords (floorTypeCounts p N j)) : ℝ) /
        (∑ i, floorTypeCounts p N j i : ℕ)) atTop (𝓝 (finiteEntropy p)) := by
  have hex : ∃ i, 0 < p i := by
    by_contra hn
    have hz : ∀ i, p i = 0 := by
      intro i
      have hnot : ¬ 0 < p i := fun hi => hn ⟨i, hi⟩
      exact le_antisymm (le_of_not_gt hnot) (hp i)
    have : (∑ i, p i) = 0 := by simp only [hz, Finset.sum_const_zero]
    linarith
  obtain ⟨i₀, hi₀⟩ := hex
  have hfloor := floor_linear_tendsto_atTop (p i₀) hi₀
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hfloor.eventually (eventually_ge_atTop (1 : ℕ)))
  have hshift : Tendsto (fun j : ℕ => j + N) atTop atTop :=
    tendsto_atTop_mono (fun j => by change j ≤ j + N; omega) tendsto_id
  have hpositive (j : ℕ) : 1 ≤ ∑ i, floorTypeCounts p N j i := by
    calc
      1 ≤ floorTypeCounts p N j i₀ := hN (j + N) (by omega)
      _ ≤ ∑ i, floorTypeCounts p N j i :=
        Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ i₀)
  have htotal : Tendsto (fun j => ∑ i, floorTypeCounts p N j i) atTop atTop := by
    apply tendsto_atTop_mono (fun j =>
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ i₀))
    exact hfloor.comp hshift
  have hcounts (i : ι) : Tendsto (fun j => (floorTypeCounts p N j i : ℝ) /
      ((j + N : ℕ) : ℝ)) atTop (𝓝 (p i)) :=
    (floor_linear_div_tendsto (p i) (hp i)).comp hshift
  have htotal_ratio : Tendsto (fun j => ((∑ i, floorTypeCounts p N j i : ℕ) : ℝ) /
      ((j + N : ℕ) : ℝ)) atTop (𝓝 1) := by
    have ht := tendsto_finsetSum Finset.univ (fun i _ => hcounts i)
    simpa only [← Finset.sum_div, ← Nat.cast_sum, hsum] using ht
  have hempirical (i : ι) : Tendsto (fun j => (floorTypeCounts p N j i : ℝ) /
      (∑ l, floorTypeCounts p N j l : ℕ)) atTop (𝓝 (p i)) := by
    have hlim := (hcounts i).div htotal_ratio (by norm_num : (1 : ℝ) ≠ 0)
    simp only [div_one] at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
    have hbase : ((j + N : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (show j + N ≠ 0 by omega)
    have htot : ((∑ l, floorTypeCounts p N j l : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hpositive j)))
    change ((floorTypeCounts p N j i : ℝ) / ((j + N : ℕ) : ℝ)) /
        (((∑ l, floorTypeCounts p N j l : ℕ) : ℝ) / ((j + N : ℕ) : ℝ)) =
      (floorTypeCounts p N j i : ℝ) / (∑ l, floorTypeCounts p N j l : ℕ)
    field_simp [hbase, htot]
  exact ⟨N, hpositive, htotal, hempirical,
    tendsto_log_exactWords_card_of_empirical_tendsto (floorTypeCounts p N) p htotal hempirical⟩

end BlockIdentities.Square
