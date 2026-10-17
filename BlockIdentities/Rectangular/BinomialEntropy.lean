/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Square.TypeCountSchedules

/-! Actual binomial entropy schedules from the proved finite multinomial
counting theorem. All normalizations count individual letters. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open Filter
open scoped BigOperators Topology

/-- Actual repeated-letter type schedule, isolated from tensor-valued consumers. -/
theorem exists_binomial_entropy_schedule (n : ℕ) (hn : 1 ≤ n)
    (p : Fin 2 → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) :
    ∃ c : ℕ → Fin 2 → ℕ,
      (∀ j, 1 ≤ ∑ i, c j i) ∧
      (∀ i, Tendsto (fun j => (c j i : ℝ) / (∑ l, c j l : ℕ)) atTop (𝓝 (p i))) ∧
      Tendsto (fun j => Real.log ((n * (∑ i, c j i)).choose (n * c j 0) : ℝ) /
        ((n * (∑ i, c j i) : ℕ) : ℝ)) atTop (𝓝 (finiteEntropy p)) := by
  obtain ⟨offset, hpositive, htotal, hpopulation, _⟩ := exists_floorTypeCounts_schedule p hp hpsum
  let c := floorTypeCounts p offset
  let N : ℕ → ℕ := fun j => ∑ i, c j i
  let L : ℕ → Fin 2 → ℕ := fun j i => n * c j i
  have hN (j : ℕ) : 1 ≤ N j := hpositive j
  have hLtotal (j : ℕ) : (∑ i, L j i) = n * N j := by
    simp only [L, N, Finset.mul_sum]
  have hLgrowth : Tendsto (fun j => ∑ i, L j i) atTop atTop := by
    apply tendsto_atTop_mono (fun j => ?_) htotal
    rw [hLtotal]
    simpa only [one_mul] using Nat.mul_le_mul_right (N j) hn
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hLpopulation (i : Fin 2) : Tendsto
      (fun j => (L j i : ℝ) / (∑ l, L j l : ℕ)) atTop (𝓝 (p i)) := by
    have heq : (fun j => (L j i : ℝ) / (∑ l, L j l : ℕ)) =
        (fun j => (c j i : ℝ) / (N j : ℝ)) := by
      funext j
      rw [hLtotal]
      dsimp only [L]
      push_cast
      have hNr : (N j : ℝ) ≠ 0 := by exact_mod_cast (by have := hN j; omega : N j ≠ 0)
      field_simp [hnreal, hNr]
    rw [heq]
    exact hpopulation i
  have hentropy := tendsto_log_multinomial_of_empirical_tendsto L p hLgrowth hLpopulation
  have hcard (j : ℕ) : Nat.multinomial Finset.univ (L j) =
      (n * N j).choose (n * c j 0) := by
    have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by
      ext i
      fin_cases i <;> simp
    rw [huniv, Nat.binomial_eq_choose (by decide : (0 : Fin 2) ≠ 1)]
    congr 1
    change n * c j 0 + n * c j 1 = n * ∑ i, c j i
    rw [Fin.sum_univ_two, Nat.mul_add]
  refine ⟨c, hN, hpopulation, ?_⟩
  apply hentropy.congr
  intro j
  have hnum := congrArg (fun z : ℕ => Real.log (z : ℝ)) (hcard j)
  have hden := congrArg (fun z : ℕ => (z : ℝ)) (hLtotal j)
  exact congrArg₂ (fun x y : ℝ => x / y) hnum hden

end BlockIdentities.Rectangular
