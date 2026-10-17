/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Square.Certificate
public import BlockIdentities.Square.Yield

/-! Internal scalar consumption of the actual convolution potential inequalities. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open scoped BigOperators

private def rowFactor (r : ℕ) : ℝ := (3 * (r : ℝ) + 1) / (3 * (r : ℝ) - 3)
private def outerFactor (r : ℕ) : ℝ := (3 * (r : ℝ) - 1) / (3 * (r : ℝ) - 3)

private theorem row_bound (x : ℕ → ℝ) (r : ℕ) (hr : 2 ≤ r)
    (hneighbor : ∀ b ∈ Finset.Ico r (4 * r - 1), x (b - 1) + x (b + 1) ≤ 2 * x b)
    (htripling : 3 * x r ≤ x (4 * r - 1)) (inner : Bool) :
    (if inner then rowFactor r else outerFactor r) * x (r - 1) ≤
      (if inner then x (r + 1) else x r) := by
  let q : ℝ := if inner then 2 else 1
  let ν := q / (3 * (r : ℝ) - 3)
  have hrreal : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hden : 0 < 3 * (r : ℝ) - 3 := by linarith
  have hq : 0 < q := by cases inner <;> norm_num [q]
  have hν : 0 ≤ ν := (div_pos hq hden).le
  have hbalance : ν * (3 * (r : ℝ) - 3) = (if inner then 2 else 1) * (1 : ℝ) := by
    dsimp only [ν, q]
    rw [div_mul_cancel₀ _ (ne_of_gt hden), mul_one]
  have hrow := convolution_row_certificate x ν 1 r hr inner hbalance
  have hweights : ∀ b ∈ Finset.Ico r (4 * r - 1),
      0 ≤ ν * ((4 * (r : ℝ) - 1) - b) - (if inner && (b == r) then (1 : ℝ) else 0) := by
    intro b hb
    have hbi := (Finset.mem_Ico.mp hb).2
    have hbr : (b : ℝ) ≤ 4 * (r : ℝ) - 2 := by
      have hn : b ≤ 4 * r - 2 := by omega
      have hc : ((4 * r - 2 : ℕ) : ℝ) = 4 * (r : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ 4 * r)]
        norm_num
      rw [← hc]
      exact_mod_cast hn
    cases inner
    · simpa using (mul_nonneg hν (show 0 ≤ (4 * (r : ℝ) - 1) - b by linarith))
    · by_cases he : b = r
      · subst b
        simp only [beq_self_eq_true]
        change 0 ≤ ν * ((4 * (r : ℝ) - 1) - r) - 1
        have hb' : ν * (3 * (r : ℝ) - 3) = 2 := by simpa using hbalance
        nlinarith
      · have hbe : (b == r) = false := by simp [he]
        simpa [hbe] using (mul_nonneg hν (show 0 ≤ (4 * (r : ℝ) - 1) - b by linarith))
  have hsum : 0 ≤ (∑ b ∈ Finset.Ico r (4 * r - 1),
      (ν * ((4 * (r : ℝ) - 1) - b) - (if inner && (b == r) then (1 : ℝ) else 0)) *
        (2 * x b - x (b - 1) - x (b + 1))) :=
    Finset.sum_nonneg (fun b hb => mul_nonneg (hweights b hb) (by linarith [hneighbor b hb]))
  have ht : 0 ≤ ν * (x (4 * r - 1) - 3 * x r) := mul_nonneg hν (sub_nonneg.mpr htripling)
  have hc : ν * (3 * (r : ℝ) - 1) - (if inner then (1 : ℝ) else 0) =
      if inner then rowFactor r else outerFactor r := by
    have hrone : (r : ℝ) - 1 ≠ 0 := by linarith
    cases inner <;> simp [ν, q, rowFactor, outerFactor] <;>
      field_simp [ne_of_gt hden, hrone] <;> ring
  rw [hc] at hrow
  linarith

private theorem profile_eq_yield (a : ℕ) (ha : 2 ≤ a) :
    outerFactor a * (∏ r ∈ Finset.Ico 2 a, rowFactor r) = convolutionYield ⟨a, ha⟩ := by
  induction a, ha using Nat.le_induction with
  | base => norm_num [outerFactor, convolutionYield, Finset.prod_Ico_succ_top]
  | succ a ha ih =>
    have hapos : (2 : ℝ) ≤ a := by exact_mod_cast ha
    have hd : (3 * (a : ℝ) - 3) ≠ 0 := by linarith
    have hda : (a : ℝ) ≠ 0 := by linarith
    have hcoef : outerFactor (a + 1) * rowFactor a =
        outerFactor a * ((3 * ((a : ℝ) + 1) - 1) / (3 * (a : ℝ) - 1)) *
          (1 + 1 / (3 * (a : ℝ))) := by
      simp only [outerFactor, rowFactor, Nat.cast_add, Nat.cast_one]
      have hd' : 3 * (a : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hd, hda, hd'] <;> ring
    rw [Finset.prod_Ico_succ_top ha]
    calc
      outerFactor (a + 1) * ((∏ r ∈ Finset.Ico 2 a, rowFactor r) * rowFactor a) =
          (outerFactor a * ∏ r ∈ Finset.Ico 2 a, rowFactor r) *
            ((3 * ((a : ℝ) + 1) - 1) / (3 * (a : ℝ) - 1)) * (1 + 1 / (3 * (a : ℝ))) := by
        calc
          _ = (outerFactor (a + 1) * rowFactor a) * (∏ r ∈ Finset.Ico 2 a, rowFactor r) := by ring
          _ = _ := by rw [hcoef]; ring
      _ = convolutionYield ⟨a + 1, by omega⟩ := by
        rw [ih]
        unfold convolutionYield
        rw [Finset.prod_Ico_succ_top (by omega : 1 ≤ a)]
        simp only [Nat.cast_add, Nat.cast_one]
        have hd' : 3 * (a : ℝ) - 1 ≠ 0 := by linarith
        field_simp [hd'] <;> ring

/-- Internal scalar certificate consequence. Off-domain zero indices of x are
never used; all row and boundary inputs lie in the positive convolution domain. -/
theorem convolutionPotential_diagonal_lower (x : ℕ → ℕ → ℝ)
    (hx : ∀ r b, 1 ≤ r → 1 ≤ b → 0 < x r b)
    (hneighbor : ∀ r b, 2 ≤ r → r ≤ b → b ≤ 4 * r - 2 →
      x r (b - 1) + x r (b + 1) ≤ 2 * x r b)
    (htripling : ∀ r, 2 ≤ r → 3 * x r r ≤ x r (4 * r - 1))
    (hboundary : ∀ r, 3 ≤ r → x r (r - 1) = x (r - 1) r)
    (a : {n : ℕ // 2 ≤ n}) :
    convolutionYield a * x 2 1 ≤ x a.val a.val := by
  have hrow (r : ℕ) (hr : 2 ≤ r) (inner : Bool) := row_bound (x r) r hr
    (fun b hb => hneighbor r b hr (Finset.mem_Ico.mp hb).1 (by
      have := (Finset.mem_Ico.mp hb).2
      omega)) (htripling r hr) inner
  have hfactor (r : ℕ) (hr : 2 ≤ r) : 0 ≤ rowFactor r := by
    have hrreal : (2 : ℝ) ≤ r := by exact_mod_cast hr
    unfold rowFactor
    apply div_nonneg <;> linarith
  have houter (r : ℕ) (hr : 2 ≤ r) : 0 ≤ outerFactor r := by
    have hrreal : (2 : ℝ) ≤ r := by exact_mod_cast hr
    unfold outerFactor
    apply div_nonneg <;> linarith
  have hchain (r : ℕ) (hr : 2 ≤ r) :
      (∏ t ∈ Finset.Ico 2 (r + 1), rowFactor t) * x 2 1 ≤ x r (r + 1) := by
    induction r, hr using Nat.le_induction with
    | base => simpa [Finset.prod_Ico_succ_top] using hrow 2 (by omega) true
    | succ r hr ih =>
      have hb := hrow (r + 1) (by omega) true
      change rowFactor (r + 1) * x (r + 1) (r + 1 - 1) ≤ x (r + 1) (r + 1 + 1) at hb
      rw [hboundary (r + 1) (by omega)] at hb
      rw [Nat.add_sub_cancel] at hb
      rw [Finset.prod_Ico_succ_top (by omega : 2 ≤ r + 1)]
      have hm := mul_le_mul_of_nonneg_left ih (hfactor (r + 1) (by omega))
      nlinarith [hm, hb]
  have ha := a.property
  have hb := hrow a.val ha false
  change outerFactor a.val * x a.val (a.val - 1) ≤ x a.val a.val at hb
  by_cases he : a.val = 2
  · rw [he] at hb ⊢
    norm_num [convolutionYield, outerFactor, he] at hb ⊢
    exact hb
  · have ha3 : 3 ≤ a.val := by omega
    rw [hboundary a.val ha3] at hb
    have hc := hchain (a.val - 1) (by omega)
    have heq : a.val - 1 + 1 = a.val := by omega
    rw [heq] at hc
    have hm := mul_le_mul_of_nonneg_left hc (houter a.val ha)
    have hy := profile_eq_yield a.val ha
    rw [← hy]
    nlinarith [hm, hb]

end BlockIdentities.Square
