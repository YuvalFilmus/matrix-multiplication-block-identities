/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.NormNum

/-! Numerical weak duality used in the square criterion. No tensor claims occur here. -/

@[expose] public section

namespace BlockIdentities.Square

open scoped BigOperators

/-- Outgoing weighted cost minus incoming weighted multiplicity at a node. -/
noncomputable def certificateResidual {V E : Type*} [Fintype E] [DecidableEq V]
    (source : E → V) (cost μ : E → ℝ) (multiplicity : E → V → ℝ) (v : V) : ℝ :=
  (∑ e, if source e = v then cost e * μ e else 0) -
    ∑ e, multiplicity e v * μ e

/-- Internal numerical weak duality: feasible node potentials bound a nonnegative
edge certificate's terminal yield. The source and terminal are distinct, and no
edge leaves the terminal. This proves only the finite scalar step of the manuscript
criterion, not the value inequalities supplying its hypotheses. -/
theorem certificate_weakDuality {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (s t : V) (hst : s ≠ t) (source : E → V)
    (cost μ : E → ℝ) (multiplicity : E → V → ℝ) (z : V → ℝ)
    (hz : ∀ v, 0 ≤ z v) (hzt : z t = 1)
    (hsource : ∀ e, source e ≠ t) (hμ : ∀ e, 0 ≤ μ e)
    (hrow : ∀ e, ∑ v, multiplicity e v * z v ≤ cost e * z (source e))
    (hcert : ∀ v, v ≠ t → certificateResidual source cost μ multiplicity v ≤
      if v = s then 1 else 0) :
    ∑ e, multiplicity e t * μ e ≤ z s := by
  classical
  have htotal : 0 ≤ ∑ v, z v * certificateResidual source cost μ multiplicity v := by
    have hid : (∑ v, z v * certificateResidual source cost μ multiplicity v) =
        ∑ e, μ e * (cost e * z (source e) - ∑ v, multiplicity e v * z v) := by
      simp only [certificateResidual, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro e _
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        ring
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro e _
        apply Finset.sum_congr rfl
        intro v _
        ring
    rw [hid]
    exact Finset.sum_nonneg fun e _ => mul_nonneg (hμ e) (sub_nonneg.mpr (hrow e))
  have ht : certificateResidual source cost μ multiplicity t =
      -(∑ e, multiplicity e t * μ e) := by
    simp [certificateResidual, hsource]
  have hupper : (∑ v, z v * certificateResidual source cost μ multiplicity v) ≤
      z s - ∑ e, multiplicity e t * μ e := by
    calc
      _ ≤ ∑ v, if v = t then -(∑ e, multiplicity e t * μ e)
          else z v * (if v = s then 1 else 0) := by
        apply Finset.sum_le_sum
        intro v _
        by_cases hvt : v = t
        · subst v
          simp [ht, hzt]
        · simp only [hvt, ite_false]
          exact mul_le_mul_of_nonneg_left (hcert v hvt) (hz v)
      _ = _ := by
        calc
          _ = ∑ v : V, ((if v = t then -(∑ e, multiplicity e t * μ e) else 0) +
              (if v = s then z s else 0)) := by
            apply Finset.sum_congr rfl
            intro v _
            by_cases hvt : v = t
            · subst v
              simp [Ne.symm hst]
            · by_cases hvs : v = s
              · subst v
                simp [hst]
              · simp [hvt, hvs]
          _ = _ := by
            simp [Finset.sum_add_distrib, sub_eq_add_neg, add_comm]
  linarith

/-- The affine row weights telescope. The index interval is `Ico r N`, i.e.
the manuscript's inclusive range `r,…,N-1`. Real subtraction in the weight
avoids truncated natural-number arithmetic. -/
theorem affine_row_identity (x : ℕ → ℝ) (ν : ℝ) (r N : ℕ)
    (_hr : 2 ≤ r) (hrN : r < N) :
    (∑ b ∈ Finset.Ico r N, ν * ((N : ℝ) - b) *
      (2 * x b - x (b - 1) - x (b + 1))) + ν * (x N - 3 * x r) =
      ν * ((N : ℝ) - r - 2) * x r - ν * ((N : ℝ) - r) * x (r - 1) := by
  let f : ℕ → ℝ := fun b => ν * (((N : ℝ) - b) * (x b - x (b - 1)) + x b)
  have hlocal : ∀ b ∈ Finset.Ico r N,
      ν * ((N : ℝ) - b) * (2 * x b - x (b - 1) - x (b + 1)) =
        f b - f (b + 1) := by
    intro b _hb
    simp only [f, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring
  have hsum : (∑ b ∈ Finset.Ico r N,
      ν * ((N : ℝ) - b) * (2 * x b - x (b - 1) - x (b + 1))) = f r - f N := by
    rw [Finset.sum_congr rfl hlocal]
    rw [Finset.sum_Ico_eq_sub _ (Nat.le_of_lt hrN),
      Finset.sum_range_sub', Finset.sum_range_sub']
    ring
  rw [hsum]
  simp only [f]
  ring

/-- Subtracting a first-position correction changes exactly the three boundary
coefficients. This is the scalar row identity before choosing the cutoff case. -/
theorem corrected_affine_row_identity (x : ℕ → ℝ) (ν q : ℝ) (r N : ℕ)
    (hr : 2 ≤ r) (hrN : r < N) :
    (∑ b ∈ Finset.Ico r N, (ν * ((N : ℝ) - b) - (if b = r then q else 0)) *
      (2 * x b - x (b - 1) - x (b + 1))) + ν * (x N - 3 * x r) =
      (ν * ((N : ℝ) - r - 2) - 2 * q) * x r + q * x (r + 1) -
        (ν * ((N : ℝ) - r) - q) * x (r - 1) := by
  have hbase := affine_row_identity x ν r N hr hrN
  have hmem : r ∈ Finset.Ico r N := Finset.mem_Ico.mpr ⟨le_rfl, hrN⟩
  simp only [sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', hmem, ite_true]
  nlinarith [hbase]

/-- The two scalar boundary cases of the manuscript row certificate, with
`inner = false` for the cutoff row and `inner = true` below it. The balance
assumption is exactly `(3*r-3)*ν = h*w`, where `h` is respectively one or two. -/
theorem convolution_row_certificate (x : ℕ → ℝ) (ν w : ℝ) (r : ℕ)
    (hr : 2 ≤ r) (inner : Bool)
    (hbalance : ν * (3 * (r : ℝ) - 3) = (if inner then 2 else 1) * w) :
    (∑ b ∈ Finset.Ico r (4 * r - 1),
      (ν * ((4 * (r : ℝ) - 1) - b) - (if inner && (b == r) then w else 0)) *
        (2 * x b - x (b - 1) - x (b + 1))) +
      ν * (x (4 * r - 1) - 3 * x r) =
      w * (if inner then x (r + 1) else x r) -
        (ν * (3 * (r : ℝ) - 1) - (if inner then w else 0)) * x (r - 1) := by
  have hrN : r < 4 * r - 1 := by omega
  have hcast : ((4 * r - 1 : ℕ) : ℝ) = 4 * (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 4 * r)]
    norm_num
  have hrow := corrected_affine_row_identity x ν (if inner then w else 0)
    r (4 * r - 1) hr hrN
  rw [hcast] at hrow
  cases inner <;> simp at hbalance hrow ⊢
  · convert hrow using 1; nlinarith [congrArg (fun a : ℝ => a * x r) hbalance]
  · convert hrow using 1; nlinarith [congrArg (fun a : ℝ => a * x r) hbalance]

end BlockIdentities.Square
