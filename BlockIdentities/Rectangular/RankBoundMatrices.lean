/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.ShapeRankAsymptotics
public import BlockIdentities.Rectangular.OrientedGeometry
public import BlockIdentities.Square.MatrixRateLimits

/-! Literal positive matrix dimensions for the large auxiliary matrix in the
oriented value rank bound. The same rounded padding is retained on the output. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open Filter
open OAI.MatrixMultiplication.AuxiliarySeparation
open BlockIdentities.Arithmetic
open BlockIdentities.Square
open scoped Topology NNReal BigOperators
variable {F : Type*} [Field F]

/-- A single large scale strictly dominates all three fixed input dimensions. -/
theorem exists_auxiliary_scale (S : InteriorSupport F) (D : MatrixShape) :
    ∃ L : ℝ, 0 < L ∧ ∀ i, logDotDimensions D i < L * (S.direction i : ℝ) := by
  classical
  let v : Axis → ℝ := fun i => (S.direction i : ℝ)
  let d : Axis → ℝ := logDotDimensions D
  let L : ℝ := 1 + ∑ i : Axis, max (d i) 0 / v i
  have hv (i : Axis) : 0 < v i := by exact_mod_cast S.direction_pos i
  have hnonneg (i : Axis) : 0 ≤ max (d i) 0 / v i :=
    div_nonneg (le_max_right _ _) (hv i).le
  have hsum : 0 ≤ ∑ i : Axis, max (d i) 0 / v i := Finset.sum_nonneg (fun i _ => hnonneg i)
  refine ⟨L, by dsimp [L]; linarith, ?_⟩
  intro i
  have hi : max (d i) 0 / v i ≤ ∑ j : Axis, max (d j) 0 / v j :=
    Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  have hlt : max (d i) 0 / v i < L := by dsimp [L]; linarith
  have hh := (div_lt_iff₀ (hv i)).mp hlt
  exact (le_max_left _ _).trans_lt hh

/-- The literal rounded factor; writing it as a power exposes the existing
floor-rate theorem without changing the exponential in the manuscript. -/
def auxiliaryPadding (q : ℝ) (j : ℕ) : ℕ := Nat.floor (Real.exp q ^ (j + 1))

theorem auxiliaryPadding_eq (q : ℝ) (j : ℕ) :
    auxiliaryPadding q j = Nat.floor (Real.exp (((j : ℝ) + 1) * q)) := by
  unfold auxiliaryPadding
  congr 1
  simpa only [Nat.cast_add, Nat.cast_one] using (Real.exp_nat_mul q (j + 1)).symm

theorem auxiliaryPadding_pos {q : ℝ} (hq : 0 ≤ q) (j : ℕ) :
    1 ≤ auxiliaryPadding q j :=
  Square.one_le_natFloor_pow (Real.exp q) (Real.one_le_exp_iff.mpr hq) (j + 1)

theorem auxiliaryPadding_log_rate {q : ℝ} (hq : 0 ≤ q) :
    Tendsto (fun j : ℕ => Real.log (auxiliaryPadding q j : ℝ) / ((j : ℝ) + 1))
      atTop (𝓝 q) := by
  have hn : Tendsto (fun j : ℕ => j + 1) atTop atTop :=
    tendsto_atTop_mono (fun j : ℕ => Nat.le_succ j) (tendsto_id : Tendsto (fun j : ℕ => j) atTop atTop)
  have h := (Square.tendsto_log_natFloor_pow_div (Real.exp q)
    (Real.one_le_exp_iff.mpr hq)).comp hn
  change Tendsto (fun j : ℕ => Real.log (auxiliaryPadding q j : ℝ) /
    ((j + 1 : ℕ) : ℝ)) atTop (𝓝 (Real.log (Real.exp q))) at h
  rw [Real.log_exp] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- Repeating a fixed positive dimension and retaining the same rounded padding
has exactly the sum of their logarithmic rates. -/
theorem repeated_dimension_log_rate (d : ℕ) (hd : 1 ≤ d)
    {q : ℝ} (hq : 0 ≤ q) :
    Tendsto (fun j : ℕ => Real.log ((d ^ (j + 1) * auxiliaryPadding q j : ℕ) : ℝ) /
      ((j : ℝ) + 1)) atTop (𝓝 (Real.log (d : ℝ) + q)) := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have heq (j : ℕ) :
      Real.log ((d ^ (j + 1) * auxiliaryPadding q j : ℕ) : ℝ) / ((j : ℝ) + 1) =
        Real.log (d : ℝ) + Real.log (auxiliaryPadding q j : ℝ) / ((j : ℝ) + 1) := by
    have hp : 0 < (auxiliaryPadding q j : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (auxiliaryPadding_pos hq j))
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (ne_of_gt (pow_pos hdpos _))
      (ne_of_gt hp), Real.log_pow]
    push_cast
    field_simp [ne_of_gt (show 0 < (j : ℝ) + 1 by positivity)]

  simp_rw [heq]
  exact tendsto_const_nhds.add (auxiliaryPadding_log_rate hq)

/-- The input auxiliary dimension has rate L v, not an estimate obtained by
subtracting unrelated bounds on the exponent function. -/
theorem auxiliary_input_log_rate (d : ℕ) (hd : 1 ≤ d) (w : ℝ)
    (hw : Real.log (d : ℝ) ≤ w) :
    Tendsto (fun j : ℕ => Real.log
      ((d ^ (j + 1) * auxiliaryPadding (w - Real.log (d : ℝ)) j : ℕ) : ℝ) /
        ((j : ℝ) + 1)) atTop (𝓝 w) := by
  simpa only [add_sub_cancel] using
    repeated_dimension_log_rate d hd (sub_nonneg.mpr hw)

/-- On the output the input complement is unchanged. Consequently the rate is
L v + e - d, with the actual input and output logarithms in their source order. -/
theorem auxiliary_output_log_rate (d e : ℕ) (he : 1 ≤ e) (w : ℝ)
    (hw : Real.log (d : ℝ) ≤ w) :
    Tendsto (fun j : ℕ => Real.log
      ((e ^ (j + 1) * auxiliaryPadding (w - Real.log (d : ℝ)) j : ℕ) : ℝ) /
        ((j : ℝ) + 1)) atTop (𝓝 (w + Real.log (e : ℝ) - Real.log (d : ℝ))) := by
  have h := repeated_dimension_log_rate e he (sub_nonneg.mpr hw)
  have heq : Real.log (e : ℝ) + (w - Real.log (d : ℝ)) =
      w + Real.log (e : ℝ) - Real.log (d : ℝ) := by ring
  rw [heq] at h
  exact h

/-- The actual auxiliary matrix rank has rate L W(v). All three rounded
coordinates are supplied to the varying-dimension rank theorem. -/
theorem auxiliary_matrix_rank_log_rate (S : InteriorSupport F) (D : MatrixShape)
    (L : ℝ≥0) (hL : ∀ i, logDotDimensions D i ≤ (L : ℝ) * (S.direction i : ℝ)) :
    Tendsto (fun j : ℕ => Real.log (exactRank
      (matrixMultiplicationTensor (K := AlgebraicClosure F)
        (D.a ^ (j + 1) * auxiliaryPadding
          ((L : ℝ) * (S.direction 1 : ℝ) - Real.log (D.a : ℝ)) j)
        (D.b ^ (j + 1) * auxiliaryPadding
          ((L : ℝ) * (S.direction 2 : ℝ) - Real.log (D.b : ℝ)) j)
        (D.c ^ (j + 1) * auxiliaryPadding
          ((L : ℝ) * (S.direction 0 : ℝ) - Real.log (D.c : ℝ)) j)) : ℝ) /
        ((j : ℝ) + 1)) atTop (𝓝 ((L : ℝ) * orientedExponent F S.direction)) := by
  have ha : Real.log (D.a : ℝ) ≤ (L : ℝ) * (S.direction 1 : ℝ) := by
    simpa [logDotDimensions] using hL 1
  have hb : Real.log (D.b : ℝ) ≤ (L : ℝ) * (S.direction 2 : ℝ) := by
    simpa [logDotDimensions] using hL 2
  have hc : Real.log (D.c : ℝ) ≤ (L : ℝ) * (S.direction 0 : ℝ) := by
    simpa [logDotDimensions] using hL 0
  have pos (d : ℕ) (hd : 0 < d) (q : ℝ) (hq : 0 ≤ q) (j : ℕ) :
      1 ≤ d ^ (j + 1) * auxiliaryPadding q j :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos (pow_pos hd _)
      (lt_of_lt_of_le Nat.zero_lt_one (auxiliaryPadding_pos hq j))))
  have h := tendsto_log_exactRank_matrix_of_log_dimensions (F := AlgebraicClosure F)
    (L * S.direction 1) (L * S.direction 2) (L * S.direction 0)
    (fun j => D.a ^ (j + 1) * auxiliaryPadding
      ((L : ℝ) * (S.direction 1 : ℝ) - Real.log (D.a : ℝ)) j)
    (fun j => D.b ^ (j + 1) * auxiliaryPadding
      ((L : ℝ) * (S.direction 2 : ℝ) - Real.log (D.b : ℝ)) j)
    (fun j => D.c ^ (j + 1) * auxiliaryPadding
      ((L : ℝ) * (S.direction 0 : ℝ) - Real.log (D.c : ℝ)) j)
    (pos D.a D.a_pos _ (sub_nonneg.mpr ha))
    (pos D.b D.b_pos _ (sub_nonneg.mpr hb))
    (pos D.c D.c_pos _ (sub_nonneg.mpr hc))
    (by
      change Tendsto _ _ (𝓝 ((L : ℝ) * (S.direction 1 : ℝ)))
      exact auxiliary_input_log_rate D.a (by have hp := D.a_pos; omega) _ ha)
    (by
      change Tendsto _ _ (𝓝 ((L : ℝ) * (S.direction 2 : ℝ)))
      exact auxiliary_input_log_rate D.b (by have hp := D.b_pos; omega) _ hb)
    (by
      change Tendsto _ _ (𝓝 ((L : ℝ) * (S.direction 0 : ℝ)))
      exact auxiliary_input_log_rate D.c (by have hp := D.c_pos; omega) _ hc)
  rw [formalShapeOmega_mul] at h
  exact h

end BlockIdentities.Rectangular
