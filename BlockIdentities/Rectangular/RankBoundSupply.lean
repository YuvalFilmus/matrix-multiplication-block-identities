/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.RankBoundMatrices
public import BlockIdentities.Tensor.ScalarSupply
public import BlockIdentities.Rectangular.AsymptoticRankBasics

/-! Actual rounded diagonal-to-matrix supply in the interior support direction. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open Filter
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open BlockIdentities.Arithmetic BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped Topology NNReal
variable {F : Type*} [Field F]

theorem interiorSupport_exponent_pos (S : InteriorSupport F) :
    0 < orientedExponent F S.direction := by
  have hb := formalShapeOmega_output_le (F := AlgebraicClosure F)
    (S.direction 1) (S.direction 2) (S.direction 0)
  have hp : 0 < (S.direction 0 : ℝ) := by exact_mod_cast S.direction_pos 0
  have hn := (S.direction 1).property
  change 0 < formalShapeOmega (AlgebraicClosure F) _ _ _
  linarith

/-- This is the source scalar t, before any eventual rank estimate. -/
def diagonalSupplyScale (S : InteriorSupport F) (h : ℕ) (ε : ℝ) : ℝ :=
  Real.log (h : ℝ) / (orientedExponent F S.direction + ε)

theorem diagonalSupplyScale_nonneg (S : InteriorSupport F) {h : ℕ} (hh : 1 ≤ h)
    {ε : ℝ} (hε : 0 < ε) : 0 ≤ diagonalSupplyScale S h ε :=
  div_nonneg (Real.log_nonneg (by exact_mod_cast hh))
    (by have hw := interiorSupport_exponent_pos S; linarith)

def diagonalSupplyDimension (S : InteriorSupport F) (h : ℕ) (ε : ℝ)
    (i : Axis) (j : ℕ) : ℕ :=
  auxiliaryPadding (diagonalSupplyScale S h ε * (S.direction i : ℝ)) j

theorem diagonalSupplyDimension_pos (S : InteriorSupport F) {h : ℕ} (hh : 1 ≤ h)
    {ε : ℝ} (hε : 0 < ε) (i : Axis) (j : ℕ) :
    1 ≤ diagonalSupplyDimension S h ε i j :=
  auxiliaryPadding_pos (mul_nonneg (diagonalSupplyScale_nonneg S hh hε)
    (S.direction i).property) j

theorem diagonalSupplyDimension_log_rate (S : InteriorSupport F) {h : ℕ} (hh : 1 ≤ h)
    {ε : ℝ} (hε : 0 < ε) (i : Axis) :
    Tendsto (fun j : ℕ => Real.log (diagonalSupplyDimension S h ε i j : ℝ) /
      ((j : ℝ) + 1)) atTop
      (𝓝 (diagonalSupplyScale S h ε * (S.direction i : ℝ))) :=
  auxiliaryPadding_log_rate (mul_nonneg (diagonalSupplyScale_nonneg S hh hε)
    (S.direction i).property)

private theorem scalar_matrix_rank :
    Tensor.RankAtMost (matrixMultiplicationTensor (K := AlgebraicClosure F) 1 1 1) 1 := by
  classical
  refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, ?_⟩
  funext x y z
  simp [matrixMultiplicationTensor, Tensor.rankOne]
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Strict epsilon slack gives an actual eventual finite rank budget. The
h=1 branch is the scalar tensor and uses no strict exponential comparison. -/
theorem eventually_diagonalSupply_rank (S : InteriorSupport F) {h : ℕ} (hh : 1 ≤ h)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, exactRank (matrixMultiplicationTensor (K := AlgebraicClosure F)
      (diagonalSupplyDimension S h ε 1 j) (diagonalSupplyDimension S h ε 2 j)
      (diagonalSupplyDimension S h ε 0 j)) ≤ h ^ (j + 1) := by
  by_cases h1 : h = 1
  · subst h
    have hscalar := exactRank_le (scalar_matrix_rank (F := F))
    filter_upwards [] with j
    have hd (i : Axis) : diagonalSupplyDimension S 1 ε i j = 1 := by
      rw [diagonalSupplyDimension, diagonalSupplyScale, Nat.cast_one, Real.log_one,
        zero_div, zero_mul, auxiliaryPadding, Real.exp_zero, one_pow, Nat.floor_one]
    rw [hd 1, hd 2, hd 0, one_pow]
    exact hscalar
  have hhp : 0 < (h : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hhlt : 1 < (h : ℝ) := by exact_mod_cast (show 1 < h by omega)
  have hlog : 0 < Real.log (h : ℝ) := Real.log_pos hhlt
  have hw := interiorSupport_exponent_pos S
  have hden : 0 < orientedExponent F S.direction + ε := by linarith
  let t : ℝ≥0 := ⟨diagonalSupplyScale S h ε, diagonalSupplyScale_nonneg S hh hε⟩
  have hmargin : (t : ℝ) * orientedExponent F S.direction < Real.log (h : ℝ) := by
    change (Real.log (h : ℝ) / (orientedExponent F S.direction + ε)) *
      orientedExponent F S.direction < Real.log (h : ℝ)
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hlim := tendsto_log_exactRank_matrix_of_log_dimensions (F := AlgebraicClosure F)
    (t * S.direction 1) (t * S.direction 2) (t * S.direction 0)
    (diagonalSupplyDimension S h ε 1) (diagonalSupplyDimension S h ε 2)
    (diagonalSupplyDimension S h ε 0)
    (diagonalSupplyDimension_pos S hh hε 1) (diagonalSupplyDimension_pos S hh hε 2)
    (diagonalSupplyDimension_pos S hh hε 0)
    (by
      change Tendsto _ _ (𝓝 (diagonalSupplyScale S h ε * (S.direction 1 : ℝ)))
      exact diagonalSupplyDimension_log_rate S hh hε 1)
    (by
      change Tendsto _ _ (𝓝 (diagonalSupplyScale S h ε * (S.direction 2 : ℝ)))
      exact diagonalSupplyDimension_log_rate S hh hε 2)
    (by
      change Tendsto _ _ (𝓝 (diagonalSupplyScale S h ε * (S.direction 0 : ℝ)))
      exact diagonalSupplyDimension_log_rate S hh hε 0)
  rw [formalShapeOmega_mul] at hlim
  have hevent := hlim.eventually (eventually_lt_nhds hmargin)
  filter_upwards [hevent] with j hj
  have hjpos : 0 < (j : ℝ) + 1 := by positivity
  have hlogbound := (div_lt_iff₀ hjpos).mp hj
  have hrpos : 0 < (exactRank (matrixMultiplicationTensor (K := AlgebraicClosure F)
      (diagonalSupplyDimension S h ε 1 j) (diagonalSupplyDimension S h ε 2 j)
      (diagonalSupplyDimension S h ε 0 j)) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_exactRank_matrix
      (F := AlgebraicClosure F) (diagonalSupplyDimension_pos S hh hε 1 j)
      (diagonalSupplyDimension_pos S hh hε 2 j) (diagonalSupplyDimension_pos S hh hε 0 j)))
  have hlogpow : Real.log ((h ^ (j + 1) : ℕ) : ℝ) =
      Real.log (h : ℝ) * ((j : ℝ) + 1) := by
    rw [Nat.cast_pow, Real.log_pow]
    push_cast
    ring
  rw [← hlogpow] at hlogbound
  have hbudget := (Real.log_le_log_iff hrpos (by positivity)).mp hlogbound.le
  exact_mod_cast hbudget

/-- The finite rank budget is consumed as actual diagonal restriction maps. -/
theorem eventually_diagonalSupply_degeneration (S : InteriorSupport F) {h : ℕ}
    (hh : 1 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, Degenerates (diagonal (K := AlgebraicClosure F) (h ^ (j + 1)))
      (matrix (diagonalSupplyDimension S h ε 1 j) (diagonalSupplyDimension S h ε 2 j)
        (diagonalSupplyDimension S h ε 0 j)) := by
  filter_upwards [eventually_diagonalSupply_rank S hh hε] with j hj
  let A : FiniteTensor (AlgebraicClosure F) :=
    matrix (diagonalSupplyDimension S h ε 1 j) (diagonalSupplyDimension S h ε 2 j)
      (diagonalSupplyDimension S h ε 0 j)
  have hjA : exactRank A.coeff ≤ h ^ (j + 1) := by
    change exactRank (FiniteTensor.ofTensor _).coeff ≤ _
    rw [exactRank_ofTensor]
    exact hj
  have hc : ClassDegenerates ((h ^ (j + 1) : ℕ) : TensorClass (AlgebraicClosure F))
      (tensorClass A) :=
    (ClassDegenerates.of_le (Nat.mono_cast hjA)).trans (rank_scalar_supply A)
  apply (classDegenerates_tensorClass_iff _ A).mp
  simpa only [tensorClass_diagonal_eq] using hc

end BlockIdentities.Rectangular
