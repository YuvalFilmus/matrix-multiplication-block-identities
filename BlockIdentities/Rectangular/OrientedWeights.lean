/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Definitions

/-! Positivity and logarithmic interpretation of the literal oriented matrix
weight. These identities retain the ordered physical tensor legs. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open scoped BigOperators NNReal
variable {F : Type*} [Field F]

theorem matrixWeight_pos (S : InteriorSupport F) (D : MatrixShape) :
    0 < matrixWeight S D := by
  unfold matrixWeight
  exact mul_pos (mul_pos
    (Real.rpow_pos_of_pos (by exact_mod_cast D.a_pos) _)
    (Real.rpow_pos_of_pos (by exact_mod_cast D.b_pos) _))
    (Real.rpow_pos_of_pos (by exact_mod_cast D.c_pos) _)

theorem matrixWeight_scalar (S : InteriorSupport F) : matrixWeight S scalarShape = 1 := by
  simp [matrixWeight, scalarShape]

theorem log_matrixWeight (S : InteriorSupport F) (D : MatrixShape) :
    Real.log (matrixWeight S D) =
      ∑ i, S.weight i * logDotDimensions D i := by
  have ha : 0 < (D.a : ℝ) := by exact_mod_cast D.a_pos
  have hb : 0 < (D.b : ℝ) := by exact_mod_cast D.b_pos
  have hc : 0 < (D.c : ℝ) := by exact_mod_cast D.c_pos
  simp only [matrixWeight, Real.log_mul
    (ne_of_gt (mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)))
    (ne_of_gt (Real.rpow_pos_of_pos hc _)),
    Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos ha _))
      (ne_of_gt (Real.rpow_pos_of_pos hb _)), Real.log_rpow ha,
    Real.log_rpow hb, Real.log_rpow hc]
  simp [Fin.sum_univ_succ, logDotDimensions]
  ring

end BlockIdentities.Rectangular
