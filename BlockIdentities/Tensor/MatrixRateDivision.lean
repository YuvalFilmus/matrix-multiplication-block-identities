/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.MatrixRateCancellation
public import BlockIdentities.Tensor.MatrixRatePower
public import BlockIdentities.Tensor.MatrixRateMatrix
public import BlockIdentities.Square.MatrixCancellationScales

/-! Cancellation removes a matrix factor with an arbitrarily small rate loss. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

theorem MatrixRate.divide_matrix_of_lt {A : FiniteTensor K} (hA : Nonzero A)
    (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hRate : MatrixRate (product A (square d)) α)
    (s : ℝ) (hs : 1 ≤ s) (hmargin : s < α / d) : MatrixRate A s := by
  obtain ⟨k, b, hk, hb, hscale, hlog⟩ :=
    exists_matrixCancellation_scales d hd α s hs hmargin
  have he := matrixRate_fixed_scale_cancellation hA d hd hRate k hk b hb hscale
  have hr := (matrixRate_square (K := K) b hb).of_asymptoticallyRestricts he
  exact hr.of_power hA hk s hs hlog

end BlockIdentities.Square
