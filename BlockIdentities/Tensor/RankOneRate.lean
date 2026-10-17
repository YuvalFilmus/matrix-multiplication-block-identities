/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.MatrixRateBounds
public import BlockIdentities.Tensor.RankOneValue

/-! Rank-one sources have no matrix-dimension rate above one. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

theorem MatrixRate.eq_one_of_rankAtMost_one {A : FiniteTensor K} {r : ℝ}
    (hRate : MatrixRate A r) (hRank : Tensor.RankAtMost A.coeff 1) : r = 1 := by
  have hscalar := hRate.of_degeneration (degenerates_of_rankAtMost hRank)
  have hle := hscalar.le_coordinate_bound
  have hr : 1 ≤ r := hRate.1
  have hle' : r ≤ 1 := by simpa only [diagonal, max_self, Nat.cast_one] using hle
  exact le_antisymm hle' hr

end BlockIdentities.Square
