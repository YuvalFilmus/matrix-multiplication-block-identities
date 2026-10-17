/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ElementaryRestrictions
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Rank

/-! Interpolation supplies the actual finite convolution rank bound. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

/-- Transport the safe interpolation decomposition to the literal finite presentation. -/
theorem convolution_coeff_rankAtMost [Infinite K] (r b : ℕ+) :
    Tensor.RankAtMost (convolution (K := K) r b).coeff ((r : ℕ) + (b : ℕ) - 1) := by
  have h := OAI.MatrixMultiplication.AuxiliarySeparation.convolution_rankAtMost (K := K) (r : ℕ) (b : ℕ)
  exact h.pullback (Fintype.equivFin (Fin r)).symm
    (Fintype.equivFin (Fin b)).symm (Fintype.equivFin (Fin ((r : ℕ) + (b : ℕ) - 1))).symm

/-- A genuine interpolation rank decomposition gives the approved border-rank predicate.
The positive carriers are those of the approved convolution definition. -/
theorem convolution_borderRankAtMost [Infinite K] (r b : ℕ+) :
    BorderRankAtMost (convolution (K := K) r b) ((r : ℕ) + (b : ℕ) - 1) :=
  degenerates_of_rankAtMost (convolution_coeff_rankAtMost r b)

end BlockIdentities.Square
