/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ClassIdentities

/-! Finite diagonal rank decompositions, independent of tensor characters. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

/-- The literal diagonal has its displayed finite rank decomposition. -/
theorem diagonal_rankAtMost (a : ℕ) : Tensor.RankAtMost (diagonal (K := K) a).coeff a := by
  classical
  change Tensor.RankAtMost (fun i j k : Fin a => if i = j ∧ j = k then (1 : K) else 0) a
  refine ⟨(fun i x => if x = i then 1 else 0),
    (fun i y => if y = i then 1 else 0),
    (fun i z => if z = i then 1 else 0), ?_⟩
  funext x y z
  simp [Tensor.rankOne, mul_ite, ite_and]
  split_ifs <;> simp_all

/-- Only the finite upper bound is needed for independent-copy estimates. -/
theorem rank_natCast_le (a : ℕ) : rank (a : TensorClass K) ≤ a := by
  rw [← tensorClass_diagonal_eq, rank_tensorClass]
  exact exactRank_le (diagonal_rankAtMost a)

end BlockIdentities.Square
