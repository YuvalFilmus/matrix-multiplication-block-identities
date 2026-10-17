/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.ShapeRankAsymptotics

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular.Providers
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem oriented_rank_asymptotics {F : Type*} [Field F]
    (u : Axis → ℝ≥0) (d : Axis → ℕ → ℕ)
    (hd : ∀ i j, 1 ≤ d i j)
    (hrates : ∀ i, Filter.Tendsto
      (fun j => Real.log (d i j : ℝ) / ((j : ℝ) + 1))
      Filter.atTop (nhds (u i : ℝ))) :
  Filter.Tendsto
      (fun j => Real.log (exactRank (matrixMultiplicationTensor (K := AlgebraicClosure F)
        (d 1 j) (d 2 j) (d 0 j)) : ℝ) / ((j : ℝ) + 1))
      Filter.atTop (nhds (orientedExponent F u)) :=
by
  exact Arithmetic.tendsto_log_exactRank_matrix_of_log_dimensions
    (F := AlgebraicClosure F) (u 1) (u 2) (u 0) (d 1) (d 2) (d 0)
    (hd 1) (hd 2) (hd 0) (hrates 1) (hrates 2) (hrates 0)

end BlockIdentities.Rectangular.Providers
