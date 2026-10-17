/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Definitions
public import BlockIdentities.Rectangular.Providers.OrientedRankAsymptotics

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
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
-- BEGIN APPROVED PROOF REGION
by exact BlockIdentities.Rectangular.Providers.oriented_rank_asymptotics (F := F) u d hd hrates
-- END APPROVED PROOF REGION

end BlockIdentities.Rectangular
