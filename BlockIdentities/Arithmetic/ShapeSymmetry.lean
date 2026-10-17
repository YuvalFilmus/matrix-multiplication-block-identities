/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.ShapeRankSeeds

/-! Permutation symmetry of actual formal shape exponents, through finite
coefficient rank identities and formally correct recursive programs. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.Arithmetic
open scoped BigOperators NNReal
variable {F : Type*} [Field F]

theorem rectangular_matrix_rankAtMost_swap_first {a b c R : ℕ}
    (h : Tensor.RankAtMost (matrixMultiplicationTensor (K := F) a b c) R) :
    Tensor.RankAtMost (matrixMultiplicationTensor (K := F) b a c) R := by
  obtain ⟨L, M, N, he⟩ := h
  refine ⟨(fun q x => L q (x.2, x.1)), (fun q y => N q (y.2, y.1)),
    (fun q z => M q (z.2, z.1)), ?_⟩
  funext x y z
  calc
    matrixMultiplicationTensor (K := F) b a c x y z =
        matrixMultiplicationTensor (K := F) a b c (x.2, x.1) (z.2, z.1) (y.2, y.1) := by
      simp only [matrixMultiplicationTensor, eq_comm, and_assoc, and_comm, and_left_comm]
    _ = ∑ q, Tensor.rankOne (L q) (M q) (N q)
        (x.2, x.1) (z.2, z.1) (y.2, y.1) :=
      congrFun (congrFun (congrFun he (x.2, x.1)) (z.2, z.1)) (y.2, y.1)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      dsimp only [Tensor.rankOne]
      ring

private theorem formalShapeOmega_cyclic_le (a b c : ℝ≥0) :
    formalShapeOmega F b c a ≤ formalShapeOmega F a b c := by
  apply (formalShapeOmega_le_iff_rank_seeds b c a _).mpr
  intro ε hε
  obtain ⟨N, R, hN, hRank, hR⟩ :=
    (formalShapeOmega_le_iff_rank_seeds (F := F) a b c _).mp le_rfl ε hε
  exact ⟨N, R, hN, Tensor.matrixCoefficients_cyclic_rank hRank, hR⟩

theorem formalShapeOmega_cyclic (a b c : ℝ≥0) :
    formalShapeOmega F b c a = formalShapeOmega F a b c :=
  le_antisymm (formalShapeOmega_cyclic_le a b c)
    ((formalShapeOmega_cyclic_le c a b).trans (formalShapeOmega_cyclic_le b c a))

private theorem formalShapeOmega_swap_first_le (a b c : ℝ≥0) :
    formalShapeOmega F b a c ≤ formalShapeOmega F a b c := by
  apply (formalShapeOmega_le_iff_rank_seeds b a c _).mpr
  intro ε hε
  obtain ⟨N, R, hN, hRank, hR⟩ :=
    (formalShapeOmega_le_iff_rank_seeds (F := F) a b c _).mp le_rfl ε hε
  exact ⟨N, R, hN, rectangular_matrix_rankAtMost_swap_first hRank, hR⟩

theorem formalShapeOmega_swap_first (a b c : ℝ≥0) :
    formalShapeOmega F b a c = formalShapeOmega F a b c :=
  le_antisymm (formalShapeOmega_swap_first_le a b c)
    (formalShapeOmega_swap_first_le b a c)

end BlockIdentities.Arithmetic
