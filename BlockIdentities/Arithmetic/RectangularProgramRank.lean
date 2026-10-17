/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.ProgramRank
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.MatrixMultiplication

/-! The genuine shared-register bilinearization bound for all rectangular sizes. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Arithmetic
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators
variable {F X Y : Type*} [Field F]

private theorem rectangular_mixedJet_sum {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial (X ⊕ Y) F) (x : X) (y : Y) :
    mixedJet (∑ i, f i) x y = ∑ i, mixedJet (f i) x y := by
  simp [mixedJet, map_sum]

/-- Actual coefficientwise formal correctness supplies a rectangular tensor rank
bound with the original program operation cost, in every characteristic. -/
theorem rectangular_matrix_rankAtMost_of_formalCorrect {a b c : ℕ}
    (P : MatrixAlgorithm F a b c) (hP : FormalCorrect P) :
    Tensor.RankAtMost (matrixMultiplicationTensor (K := F) a b c) (2 * P.cost) := by
  classical
  have h := program_outputs_mixedJet_rankAtMost P.program
    (fun z : Fin c × Fin a => P.output z.2 z.1)
  convert h using 1
  · funext x y z
    rw [hP z.2 z.1, rectangular_mixedJet_sum]
    rw [Finset.sum_eq_single y.1]
    · simp only [mixedJet_X_left_mul_X_right]
      by_cases hxy : x.2 = y.1 <;>
        by_cases hxz : x.1 = z.2 <;>
        by_cases hyz : y.2 = z.1 <;>
        simp [matrixMultiplicationTensor, Prod.ext_iff, hxy, hxz, hyz, eq_comm]
    · intro j _ hj
      have hne : y ≠ (j, z.1) := by
        intro he
        exact hj (congrArg Prod.fst he).symm
      simp [mixedJet_X_left_mul_X_right, hne]
    · simp
  · rfl
end BlockIdentities.Arithmetic
