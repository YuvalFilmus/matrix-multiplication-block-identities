/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Frozen.formalRectangularOmega_curve
public import BlockIdentities.Arithmetic.RectangularBasics

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular.Providers
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem formal_rectangular_cost_le (F : Type*) [Field F] (k : ℝ) (hk : 0 ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : OAI.MatrixMultiplication.Arithmetic.MatrixAlgorithm F n
        (OAI.MatrixMultiplication.Arithmetic.innerSize n k) n,
        Arithmetic.FormalCorrect P ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^
          ((if k ≤ (1 : ℝ) / 2 then 2 else 1 + k + 1 / (4 * k)) + ε) :=
by
  exact (Arithmetic.formalRectangularAdmissibleExponent_of_omega_le
    (BlockIdentities.Rectangular.formalRectangularOmega_curve F k hk)) ε hε

end BlockIdentities.Rectangular.Providers
