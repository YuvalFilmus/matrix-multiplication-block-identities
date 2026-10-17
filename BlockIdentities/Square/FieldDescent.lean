/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.FieldDescent

/-! The manuscript's fixed-overhead scalar descent, in exact coefficient form. -/

public section

namespace BlockIdentities.Square

open OAI.MatrixMultiplication.Foundation

/-- One fixed decomposition over the algebraic closure gives one fixed coefficient
extension dimension q, before the tensor power m varies. No separability is used. -/
theorem scalar_descent_bound {F X Y Z : Type*} [Field F]
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor F X Y Z) (r : ℕ)
    (h : Tensor.RankAtMost
      (fun x y z => algebraMap F (AlgebraicClosure F) (T x y z)) r) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ m : ℕ, 1 ≤ m →
      Tensor.RankAtMost (Tensor.power T m) (q ^ 2 * r ^ m) := by
  obtain ⟨q, hq, hpow⟩ := h.descend_algebraicClosure_powers
  refine ⟨q, hq, fun m _hm => ?_⟩
  rw [show q ^ 2 * r ^ m = r ^ m * q * q by ring]
  exact hpow m

end BlockIdentities.Square
