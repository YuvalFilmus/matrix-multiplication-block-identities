/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Square.Certificate

/-! Group actual edge occurrences by their destination vertices. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open scoped BigOperators

/-- Summing the actual weighted occurrence count at each destination gives
exactly the sum over the original occurrence indices. Repeated labels add. -/
theorem sum_multiplicity_mul {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (w : I → V) (k : I → ℝ) (x : V → ℝ) :
    (∑ v, (∑ i, if w i = v then k i else 0) * x v) = ∑ i, k i * x (w i) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end BlockIdentities.Square
