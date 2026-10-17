/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.SharedEntropyInequality
public import BlockIdentities.Square.EntropyValueOptimization

/-! The actual shared-leg extraction followed by entropy optimization. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Providers
open BlockIdentities.Square
open scoped BigOperators

theorem shared_leg_value_inequality {K : Type*} [Field K] [IsAlgClosed K]
    {ι : Type} [Fintype ι] (A : NonzeroTensor K) (B : ι → NonzeroTensor K)
    (D : MatrixShape) (E : ι → MatrixShape)
    (identity : SharedLegIdentity A.val (fun i => (B i).val) D E) :
    (D.volume : ℝ) * normalizedValueAtOmega A ≥
      ∑ i, ((E i).volume : ℝ) * normalizedValueAtOmega (B i) := by
  classical
  let ρ : Set.Icc (2 : ℝ) 3 :=
    ⟨Arithmetic.formalOmega K, Arithmetic.formalOmega_mem_Icc (F := K)⟩
  have hν : 0 < Arithmetic.formalOmega K := by
    have := Arithmetic.formalOmega_mem_Icc (F := K)
    linarith [this.1]
  have hV : 0 < valueAtOmega A := lt_of_lt_of_le zero_lt_one (one_le_value A ρ)
  have hB : ∀ i, 0 < valueAtOmega (B i) :=
    fun i => lt_of_lt_of_le zero_lt_one (one_le_value (B i) ρ)
  have hD : 0 < (D.volume : ℝ) := by
    exact_mod_cast (Nat.mul_pos (Nat.mul_pos D.a_pos D.b_pos) D.c_pos)
  have hE : ∀ i, 0 < ((E i).volume : ℝ) := by
    intro i
    exact_mod_cast (Nat.mul_pos (Nat.mul_pos (E i).a_pos (E i).b_pos) (E i).c_pos)
  exact normalizedValue_sum_le_of_entropy_bounds (valueAtOmega A)
    (fun i => valueAtOmega (B i)) (fun i => ((E i).volume : ℝ))
    (D.volume : ℝ) (Arithmetic.formalOmega K) hV hB hE hD hν
    (fun p hp hsum => identity.entropy_inequality A B p hp hsum)

end BlockIdentities.Providers
