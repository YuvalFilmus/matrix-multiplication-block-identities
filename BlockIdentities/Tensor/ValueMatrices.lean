/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ValueProductList
public import BlockIdentities.Tensor.ValueMatrixFactorEquality

/-! Matrix values and the exact normalized value of a terminal tensor. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K] [IsAlgClosed K]

theorem valueAtOmega_square (d : ℕ) (hd : 1 ≤ d) :
    valueAtOmega (nonzeroSquare (K := K) d hd) = (d : ℝ) ^ Arithmetic.formalOmega K := by
  let S := nonzeroSquare (K := K) 1 le_rfl
  let ρ : Set.Icc (2 : ℝ) 3 :=
    ⟨Arithmetic.formalOmega K, Arithmetic.formalOmega_mem_Icc (F := K)⟩
  have hS : cycleClass (tensorClass S.val) = tensorClass S.val := by
    change cycleClass (tensorClass (square (K := K) 1)) = tensorClass (square 1)
    rw [tensorClass_square_eq, cycleClass_matrixClass]
  have heq : tensorClass (S.product (nonzeroSquare d hd)).val =
      tensorClass (nonzeroSquare (K := K) d hd).val := by
    change tensorClass (product (square (K := K) 1) (square d)) = tensorClass (square d)
    simp only [tensorClass_product_eq, tensorClass_square_eq, matrixClass_one, one_mul]
  have hv := value_eq_of_tensorClass_eq ρ (S.product (nonzeroSquare d hd)) (nonzeroSquare d hd) heq
  change valueAtOmega (S.product (nonzeroSquare d hd)) = valueAtOmega (nonzeroSquare d hd) at hv
  have hp := valueAtOmega_product_square S hS d hd
  have hsval : valueAtOmega S = 1 := valueAtOmega_scalar
  rw [hsval, mul_one] at hp
  exact hv.symm.trans hp

theorem normalizedValueAtOmega_terminal (A : NonzeroTensor K) (d : ℕ) (hd : 1 ≤ d)
    (h : Isomorphic (symmetrize A.val) (square d)) : normalizedValueAtOmega A = d := by
  let ν := Arithmetic.formalOmega K
  let ρ : Set.Icc (2 : ℝ) 3 := ⟨ν, Arithmetic.formalOmega_mem_Icc (F := K)⟩
  have hν : 0 < ν := by have := ρ.property; change 2 ≤ ν ∧ ν ≤ 3 at this; linarith [this.1]
  have hV : 0 ≤ valueAtOmega A := (one_le_value A ρ).trans' zero_le_one
  have heq := value_eq_of_tensorClass_eq ρ A.symmetrize (nonzeroSquare d hd) h.tensorClass_eq
  change valueAtOmega A.symmetrize = valueAtOmega (nonzeroSquare d hd) at heq
  have hv : valueAtOmega A ^ 3 = (d : ℝ) ^ ν := by
    change value ρ A ^ 3 = (d : ℝ) ^ ν
    rw [← value_symmetrize ρ A]
    exact heq.trans (valueAtOmega_square d hd)
  have hp : normalizedValueAtOmega A ^ ν = (d : ℝ) ^ ν := by
    change (valueAtOmega A ^ (3 / ν)) ^ ν = _
    rw [← Real.rpow_mul hV, div_mul_cancel₀ _ (ne_of_gt hν)]
    simpa only [Real.rpow_ofNat] using hv
  apply le_antisymm
  · exact (Real.rpow_le_rpow_iff (Real.rpow_nonneg hV _) (Nat.cast_nonneg d) hν).1 hp.le
  · exact (Real.rpow_le_rpow_iff (Nat.cast_nonneg d) (Real.rpow_nonneg hV _) hν).1 hp.ge

end BlockIdentities.Square
