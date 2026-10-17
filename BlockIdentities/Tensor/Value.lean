/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.Definitions
public import BlockIdentities.Arithmetic.FormalBounds

/-! Ordinary value on exactly the manuscript's nonzero-tensor and exponent domains. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators

variable {K : Type*} [Field K]

abbrev NonzeroTensor (K : Type*) [Field K] := {A : FiniteTensor K // Nonzero A}

theorem nonzero_iff (A : FiniteTensor K) :
    Nonzero A ↔ ∃ x y z, A.coeff x y z ≠ 0 := by
  simp only [Nonzero, Function.ne_iff, Pi.zero_apply]

theorem nonzero_ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor K X Y Z} (hT : T ≠ 0) :
    Nonzero (TensorSemiring.FiniteTensor.ofTensor T) := by
  rcases Function.ne_iff.mp hT with ⟨x, hx⟩
  rcases Function.ne_iff.mp hx with ⟨y, hy⟩
  rcases Function.ne_iff.mp hy with ⟨z, hz⟩
  apply (nonzero_iff _).mpr
  refine ⟨Fintype.equivFin X x, Fintype.equivFin Y y, Fintype.equivFin Z z, ?_⟩
  simpa [TensorSemiring.FiniteTensor.ofTensor, Tensor.pullback] using hz

theorem nonzero_product {A B : FiniteTensor K} (hA : Nonzero A) (hB : Nonzero B) :
    Nonzero (product A B) := by
  rcases (nonzero_iff A).mp hA with ⟨x, y, z, h⟩
  rcases (nonzero_iff B).mp hB with ⟨u, v, w, h'⟩
  apply nonzero_ofTensor
  intro hz
  have hval := congrFun (congrFun (congrFun hz (x, u)) (y, v)) (z, w)
  exact (mul_ne_zero h h') hval

theorem nonzero_square {d : ℕ} (hd : 1 ≤ d) : Nonzero (square (K := K) d) := by
  apply nonzero_ofTensor
  let i : Fin d := ⟨0, lt_of_lt_of_le Nat.zero_lt_one hd⟩
  intro hz
  have hval := congrFun (congrFun (congrFun hz (i, i)) (i, i)) (i, i)
  simp [matrixMultiplicationTensor] at hval

theorem nonzero_copies {A : FiniteTensor K} (hA : Nonzero A)
    {b : ℕ} (hb : 1 ≤ b) : Nonzero (copies b A) := by
  rcases (nonzero_iff A).mp hA with ⟨x, y, z, h⟩
  apply nonzero_ofTensor
  let i : Fin b := ⟨0, lt_of_lt_of_le Nat.zero_lt_one hb⟩
  intro hz
  have hval := congrFun (congrFun (congrFun hz (i, x)) (i, y)) (i, z)
  apply h
  simpa [Tensor.directSum] using hval

def NonzeroTensor.product (A B : NonzeroTensor K) : NonzeroTensor K :=
  ⟨BlockIdentities.Square.product A.val B.val, nonzero_product A.property B.property⟩

def nonzeroSquare (d : ℕ) (hd : 1 ≤ d) : NonzeroTensor K :=
  ⟨square d, nonzero_square hd⟩

def NonzeroTensor.copies (A : NonzeroTensor K) (b : ℕ) (hb : 1 ≤ b) : NonzeroTensor K :=
  ⟨BlockIdentities.Square.copies b A.val, nonzero_copies A.property hb⟩

/-- The source formula, restricted to nonzero tensors and 2 ≤ ρ ≤ 3. -/
def value [IsAlgClosed K] (ρ : Set.Icc (2 : ℝ) 3) (A : NonzeroTensor K) : ℝ :=
  sSup {v : ℝ | ∃ n h m : ℕ, 1 ≤ n ∧ 1 ≤ h ∧ 1 ≤ m ∧
    Degenerates (power (symmetrize A.val) n) (copies h (square m)) ∧
    v = ((h : ℝ) * (m : ℝ) ^ (ρ : ℝ)) ^ (1 / (3 * (n : ℝ)))}

/-- Source specialization at the true formal-polynomial exponent. -/
def valueAtOmega [IsAlgClosed K] (A : NonzeroTensor K) : ℝ :=
  value ⟨Arithmetic.formalOmega K, Arithmetic.formalOmega_mem_Icc (F := K)⟩ A

/-- The normalized value x(A) in the shared-leg value inequality. -/
def normalizedValueAtOmega [IsAlgClosed K] (A : NonzeroTensor K) : ℝ :=
  valueAtOmega A ^ (3 / Arithmetic.formalOmega K)

end BlockIdentities.Square
