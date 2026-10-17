/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import OAI.LinearAlgebra.MatrixMultiplication.Model
public import Mathlib.Algebra.MvPolynomial.Eval

/-! Polynomial semantics for the unchanged upstream division-free circuits. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Arithmetic

open OAI.MatrixMultiplication.Arithmetic
open scoped BigOperators

variable {F Input Register : Type*}

/-- Interpret a gate in a commutative ring using the supplied coefficient map. -/
def evalGateIn {R : Type*} [CommRing R] (φ : F → R)
    (g : Gate F Input Register) (inputs : Input → R) (registers : Register → R) : R :=
  match g with
  | .constant c => φ c
  | .input i => inputs i
  | .add i j => registers i + registers j
  | .sub i j => registers i - registers j
  | .mul i j => registers i * registers j

/-- Interpret a program without requiring the target ring to be a field. -/
def evalProgramIn {R : Type*} [CommRing R] (φ : F → R) :
    {r : ℕ} → Program F Input r → (Input → R) → Fin r → R
  | 0, .nil, _ => Fin.elim0
  | _ + 1, .step p g, inputs =>
      Fin.cases (evalGateIn φ g inputs (evalProgramIn φ p inputs))
        (evalProgramIn φ p inputs)

/-- Interpretation commutes with a homomorphism of the target rings. -/
theorem map_evalProgramIn {R S : Type*} [CommRing R] [CommRing S]
    (φ : F → R) (ψ : R →+* S) {r : ℕ} (p : Program F Input r)
    (inputs : Input → R) (i : Fin r) :
    ψ (evalProgramIn φ p inputs i) =
      evalProgramIn (fun c => ψ (φ c)) p (fun j => ψ (inputs j)) i := by
  induction p with
  | nil => exact Fin.elim0 i
  | @step r p g ih =>
    refine Fin.cases ?_ (fun j => ih j) i
    cases g <;> simp [evalProgramIn, evalGateIn, ih]

/-- Interpreting in the original field agrees with the upstream evaluator. -/
theorem evalProgramIn_id [Field F] {r : ℕ} (p : Program F Input r)
    (inputs : Input → F) (i : Fin r) :
    evalProgramIn id p inputs i = p.eval inputs i := by
  induction p with
  | nil => exact Fin.elim0 i
  | @step r p g ih =>
    refine Fin.cases ?_ (fun j => ih j) i
    cases g <;> simp [evalProgramIn, evalGateIn, Program.eval, Gate.eval, ih]

/-- The formal output polynomials of a program; all inputs are indeterminates. -/
def polynomialOutputs [CommRing F] {r : ℕ} (p : Program F Input r) :
    Fin r → MvPolynomial Input F :=
  evalProgramIn MvPolynomial.C p MvPolynomial.X

/-- Evaluating the formal outputs recovers the upstream field evaluation. -/
theorem eval_polynomialOutputs [Field F] {r : ℕ} (p : Program F Input r)
    (inputs : Input → F) (i : Fin r) :
    MvPolynomial.eval inputs (polynomialOutputs p i) = p.eval inputs i := by
  induction p with
  | nil => exact Fin.elim0 i
  | @step r p g ih =>
    simp only [polynomialOutputs] at ih
    refine Fin.cases ?_ (fun j => ih j) i
    cases g <;> simp [polynomialOutputs, evalProgramIn, evalGateIn,
      Program.eval, Gate.eval, ih]

/-- Correctness is coefficientwise equality in the polynomial ring, over every field. -/
def FormalCorrect [Field F] {a b c : ℕ} (P : MatrixAlgorithm F a b c) : Prop :=
  ∀ (i : Fin a) (k : Fin c),
    polynomialOutputs P.program (P.output i k) =
      ∑ j : Fin b,
        MvPolynomial.X (Sum.inl (i, j)) * MvPolynomial.X (Sum.inr (j, k))

/-- Polynomial correctness specializes to correctness on field-valued inputs. -/
theorem formalCorrect_implies_correct [Field F] {a b c : ℕ}
    (P : MatrixAlgorithm F a b c) (hP : FormalCorrect P) : P.Correct := by
  intro A B
  funext i k
  have h := congrArg (MvPolynomial.eval (matrixInputs A B)) (hP i k)
  rw [eval_polynomialOutputs] at h
  simpa only [map_sum, map_mul, MvPolynomial.eval_X, matrixInputs,
    MatrixAlgorithm.eval, Matrix.mul_apply] using h

/-- Positive slack and a size-uniform cost constant, with formal correctness. -/
def FormalAdmissibleExponent (F : Type*) [Field F] (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n n n,
      FormalCorrect P ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

/-- The manuscript's formal-polynomial exponent, distinct from upstream omega. -/
noncomputable def formalOmega (F : Type*) [Field F] : ℝ :=
  sInf {τ : ℝ | FormalAdmissibleExponent F τ}

end BlockIdentities.Arithmetic
