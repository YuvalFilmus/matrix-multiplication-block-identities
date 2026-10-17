/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Arithmetic.FormalPolynomial
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.NaiveAlgorithm
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.LowerBound

/-! A formally correct cubic algorithm and nonemptiness of the formal exponent set.
The expression compiler is interpreted directly in the polynomial coefficient ring;
no passage from finite-field input equality to polynomial equality is used. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Arithmetic

open OAI.MatrixMultiplication.Arithmetic
open scoped BigOperators

variable {F Input R : Type*} [Field F] [CommRing R]

omit [Field F] in
private theorem evalGateIn_mapRegister {S T : Type*} (φ : F → R)
    (g : Gate F Input S) (f : S → T) (inputs : Input → R) (registers : T → R) :
    evalGateIn φ (g.mapRegister f) inputs registers =
      evalGateIn φ g inputs (fun i => registers (f i)) := by
  cases g <;> rfl

omit [Field F] in
private theorem evalProgramIn_append_new (φ : F → R) {r s : ℕ}
    (p : Program F Input r) (q : Program F Input s) (inputs : Input → R) :
    ∀ i : Fin s, evalProgramIn φ (p.append q) inputs (Program.newIndex r s i) =
      evalProgramIn φ q inputs i := by
  induction q with
  | nil => intro i; exact Fin.elim0 i
  | @step s q g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Program.append, Program.newIndex_zero, evalProgramIn,
        Fin.cases_zero, evalGateIn_mapRegister]
      rw [funext ih]
    · simpa only [Program.append, Program.newIndex_succ, evalProgramIn,
        Fin.cases_succ] using ih j

omit [Field F] in
private theorem evalProgramIn_append_old (φ : F → R) {r s : ℕ}
    (p : Program F Input r) (q : Program F Input s) (inputs : Input → R) :
    ∀ i : Fin r, evalProgramIn φ (p.append q) inputs (Program.oldIndex r s i) =
      evalProgramIn φ p inputs i := by
  induction q with
  | nil => intro i; simp [Program.append]
  | @step s q g ih =>
    intro i
    simpa only [Program.append, Program.oldIndex_succ, evalProgramIn,
      Fin.cases_succ] using ih i

/-- Expression semantics in any commutative coefficient ring. -/
def evalExpressionIn (φ : F → R) (inputs : Input → R) : Expression F Input → R
  | .constant c => φ c
  | .input i => inputs i
  | .add e f => evalExpressionIn φ inputs e + evalExpressionIn φ inputs f
  | .sub e f => evalExpressionIn φ inputs e - evalExpressionIn φ inputs f
  | .mul e f => evalExpressionIn φ inputs e * evalExpressionIn φ inputs f

/-- The upstream compiler preserves ring-valued, hence polynomial, semantics. -/
theorem evalProgramIn_compile (φ : F → R) (inputs : Input → R)
    (e : Expression F Input) :
    evalProgramIn φ (Expression.compile e).program inputs (Expression.compile e).output =
      evalExpressionIn φ inputs e := by
  induction e with
  | constant c => rfl
  | input i => rfl
  | add e f he hf =>
    simpa only [Expression.compile, evalProgramIn, Fin.cases_zero, evalGateIn,
      evalProgramIn_append_old, evalProgramIn_append_new, evalExpressionIn] using
      congrArg₂ (fun x y : R => x + y) he hf
  | sub e f he hf =>
    simpa only [Expression.compile, evalProgramIn, Fin.cases_zero, evalGateIn,
      evalProgramIn_append_old, evalProgramIn_append_new, evalExpressionIn] using
      congrArg₂ (fun x y : R => x - y) he hf
  | mul e f he hf =>
    simpa only [Expression.compile, evalProgramIn, Fin.cases_zero, evalGateIn,
      evalProgramIn_append_old, evalProgramIn_append_new, evalExpressionIn] using
      congrArg₂ (fun x y : R => x * y) he hf

private theorem evalProgramIn_compileFinFamily (φ : F → R) (inputs : Input → R)
    (n : ℕ) (expressions : Fin n → Expression F Input) (i : Fin n) :
    evalProgramIn φ (Expression.compileFinFamily n expressions).program inputs
      ((Expression.compileFinFamily n expressions).output i) =
      evalExpressionIn φ inputs (expressions i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Expression.compileFinFamily, Fin.cases_zero,
        evalProgramIn_append_old] using evalProgramIn_compile φ inputs (expressions 0)
    · simpa only [Expression.compileFinFamily, Fin.cases_succ,
        evalProgramIn_append_new] using ih (fun j => expressions j.succ) j

/-- A finite family compiled upstream retains exact ring-valued semantics. -/
theorem evalProgramIn_compileFamily {Output : Type*} [Fintype Output]
    (φ : F → R) (inputs : Input → R) (expressions : Output → Expression F Input)
    (i : Output) :
    evalProgramIn φ (Expression.compileFamily expressions).program inputs
      ((Expression.compileFamily expressions).output i) =
      evalExpressionIn φ inputs (expressions i) := by
  simpa only [Expression.compileFamily, Equiv.symm_apply_apply] using
    evalProgramIn_compileFinFamily φ inputs (Fintype.card Output)
      (fun j => expressions ((Fintype.equivFin Output).symm j))
      ((Fintype.equivFin Output) i)

private theorem evalExpressionIn_sumFin (φ : F →+* R) (inputs : Input → R)
    {n : ℕ} (f : Fin n → Expression F Input) :
    evalExpressionIn φ inputs (Expression.sumFin f) =
      ∑ i, evalExpressionIn φ inputs (f i) := by
  induction n with
  | zero => simp [Expression.sumFin, evalExpressionIn]
  | succ n ih => simp [Expression.sumFin, evalExpressionIn, ih, Fin.sum_univ_succ]

/-- The naive algorithm computes formal matrix-entry polynomials over every field. -/
theorem naiveAlgorithm_formalCorrect (a b c : ℕ) :
    FormalCorrect (naiveAlgorithm (F := F) a b c) := by
  intro i k
  change evalProgramIn MvPolynomial.C
    (Expression.compileFamily (fun ik : Fin a × Fin c =>
      naiveEntry (F := F) (b := b) ik.1 ik.2)).program MvPolynomial.X
    ((Expression.compileFamily (fun ik : Fin a × Fin c =>
      naiveEntry (F := F) (b := b) ik.1 ik.2)).output (i, k)) = _
  rw [evalProgramIn_compileFamily]
  simp only [naiveEntry, evalExpressionIn_sumFin, evalExpressionIn]

/-- Cubic multiplication is admissible with formal polynomial correctness. -/
theorem formalAdmissibleExponent_three : FormalAdmissibleExponent F 3 := by
  intro ε hε
  refine ⟨2, by norm_num, ?_⟩
  intro n hn
  refine ⟨naiveAlgorithm n n n, naiveAlgorithm_formalCorrect n n n, ?_⟩
  rw [naiveAlgorithm_cost]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) ^ (3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hnR (le_add_of_nonneg_right hε.le)
  calc
    ((2 * n * n * n : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℝ) := by
      calc
        ((2 * n * n * n : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℕ) := by
          push_cast
          ring
        _ = 2 * (n : ℝ) ^ (3 : ℝ) :=
          congrArg (fun t : ℝ => 2 * t) (Real.rpow_natCast (n : ℝ) 3).symm
    _ ≤ 2 * (n : ℝ) ^ (3 + ε) := mul_le_mul_of_nonneg_left hpow (by norm_num)

/-- The formal-admissible set is nonempty without assumptions on the field. -/
theorem formalAdmissibleExponent_nonempty :
    Set.Nonempty {τ : ℝ | FormalAdmissibleExponent F τ} :=
  ⟨3, formalAdmissibleExponent_three⟩

/-- Formal polynomial algorithms are admissible in the original input model. -/
theorem FormalAdmissibleExponent.admissibleExponent {τ : ℝ}
    (hτ : FormalAdmissibleExponent F τ) : AdmissibleExponent F τ := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := hτ ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := h n hn
  exact ⟨P, formalCorrect_implies_correct P hP, hcost⟩

/-- The quadratic operation-count lower bound applies to formal algorithms. -/
theorem formalAdmissibleExponent_two_le {τ : ℝ}
    (hτ : FormalAdmissibleExponent F τ) : 2 ≤ τ :=
  admissibleExponent_two_le hτ.admissibleExponent

/-- Formal admissible exponents have the uniform lower bound two. -/
theorem formalAdmissibleExponent_bddBelow :
    BddBelow {τ : ℝ | FormalAdmissibleExponent F τ} :=
  ⟨2, fun _ h => formalAdmissibleExponent_two_le h⟩

/-- Every admissible formal exponent bounds the formal infimum. -/
theorem formalOmega_le_of_formalAdmissibleExponent {τ : ℝ}
    (hτ : FormalAdmissibleExponent F τ) : formalOmega F ≤ τ :=
  csInf_le formalAdmissibleExponent_bddBelow hτ

/-- The formal-polynomial exponent is at least two, including over finite fields. -/
theorem two_le_formalOmega : 2 ≤ formalOmega F :=
  le_csInf formalAdmissibleExponent_nonempty
    (fun _ hτ => formalAdmissibleExponent_two_le hτ)

/-- The formally correct naive algorithm bounds the exponent by three. -/
theorem formalOmega_le_three : formalOmega F ≤ 3 :=
  formalOmega_le_of_formalAdmissibleExponent formalAdmissibleExponent_three

/-- A domain witness for ordinary value at the actual formal exponent. -/
theorem formalOmega_mem_Icc : formalOmega F ∈ Set.Icc (2 : ℝ) 3 :=
  ⟨two_le_formalOmega, formalOmega_le_three⟩

end BlockIdentities.Arithmetic
