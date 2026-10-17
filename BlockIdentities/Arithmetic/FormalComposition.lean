/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Arithmetic.FormalBounds
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.RecursiveBlockPrograms

/-! Ring-valued semantics of the existing finite program composition constructors.
All identities hold directly over the target coefficient ring, including a formal
polynomial ring; correctness on finite-field inputs is never used as a converse. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Arithmetic

open OAI.MatrixMultiplication.Arithmetic
open scoped BigOperators

variable {F Input Input' Mid Output R : Type*} [Field F] [CommRing R]

omit [Field F] in
theorem evalGateIn_mapInput (φ : F → R) (f : Input → Input')
    {Register : Type*} (g : Gate F Input Register)
    (inputs : Input' → R) (registers : Register → R) :
    evalGateIn φ (g.mapInput f) inputs registers =
      evalGateIn φ g (inputs ∘ f) registers := by
  cases g <;> rfl

omit [Field F] in
theorem evalGateIn_mapSource (φ : F → R) (f : Input → Input' ⊕ F)
    {Register : Type*} (g : Gate F Input Register)
    (inputs : Input' → R) (registers : Register → R) :
    evalGateIn φ (g.mapSource f) inputs registers =
      evalGateIn φ g (fun i => Sum.elim inputs φ (f i)) registers := by
  cases g with
  | input i => cases h : f i <;> simp [Gate.mapSource, h, evalGateIn]
  | constant => rfl
  | add => rfl
  | sub => rfl
  | mul => rfl

omit [Field F] in
theorem evalProgramIn_mapInput (φ : F → R) (f : Input → Input')
    {r : ℕ} (p : Program F Input r) (inputs : Input' → R) :
    ∀ i : Fin r, evalProgramIn φ (p.mapInput f) inputs i =
      evalProgramIn φ p (inputs ∘ f) i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ih j) i
    simp only [Program.mapInput, evalProgramIn, Fin.cases_zero, evalGateIn_mapInput]
    rw [funext ih]

omit [Field F] in
theorem evalProgramIn_mapSource (φ : F → R) (f : Input → Input' ⊕ F)
    {r : ℕ} (p : Program F Input r) (inputs : Input' → R) :
    ∀ i : Fin r, evalProgramIn φ (p.mapSource f) inputs i =
      evalProgramIn φ p (fun j => Sum.elim inputs φ (f j)) i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ih j) i
    simp only [Program.mapSource, evalProgramIn, Fin.cases_zero, evalGateIn_mapSource]
    rw [funext ih]

omit [Field F] in
private theorem evalGateIn_mapRegister' {S T : Type*} (φ : F → R)
    (g : Gate F Input S) (f : S → T) (inputs : Input → R) (registers : T → R) :
    evalGateIn φ (g.mapRegister f) inputs registers =
      evalGateIn φ g inputs (fun i => registers (f i)) := by
  cases g <;> rfl

omit [Field F] in
theorem evalProgramIn_append_new (φ : F → R) {r s : ℕ}
    (p : Program F Input r) (q : Program F Input s) (inputs : Input → R) :
    ∀ i : Fin s, evalProgramIn φ (p.append q) inputs (Program.newIndex r s i) =
      evalProgramIn φ q inputs i := by
  induction q with
  | nil => intro i; exact Fin.elim0 i
  | @step s q g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Program.append, Program.newIndex_zero, evalProgramIn,
        Fin.cases_zero, evalGateIn_mapRegister']
      rw [funext ih]
    · simpa only [Program.append, Program.newIndex_succ, evalProgramIn,
        Fin.cases_succ] using ih j

omit [Field F] in
theorem evalProgramIn_append_old (φ : F → R) {r s : ℕ}
    (p : Program F Input r) (q : Program F Input s) (inputs : Input → R) :
    ∀ i : Fin r, evalProgramIn φ (p.append q) inputs (Program.oldIndex r s i) =
      evalProgramIn φ p inputs i := by
  induction q with
  | nil => intro i; simp [Program.append]
  | @step s q g ih =>
    intro i
    simpa only [Program.append, Program.oldIndex_succ, evalProgramIn,
      Fin.cases_succ] using ih i

/-- Substitution preserves both the old outputs and every substituted output. -/
theorem evalProgramIn_substitute (φ : F → R) {r s : ℕ}
    (p : Program F Input r) (q : Program F Mid s) (wires : Mid → Fin r)
    (inputs : Input → R) :
    (∀ i, evalProgramIn φ (p.substitute q wires).program inputs
      ((p.substitute q wires).oldOutput i) = evalProgramIn φ p inputs i) ∧
    (∀ i, evalProgramIn φ (p.substitute q wires).program inputs
      ((p.substitute q wires).output i) =
      evalProgramIn φ q (fun j => evalProgramIn φ p inputs (wires j)) i) := by
  induction q with
  | nil => exact ⟨fun _ => rfl, fun i => Fin.elim0 i⟩
  | @step s q g ih =>
    cases g with
    | input j =>
      refine ⟨ih.1, ?_⟩
      intro i
      exact Fin.cases (ih.1 (wires j)) (fun k => ih.2 k) i
    | constant c =>
      refine ⟨fun i => ih.1 i, ?_⟩
      intro i
      exact Fin.cases rfl (fun k => ih.2 k) i
    | add i j =>
      refine ⟨fun k => ih.1 k, ?_⟩
      intro k
      refine Fin.cases ?_ (fun l => ih.2 l) k
      exact congrArg₂ (fun x y : R => x + y) (ih.2 i) (ih.2 j)
    | sub i j =>
      refine ⟨fun k => ih.1 k, ?_⟩
      intro k
      refine Fin.cases ?_ (fun l => ih.2 l) k
      exact congrArg₂ (fun x y : R => x - y) (ih.2 i) (ih.2 j)
    | mul i j =>
      refine ⟨fun k => ih.1 k, ?_⟩
      intro k
      refine Fin.cases ?_ (fun l => ih.2 l) k
      exact congrArg₂ (fun x y : R => x * y) (ih.2 i) (ih.2 j)

/-- Ring-valued interpretation of the existing upstream output-family object. -/
def evalFamilyIn (φ : F → R) (p : RecursiveBlock.Family F Input Output)
    (inputs : Input → R) (o : Output) : R :=
  evalProgramIn φ p.program inputs (p.output o)

 theorem evalFamilyIn_expressions [Fintype Output] (φ : F → R)
    (e : Output → Expression F Input) (inputs : Input → R) (o : Output) :
    evalFamilyIn φ (RecursiveBlock.Family.expressions e) inputs o =
      evalExpressionIn φ inputs (e o) :=
  evalProgramIn_compileFamily φ inputs e o

 theorem evalFamilyIn_compose (φ : F → R)
    (p : RecursiveBlock.Family F Input Mid) (q : RecursiveBlock.Family F Mid Output)
    (inputs : Input → R) (o : Output) :
    evalFamilyIn φ (p.compose q) inputs o =
      evalFamilyIn φ q (evalFamilyIn φ p inputs) o :=
  (evalProgramIn_substitute φ p.program q.program p.output inputs).2 (q.output o)

omit [Field F] in
theorem evalFamilyIn_mapInputs (φ : F → R) (f : Input → Input')
    (p : RecursiveBlock.Family F Input Output) (inputs : Input' → R) (o : Output) :
    evalFamilyIn φ (p.mapInputs f) inputs o =
      evalFamilyIn φ p (inputs ∘ f) o :=
  evalProgramIn_mapInput φ f p.program inputs (p.output o)

omit [Field F] in
theorem evalFamilyIn_parallel (φ : F → R) (r : ℕ)
    (p : Fin r → RecursiveBlock.Family F Input Output) (inputs : Input → R)
    (o : Fin r × Output) :
    evalFamilyIn φ (RecursiveBlock.Family.parallel r p) inputs o =
      evalFamilyIn φ (p o.1) inputs o.2 := by
  induction r with
  | zero => exact Fin.elim0 o.1
  | succ r ih =>
    rcases o with ⟨i, o⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact evalProgramIn_append_old φ _ _ inputs _
    · exact (evalProgramIn_append_new φ _ _ inputs _).trans
        (ih (fun j => p j.succ) (j, o))

 omit [Field F] in
theorem evalFamilyIn_copies (φ : F → R) (r : ℕ)
    (p : RecursiveBlock.Family F Input Output) (inputs : Fin r × Input → R)
    (o : Fin r × Output) :
    evalFamilyIn φ (RecursiveBlock.Family.copies r p) inputs o =
      evalFamilyIn φ p (fun i => inputs (o.1, i)) o.2 := by
  rw [RecursiveBlock.Family.copies, evalFamilyIn_parallel, evalFamilyIn_mapInputs]
  rfl

end BlockIdentities.Arithmetic
