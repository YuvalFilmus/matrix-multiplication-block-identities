/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Arithmetic.FormalRecursive
public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Padding

/-! Zero padding preserves polynomial correctness without changing program costs. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Arithmetic

open OAI.MatrixMultiplication.Arithmetic
open scoped BigOperators

variable {F : Type*} [Field F]

/-- Zero-padding the original input syntax preserves exact output polynomials. -/
theorem FormalCorrect.pad {a b c A B C : ℕ}
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    {P : MatrixAlgorithm F A B C} (hP : FormalCorrect P) :
    FormalCorrect (P.pad ha hb hc) := by
  intro i k
  change BlockIdentities.Arithmetic.evalProgramIn MvPolynomial.C
    (P.program.mapSource (padSource (a := a) (b := b) (c := c))) MvPolynomial.X
    (P.output (Fin.castLE ha i) (Fin.castLE hc k)) = _
  rw [evalProgramIn_mapSource]
  rw [hP.evalProgramIn MvPolynomial.C]
  let padInput : MatrixInput A B C → MatrixInput a b c ⊕ F := padSource
  let f : Fin B → MvPolynomial (MatrixInput a b c) F := fun j =>
    Sum.elim MvPolynomial.X MvPolynomial.C
      (padInput (.inl (Fin.castLE ha i, j))) *
    Sum.elim MvPolynomial.X MvPolynomial.C
      (padInput (.inr (j, Fin.castLE hc k)))
  change (∑ j : Fin B, f j) = _
  have hsum : (∑ j : Fin B, f j) = ∑ j : Fin b, f (Fin.castLE hb j) := by
    symm
    refine Fintype.sum_of_injective (Fin.castLE hb) ?_
      (fun j : Fin b => f (Fin.castLE hb j)) f ?_ (fun _ => rfl)
    · intro j l hjl
      exact Fin.ext (congrArg (fun x : Fin B => x.val) hjl)
    · intro j hj
      have hlarge : b ≤ j.val :=
        le_of_not_gt fun hsmall => hj ⟨⟨j.val, hsmall⟩, Fin.ext rfl⟩
      simp [f, padInput, padSource, not_lt_of_ge hlarge]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp [f, padInput, padSource, i.is_lt, j.is_lt, k.is_lt]

end BlockIdentities.Arithmetic
