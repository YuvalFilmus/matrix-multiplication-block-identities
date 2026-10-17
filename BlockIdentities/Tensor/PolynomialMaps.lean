/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.Definitions

/-! Constant restrictions are exact polynomial degenerations over every field. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open OAI.MatrixMultiplication.Foundation
open scoped BigOperators

variable {K X Y Z X' Y' Z' : Type*} [Field K]
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Regard three scalar local maps as degree-zero polynomial local maps. -/
def constantRestrictionDegeneration (T : Tensor K X Y Z)
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K) :
    Tensor.PolynomialRestrictionDegeneration T (Tensor.restrict A B C T) 0 0 0 0 where
  leftMap := fun x i => Polynomial.C (A x i)
  middleMap := fun y j => Polynomial.C (B y j)
  rightMap := fun z k => Polynomial.C (C z k)
  left_degree := by intro x i; exact Polynomial.degree_C_le
  middle_degree := by intro y j; exact Polynomial.degree_C_le
  right_degree := by intro z k; exact Polynomial.degree_C_le
  vanishes := by intro x y z j hj; exact (Nat.not_lt_zero j hj).elim
  leading := by
    intro x y z
    simp only [Tensor.restrict, ← Polynomial.C_mul, ← map_sum, Polynomial.coeff_C,
      ite_true]

/-- An actual scalar restriction is a polynomial degeneration. -/
theorem degenerates_of_restriction {A B : FiniteTensor K}
    (Lx : Fin B.nx → Fin A.nx → K) (Ly : Fin B.ny → Fin A.ny → K)
    (Lz : Fin B.nz → Fin A.nz → K)
    (h : B.coeff = Tensor.restrict Lx Ly Lz A.coeff) : Degenerates A B := by
  refine ⟨0, 0, 0, 0, ⟨?_⟩⟩
  rw [h]
  exact constantRestrictionDegeneration A.coeff Lx Ly Lz

/-- Identity local maps give reflexivity without a field-size hypothesis. -/
theorem Degenerates.refl (A : FiniteTensor K) : Degenerates A A := by
  apply degenerates_of_restriction
    (fun x i => if i = x then 1 else 0)
    (fun y j => if j = y then 1 else 0)
    (fun z k => if k = z then 1 else 0)
  exact (Tensor.restrict_identity A.coeff).symm

/-- Invertible scalar changes of variables are polynomial degenerations. -/
theorem Isomorphic.degenerates {A B : FiniteTensor K} (h : Isomorphic A B) :
    Degenerates A B := by
  obtain ⟨ex, ey, ez, h⟩ := h
  exact degenerates_of_restriction _ _ _ h

/-- Cyclic permutation of all three local maps preserves degeneration. -/
theorem Degenerates.cyclic {A B : FiniteTensor K} (h : Degenerates A B) :
    Degenerates (permute .yzx A) (permute .yzx B) := by
  obtain ⟨k, Lx, Ly, Lz, ⟨L⟩⟩ := h
  exact ⟨k, Ly, Lz, Lx, ⟨L.cyclic⟩⟩

end BlockIdentities.Square
