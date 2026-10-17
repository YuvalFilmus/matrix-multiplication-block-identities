/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.PolynomialMaps
public import BlockIdentities.Tensor.Value

/-! Scalar supply and exact-rank restrictions used in finite catalytic cancellation. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open OAI.MatrixMultiplication.Foundation
open scoped BigOperators

variable {K : Type*} [Field K]

/-- A finite rank decomposition is an actual restriction of a diagonal tensor. -/
theorem degenerates_of_rankAtMost {A : FiniteTensor K} {r : ℕ}
    (h : Tensor.RankAtMost A.coeff r) : Degenerates (diagonal r) A := by
  classical
  obtain ⟨a, b, c, h⟩ := h
  apply degenerates_of_restriction (fun x i => a i x) (fun y i => b i y)
    (fun z i => c i z)
  funext x y z
  rw [h]
  change (∑ i : Fin r, a i x * b i y * c i z) =
    ∑ i : Fin r, ∑ j : Fin r, ∑ k : Fin r,
      a i x * b j y * c k z * (if i = j ∧ j = k then 1 else 0)
  simp [mul_ite, ite_and]

/-- Any nonzero tensor supplies one scalar, by selecting a nonzero coefficient. -/
theorem degenerates_to_scalar {A : FiniteTensor K} (hA : Nonzero A) :
    Degenerates A (diagonal 1) := by
  classical
  obtain ⟨x, y, z, h⟩ := (nonzero_iff A).mp hA
  apply degenerates_of_restriction
    (fun _ i => if i = x then (A.coeff x y z)⁻¹ else 0)
    (fun _ j => if j = y then 1 else 0)
    (fun _ k => if k = z then 1 else 0)
  funext i j k
  change Fin 1 at i j k
  have hij : i = j := Subsingleton.elim _ _
  have hjk : j = k := Subsingleton.elim _ _
  simp [Tensor.restrict, diagonal, hij, hjk, mul_ite, ite_mul, h]

/-- The zero target of any dimensions is a restriction with zero local maps. -/
theorem degenerates_of_target_zero {A B : FiniteTensor K} (hB : B.coeff = 0) :
    Degenerates A B := by
  apply degenerates_of_restriction (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
  rw [hB]
  funext x y z
  simp [Tensor.restrict]

/-- Polynomial local maps cannot create a nonzero tensor from a zero source. -/
theorem Degenerates.target_zero_of_source_zero {A B : FiniteTensor K}
    (h : Degenerates A B) (hA : A.coeff = 0) : B.coeff = 0 := by
  obtain ⟨k, Lx, Ly, Lz, ⟨L⟩⟩ := h
  funext x y z
  have hlead := L.leading x y z
  simpa only [Tensor.restrict, hA, Pi.zero_apply, Polynomial.C_0, mul_zero,
    Finset.sum_const_zero, Polynomial.coeff_zero] using hlead.symm

/-- Nonzero outputs of degeneration force the source to be nonzero. -/
theorem Degenerates.source_nonzero {A B : FiniteTensor K}
    (h : Degenerates A B) (hB : Nonzero B) : Nonzero A := by
  intro hA
  exact hB (h.target_zero_of_source_zero hA)

end BlockIdentities.Square
