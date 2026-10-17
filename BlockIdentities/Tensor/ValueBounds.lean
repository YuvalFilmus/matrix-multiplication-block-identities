/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.DegenerationFlattening
public import BlockIdentities.Tensor.ScalarSupply
public import BlockIdentities.Square.ValueGainBound

/-! Finite extraction bounds and positivity for the literal ordinary value. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K : Type*} [Field K]

/-- A square direct sum has an identity minor of size h*m². -/
theorem Degenerates.copies_square_dimension_le {A : FiniteTensor K}
    {h m : ℕ} (hm : 1 ≤ m) (hdeg : Degenerates A (copies h (square m))) :
    h * m ^ 2 ≤ A.nz := by
  classical
  let o : Fin m := ⟨0, by omega⟩
  let E := Fintype.equivFin (Fin m × Fin m)
  let C := Fintype.equivFin (Fin h × Fin (Fintype.card (Fin m × Fin m)))
  let x : (Fin h × (Fin m × Fin m)) → Fin (copies h (square (K := K) m)).nx :=
    fun i => C (i.1, E (i.2.2, o))
  let y : (Fin h × (Fin m × Fin m)) → Fin (copies h (square (K := K) m)).ny :=
    fun i => C (i.1, E (o, i.2.1))
  let z : (Fin h × (Fin m × Fin m)) → Fin (copies h (square (K := K) m)).nz :=
    fun i => C (i.1, E (i.2.1, i.2.2))
  have hi : ∀ i j, (copies h (square (K := K) m)).coeff (x i) (y i) (z j) =
      if i = j then 1 else 0 := by
    intro i j
    change Tensor.directSum (fun _ : Fin h => Tensor.pullback E.symm E.symm E.symm
      (matrixMultiplicationTensor (K := K) m m m))
      (C.symm (C (i.1, E (i.2.2, o))))
      (C.symm (C (i.1, E (o, i.2.1))))
      (C.symm (C (j.1, E j.2))) = if i = j then 1 else 0
    simp only [Equiv.symm_apply_apply, Tensor.directSum, Tensor.pullback,
      matrixMultiplicationTensor]
    split_ifs <;> simp_all [Prod.ext_iff]
  have hd := hdeg.identityMinor_card_le x y z hi
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using hd

theorem nonzero_permute {A : FiniteTensor K} (hA : Nonzero A) (π : LegPermutation) :
    Nonzero (permute π A) := by
  obtain ⟨x, y, z, h⟩ := (nonzero_iff A).1 hA
  apply (nonzero_iff _).2
  cases π with
  | xyz => exact ⟨x, y, z, h⟩
  | xzy => exact ⟨x, z, y, h⟩
  | yxz => exact ⟨y, x, z, h⟩
  | yzx => exact ⟨y, z, x, h⟩
  | zxy => exact ⟨z, x, y, h⟩
  | zyx => exact ⟨z, y, x, h⟩

theorem nonzero_symmetrize {A : FiniteTensor K} (hA : Nonzero A) :
    Nonzero (symmetrize A) :=
  nonzero_product (nonzero_product hA (nonzero_permute hA .yzx)) (nonzero_permute hA .zxy)

/-- A uniform finite bound on every witness in the actual value supremum. -/
theorem value_witness_le (A : NonzeroTensor K) (ρ : Set.Icc (2 : ℝ) 3)
    {n h m : ℕ} (hn : 1 ≤ n) (hh : 1 ≤ h) (hm : 1 ≤ m)
    (hdeg : Degenerates (power (symmetrize A.val) n) (copies h (square m))) :
    ((h : ℝ) * (m : ℝ) ^ (ρ : ℝ)) ^ (1 / (3 * (n : ℝ))) ≤
      (max 1 (symmetrize A.val).nz : ℕ) := by
  have hd := hdeg.copies_square_dimension_le hm
  have hp : (power (symmetrize A.val) n).nz = (symmetrize A.val).nz ^ n := by
    simp only [power, FiniteTensor.ofTensor, Fintype.card_pi_const, Fintype.card_fin]
  rw [hp] at hd
  apply valueGain_le_of_quadratic_dimension_bound n h m (max 1 (symmetrize A.val).nz)
    hn hh hm (le_max_left _ _) ρ ρ.property
  exact hd.trans (Nat.pow_le_pow_left (le_max_right _ _) n)

/-- The witness set is bounded above; no special behavior of an unbounded sSup
is used when working with the real-valued ordinary value. -/
theorem value_witnesses_bddAbove (A : NonzeroTensor K) (ρ : Set.Icc (2 : ℝ) 3) :
    BddAbove {v : ℝ | ∃ n h m : ℕ, 1 ≤ n ∧ 1 ≤ h ∧ 1 ≤ m ∧
      Degenerates (power (symmetrize A.val) n) (copies h (square m)) ∧
      v = ((h : ℝ) * (m : ℝ) ^ (ρ : ℝ)) ^ (1 / (3 * (n : ℝ)))} := by
  refine ⟨(max 1 (symmetrize A.val).nz : ℕ), ?_⟩
  rintro v ⟨n, h, m, hn, hh, hm, hdeg, rfl⟩
  exact value_witness_le A ρ hn hh hm hdeg

/-- Every nonzero tensor has the scalar extraction witness. -/
theorem scalar_value_witness (A : NonzeroTensor K) :
    Degenerates (power (symmetrize A.val) 1) (copies 1 (square 1)) := by
  apply (classDegenerates_tensorClass_iff _ _).1
  have hsquare : tensorClass (square (K := K) 1) = (1 : TensorClass K) := matrixClass_one
  simpa only [tensorClass_power_eq, tensorClass_copies_eq, pow_one, Nat.cast_one,
    hsquare, one_mul] using nonzero_scalar_recovery (nonzero_symmetrize A.property)

/-- The real supremum is nonempty on exactly its approved nonzero carrier. -/
theorem value_witnesses_nonempty (A : NonzeroTensor K) (ρ : Set.Icc (2 : ℝ) 3) :
    {v : ℝ | ∃ n h m : ℕ, 1 ≤ n ∧ 1 ≤ h ∧ 1 ≤ m ∧
      Degenerates (power (symmetrize A.val) n) (copies h (square m)) ∧
      v = ((h : ℝ) * (m : ℝ) ^ (ρ : ℝ)) ^ (1 / (3 * (n : ℝ)))}.Nonempty := by
  refine ⟨1, 1, 1, 1, le_rfl, le_rfl, le_rfl, scalar_value_witness A, ?_⟩
  simp

/-- Ordinary value is at least one, justified by a bounded nonempty supremum. -/
theorem one_le_value [IsAlgClosed K] (A : NonzeroTensor K) (ρ : Set.Icc (2 : ℝ) 3) :
    1 ≤ value ρ A := by
  apply le_csSup (value_witnesses_bddAbove A ρ)
  refine ⟨1, 1, 1, le_rfl, le_rfl, le_rfl, scalar_value_witness A, ?_⟩
  simp

end BlockIdentities.Square
