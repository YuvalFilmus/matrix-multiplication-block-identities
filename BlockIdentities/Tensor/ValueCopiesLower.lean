/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ValueBounds
public import BlockIdentities.Tensor.MatrixSymmetries
public import BlockIdentities.Square.ValuePowerNumerics

/-! Independent copies increase ordinary value by at least their multiplicity. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

theorem symmetrize_copies_class (A : FiniteTensor K) (b : ℕ) :
    tensorClass (symmetrize (copies b A)) =
      (b : TensorClass K) ^ 3 * tensorClass (symmetrize A) := by
  simp only [tensorClass_symmetrize_eq, tensorClass_copies_eq, cycleClass_mul,
    cycleClass_natCast]
  ring

theorem value_extraction_scale_copies {A : FiniteTensor K} {n h m b : ℕ}
    (hex : Degenerates (power (symmetrize A) n) (copies h (square m))) :
    Degenerates (power (symmetrize (copies b A)) n)
      (copies (b ^ (3 * n) * h) (square m)) := by
  have hc := (classDegenerates_tensorClass_iff _ _).2 hex
  simp only [tensorClass_power_eq, tensorClass_copies_eq, tensorClass_square_eq] at hc
  have hs := (ClassDegenerates.refl ((b : TensorClass K) ^ (3 * n))).mul hc
  apply (classDegenerates_tensorClass_iff _ _).1
  simpa only [tensorClass_power_eq, symmetrize_copies_class, mul_pow, ← pow_mul,
    tensorClass_copies_eq, tensorClass_square_eq, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hs

theorem mul_value_le_value_copies [IsAlgClosed K] (ρ : Set.Icc (2 : ℝ) 3)
    (A : NonzeroTensor K) (b : ℕ) (hb : 1 ≤ b) :
    (b : ℝ) * value ρ A ≤ value ρ (A.copies b hb) := by
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hb)
  rw [mul_comm]
  apply (le_div_iff₀ hbpos).1
  apply csSup_le (value_witnesses_nonempty A ρ)
  rintro v ⟨n, h, m, hn, hh, hm, hex, rfl⟩
  apply (le_div_iff₀ hbpos).2
  rw [mul_comm]
  rw [← matrixValueGain_scale_copies n hn h hh m hm b hb (ρ : ℝ)]
  apply le_csSup (value_witnesses_bddAbove (A.copies b hb) ρ)
  refine ⟨n, b ^ (3 * n) * h, m, hn, ?_, hm, ?_, rfl⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (by omega))
  · exact value_extraction_scale_copies hex

end BlockIdentities.Square
