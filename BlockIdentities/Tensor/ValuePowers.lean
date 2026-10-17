/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.RankOneValue
public import BlockIdentities.Tensor.PowerClasses
public import BlockIdentities.Tensor.ValueSymmetries
public import BlockIdentities.Square.ValuePowerNumerics

/-! Exact power laws from the literal finite ordinary-value witnesses. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

/-- Reinterpret a power-source extraction at its actual total source scale. -/
theorem value_power_extraction_reindex {A : FiniteTensor K} {k n h m : ℕ}
    (he : Degenerates (power (symmetrize (power A k)) n) (copies h (square m))) :
    Degenerates (power (symmetrize A) (k * n)) (copies h (square m)) := by
  apply (classDegenerates_tensorClass_iff _ _).1
  have hc := (classDegenerates_tensorClass_iff _ _).2 he
  simpa only [tensorClass_power_eq, symmetrize_power_class, ← pow_mul] using hc

/-- Repeating a finite extraction supplies the actual powered output dimensions. -/
theorem value_extraction_power_dimensions {A : FiniteTensor K} {n h m : ℕ}
    (he : Degenerates (power (symmetrize A) n) (copies h (square m))) (k : ℕ) :
    Degenerates (power (symmetrize (power A k)) n) (copies (h ^ k) (square (m ^ k))) := by
  apply (classDegenerates_tensorClass_iff _ _).1
  have hc := ((classDegenerates_tensorClass_iff _ _).2 he).pow k
  simpa only [tensorClass_power_eq, symmetrize_power_class, tensorClass_copies_eq,
    tensorClass_square_eq, matrixClass_pow, Nat.cast_pow, mul_pow, ← pow_mul,
    Nat.mul_comm] using hc

/-- Literal ordinary value commutes with positive natural tensor powers. -/
theorem value_power [IsAlgClosed K] (ρ : Set.Icc (2 : ℝ) 3)
    (A : NonzeroTensor K) (k : ℕ) (hk : 1 ≤ k) :
    value ρ (A.power k) = value ρ A ^ k := by
  have hVA : 0 ≤ value ρ A := (one_le_value A ρ).trans' zero_le_one
  have hVP : 0 ≤ value ρ (A.power k) := (one_le_value (A.power k) ρ).trans' zero_le_one
  apply le_antisymm
  · apply csSup_le (value_witnesses_nonempty (A.power k) ρ)
    rintro v ⟨n, h, m, hn, hh, hm, he, rfl⟩
    have hkn : 1 ≤ k * n := by nlinarith
    have hw : ((h : ℝ) * (m : ℝ) ^ (ρ : ℝ)) ^
        (1 / (3 * ((k * n : ℕ) : ℝ))) ≤ value ρ A := by
      apply le_csSup (value_witnesses_bddAbove A ρ)
      exact ⟨k * n, h, m, hkn, hh, hm, value_power_extraction_reindex he, rfl⟩
    rw [matrixValueGain_reindex_power n hn h hh m hm k hk (ρ : ℝ)]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _) hw k
  · let B := value ρ (A.power k) ^ (1 / (k : ℝ))
    have hB : 0 ≤ B := Real.rpow_nonneg hVP _
    have hBpow : B ^ k = value ρ (A.power k) := by
      dsimp only [B]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hVP,
        one_div_mul_cancel (by exact_mod_cast (show k ≠ 0 by omega)), Real.rpow_one]
    have hsup : value ρ A ≤ B := by
      apply csSup_le (value_witnesses_nonempty A ρ)
      rintro v ⟨n, h, m, hn, hh, hm, he, rfl⟩
      have hw : (((h : ℝ) * (m : ℝ) ^ (ρ : ℝ)) ^
          (1 / (3 * (n : ℝ)))) ^ k ≤ value ρ (A.power k) := by
        rw [← matrixValueGain_pow_dimensions n hn h hh m hm k hk (ρ : ℝ)]
        apply le_csSup (value_witnesses_bddAbove (A.power k) ρ)
        refine ⟨n, h ^ k, m ^ k, hn, Nat.one_le_pow _ _ hh,
          Nat.one_le_pow _ _ hm, ?_, rfl⟩
        exact value_extraction_power_dimensions he k
      apply le_of_pow_le_pow_left₀ (by omega : k ≠ 0) hB
      exact hw.trans_eq hBpow.symm
    exact (pow_le_pow_left₀ hVA hsup k).trans_eq hBpow

/-- The empty tensor product is an actual scalar rank-one tensor. -/
theorem value_power_zero [IsAlgClosed K] (ρ : Set.Icc (2 : ℝ) 3)
    (A : NonzeroTensor K) : value ρ (A.power 0) = 1 := by
  apply value_eq_one_of_rankAtMost_one
  have ht : (power A.val 0).coeff =
      Tensor.rankOne (fun _ => (1 : K)) (fun _ => (1 : K)) (fun _ => (1 : K)) := by
    funext x y z
    simp [power, FiniteTensor.ofTensor, Tensor.pullback, Tensor.power, Tensor.rankOne]
  change Tensor.RankAtMost (power A.val 0).coeff 1
  rw [ht]
  exact Tensor.rankOne_rankAtMost _ _ _

/-- Ordinary value commutes with every natural tensor power, including zero. -/
theorem value_power_nat [IsAlgClosed K] (ρ : Set.Icc (2 : ℝ) 3)
    (A : NonzeroTensor K) (k : ℕ) : value ρ (A.power k) = value ρ A ^ k := by
  cases k with
  | zero => simpa only [pow_zero] using value_power_zero ρ A
  | succ k => exact value_power ρ A (k + 1) (by omega)

/-- Any nonzero presentation of the scalar tensor class has value one. -/
theorem value_eq_one_of_tensorClass_eq_one [IsAlgClosed K]
    (ρ : Set.Icc (2 : ℝ) 3) (A : NonzeroTensor K)
    (hA : tensorClass A.val = 1) : value ρ A = 1 := by
  have hc : tensorClass A.val = tensorClass (A.power 0).val := by
    change tensorClass A.val = tensorClass (power A.val 0)
    rw [tensorClass_power_eq, pow_zero, hA]
  exact (value_eq_of_tensorClass_eq ρ A (A.power 0) hc).trans (value_power_zero ρ A)

/-- Symmetrization has the value of three tensor copies. -/
theorem value_symmetrize [IsAlgClosed K] (ρ : Set.Icc (2 : ℝ) 3)
    (A : NonzeroTensor K) : value ρ A.symmetrize = value ρ A ^ 3 := by
  have hc : tensorClass (symmetrize A.symmetrize.val) =
      tensorClass (symmetrize (A.power 3).val) := by
    change tensorClass (symmetrize (symmetrize A.val)) =
      tensorClass (symmetrize (power A.val 3))
    rw [symmetrize_class_eq_cube (symmetrize_cycleClass_fixed A.val),
      symmetrize_power_class]
  exact (value_eq_of_symmetrize_class_eq ρ A.symmetrize (A.power 3) hc).trans
    (value_power ρ A 3 (by omega))

end BlockIdentities.Square
