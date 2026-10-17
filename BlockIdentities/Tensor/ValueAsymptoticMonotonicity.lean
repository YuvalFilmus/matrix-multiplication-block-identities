/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.MatrixRateValue
public import BlockIdentities.Tensor.RankOneRate
public import BlockIdentities.Tensor.ValueRateUpperBound

/-! Asymptotic restriction monotonicity from actual matrix-rate witnesses. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K] [IsAlgClosed K]

theorem matrixRate_rpow_le_value_of_cyclic (ρ : Set.Icc (2 : ℝ) 3)
    (A : NonzeroTensor K) (hcycle : cycleClass (tensorClass A.val) = tensorClass A.val)
    {r : ℝ} (hr : MatrixRate A.val r) : r ^ (ρ : ℝ) ≤ value ρ A := by
  by_cases hRank : Tensor.RankAtMost A.val.coeff 1
  · rw [hr.eq_one_of_rankAtMost_one hRank, Real.one_rpow]
    exact one_le_value A ρ
  · exact matrixRate_rpow_le_value ρ A hcycle hRank hr

theorem valueAtOmega_le_rpow_iff_matrixRate_bounds
    (A : NonzeroTensor K)
    (hA : cycleClass (tensorClass A.val) = tensorClass A.val)
    (R : ℝ) (hR : 1 ≤ R) :
    valueAtOmega A ≤ R ^ Arithmetic.formalOmega K ↔
      ∀ r : ℝ, MatrixRate A.val r → r ≤ R := by
  constructor
  · intro hv r hr
    have hν : 0 < Arithmetic.formalOmega K := by
      have := Arithmetic.formalOmega_mem_Icc (F := K)
      linarith [this.1]
    have hle := matrixRate_rpow_le_value_of_cyclic
      ⟨Arithmetic.formalOmega K, Arithmetic.formalOmega_mem_Icc (F := K)⟩ A hA hr
    apply (Real.rpow_le_rpow_iff (by linarith [hr.1]) (by linarith) hν).1
    exact hle.trans hv
  · exact valueAtOmega_le_of_matrixRate_bounds A hA R hR

theorem valueAtOmega_mono_of_asymptoticallyRestricts
    (A B : NonzeroTensor K)
    (hA : cycleClass (tensorClass A.val) = tensorClass A.val)
    (hB : cycleClass (tensorClass B.val) = tensorClass B.val)
    (hAB : AsymptoticallyRestricts A.val B.val) : valueAtOmega B ≤ valueAtOmega A := by
  let ν := Arithmetic.formalOmega K
  let ρ : Set.Icc (2 : ℝ) 3 := ⟨ν, Arithmetic.formalOmega_mem_Icc (F := K)⟩
  have hν : 0 < ν := by have := ρ.property; dsimp only [ρ] at this; linarith [this.1]
  have hV : 1 ≤ valueAtOmega A := one_le_value A ρ
  let R := valueAtOmega A ^ (1 / ν)
  have hR : 1 ≤ R := Real.one_le_rpow hV (by positivity)
  have hpow : R ^ ν = valueAtOmega A := by
    dsimp only [R]
    rw [← Real.rpow_mul (by linarith : 0 ≤ valueAtOmega A)]
    rw [one_div_mul_cancel (ne_of_gt hν), Real.rpow_one]
  have hupper : ∀ r : ℝ, MatrixRate B.val r → r ≤ R := by
    intro r hr
    have ha := hr.of_asymptoticallyRestricts hAB
    have hle := matrixRate_rpow_le_value_of_cyclic ρ A hA ha
    change r ^ ν ≤ valueAtOmega A at hle
    have hle' : r ^ ν ≤ R ^ ν := by simpa only [hpow] using hle
    exact (Real.rpow_le_rpow_iff (by linarith [hr.1]) (by linarith) hν).1 hle'
  exact (valueAtOmega_le_of_matrixRate_bounds B hB R hR hupper).trans_eq hpow

end BlockIdentities.Square
