/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.DiagonalMatrixRate
public import BlockIdentities.Tensor.ValueRateUpperBound
public import BlockIdentities.Tensor.CyclicProductClasses
public import BlockIdentities.Tensor.ValuePowers

/-! Actual polynomial border rank bounds ordinary value. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Every genuine polynomial degeneration from a rank-r diagonal bounds value. -/
theorem valueAtOmega_le_of_borderRankAtMost (A : NonzeroTensor K) (r : ℕ)
    (hr : 1 ≤ r) (hborder : BorderRankAtMost A.val r) : valueAtOmega A ≤ (r : ℝ) := by
  let ν := Arithmetic.formalOmega K
  let ρ : Set.Icc (2 : ℝ) 3 := ⟨ν, Arithmetic.formalOmega_mem_Icc (F := K)⟩
  have hν : 0 < ν := by have h := ρ.property; linarith [h.1]
  have hrreal : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpow : (1 : ℝ) ≤ (r : ℝ) ^ 3 := one_le_pow₀ hrreal
  let R : ℝ := ((r : ℝ) ^ 3) ^ (1 / ν)
  have hR : 1 ≤ R := Real.one_le_rpow hrpow (by positivity)
  have hRpow : R ^ ν = (r : ℝ) ^ 3 := by
    dsimp only [R]
    rw [← Real.rpow_mul (by positivity : 0 ≤ (r : ℝ) ^ 3),
      one_div_mul_cancel (ne_of_gt hν), Real.rpow_one]
  have hd : Degenerates (diagonal (K := K) (r ^ 3)) A.symmetrize.val := by
    apply (classDegenerates_tensorClass_iff _ _).1
    have hc := ((classDegenerates_tensorClass_iff _ _).2 hborder).cyclicProduct
    simpa only [tensorClass_diagonal_eq, cyclicProduct_natCast,
      cyclicProduct_tensorClass, NonzeroTensor.symmetrize] using hc
  have hbound (q : ℝ) (hq : MatrixRate A.symmetrize.val q) : q ≤ R := by
    have hh := (hq.of_degeneration hd).diagonal_rpow_le (Nat.one_le_pow _ _ hr)
    rw [← Providers.formalOmega_eq_exactRankExponent K] at hh
    have hh' : q ^ ν ≤ R ^ ν := by
      rw [hRpow]
      simpa only [Nat.cast_pow] using hh
    exact (Real.rpow_le_rpow_iff (by linarith [hq.1]) (by linarith [hR]) hν).1 hh'
  have hv := valueAtOmega_le_of_matrixRate_bounds A.symmetrize
    (symmetrize_cycleClass_fixed A.val) R hR hbound
  rw [hRpow] at hv
  have hcube : valueAtOmega A ^ 3 ≤ (r : ℝ) ^ 3 := by
    change value ρ A.symmetrize ≤ _ at hv
    rwa [value_symmetrize ρ A] at hv
  exact le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (by positivity : 0 ≤ (r : ℝ)) hcube

/-- The manuscript's normalized value has the corresponding rank power bound. -/
theorem normalizedValueAtOmega_le_of_borderRankAtMost (A : NonzeroTensor K) (r : ℕ)
    (hr : 1 ≤ r) (hborder : BorderRankAtMost A.val r) :
    normalizedValueAtOmega A ≤ (r : ℝ) ^ (3 / Arithmetic.formalOmega K) := by
  have hν := Arithmetic.formalOmega_mem_Icc (F := K)
  apply Real.rpow_le_rpow
    (le_trans zero_le_one (one_le_value A ⟨_, hν⟩))
    (valueAtOmega_le_of_borderRankAtMost A r hr hborder)
  exact div_nonneg (by norm_num) (by linarith [hν.1])
end BlockIdentities.Square
