/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ValueAsymptoticMonotonicity
public import BlockIdentities.Tensor.MatrixRateProduct

/-! Cyclic ordinary value is supermultiplicative through actual matrix rates. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Tensoring actual extraction rates and taking strict dimension margins gives
supermultiplicativity at the true arithmetic exponent. -/
theorem valueAtOmega_supermultiplicative (A B : NonzeroTensor K)
    (hA : cycleClass (tensorClass A.val) = tensorClass A.val)
    (hB : cycleClass (tensorClass B.val) = tensorClass B.val) :
    valueAtOmega A * valueAtOmega B ≤ valueAtOmega (A.product B) := by
  let ν := Arithmetic.formalOmega K
  let ρ : Set.Icc (2 : ℝ) 3 := ⟨ν, Arithmetic.formalOmega_mem_Icc (F := K)⟩
  have hν : 0 < ν := by
    have h := ρ.property
    change 2 ≤ ν ∧ ν ≤ 3 at h
    linarith [h.1]
  let P := A.product B
  have hP : cycleClass (tensorClass P.val) = tensorClass P.val := by
    change cycleClass (tensorClass (product A.val B.val)) =
      tensorClass (product A.val B.val)
    simp only [tensorClass_product_eq, cycleClass_mul, hA, hB]
  have hVB : 1 ≤ valueAtOmega B := one_le_value B ρ
  have hVP : 1 ≤ valueAtOmega P := one_le_value P ρ
  let Q := valueAtOmega B ^ (1 / ν)
  let S := valueAtOmega P ^ (1 / ν)
  have hQ : 1 ≤ Q := Real.one_le_rpow hVB (by positivity)
  have hS : 1 ≤ S := Real.one_le_rpow hVP (by positivity)
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hQpow : Q ^ ν = valueAtOmega B := by
    dsimp only [Q]
    rw [← Real.rpow_mul (by linarith : 0 ≤ valueAtOmega B),
      one_div_mul_cancel (ne_of_gt hν), Real.rpow_one]
  have hSpow : S ^ ν = valueAtOmega P := by
    dsimp only [S]
    rw [← Real.rpow_mul (by linarith : 0 ≤ valueAtOmega P),
      one_div_mul_cancel (ne_of_gt hν), Real.rpow_one]
  have hPrates : ∀ t : ℝ, MatrixRate P.val t → t ≤ S :=
    (valueAtOmega_le_rpow_iff_matrixRate_bounds P hP S hS).1 hSpow.ge
  have hpairs : ∀ r s : ℝ, MatrixRate A.val r → MatrixRate B.val s → r * s ≤ S := by
    intro r s hr hs
    apply le_of_forall_lt_imp_le_of_dense
    intro t ht
    by_cases htone : 1 ≤ t
    · exact hPrates t (hr.product_of_lt hs htone ht)
    · exact (le_of_not_ge htone).trans hS
  have hArates : ∀ r : ℝ, MatrixRate A.val r → r ≤ S / Q := by
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr.1
    have hrS : r ≤ S := by
      simpa only [mul_one] using hpairs r 1 hr (matrixRate_one B.property)
    have hquot : 1 ≤ S / r := by
      apply (le_div_iff₀ hrpos).2
      simpa only [one_mul] using hrS
    have hBrates : ∀ s : ℝ, MatrixRate B.val s → s ≤ S / r := by
      intro s hs
      apply (le_div_iff₀ hrpos).2
      simpa only [mul_comm] using hpairs r s hr hs
    have hvB := (valueAtOmega_le_rpow_iff_matrixRate_bounds B hB (S / r) hquot).2 hBrates
    have hpower : Q ^ ν ≤ (S / r) ^ ν := by rw [hQpow]; exact hvB
    have hbase : Q ≤ S / r :=
      (Real.rpow_le_rpow_iff hQpos.le (by linarith [hquot]) hν).1 hpower
    have hmul := (le_div_iff₀ hrpos).1 hbase
    apply (le_div_iff₀ hQpos).2
    nlinarith
  have hSQ : 1 ≤ S / Q := by
    simpa only [one_mul] using hArates 1 (matrixRate_one A.property)
  have hvA := (valueAtOmega_le_rpow_iff_matrixRate_bounds A hA (S / Q) hSQ).2 hArates
  calc
    valueAtOmega A * valueAtOmega B ≤ (S / Q) ^ ν * valueAtOmega B :=
      mul_le_mul_of_nonneg_right hvA (by linarith)
    _ = (S / Q) ^ ν * Q ^ ν := by rw [hQpow]
    _ = ((S / Q) * Q) ^ ν :=
      (Real.mul_rpow (div_nonneg (by linarith) hQpos.le) hQpos.le).symm
    _ = S ^ ν := by rw [div_mul_cancel₀ S (ne_of_gt hQpos)]
    _ = valueAtOmega P := hSpow

end BlockIdentities.Square
