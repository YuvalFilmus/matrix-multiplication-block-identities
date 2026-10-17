/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ValueAsymptoticMonotonicity
public import BlockIdentities.Tensor.MatrixRateDivision
public import BlockIdentities.Tensor.MatrixRateMatrix

/-! Exact square-matrix scaling from genuine matrix-rate bounds and cancellation. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Supplying a square matrix factor scales ordinary value at the true exponent.
Both inequalities are proved through actual matrix extraction rates. -/
theorem valueAtOmega_product_square (T : NonzeroTensor K)
    (hcycle : cycleClass (tensorClass T.val) = tensorClass T.val)
    (d : ℕ) (hd : 1 ≤ d) :
    valueAtOmega (T.product (nonzeroSquare d hd)) =
      (d : ℝ) ^ Arithmetic.formalOmega K * valueAtOmega T := by
  let ν := Arithmetic.formalOmega K
  let ρ : Set.Icc (2 : ℝ) 3 := ⟨ν, Arithmetic.formalOmega_mem_Icc (F := K)⟩
  have hν : 0 < ν := by
    have h := ρ.property
    change 2 ≤ ν ∧ ν ≤ 3 at h
    linarith [h.1]
  let P := T.product (nonzeroSquare d hd)
  have hPcycle : cycleClass (tensorClass P.val) = tensorClass P.val :=
    product_square_cycleClass_fixed hcycle d
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := lt_of_lt_of_le zero_lt_one hdR
  have hVT : 1 ≤ valueAtOmega T := one_le_value T ρ
  have hVP : 1 ≤ valueAtOmega P := one_le_value P ρ
  let R := valueAtOmega T ^ (1 / ν)
  let S := valueAtOmega P ^ (1 / ν)
  have hR : 1 ≤ R := Real.one_le_rpow hVT (by positivity)
  have hS : 1 ≤ S := Real.one_le_rpow hVP (by positivity)
  have hRpow : R ^ ν = valueAtOmega T := by
    dsimp only [R]
    rw [← Real.rpow_mul (by linarith : 0 ≤ valueAtOmega T),
      one_div_mul_cancel (ne_of_gt hν), Real.rpow_one]
  have hSpow : S ^ ν = valueAtOmega P := by
    dsimp only [S]
    rw [← Real.rpow_mul (by linarith : 0 ≤ valueAtOmega P),
      one_div_mul_cancel (ne_of_gt hν), Real.rpow_one]
  have hTrates : ∀ r : ℝ, MatrixRate T.val r → r ≤ R :=
    (valueAtOmega_le_rpow_iff_matrixRate_bounds T hcycle R hR).1 hRpow.ge
  have hPrates : ∀ s : ℝ, MatrixRate P.val s → s ≤ S :=
    (valueAtOmega_le_rpow_iff_matrixRate_bounds P hPcycle S hS).1 hSpow.ge
  apply le_antisymm
  · have hcap : 1 ≤ (d : ℝ) * R := by nlinarith
    have hupper : ∀ α : ℝ, MatrixRate P.val α → α ≤ (d : ℝ) * R := by
      intro α hα
      have hdiv : α / (d : ℝ) ≤ R := by
        apply le_of_forall_lt_imp_le_of_dense
        intro s hslt
        by_cases hs : 1 ≤ s
        · apply hTrates s
          change MatrixRate (product T.val (square d)) α at hα
          exact hα.divide_matrix_of_lt T.property d hd s hs hslt
        · exact (le_of_not_ge hs).trans hR
      have hmul := (div_le_iff₀ hdpos).1 hdiv
      nlinarith
    have hv := (valueAtOmega_le_rpow_iff_matrixRate_bounds P hPcycle
      ((d : ℝ) * R) hcap).2 hupper
    calc
      valueAtOmega P ≤ ((d : ℝ) * R) ^ ν := hv
      _ = (d : ℝ) ^ ν * valueAtOmega T := by
        rw [Real.mul_rpow hdpos.le (by linarith : 0 ≤ R), hRpow]
  · have hmulrate : ∀ r : ℝ, MatrixRate T.val r → r * (d : ℝ) ≤ S := by
      intro r hr
      apply le_of_forall_lt_imp_le_of_dense
      intro t ht
      by_cases htone : 1 ≤ t
      · apply hPrates t
        exact hr.product_of_lt (matrixRate_square (K := K) d hd) htone ht
      · exact (le_of_not_ge htone).trans hS
    have hdS : (d : ℝ) ≤ S := by
      simpa only [one_mul] using hmulrate 1 (matrixRate_one T.property)
    have hquot : 1 ≤ S / (d : ℝ) := by
      apply (le_div_iff₀ hdpos).2
      simpa only [one_mul] using hdS
    have hupperT : ∀ r : ℝ, MatrixRate T.val r → r ≤ S / (d : ℝ) := by
      intro r hr
      exact (le_div_iff₀ hdpos).2 (hmulrate r hr)
    have hvT := (valueAtOmega_le_rpow_iff_matrixRate_bounds T hcycle
      (S / (d : ℝ)) hquot).2 hupperT
    calc
      (d : ℝ) ^ ν * valueAtOmega T ≤ (d : ℝ) ^ ν * (S / (d : ℝ)) ^ ν :=
        mul_le_mul_of_nonneg_left hvT (Real.rpow_pos_of_pos hdpos ν).le
      _ = ((d : ℝ) * (S / (d : ℝ))) ^ ν :=
        (Real.mul_rpow hdpos.le (div_nonneg (by linarith) hdpos.le)).symm
      _ = S ^ ν := by congr 1; field_simp [ne_of_gt hdpos]
      _ = valueAtOmega P := hSpow

end BlockIdentities.Square
