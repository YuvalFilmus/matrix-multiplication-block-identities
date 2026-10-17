/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ExtractionRankSupply
public import BlockIdentities.Square.DivisionRateLimits

/-! Fixed-scale extraction witnesses produce matrix-dimension rates. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped Topology
variable {K : Type*} [Field K]

theorem matrixRate_of_fixed_extraction {A : FiniteTensor K} (hA : Nonzero A)
    {k h m : ℕ} (hk : 1 ≤ k) (hh : 1 ≤ h) (hm : 1 ≤ m)
    (hex : Degenerates (power A k) (copies h (square m)))
    (ε : ℝ) (hε : 0 < ε) (r : ℝ) (hr : 1 ≤ r)
    (hmargin : Real.log r <
      (Real.log h / (exactRankExponent K + ε) + Real.log m) / k) :
    MatrixRate A r := by
  obtain ⟨N, hN, hRate, hExtract⟩ := repeated_extraction_matrix_supply hex hh ε hε
  let D : ℕ → ℕ := fun j => N j * m ^ j
  have hD : ∀ j, 1 ≤ D j := fun j => Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := hN j; omega) (pow_ne_zero _ (by omega)))
  have hDrate : Tendsto (fun j : ℕ => Real.log (D j : ℝ) / (j : ℝ)) atTop
      (𝓝 (Real.log h / (exactRankExponent K + ε) + Real.log m)) := by
    have hid : ∀ᶠ j : ℕ in atTop, Real.log (D j : ℝ) / (j : ℝ) =
        Real.log (N j : ℝ) / (j : ℝ) + Real.log (m : ℝ) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
      have hNj : (N j : ℝ) ≠ 0 := by exact_mod_cast (show N j ≠ 0 by have := hN j; omega)
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
      simp only [D, Nat.cast_mul, Nat.cast_pow, Real.log_mul hNj (pow_ne_zero _ hmR),
        Real.log_pow]
      field_simp
    exact (hRate.add_const (Real.log m)).congr' (Filter.EventuallyEq.symm hid)
  have hdim := eventually_natFloor_pow_le_division D hD hDrate k hk r hr hmargin
  rw [matrixRate_iff_classes]
  refine ⟨hr, fun _ => 1, fun _ => Nat.zero_lt_one, by simp, ?_⟩
  filter_upwards [hdim] with n hn
  have htrim := (ClassDegenerates.refl (tensorClass A ^ (k * (n / k)))).mul
    ((nonzero_scalar_recovery hA).pow (n % k))
  have hdecomp : k * (n / k) + n % k = n := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod n k
  simp only [one_pow, mul_one, ← pow_add, hdecomp] at htrim
  have hout := (htrim.trans (hExtract (n / k))).trans
    (ClassDegenerates.of_le (matrixClass_mono hn))
  simpa only [Nat.cast_one, one_mul] using hout

end BlockIdentities.Square
