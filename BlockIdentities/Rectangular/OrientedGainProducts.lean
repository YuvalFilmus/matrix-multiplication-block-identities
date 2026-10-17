/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedGainOperations

/-! Products of actual oriented gain witnesses, after finite repetition to a
common source length. No boundedness or supremum hypothesis is used. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {F : Type*} [Field F]

/-- Tensor two actual conversions of the same source length. -/
theorem oriented_conversion_product (T U : TensorOf F) (n h k : ℕ)
    (D E P Q : MatrixShape)
    (hT : AsymptoticallyRestricts (product (power T.val n) D.tensor) (copies h E.tensor))
    (hU : AsymptoticallyRestricts (product (power U.val n) P.tensor) (copies k Q.tensor)) :
    AsymptoticallyRestricts
      (product (power (T.product U).val n) (D.product P).tensor)
      (copies (h * k) (E.product Q).tensor) := by
  apply (hT.product hU).congr_classes
  · simp only [NonzeroTensor.product, tensorClass_product_eq, tensorClass_power_eq,
      tensorClass_matrixShape_product, mul_pow, mul_assoc, mul_left_comm, mul_comm]
  · simp only [tensorClass_product_eq, tensorClass_copies_eq,
      tensorClass_matrixShape_product, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]

/-- At a common source length the numerical gains multiply exactly. -/
theorem oriented_gain_product_same_length (S : InteriorSupport F)
    (n h k : ℕ) (hh : 1 ≤ h) (hk : 1 ≤ k) (D E P Q : MatrixShape) :
    (((h * k : ℕ) : ℝ) * matrixWeight S (E.product Q) /
      matrixWeight S (D.product P)) ^ (1 / (n : ℝ)) =
      ((h : ℝ) * matrixWeight S E / matrixWeight S D) ^ (1 / (n : ℝ)) *
      ((k : ℝ) * matrixWeight S Q / matrixWeight S P) ^ (1 / (n : ℝ)) := by
  have hx : 0 ≤ (h : ℝ) * matrixWeight S E / matrixWeight S D :=
    (div_pos (mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh))
      (matrixWeight_pos S E)) (matrixWeight_pos S D)).le
  have hy : 0 ≤ (k : ℝ) * matrixWeight S Q / matrixWeight S P :=
    (div_pos (mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk))
      (matrixWeight_pos S Q)) (matrixWeight_pos S P)).le
  have heq : ((h * k : ℕ) : ℝ) * matrixWeight S (E.product Q) /
      matrixWeight S (D.product P) =
      ((h : ℝ) * matrixWeight S E / matrixWeight S D) *
      ((k : ℝ) * matrixWeight S Q / matrixWeight S P) := by
    rw [Nat.cast_mul, matrixWeight_product, matrixWeight_product]
    field_simp [(matrixWeight_pos S D).ne', (matrixWeight_pos S P).ne']
  rw [heq, Real.mul_rpow hx hy]

/-- Arbitrary literal gains are synchronized at n*m and then tensored. -/
theorem mul_mem_orientedGains (S : InteriorSupport F) (T U : TensorOf F)
    {v w : ℝ} (hv : v ∈ orientedGains S T) (hw : w ∈ orientedGains S U) :
    v * w ∈ orientedGains S (T.product U) := by
  obtain ⟨n, h, hn, hh, D, E, hT, hv⟩ := hv
  obtain ⟨m, k, hm, hk, P, Q, hU, hw⟩ := hw
  have hTrep := oriented_conversion_repeat T n h D E hT m
  have hUrep : AsymptoticallyRestricts (product (power U.val (n * m)) (P.power n).tensor)
      (copies (k ^ n) (Q.power n).tensor) := by
    simpa only [Nat.mul_comm m n] using oriented_conversion_repeat U m k P Q hU n
  refine ⟨n * m, h ^ m * k ^ n,
    Nat.mul_le_mul hn hm, ?_, (D.power m).product (P.power n),
    (E.power m).product (Q.power n),
    oriented_conversion_product T U (n * m) (h ^ m) (k ^ n)
      (D.power m) (E.power m) (P.power n) (Q.power n) hTrep hUrep, ?_⟩
  · have hhpow : 1 ≤ h ^ m := by have := pow_pos (by omega : 0 < h) m; omega
    have hkpow : 1 ≤ k ^ n := by have := pow_pos (by omega : 0 < k) n; omega
    exact Nat.mul_le_mul hhpow hkpow
  · have hhpow : 1 ≤ h ^ m := by have := pow_pos (by omega : 0 < h) m; omega
    have hkpow : 1 ≤ k ^ n := by have := pow_pos (by omega : 0 < k) n; omega
    have hnumT := oriented_gain_repeat S n h hn hh D E m hm
    have hnumU : (((k ^ n : ℕ) : ℝ) * matrixWeight S (Q.power n) /
        matrixWeight S (P.power n)) ^ (1 / ((n * m : ℕ) : ℝ)) =
        ((k : ℝ) * matrixWeight S Q / matrixWeight S P) ^ (1 / (m : ℝ)) := by
      simpa only [Nat.mul_comm m n] using oriented_gain_repeat S m k hm hk P Q n hn
    symm
    rw [oriented_gain_product_same_length S (n * m) (h ^ m) (k ^ n) hhpow hkpow,
      hnumT, hnumU, hv, hw]

end BlockIdentities.Rectangular
