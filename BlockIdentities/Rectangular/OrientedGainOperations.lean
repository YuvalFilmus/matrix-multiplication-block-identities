/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedGainBasics
public import BlockIdentities.Rectangular.MatrixShapeClasses

/-! Actual asymptotic-conversion operations and oriented extraction witnesses,
independent of boundedness of the gain supremum. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped Topology
variable {K : Type*} [Field K]

private theorem log_product_overhead {a b : ℕ → ℕ}
    (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    (hla : Tendsto (fun n : ℕ => Real.log (a n : ℝ) / (n : ℝ)) atTop (𝓝 0))
    (hlb : Tendsto (fun n : ℕ => Real.log (b n : ℝ) / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log ((a n * b n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have heq (n : ℕ) : Real.log ((a n * b n : ℕ) : ℝ) / (n : ℝ) =
      Real.log (a n : ℝ) / (n : ℝ) + Real.log (b n : ℝ) / (n : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul
      (by exact_mod_cast (Nat.ne_zero_of_lt (ha n)))
      (by exact_mod_cast (Nat.ne_zero_of_lt (hb n))), add_div]
  simpa only [heq, zero_add] using hla.add hlb

/-- Full-source overheads multiply under composition. -/
theorem AsymptoticallyRestricts.trans {A B C : FiniteTensor K}
    (hAB : AsymptoticallyRestricts A B) (hBC : AsymptoticallyRestricts B C) :
    AsymptoticallyRestricts A C := by
  rw [asymptoticallyRestricts_iff_classes] at hAB hBC ⊢
  obtain ⟨a, ha, hla, hAB⟩ := hAB
  obtain ⟨b, hb, hlb, hBC⟩ := hBC
  refine ⟨fun n => a n * b n, fun n => Nat.mul_pos (ha n) (hb n),
    log_product_overhead ha hb hla hlb, ?_⟩
  intro n hn
  have hfirst := (ClassDegenerates.refl (b n : TensorClass K)).mul (hAB n hn)
  have hchain := hfirst.trans (hBC n hn)
  simpa only [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hchain

/-- Tensor products multiply the actual full-source overheads. -/
theorem AsymptoticallyRestricts.product {A B C D : FiniteTensor K}
    (hAB : AsymptoticallyRestricts A B) (hCD : AsymptoticallyRestricts C D) :
    AsymptoticallyRestricts (product A C) (product B D) := by
  rw [asymptoticallyRestricts_iff_classes] at hAB hCD ⊢
  obtain ⟨a, ha, hla, hAB⟩ := hAB
  obtain ⟨b, hb, hlb, hCD⟩ := hCD
  refine ⟨fun n => a n * b n, fun n => Nat.mul_pos (ha n) (hb n),
    log_product_overhead ha hb hla hlb, ?_⟩
  intro n hn
  have hprod := (hAB n hn).mul (hCD n hn)
  simpa only [tensorClass_product_eq, mul_pow, Nat.cast_mul,
    mul_assoc, mul_left_comm, mul_comm] using hprod

/-- Fixed tensor powering raises, rather than resamples, the source overhead. -/
theorem AsymptoticallyRestricts.power {A B : FiniteTensor K}
    (hAB : AsymptoticallyRestricts A B) (k : ℕ) :
    AsymptoticallyRestricts (power A k) (power B k) := by
  rw [asymptoticallyRestricts_iff_classes] at hAB ⊢
  obtain ⟨a, ha, hla, hAB⟩ := hAB
  refine ⟨fun n => a n ^ k, fun n => pow_pos (ha n) k, ?_, ?_⟩
  · have heq (n : ℕ) : Real.log ((a n ^ k : ℕ) : ℝ) / (n : ℝ) =
        (k : ℝ) * (Real.log (a n : ℝ) / (n : ℝ)) := by
      rw [Nat.cast_pow, Real.log_pow]
      ring
    simpa only [heq, mul_zero] using hla.const_mul (k : ℝ)
  · intro n hn
    have hp := (hAB n hn).pow k
    simpa only [tensorClass_power_eq, mul_pow, Nat.cast_pow, ← pow_mul,
      Nat.mul_comm n k] using hp

/-- Only finite mutual-restriction identifications are changed. -/
theorem AsymptoticallyRestricts.congr_classes {A B C D : FiniteTensor K}
    (h : AsymptoticallyRestricts A B)
    (hA : tensorClass A = tensorClass C) (hB : tensorClass B = tensorClass D) :
    AsymptoticallyRestricts C D := by
  rw [asymptoticallyRestricts_iff_classes] at h ⊢
  simpa only [hA, hB] using h

end BlockIdentities.Square

namespace BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

theorem AsymptoticallyRestricts.refl (A : FiniteTensor K) : AsymptoticallyRestricts A A :=
  asymptoticallyRestricts_of_classDegenerates (ClassDegenerates.refl _)

end BlockIdentities.Square
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {F : Type*} [Field F]

/-- An actual source conversion transports every literal gain witness. -/
theorem orientedGains_mono_of_asymptoticallyRestricts (S : InteriorSupport F)
    (T U : TensorOf F) (hTU : AsymptoticallyRestricts T.val U.val) :
    orientedGains S U ⊆ orientedGains S T := by
  rintro v ⟨n, h, hn, hh, D, E, hconv, hv⟩
  refine ⟨n, h, hn, hh, D, E, ?_, hv⟩
  exact ((hTU.power n).product (AsymptoticallyRestricts.refl D.tensor)).trans hconv

/-- Repeat a genuine extraction. The positive copy and matrix auxiliary data
are actual products, preserving the physical leg order. -/
theorem oriented_conversion_repeat (T : TensorOf F) (n h : ℕ) (D E : MatrixShape)
    (hconv : AsymptoticallyRestricts (product (power T.val n) D.tensor)
      (copies h E.tensor)) (k : ℕ) :
    AsymptoticallyRestricts (product (power T.val (n * k)) (D.power k).tensor)
      (copies (h ^ k) (E.power k).tensor) := by
  apply (hconv.power k).congr_classes
  · simp only [tensorClass_power_eq, tensorClass_product_eq,
      tensorClass_matrixShape_power, mul_pow, pow_mul]
  · simp only [tensorClass_power_eq, tensorClass_copies_eq,
      tensorClass_matrixShape_power, mul_pow, Nat.cast_pow]

/-- Repetition leaves the normalized positive gain exactly unchanged. -/
theorem oriented_gain_repeat (S : InteriorSupport F) (n h : ℕ)
    (hn : 1 ≤ n) (hh : 1 ≤ h) (D E : MatrixShape) (k : ℕ) (hk : 1 ≤ k) :
    (((h ^ k : ℕ) : ℝ) * matrixWeight S (E.power k) /
      matrixWeight S (D.power k)) ^ (1 / ((n * k : ℕ) : ℝ)) =
      ((h : ℝ) * matrixWeight S E / matrixWeight S D) ^ (1 / (n : ℝ)) := by
  have hbase : 0 ≤ (h : ℝ) * matrixWeight S E / matrixWeight S D :=
    (div_pos (mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh))
      (matrixWeight_pos S E)) (matrixWeight_pos S D)).le
  rw [matrixWeight_power, matrixWeight_power, Nat.cast_pow, ← mul_pow, ← div_pow,
    ← Real.rpow_natCast, ← Real.rpow_mul hbase]
  congr 1
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  rw [Nat.cast_mul]
  field_simp [hnreal, hkreal]

end BlockIdentities.Rectangular
