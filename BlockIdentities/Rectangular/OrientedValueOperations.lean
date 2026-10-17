/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedGainProducts
public import BlockIdentities.Rectangular.OrientedGainMatrix
public import BlockIdentities.Rectangular.OrientedGainRankLimit
public import BlockIdentities.Tensor.ScalarRank

/-! Supremum consumers of actual oriented extraction witnesses. All boundedness
used below is proved from the actual gain rank theorem. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {F : Type*} [Field F]

/-- Actual source conversion gives inclusion of the literal gain sets. -/
theorem orientedValue_mono (S : InteriorSupport F) (T U : TensorOf F)
    (hTU : AsymptoticallyRestricts T.val U.val) : orientedValue S U ≤ orientedValue S T := by
  apply csSup_le (orientedGains_nonempty S U)
  intro v hv
  exact le_csSup (orientedGains_bddAbove S T)
    (orientedGains_mono_of_asymptoticallyRestricts S T U hTU hv)

theorem orientedValue_eq_of_tensorClass_eq (S : InteriorSupport F) (T U : TensorOf F)
    (h : tensorClass T.val = tensorClass U.val) : orientedValue S T = orientedValue S U := by
  apply le_antisymm
  · exact orientedValue_mono S U T
      ((AsymptoticallyRestricts.refl U.val).congr_classes rfl h.symm)
  · exact orientedValue_mono S T U
      ((AsymptoticallyRestricts.refl T.val).congr_classes rfl h)

/-- Common-length finite extraction products give supermultiplicativity. -/
theorem orientedValue_product_le (S : InteriorSupport F) (T U : TensorOf F) :
    orientedValue S T * orientedValue S U ≤ orientedValue S (T.product U) := by
  have hUpos : 0 < orientedValue S U := lt_of_lt_of_le zero_lt_one (one_le_orientedValue S U)
  have hfixed {v : ℝ} (hv : v ∈ orientedGains S T) :
      v * orientedValue S U ≤ orientedValue S (T.product U) := by
    have hvpos := orientedGain_pos S T hv
    have hs : orientedValue S U ≤ orientedValue S (T.product U) / v := by
      apply csSup_le (orientedGains_nonempty S U)
      intro w hw
      apply (le_div_iff₀ hvpos).mpr
      change w * v ≤ sSup (orientedGains S (T.product U))
      rw [mul_comm w v]
      exact le_csSup (orientedGains_bddAbove S (T.product U))
        (mul_mem_orientedGains S T U hv hw)
    simpa only [mul_comm] using (le_div_iff₀ hvpos).mp hs
  apply (le_div_iff₀ hUpos).mp
  apply csSup_le (orientedGains_nonempty S T)
  intro v hv
  exact (le_div_iff₀ hUpos).mpr (hfixed hv)

/-- Charged matrix auxiliaries give both scaling inequalities on actual gains. -/
theorem orientedValue_product_matrix (S : InteriorSupport F) (T : TensorOf F)
    (M : MatrixShape) : orientedValue S (T.product M.nonzeroTensor) =
      matrixWeight S M * orientedValue S T := by
  have hw := matrixWeight_pos S M
  apply le_antisymm
  · apply csSup_le (orientedGains_nonempty S (T.product M.nonzeroTensor))
    intro v hv
    have hh := le_csSup (orientedGains_bddAbove S T)
      (div_matrixWeight_mem_orientedGains S T M hv)
    rw [mul_comm (matrixWeight S M)]
    change v ≤ sSup (orientedGains S T) * matrixWeight S M
    exact (div_le_iff₀ hw).mp hh
  · have hs : orientedValue S T ≤ orientedValue S (T.product M.nonzeroTensor) / matrixWeight S M := by
      apply csSup_le (orientedGains_nonempty S T)
      intro v hv
      apply (le_div_iff₀ hw).mpr
      change v * matrixWeight S M ≤ sSup (orientedGains S (T.product M.nonzeroTensor))
      rw [mul_comm v (matrixWeight S M)]
      exact le_csSup (orientedGains_bddAbove S (T.product M.nonzeroTensor))
        (matrixWeight_mul_mem_orientedGains S T M hv)
    simpa only [mul_comm] using (le_div_iff₀ hw).mp hs

/-- The scalar has value exactly one by its actual exact rank upper bound. -/
theorem orientedValue_scalar (S : InteriorSupport F) :
    orientedValue S (scalarShape.nonzeroTensor (K := AlgebraicClosure F)) = 1 := by
  apply le_antisymm
  · have h := (orientedValue_le_tensorAsymptoticRank S
      (scalarShape.nonzeroTensor (K := AlgebraicClosure F))).trans
      (tensorAsymptoticRank_le_exactRank (scalarShape.nonzeroTensor (K := AlgebraicClosure F)))
    have hr : OAI.MatrixMultiplication.AuxiliarySeparation.exactRank
        (scalarShape.tensor (K := AlgebraicClosure F)).coeff ≤ 1 := by
      change rank (tensorClass (scalarShape.tensor (K := AlgebraicClosure F))) ≤ 1
      rw [tensorClass_matrixShape_scalar]
      simpa only [Nat.cast_one] using rank_natCast_le (K := AlgebraicClosure F) 1
    exact h.trans (by exact_mod_cast hr)
  · exact one_le_orientedValue S _

/-- A positive matrix tensor has exactly its prescribed oriented weight. -/
theorem orientedValue_matrix (S : InteriorSupport F) (M : MatrixShape) :
    orientedValue S (M.nonzeroTensor (K := AlgebraicClosure F)) = matrixWeight S M := by
  have hclass : tensorClass
      ((scalarShape.nonzeroTensor (K := AlgebraicClosure F)).product M.nonzeroTensor).val =
      tensorClass (M.nonzeroTensor (K := AlgebraicClosure F)).val := by
    simp only [NonzeroTensor.product, MatrixShape.nonzeroTensor, tensorClass_product_eq,
      tensorClass_matrixShape_scalar, one_mul]
  have hv := orientedValue_eq_of_tensorClass_eq S _ _ hclass
  rw [orientedValue_product_matrix, orientedValue_scalar, mul_one] at hv
  exact hv.symm

/-- Actual zeroth powers are the scalar class. -/
theorem orientedValue_power_zero (S : InteriorSupport F) (T : TensorOf F) :
    orientedValue S (T.power 0) = 1 := by
  have hclass : tensorClass (T.power 0).val =
      tensorClass (scalarShape.nonzeroTensor (K := AlgebraicClosure F)).val := by
    simp only [NonzeroTensor.power, MatrixShape.nonzeroTensor,
      tensorClass_power_eq, pow_zero, tensorClass_matrixShape_scalar]
  exact (orientedValue_eq_of_tensorClass_eq S _ _ hclass).trans (orientedValue_scalar S)

/-- Iterated genuine tensor products give the lower power inequality. -/
theorem orientedValue_pow_le (S : InteriorSupport F) (T : TensorOf F) (k : ℕ) :
    orientedValue S T ^ k ≤ orientedValue S (T.power k) := by
  induction k with
  | zero => simp only [pow_zero, orientedValue_power_zero, le_refl]
  | succ k ih =>
    have hclass : tensorClass ((T.power k).product T).val = tensorClass (T.power (k + 1)).val := by
      simp only [NonzeroTensor.product, NonzeroTensor.power, tensorClass_product_eq,
        tensorClass_power_eq, pow_succ]
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right ih
      (zero_le_one.trans (one_le_orientedValue S T))).trans
      ((orientedValue_product_le S (T.power k) T).trans_eq
        (orientedValue_eq_of_tensorClass_eq S _ _ hclass))

/-- Every extraction from a positive power is an extraction at source length k*n.
Testing its genuine normalized gain gives the upper power inequality. -/
theorem orientedValue_power_le (S : InteriorSupport F) (T : TensorOf F) (k : ℕ) :
    orientedValue S (T.power k) ≤ orientedValue S T ^ k := by
  by_cases hk : k = 0
  · subst k
    simp only [orientedValue_power_zero, pow_zero, le_refl]
  apply csSup_le (orientedGains_nonempty S (T.power k))
  rintro v ⟨n, h, hn, hh, D, E, hconv, hv⟩
  have hconv' : AsymptoticallyRestricts (product (power T.val (k * n)) D.tensor)
      (copies h E.tensor) := by
    apply hconv.congr_classes
    · simp only [NonzeroTensor.power, tensorClass_product_eq, tensorClass_power_eq, pow_mul]
    · rfl
  have hkn : 1 ≤ k * n := by
    have hkp : 0 < k := Nat.pos_of_ne_zero hk
    have hnp : 0 < n := by omega
    have := Nat.mul_pos hkp hnp
    omega
  have hg : ((h : ℝ) * matrixWeight S E / matrixWeight S D) ^ (1 / ((k * n : ℕ) : ℝ)) ∈
      orientedGains S T := ⟨k * n, h, hkn, hh, D, E, hconv', rfl⟩
  have hgle := le_csSup (orientedGains_bddAbove S T) hg
  have hpow := pow_le_pow_left₀ (orientedGain_pos S T hg).le hgle k
  have hbase : 0 ≤ (h : ℝ) * matrixWeight S E / matrixWeight S D :=
    (div_pos (mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh))
      (matrixWeight_pos S E)) (matrixWeight_pos S D)).le
  have heq :
      (((h : ℝ) * matrixWeight S E / matrixWeight S D) ^ (1 / ((k * n : ℕ) : ℝ))) ^ k = v := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hbase]
    congr 1
    have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [Nat.cast_mul]
    field_simp [hkreal, hnreal]
  rw [heq] at hpow
  exact hpow

theorem orientedValue_power (S : InteriorSupport F) (T : TensorOf F) (k : ℕ) :
    orientedValue S (T.power k) = orientedValue S T ^ k :=
  le_antisymm (orientedValue_power_le S T k) (orientedValue_pow_le S T k)

end BlockIdentities.Rectangular
