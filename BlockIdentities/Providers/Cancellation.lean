/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.AsymptoticClasses
public import BlockIdentities.Tensor.ScalarSupply
public import BlockIdentities.Tensor.FiniteCancellation
public import BlockIdentities.Square.SlowScale

/-! Finite catalytic reuse with rounded powers proves asymptotic cancellation. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Providers
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open BlockIdentities.Square

/-- Cancellation for the literal subexponential-copy degeneration preorder.
The argument actually needs only a field, and so includes finite fields. -/
theorem asymptotic_cancellation {K : Type*} [Field K]
    (A B Z : FiniteTensor K) (hZ : Nonzero Z)
    (h : AsymptoticallyRestricts (product A Z) (product B Z)) :
    AsymptoticallyRestricts A B := by
  rw [asymptoticallyRestricts_iff_classes] at h ⊢
  obtain ⟨a, ha, harate, h⟩ := h
  by_cases hBzero : tensorClass B = 0
  · refine ⟨fun _ => 1, fun _ => Nat.zero_lt_one, ?_, ?_⟩
    · simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ))
        Filter.atTop (nhds 0))
    · intro n hn
      have hbpow : tensorClass B ^ n = 0 := by
        rw [hBzero, zero_pow (show n ≠ 0 by omega)]
      rw [hbpow]
      exact ClassDegenerates.of_le (zero_le _)
  have hBnonzero : Nonzero B := by
    intro hz
    exact hBzero ((tensorClass_eq_zero_iff B).2 hz)
  have hBZnonzero : tensorClass B * tensorClass Z ≠ 0 := by
    rw [← tensorClass_product_eq]
    intro hz
    exact nonzero_product hBnonzero hZ ((tensorClass_eq_zero_iff _).1 hz)
  have hAnonzero : tensorClass A ≠ 0 := by
    intro hz
    have h1 := h 1 (by omega)
    simp only [tensorClass_product_eq, pow_one, hz, zero_mul, mul_zero] at h1
    exact hBZnonzero h1.target_zero
  let R := max 1 (exactRank Z.coeff)
  let S := max 1 (exactRank B.coeff)
  have hRpos : 0 < R := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hSpos : 0 < S := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hR : ClassDegenerates (R : TensorClass K) (tensorClass Z) :=
    (ClassDegenerates.of_le (Nat.mono_cast (le_max_right 1 (exactRank Z.coeff)))).trans
      (rank_scalar_supply Z)
  have hS : ClassDegenerates (S : TensorClass K) (tensorClass B) :=
    (ClassDegenerates.of_le (Nat.mono_cast (le_max_right 1 (exactRank B.coeff)))).trans
      (rank_scalar_supply B)
  have hZscalar := nonzero_scalar_recovery hZ
  have hAscalar : ClassDegenerates (tensorClass A) 1 :=
    ClassDegenerates.of_le (one_le_of_ne_zero hAnonzero)
  obtain ⟨c, hc, hcrate, hcost⟩ := exists_slowScale_overhead a ha harate R S hRpos hSpos
  refine ⟨c, hc, hcrate, ?_⟩
  intro n hn
  obtain ⟨k, hk, _hkn, hkncost⟩ := hcost n hn
  have hstep : ClassDegenerates
      ((a k : TensorClass K) * tensorClass A ^ k * tensorClass Z ^ k)
      (tensorClass B ^ k * tensorClass Z ^ k) := by
    simpa only [tensorClass_product_eq, mul_pow, mul_assoc] using h k hk
  have hRsupply : ClassDegenerates ((R ^ k : ℕ) : TensorClass K)
      (tensorClass Z ^ k) := by simpa only [Nat.cast_pow] using hR.pow k
  have hZdiscard : ClassDegenerates (tensorClass Z ^ k) 1 := by
    simpa only [one_pow] using hZscalar.pow k
  have hmain := finite_catalytic_conversion (a k) (R ^ k) hstep hZdiscard hRsupply (n / k)
  have hrest := (hS.pow (n % k)).mul (hAscalar.pow (n % k))
  simp only [one_pow, mul_one] at hrest
  have hcombined := hmain.mul hrest
  have hn_split : k * (n / k) + n % k = n := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod n k
  have hapow : (tensorClass A ^ k) ^ (n / k) * tensorClass A ^ (n % k) =
      tensorClass A ^ n := by rw [← pow_mul, ← pow_add, hn_split]
  have hbpow : (tensorClass B ^ k) ^ (n / k) * tensorClass B ^ (n % k) =
      tensorClass B ^ n := by rw [← pow_mul, ← pow_add, hn_split]
  have hsource :
      (((R ^ k : ℕ) : TensorClass K) * (a k : TensorClass K) ^ (n / k) *
        (tensorClass A ^ k) ^ (n / k)) *
        ((S : TensorClass K) ^ (n % k) * tensorClass A ^ (n % k)) =
      ((R ^ k * a k ^ (n / k) * S ^ (n % k) : ℕ) : TensorClass K) *
        tensorClass A ^ n := by
    calc
      _ = (((R ^ k : ℕ) : TensorClass K) * (a k : TensorClass K) ^ (n / k) *
          (S : TensorClass K) ^ (n % k)) *
          ((tensorClass A ^ k) ^ (n / k) * tensorClass A ^ (n % k)) := by ring
      _ = _ := by rw [hapow]; simp only [Nat.cast_mul, Nat.cast_pow]
  rw [hsource, hbpow] at hcombined
  have hpad : ClassDegenerates ((c n : TensorClass K) * tensorClass A ^ n)
      (((R ^ k * a k ^ (n / k) * S ^ (n % k) : ℕ) : TensorClass K) *
        tensorClass A ^ n) :=
    ClassDegenerates.of_le (mul_mono (Nat.mono_cast hkncost) le_rfl)
  exact hpad.trans hcombined

end BlockIdentities.Providers
