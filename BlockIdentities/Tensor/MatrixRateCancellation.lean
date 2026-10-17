/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.MatrixRate
public import BlockIdentities.Tensor.EventualAsymptoticClasses
public import BlockIdentities.Tensor.Value
public import BlockIdentities.Providers.Cancellation
public import BlockIdentities.Square.AbsorptionRounding

/-! Finite initial powers in rate conversions are supplied by actual rank. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped Topology
variable {K : Type*} [Field K]

private theorem nonzero_power_of_nonzero {A : FiniteTensor K}
    (hA : Nonzero A) (k : ℕ) : Nonzero (power A k) := by
  obtain ⟨x, y, z, h⟩ := (nonzero_iff A).1 hA
  apply nonzero_ofTensor
  intro hz
  have hv := congrFun (congrFun (congrFun hz (fun _ => x)) (fun _ => y)) (fun _ => z)
  have hn : A.coeff x y z ^ k ≠ 0 := pow_ne_zero k h
  apply hn
  simpa only [Tensor.power, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Pi.zero_apply]
    using hv

/-- A strict fixed-scale matrix-rate margin supplies a cancellable catalyst,
with the finitely many initial powers filled by actual finite rank. -/
theorem matrixRate_fixed_scale_cancellation {A : FiniteTensor K}
    (hA : Nonzero A) (d : ℕ) (hd : 1 ≤ d) {α : ℝ}
    (hRate : MatrixRate (product A (square d)) α)
    (k : ℕ) (hk : 1 ≤ k) (b : ℕ) (hb : 1 ≤ b)
    (hmargin : ((d ^ k * b : ℕ) : ℝ) < α ^ k) :
    AsymptoticallyRestricts (power A k) (square b) := by
  classical
  let C := product (power A k) (square (d ^ k))
  let D := product (square (K := K) b) (square (d ^ k))
  have hdk : 1 ≤ d ^ k := Nat.one_le_pow _ _ hd
  have hC : Nonzero C := nonzero_product
    (nonzero_power_of_nonzero hA k) (nonzero_square hdk)
  obtain ⟨hα, a, ha, harate, he⟩ :=
    (matrixRate_iff_classes (product A (square d)) α).1 hRate
  have hsample : Tendsto (fun j : ℕ => Real.log (a (k * j) : ℝ) / (j : ℝ))
      atTop (𝓝 0) := by
    have h := rate_comp_floor_linear (fun n => Real.log (a n : ℝ)) 0 (k : ℝ)
      (by exact_mod_cast (show 0 < k by omega)) harate
    simpa only [zero_mul, ← Nat.cast_mul, Nat.floor_natCast] using h
  have hCD : AsymptoticallyRestricts C D := by
    apply asymptoticallyRestricts_of_eventually_classes hC (fun j => a (k * j))
      (fun j => ha (k * j)) hsample
    obtain ⟨J, hJ⟩ := eventually_atTop.1 he
    filter_upwards [eventually_ge_atTop J] with j hj
    have hkj : J ≤ k * j := by nlinarith
    have hout := hJ (k * j) hkj
    have hdim : (b * d ^ k) ^ j ≤ Nat.floor (α ^ (k * j)) := by
      apply Nat.le_floor
      have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (d ^ k * b : ℕ))
        hmargin.le j
      simpa only [Nat.cast_pow, Nat.cast_mul, ← pow_mul, Nat.mul_comm, mul_comm] using hp
    have htrim := ClassDegenerates.of_le (matrixClass_mono (K := K) hdim)
    have hout' := hout.trans htrim
    simpa only [C, D, tensorClass_product_eq, tensorClass_power_eq,
      tensorClass_square_eq, matrixClass_pow, matrixClass_mul, mul_pow, ← pow_mul,
      Nat.mul_comm, mul_comm] using hout'
  exact BlockIdentities.Providers.asymptotic_cancellation
    (power A k) (square b) (square (d ^ k)) (nonzero_square hdk) hCD

end BlockIdentities.Square
