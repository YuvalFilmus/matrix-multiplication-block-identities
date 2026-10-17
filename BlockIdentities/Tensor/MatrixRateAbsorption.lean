/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.MatrixRate
public import BlockIdentities.Square.AbsorptionRounding
public import BlockIdentities.Square.SubexponentialCopies

/-! Remove subexponential copies using an actual finite binary subrank witness. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped Topology
variable {K : Type*} [Field K]

theorem MatrixRate.absorb_copies {A : FiniteTensor K} {r : ℝ}
    (hA : Nonzero A) (p : ℕ)
    (hbinary : ClassDegenerates (tensorClass A ^ p) (2 : TensorClass K))
    (hRate : MatrixRate A r) (θ s : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hs : 1 ≤ s) (hmargin : Real.log s < θ * Real.log r) :
    ∀ᶠ N : ℕ in atTop,
      Degenerates (power A N) (square (Nat.floor (s ^ N))) := by
  obtain ⟨hr, b, hb, hbr, hextract⟩ := (matrixRate_iff_classes A r).1 hRate
  obtain ⟨ℓ, hℓbound, hℓrate⟩ := exists_subexponential_binary_schedule b hb hbr
  have hf := floor_linear_tendsto_atTop θ hθ0
  filter_upwards [hf.eventually hextract,
    eventually_floor_linear_absorption ℓ hℓrate p θ hθ0 hθ1,
    eventually_natFloor_pow_le_reindexed r s θ hr hs hθ0 hmargin] with N he hfill hdim
  let n := Nat.floor (θ * (N : ℝ))
  have hbin : ClassDegenerates (tensorClass A ^ (p * ℓ n))
      ((2 ^ ℓ n : ℕ) : TensorClass K) := by
    simpa only [pow_mul, Nat.cast_pow, Nat.cast_ofNat] using hbinary.pow (ℓ n)
  have hpad : ClassDegenerates ((2 ^ ℓ n : ℕ) : TensorClass K) (b n : TensorClass K) :=
    ClassDegenerates.of_le (Nat.mono_cast (hℓbound n))
  have hsupply := (ClassDegenerates.refl (tensorClass A ^ n)).mul (hbin.trans hpad)
  have hsource : tensorClass A ^ n * tensorClass A ^ (p * ℓ n) =
      tensorClass A ^ (n + p * ℓ n) := (pow_add _ _ _).symm
  have htarget : tensorClass A ^ n * (b n : TensorClass K) =
      (b n : TensorClass K) * tensorClass A ^ n := mul_comm _ _
  rw [hsource, htarget] at hsupply
  have hdiscard := (ClassDegenerates.refl (tensorClass A ^ (n + p * ℓ n))).mul
    ((nonzero_scalar_recovery hA).pow (N - (n + p * ℓ n)))
  have hsum : n + p * ℓ n + (N - (n + p * ℓ n)) = N := Nat.add_sub_of_le hfill
  simp only [one_pow, mul_one, ← pow_add, hsum] at hdiscard
  have hout := ((hdiscard.trans hsupply).trans he).trans
    (ClassDegenerates.of_le (matrixClass_mono hdim))
  apply (classDegenerates_tensorClass_iff _ _).1
  simpa only [tensorClass_power_eq, tensorClass_square_eq] using hout

end BlockIdentities.Square
