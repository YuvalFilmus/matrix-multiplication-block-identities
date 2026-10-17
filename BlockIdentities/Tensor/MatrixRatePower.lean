/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.MatrixRate
public import BlockIdentities.Square.DivisionRateLimits

/-! Pass matrix rates from a fixed source block to all source powers. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped Topology
variable {K : Type*} [Field K]

theorem MatrixRate.of_power {A : FiniteTensor K} (hA : Nonzero A)
    {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hRate : MatrixRate (power A k) r)
    (s : ℝ) (hs : 1 ≤ s) (hmargin : Real.log s < Real.log r / k) :
    MatrixRate A s := by
  obtain ⟨hr, b, hb, hbr, hex⟩ := (matrixRate_iff_classes _ _).1 hRate
  have hdim := eventually_natFloor_pow_le_division
    (fun j : ℕ => Nat.floor (r ^ j)) (one_le_natFloor_pow r hr)
    (tendsto_log_natFloor_pow_div r hr) k hk s hs hmargin
  rw [matrixRate_iff_classes]
  refine ⟨hs, fun n => b (n / k), fun n => hb _, ?_, ?_⟩
  · simpa using rate_comp_natDiv (fun j => Real.log (b j : ℝ)) 0 hbr k hk
  · filter_upwards [hdim, (natDiv_tendsto_atTop k hk).eventually hex] with n hn he
    have htrim := (ClassDegenerates.refl (tensorClass A ^ (k * (n / k)))).mul
      ((nonzero_scalar_recovery hA).pow (n % k))
    have hdecomp : k * (n / k) + n % k = n := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod n k
    simp only [one_pow, mul_one, ← pow_add, hdecomp] at htrim
    have hcopy := (ClassDegenerates.refl (b (n / k) : TensorClass K)).mul htrim
    simp only [tensorClass_power_eq, ← pow_mul] at he
    exact (hcopy.trans he).trans (ClassDegenerates.of_le (matrixClass_mono hn))

end BlockIdentities.Square
