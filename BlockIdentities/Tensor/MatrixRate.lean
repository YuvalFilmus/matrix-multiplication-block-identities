/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.AsymptoticClasses
public import BlockIdentities.Tensor.ScalarSupply
public import BlockIdentities.Tensor.MatrixRestrictions
public import Mathlib.Algebra.Order.Floor.Semiring

/-! The literal matrix-dimension rate witnesses used in the source's q(T).
No supremum or promised characterization is introduced here. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped Topology
variable {K : Type*} [Field K]

/-- At every sufficiently large power, extract the rounded matrix dimension
with a positive source-copy overhead of zero exponential rate. -/
def MatrixRate (A : FiniteTensor K) (r : ℝ) : Prop :=
  1 ≤ r ∧ ∃ b : ℕ → ℕ, (∀ n, 0 < b n) ∧
    Tendsto (fun n : ℕ => Real.log (b n : ℝ) / (n : ℝ)) atTop (𝓝 0) ∧
    ∀ᶠ n : ℕ in atTop,
      Degenerates (copies (b n) (power A n)) (square (Nat.floor (r ^ n)))

theorem matrixRate_iff_classes (A : FiniteTensor K) (r : ℝ) :
    MatrixRate A r ↔ 1 ≤ r ∧ ∃ b : ℕ → ℕ, (∀ n, 0 < b n) ∧
      Tendsto (fun n : ℕ => Real.log (b n : ℝ) / (n : ℝ)) atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, ClassDegenerates
        ((b n : TensorClass K) * tensorClass A ^ n) (matrixClass (Nat.floor (r ^ n))) := by
  unfold MatrixRate
  constructor <;> rintro ⟨hr, b, hb, hbr, h⟩ <;> refine ⟨hr, b, hb, hbr, ?_⟩
  · filter_upwards [h] with n hn
    have hc := (classDegenerates_tensorClass_iff _ _).2 hn
    simpa only [tensorClass_copies_eq, tensorClass_power_eq, tensorClass_square_eq] using hc
  · filter_upwards [h] with n hn
    apply (classDegenerates_tensorClass_iff _ _).1
    simpa only [tensorClass_copies_eq, tensorClass_power_eq, tensorClass_square_eq] using hn

/-- The source scalar rate is attained by every nonzero tensor. -/
theorem matrixRate_one {A : FiniteTensor K} (hA : Nonzero A) : MatrixRate A 1 := by
  rw [matrixRate_iff_classes]
  refine ⟨le_rfl, fun _ => 1, fun _ => Nat.zero_lt_one, ?_, ?_⟩
  · simp
  · apply Eventually.of_forall
    intro n
    simpa only [one_pow, Nat.floor_one, matrixClass_one, Nat.cast_one, one_mul]
      using (nonzero_scalar_recovery hA).pow n

/-- A fixed degeneration preserves all matrix-dimension rate witnesses. -/
theorem MatrixRate.of_degeneration {A B : FiniteTensor K} {r : ℝ}
    (hB : MatrixRate B r) (hAB : Degenerates A B) : MatrixRate A r := by
  rw [matrixRate_iff_classes] at hB ⊢
  obtain ⟨hr, b, hb, hbr, h⟩ := hB
  refine ⟨hr, b, hb, hbr, ?_⟩
  filter_upwards [h] with n hn
  have hp := ((classDegenerates_tensorClass_iff A B).2 hAB).pow n
  exact ((ClassDegenerates.refl (b n : TensorClass K)).mul hp).trans hn

/-- Subexponential source multiplicity composes without any monotonicity
assumption on its schedule. This is a rate theorem, not an ordinary-value claim. -/
theorem MatrixRate.of_asymptoticallyRestricts {A B : FiniteTensor K} {r : ℝ}
    (hB : MatrixRate B r) (hAB : AsymptoticallyRestricts A B) : MatrixRate A r := by
  rw [matrixRate_iff_classes] at hB ⊢
  rw [asymptoticallyRestricts_iff_classes] at hAB
  obtain ⟨hr, b, hb, hbr, hB⟩ := hB
  obtain ⟨a, ha, har, hAB⟩ := hAB
  have hlog : ∀ n : ℕ, Real.log ((b n * a n : ℕ) : ℝ) / (n : ℝ) =
      Real.log (b n : ℝ) / (n : ℝ) + Real.log (a n : ℝ) / (n : ℝ) := by
    intro n
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast ne_of_gt (hb n))
      (by exact_mod_cast ne_of_gt (ha n)), add_div]
  refine ⟨hr, fun n => b n * a n, fun n => Nat.mul_pos (hb n) (ha n), ?_, ?_⟩
  · simpa only [hlog, add_zero] using hbr.add har
  · filter_upwards [hB, eventually_ge_atTop (1 : ℕ)] with n hn hpos
    have hstep := (ClassDegenerates.refl (b n : TensorClass K)).mul (hAB n hpos)
    have hs : (b n : TensorClass K) * ((a n : TensorClass K) * tensorClass A ^ n) =
        ((b n * a n : ℕ) : TensorClass K) * tensorClass A ^ n := by
      simp only [Nat.cast_mul, mul_assoc]
    rw [hs] at hstep
    exact hstep.trans hn

end BlockIdentities.Square
