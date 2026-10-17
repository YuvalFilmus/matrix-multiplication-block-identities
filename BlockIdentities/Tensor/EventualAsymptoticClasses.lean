/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.AsymptoticClasses
public import BlockIdentities.Tensor.ScalarSupply

/-! Finite initial exceptions can be supplied explicitly from a nonzero source. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped Topology
variable {K : Type*} [Field K]

theorem asymptoticallyRestricts_of_eventually_classes {A B : FiniteTensor K}
    (hA : Nonzero A) (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (har : Tendsto (fun n : ℕ => Real.log (a n : ℝ) / (n : ℝ)) atTop (𝓝 0))
    (he : ∀ᶠ n : ℕ in atTop, ClassDegenerates
      ((a n : TensorClass K) * tensorClass A ^ n) (tensorClass B ^ n)) :
    AsymptoticallyRestricts A B := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  let R := max 1 (exactRank B.coeff)
  let b : ℕ → ℕ := fun n => if N ≤ n then a n else R ^ n
  have hR : 0 < R := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  rw [asymptoticallyRestricts_iff_classes]
  refine ⟨b, ?_, ?_, ?_⟩
  · intro n
    dsimp only [b]
    split_ifs <;> first | exact ha n | exact pow_pos hR n
  · apply har.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [b, if_pos hn]
  · intro n hn
    by_cases hlarge : N ≤ n
    · simpa only [b, if_pos hlarge] using hN n hlarge
    · have hs := (nonzero_scalar_recovery hA).pow n
      have hscalar : ClassDegenerates (R : TensorClass K) (tensorClass B) :=
        (ClassDegenerates.of_le (Nat.mono_cast (le_max_right 1 (exactRank B.coeff)))).trans
          (rank_scalar_supply B)
      have hc := (ClassDegenerates.refl ((R : TensorClass K) ^ n)).mul hs
      simp only [one_pow, mul_one] at hc
      have hout := hc.trans (hscalar.pow n)
      simpa only [b, if_neg hlarge, Nat.cast_pow] using hout

end BlockIdentities.Square
