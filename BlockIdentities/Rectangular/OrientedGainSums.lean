/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedGainProducts
public import BlockIdentities.Tensor.NonzeroSum
public import BlockIdentities.Square.TypeCountSchedules
public import Mathlib.Data.Nat.Choose.Sum

/-! Retaining an actual binomial population of letter words, with one common
charged matrix auxiliary for all retained copies. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

theorem AsymptoticallyRestricts.copies {A B : FiniteTensor K}
    (h : AsymptoticallyRestricts A B) (a : ℕ) :
    AsymptoticallyRestricts (copies a A) (copies a B) := by
  apply (h.product (AsymptoticallyRestricts.refl (diagonal a))).congr_classes
  · simp only [tensorClass_product_eq, tensorClass_diagonal_eq, tensorClass_copies_eq, mul_comm]
  · simp only [tensorClass_product_eq, tensorClass_diagonal_eq, tensorClass_copies_eq, mul_comm]

end BlockIdentities.Square
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {F : Type*} [Field F]

/-- One exact binomial term is an actual ordered tensor-semiring restriction.
Its multiplicity counts letter words, not blocks of a fixed source length. -/
theorem binomial_term_le_sum_power {K : Type*} [Field K]
    (a b : TensorClass K) (M l : ℕ) (hl : l ≤ M) :
    (M.choose l : TensorClass K) * a ^ l * b ^ (M - l) ≤ (a + b) ^ M := by
  rw [add_pow]
  have hmem : l ∈ Finset.range (M + 1) := Finset.mem_range.mpr (by omega)
  have hh := Finset.single_le_sum
    (f := fun j => a ^ j * b ^ (M - j) * (M.choose j : TensorClass K))
    (fun _ _ => zero_le _) hmem
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hh

/-- The same global auxiliary D^k P^(N-k) serves every one of the
choose(nN,nk) retained independent letter words. -/
theorem oriented_conversion_binomial (T U : TensorOf F) (n h g : ℕ)
    (D E P Q : MatrixShape)
    (hT : AsymptoticallyRestricts (product (power T.val n) D.tensor) (copies h E.tensor))
    (hU : AsymptoticallyRestricts (product (power U.val n) P.tensor) (copies g Q.tensor))
    (N k : ℕ) (hk : k ≤ N) :
    AsymptoticallyRestricts
      (product (power (T.sum U).val (n * N)) ((D.power k).product (P.power (N - k))).tensor)
      (copies ((n * N).choose (n * k) * h ^ k * g ^ (N - k))
        ((E.power k).product (Q.power (N - k))).tensor) := by
  let A := product (power T.val (n * k)) (D.power k).tensor
  let B := product (power U.val (n * (N - k))) (P.power (N - k)).tensor
  let c := (n * N).choose (n * k)
  have hretain : AsymptoticallyRestricts
      (product (power (T.sum U).val (n * N)) ((D.power k).product (P.power (N - k))).tensor)
      (copies c (product A B)) := by
    apply asymptoticallyRestricts_of_classDegenerates
    apply ClassDegenerates.of_le
    have hterm := binomial_term_le_sum_power (tensorClass T.val) (tensorClass U.val)
      (n * N) (n * k) (Nat.mul_le_mul_left n hk)
    have haux := mul_mono hterm (le_refl
      (tensorClass ((D.power k).tensor (K := AlgebraicClosure F)) *
        tensorClass ((P.power (N - k)).tensor (K := AlgebraicClosure F))))
    have hsub : n * N - n * k = n * (N - k) := (Nat.mul_sub_left_distrib n N k).symm
    change tensorClass (copies c (product A B)) ≤ _
    have hsum : tensorClass (T.sum U).val = tensorClass T.val + tensorClass U.val := rfl
    simpa only [A, B, c, tensorClass_product_eq, tensorClass_copies_eq,
      tensorClass_power_eq, tensorClass_matrixShape_product, hsum, hsub,
      mul_assoc, mul_left_comm, mul_comm] using haux
  have hprod := (oriented_conversion_repeat T n h D E hT k).product
    (oriented_conversion_repeat U n g P Q hU (N - k))
  have hfinal := hretain.trans (hprod.copies c)
  apply hfinal.congr_classes
  · rfl
  · simp only [c, tensorClass_copies_eq, tensorClass_product_eq,
      tensorClass_matrixShape_product, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]

/-- A finite binomial gain from two genuine equal-length extraction witnesses. -/
theorem binomial_mem_orientedGains (S : InteriorSupport F) (T U : TensorOf F)
    (n h g : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) (hg : 1 ≤ g) (D E P Q : MatrixShape)
    (hT : AsymptoticallyRestricts (product (power T.val n) D.tensor) (copies h E.tensor))
    (hU : AsymptoticallyRestricts (product (power U.val n) P.tensor) (copies g Q.tensor))
    (N k : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) :
    ((((n * N).choose (n * k) * h ^ k * g ^ (N - k) : ℕ) : ℝ) *
      matrixWeight S ((E.power k).product (Q.power (N - k))) /
      matrixWeight S ((D.power k).product (P.power (N - k)))) ^ (1 / ((n * N : ℕ) : ℝ)) ∈
        orientedGains S (T.sum U) := by
  refine ⟨n * N, (n * N).choose (n * k) * h ^ k * g ^ (N - k),
    Nat.mul_le_mul hn hN, ?_, (D.power k).product (P.power (N - k)),
    (E.power k).product (Q.power (N - k)),
    oriented_conversion_binomial T U n h g D E P Q hT hU N k hk, rfl⟩
  have hchoose := Nat.choose_pos (Nat.mul_le_mul_left n hk)
  have hp := Nat.mul_pos (Nat.mul_pos hchoose (pow_pos (by omega : 0 < h) k))
    (pow_pos (by omega : 0 < g) (N - k))
  omega

end BlockIdentities.Rectangular
