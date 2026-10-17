/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Definitions

/-! Elementary arithmetic facts for the formal rectangular exponent.
These use the original programs and costs, including over finite fields.
They provide the endpoint and boundedness infrastructure needed by several
rectangular proof targets; they consume no unproved rectangular anchor. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Arithmetic
open scoped NNReal
variable {F : Type*} [Field F]

theorem FormalRectangularAdmissibleExponent.admissible {k τ : ℝ}
    (hτ : FormalRectangularAdmissibleExponent F k τ) : RectangularAdmissibleExponent F k τ := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := hτ ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hp⟩ := h n hn
  exact ⟨P, formalCorrect_implies_correct P hP, hp⟩

theorem formalRectangularAdmissibleExponent_naive (k : ℝ) :
    FormalRectangularAdmissibleExponent F k (2 + max k 0) := by
  intro ε hε
  refine ⟨4, by norm_num, ?_⟩
  intro n hn
  refine ⟨naiveAlgorithm n (innerSize n k) n, naiveAlgorithm_formalCorrect _ _ _, ?_⟩
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hinner : (innerSize n k : ℝ) ≤ 2 * (n : ℝ) ^ max k 0 :=
    (Nat.cast_le.mpr (innerSize_mono hn (le_max_left k 0))).trans
      (innerSize_cast_le hn (le_max_right k 0))
  rw [naiveAlgorithm_cost]
  push_cast
  calc
    2 * (n : ℝ) * innerSize n k * n = 2 * (n : ℝ) ^ 2 * innerSize n k := by ring
    _ ≤ 2 * (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ max k 0) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 4 * (n : ℝ) ^ (2 + max k 0) := by
      rw [Real.rpow_add hnpos]
      norm_num
      ring
    _ ≤ 4 * (n : ℝ) ^ (2 + max k 0 + ε) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)) (by norm_num)

theorem formalRectangularAdmissibleExponent_nonempty (k : ℝ) :
    Set.Nonempty {τ : ℝ | FormalRectangularAdmissibleExponent F k τ} :=
  ⟨2 + max k 0, formalRectangularAdmissibleExponent_naive k⟩

theorem formalRectangularAdmissibleExponent_two_le {k τ : ℝ}
    (hτ : FormalRectangularAdmissibleExponent F k τ) : 2 ≤ τ :=
  rectangularAdmissibleExponent_two_le hτ.admissible

theorem formalRectangularAdmissibleExponent_bddBelow (k : ℝ) :
    BddBelow {τ : ℝ | FormalRectangularAdmissibleExponent F k τ} :=
  ⟨2, fun _ hτ => formalRectangularAdmissibleExponent_two_le hτ⟩

theorem formalRectangularOmega_two_le (k : ℝ) : 2 ≤ formalRectangularOmega F k :=
  le_csInf (formalRectangularAdmissibleExponent_nonempty k)
    (fun _ hτ => formalRectangularAdmissibleExponent_two_le hτ)

theorem formalRectangularOmega_le_naive (k : ℝ) :
    formalRectangularOmega F k ≤ 2 + max k 0 :=
  csInf_le (formalRectangularAdmissibleExponent_bddBelow k)
    (formalRectangularAdmissibleExponent_naive k)

theorem formalRectangularOmega_zero : formalRectangularOmega F 0 = 2 := by
  apply le_antisymm _ (formalRectangularOmega_two_le 0)
  simpa using (formalRectangularOmega_le_naive (F := F) 0)

theorem formalShapeAdmissibleExponent_iff_rectangular {k : ℝ≥0} {τ : ℝ} :
    FormalShapeAdmissibleExponent F 1 k 1 τ ↔ FormalRectangularAdmissibleExponent F k τ := by
  have hd (n : ℕ) : innerSize n ((1 : ℝ≥0) : ℝ) = n := by
    rw [NNReal.coe_one]
    exact innerSize_one n
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    exact (congrArg (fun d : ℕ =>
      ∃ P : MatrixAlgorithm F d (innerSize n (k : ℝ)) d,
        FormalCorrect P ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)) (hd n)).mp (hbound n hn)
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    exact (congrArg (fun d : ℕ =>
      ∃ P : MatrixAlgorithm F d (innerSize n (k : ℝ)) d,
        FormalCorrect P ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)) (hd n)).mpr (hbound n hn)

theorem rectangularOmega_le_formalRectangularOmega (k : ℝ) :
    rectangularOmega F k ≤ formalRectangularOmega F k :=
  le_csInf (formalRectangularAdmissibleExponent_nonempty k)
    (fun _ hτ => rectangularOmega_le_of_admissibleExponent hτ.admissible)

theorem formalAlpha_nonneg : 0 ≤ formalAlpha F := by
  apply le_csSup (show BddAbove {k : ℝ | k ∈ Set.Icc 0 1 ∧ formalRectangularOmega F k = 2}
    from ⟨1, fun _ hk => hk.1.2⟩)
  exact ⟨⟨le_rfl, zero_le_one⟩, formalRectangularOmega_zero⟩

theorem formalAlpha_le_one : formalAlpha F ≤ 1 := by
  apply csSup_le (show Set.Nonempty {k : ℝ | k ∈ Set.Icc 0 1 ∧ formalRectangularOmega F k = 2}
    from ⟨0, ⟨le_rfl, zero_le_one⟩, formalRectangularOmega_zero⟩)
  intro k hk
  exact hk.1.2

/-- Positive-slack admissibility at the actual infimum. -/
theorem formalRectangularAdmissibleExponent_formalRectangularOmega (k : ℝ) :
    FormalRectangularAdmissibleExponent F k (formalRectangularOmega F k) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨τ, hτ, hτlt⟩ := exists_lt_of_csInf_lt
    (s := {τ : ℝ | FormalRectangularAdmissibleExponent F k τ})
    (formalRectangularAdmissibleExponent_nonempty (F := F) k)
    (show sInf {τ : ℝ | FormalRectangularAdmissibleExponent F k τ} <
        formalRectangularOmega F k + ε / 2 from
      by change formalRectangularOmega F k < formalRectangularOmega F k + ε / 2; linarith)
  obtain ⟨C, hC, hcost⟩ := hτ (ε / 2) hhalf
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hPcost⟩ := hcost n hn
  refine ⟨P, hP, hPcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

/-- Any upper bound for the formal exponent supplies actual polynomial programs. -/
theorem formalRectangularAdmissibleExponent_of_omega_le {k τ : ℝ}
    (h : formalRectangularOmega F k ≤ τ) :
    FormalRectangularAdmissibleExponent F k τ := by
  intro ε hε
  obtain ⟨C, hC, hcost⟩ :=
    formalRectangularAdmissibleExponent_formalRectangularOmega (F := F) k ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hPcost⟩ := hcost n hn
  refine ⟨P, hP, hPcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith only [h])

/-- The general formal exponent specializes to the original rectangular sizes. -/
theorem formalShapeOmega_one_k_one (k : ℝ≥0) :
    formalShapeOmega F 1 k 1 = formalRectangularOmega F k := by
  unfold formalShapeOmega formalRectangularOmega
  congr 1
  ext τ
  exact formalShapeAdmissibleExponent_iff_rectangular

end BlockIdentities.Arithmetic
