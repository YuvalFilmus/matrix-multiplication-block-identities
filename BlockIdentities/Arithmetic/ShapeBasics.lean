/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Definitions

/-! Elementary formal shape admissibility, with original programs and costs. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Arithmetic
open scoped NNReal
variable {F : Type*} [Field F]

/-- Three ceiling bounds and the original naive algorithm give a uniform cost. -/
theorem formalShapeAdmissibleExponent_naive (a b c : ℝ≥0) :
    FormalShapeAdmissibleExponent F a b c ((a : ℝ) + b + c) := by
  intro ε hε
  refine ⟨16, by norm_num, ?_⟩
  intro n hn
  refine ⟨naiveAlgorithm (innerSize n a) (innerSize n b) (innerSize n c),
    naiveAlgorithm_formalCorrect _ _ _, ?_⟩
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have ha := innerSize_cast_le hn a.property
  have hb := innerSize_cast_le hn b.property
  have hc := innerSize_cast_le hn c.property
  rw [naiveAlgorithm_cost]
  push_cast
  calc
    2 * (innerSize n a : ℝ) * innerSize n b * innerSize n c ≤
        2 * (2 * (n : ℝ) ^ (a : ℝ)) * (2 * (n : ℝ) ^ (b : ℝ)) *
          (2 * (n : ℝ) ^ (c : ℝ)) := by
      have hfirst := mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℝ) ≤ 2)
      have hsecond := mul_le_mul hfirst hb (Nat.cast_nonneg (innerSize n b))
        (by positivity : 0 ≤ 2 * (2 * (n : ℝ) ^ (a : ℝ)))
      exact mul_le_mul hsecond hc (Nat.cast_nonneg (innerSize n c))
        (by positivity : 0 ≤ 2 * (2 * (n : ℝ) ^ (a : ℝ)) *
          (2 * (n : ℝ) ^ (b : ℝ)))
    _ = 16 * (n : ℝ) ^ ((a : ℝ) + b + c) := by
      rw [Real.rpow_add hnpos, Real.rpow_add hnpos]
      ring
    _ ≤ 16 * (n : ℝ) ^ ((a : ℝ) + b + c + ε) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem formalShapeAdmissibleExponent_nonempty (a b c : ℝ≥0) :
    Set.Nonempty {τ : ℝ | FormalShapeAdmissibleExponent F a b c τ} :=
  ⟨(a : ℝ) + b + c, formalShapeAdmissibleExponent_naive a b c⟩

/-- The actual number of output coordinates bounds every admissible exponent.
Polynomial correctness is specialized only in the formal-to-functional direction. -/
theorem formalShapeAdmissibleExponent_output_le {a b c : ℝ≥0} {τ : ℝ}
    (hτ : FormalShapeAdmissibleExponent F a b c τ) : (a : ℝ) + c ≤ τ := by
  by_contra hneg
  have hτlt : τ < (a : ℝ) + c := lt_of_not_ge hneg
  let ε : ℝ := ((a : ℝ) + c - τ) / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C ^ ε⁻¹) 1)
  have hnreal : 1 < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < (n : ℝ) := lt_trans zero_lt_one hnreal
  have hn1 : 1 ≤ n := (Nat.one_le_cast (α := ℝ)).mp hnreal.le
  have hpow : C < (n : ℝ) ^ ε :=
    (Real.rpow_inv_lt_iff_of_pos hC.le (Nat.cast_nonneg n) hε).mp
      (lt_of_le_of_lt (le_max_left _ _) hn)
  obtain ⟨P, hP, hcost⟩ := hbound n hn1
  have ha : (n : ℝ) ^ (a : ℝ) ≤ (innerSize n a : ℝ) := Nat.le_ceil _
  have hc : (n : ℝ) ^ (c : ℝ) ≤ (innerSize n c : ℝ) := Nat.le_ceil _
  have hlower : (n : ℝ) ^ ((a : ℝ) + c) ≤ (P.cost : ℝ) := by
    calc
      _ = (n : ℝ) ^ (a : ℝ) * (n : ℝ) ^ (c : ℝ) := Real.rpow_add hnpos _ _
      _ ≤ (innerSize n a : ℝ) * (innerSize n c : ℝ) :=
        mul_le_mul ha hc (Real.rpow_nonneg hnpos.le _) (Nat.cast_nonneg _)
      _ ≤ (P.cost : ℝ) := by
        exact_mod_cast P.output_size_le_cost (one_le_innerSize hn1 b)
          (formalCorrect_implies_correct P hP)
  have hstrict : (n : ℝ) ^ ((a : ℝ) + c) < (n : ℝ) ^ ((a : ℝ) + c) := calc
    _ ≤ C * (n : ℝ) ^ (τ + ε) := hlower.trans hcost
    _ < (n : ℝ) ^ ε * (n : ℝ) ^ (τ + ε) :=
      mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hnpos _)
    _ = (n : ℝ) ^ ((a : ℝ) + c) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      dsimp only [ε]
      ring
  exact (lt_irrefl _ hstrict)

theorem formalShapeAdmissibleExponent_bddBelow (a b c : ℝ≥0) :
    BddBelow {τ : ℝ | FormalShapeAdmissibleExponent F a b c τ} :=
  ⟨(a : ℝ) + c, fun _ hτ => formalShapeAdmissibleExponent_output_le hτ⟩

theorem formalShapeOmega_output_le (a b c : ℝ≥0) :
    (a : ℝ) + c ≤ formalShapeOmega F a b c :=
  le_csInf (formalShapeAdmissibleExponent_nonempty a b c)
    (fun _ hτ => formalShapeAdmissibleExponent_output_le hτ)

theorem formalShapeOmega_nonneg (a b c : ℝ≥0) : 0 ≤ formalShapeOmega F a b c :=
  (add_nonneg a.property c.property).trans (formalShapeOmega_output_le a b c)

theorem formalShapeOmega_le_naive (a b c : ℝ≥0) :
    formalShapeOmega F a b c ≤ (a : ℝ) + b + c :=
  csInf_le (formalShapeAdmissibleExponent_bddBelow a b c)
    (formalShapeAdmissibleExponent_naive a b c)

/-- Positive slack is attained at the actual infimum with a size-uniform constant. -/
theorem formalShapeAdmissibleExponent_formalShapeOmega (a b c : ℝ≥0) :
    FormalShapeAdmissibleExponent F a b c (formalShapeOmega F a b c) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨τ, hτ, hτlt⟩ := exists_lt_of_csInf_lt
    (s := {τ : ℝ | FormalShapeAdmissibleExponent F a b c τ})
    (formalShapeAdmissibleExponent_nonempty (F := F) a b c)
    (show sInf {τ : ℝ | FormalShapeAdmissibleExponent F a b c τ} <
        formalShapeOmega F a b c + ε / 2 from
      by change formalShapeOmega F a b c < formalShapeOmega F a b c + ε / 2; linarith)
  obtain ⟨C, hC, hcost⟩ := hτ (ε / 2) hhalf
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hPcost⟩ := hcost n hn
  refine ⟨P, hP, hPcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem formalShapeOmega_zero_zero_zero : formalShapeOmega F 0 0 0 = 0 := by
  apply le_antisymm _ (formalShapeOmega_nonneg 0 0 0)
  simpa using (formalShapeOmega_le_naive (F := F) 0 0 0)

end BlockIdentities.Arithmetic
