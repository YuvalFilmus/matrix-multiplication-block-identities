/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.MatrixRate
public import BlockIdentities.Square.RankSupplyRounding

/-! Convert repeated independent matrix outputs using genuine rank decompositions. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped Topology
variable {K : Type*} [Field K]

theorem matrix_scalar_supply {N R : ℕ} (h : exactMatrixRank K N ≤ R) :
    ClassDegenerates (R : TensorClass K) (matrixClass N) := by
  have hr := rank_scalar_supply (square (K := K) N)
  have hmono : (exactRank (square (K := K) N).coeff : TensorClass K) ≤ R :=
    Nat.mono_cast (by
      change exactRank (Tensor.pullback
        (Fintype.equivFin (Fin N × Fin N)).symm
        (Fintype.equivFin (Fin N × Fin N)).symm
        (Fintype.equivFin (Fin N × Fin N)).symm
        (matrixMultiplicationTensor (K := K) N N N)) ≤ R
      rw [exactRank_reindex]
      exact h)
  exact (ClassDegenerates.of_le hmono).trans (by
    simpa only [tensorClass_square_eq] using hr)

/-- The scalar budget one is handled separately from the logarithmic block construction. -/
theorem exists_matrix_rank_supply_of_pos (h : ℕ) (hh : 1 ≤ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ → ℕ, (∀ j, 1 ≤ N j) ∧
      (∀ j, exactMatrixRank K (N j) ≤ h ^ j) ∧
      Tendsto (fun j : ℕ => Real.log (N j : ℝ) / (j : ℝ)) atTop
        (𝓝 (Real.log h / (exactRankExponent K + ε))) := by
  by_cases he : h = 1
  · subst h
    refine ⟨fun _ => 1, fun _ => le_rfl, ?_, ?_⟩
    · intro j
      simp only [exactMatrixRank_one, one_pow, le_refl]
    · simp
  · exact exists_matrix_rank_supply h (by omega) ε hε

/-- A fixed extraction can be repeated and its independent copies converted
into one matrix output. The rank-supply dimensions have the genuine exponent
rate; this statement does not assume a value or asymptotic sum inequality. -/
theorem repeated_extraction_matrix_supply {A : FiniteTensor K} {k h m : ℕ}
    (hex : Degenerates (power A k) (copies h (square m)))
    (hh : 1 ≤ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ → ℕ, (∀ j, 1 ≤ N j) ∧
      Tendsto (fun j : ℕ => Real.log (N j : ℝ) / (j : ℝ)) atTop
        (𝓝 (Real.log h / (exactRankExponent K + ε))) ∧
      ∀ j, ClassDegenerates (tensorClass A ^ (k * j))
        (matrixClass (N j * m ^ j)) := by
  obtain ⟨N, hN, hRank, hRate⟩ := exists_matrix_rank_supply_of_pos (K := K) h hh ε hε
  refine ⟨N, hN, hRate, ?_⟩
  intro j
  have hc := ((classDegenerates_tensorClass_iff _ _).2 hex).pow j
  simp only [tensorClass_power_eq, tensorClass_copies_eq, tensorClass_square_eq,
    mul_pow, ← pow_mul, ← Nat.cast_pow, ← matrixClass_pow] at hc
  have hs := (matrix_scalar_supply (hRank j)).mul
    (ClassDegenerates.refl (matrixClass (K := K) (m ^ j)))
  rw [← matrixClass_mul] at hs
  exact hc.trans hs

end BlockIdentities.Square
