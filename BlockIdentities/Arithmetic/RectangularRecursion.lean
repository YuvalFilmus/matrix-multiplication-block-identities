/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.FormalGrowth
public import BlockIdentities.Tensor.RectangularFlattening

/-! Actual finite rectangular rank seeds yield polynomially correct recursive
programs. All three linear-work entry counts are derived from the rank seed. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Arithmetic
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
variable {F : Type*} [Field F]

private theorem rectangular_linear_work_le {a b c R : ℕ}
    (hab : a * b ≤ R) (hbc : b * c ≤ R) (hca : c * a ≤ R) (k : ℕ) :
    2 * R * (a * b * a ^ k * b ^ k + b * c * b ^ k * c ^ k +
      a * c * a ^ k * c ^ k) ≤ 6 * R * R ^ (k + 1) := by
  have hfirst : a * b * a ^ k * b ^ k ≤ R ^ (k + 1) := by
    calc
      _ = (a * b) ^ (k + 1) := by rw [pow_succ, mul_pow]; ring
      _ ≤ _ := Nat.pow_le_pow_left hab _
  have hsecond : b * c * b ^ k * c ^ k ≤ R ^ (k + 1) := by
    calc
      _ = (b * c) ^ (k + 1) := by rw [pow_succ, mul_pow]; ring
      _ ≤ _ := Nat.pow_le_pow_left hbc _
  have hthird : a * c * a ^ k * c ^ k ≤ R ^ (k + 1) := by
    calc
      _ = (c * a) ^ (k + 1) := by rw [pow_succ, mul_pow]; ring
      _ ≤ _ := Nat.pow_le_pow_left hca _
  calc
    _ ≤ 2 * R * (R ^ (k + 1) + R ^ (k + 1) + R ^ (k + 1)) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.add_le_add hfirst hsecond) hthird)
    _ = _ := by ring

/-- Reindex a genuine coefficient-rank decomposition of a matrix tensor power
as a single rectangular matrix tensor. The three coordinate equivalences are
independent; no symmetry or equality of the dimensions is used. -/
theorem rankAtMost_rectangular_of_tensor_power {a b c R k : ℕ}
    (hRank : Tensor.RankAtMost
      (Tensor.power (matrixMultiplicationTensor (K := F) a b c) k) R) :
    Tensor.RankAtMost
      (matrixMultiplicationTensor (K := F) (a ^ k) (b ^ k) (c ^ k)) R := by
  classical
  let ea : Fin (a ^ k) ≃ (Fin k → Fin a) := Fintype.equivOfCardEq (by simp)
  let eb : Fin (b ^ k) ≃ (Fin k → Fin b) := Fintype.equivOfCardEq (by simp)
  let ec : Fin (c ^ k) ≃ (Fin k → Fin c) := Fintype.equivOfCardEq (by simp)
  let f : Fin (a ^ k) × Fin (b ^ k) → Fin k → Fin a × Fin b :=
    fun x i => (ea x.1 i, eb x.2 i)
  let g : Fin (b ^ k) × Fin (c ^ k) → Fin k → Fin b × Fin c :=
    fun y i => (eb y.1 i, ec y.2 i)
  let h : Fin (c ^ k) × Fin (a ^ k) → Fin k → Fin c × Fin a :=
    fun z i => (ec z.1 i, ea z.2 i)
  have hp := hRank.pullback f g h
  have heq : Tensor.pullback f g h
      (Tensor.power (matrixMultiplicationTensor (K := F) a b c) k) =
      matrixMultiplicationTensor (K := F) (a ^ k) (b ^ k) (c ^ k) := by
    funext x y z
    simp only [Tensor.pullback, Tensor.power, matrixMultiplicationTensor, f, g, h,
      Fintype.prod_boole, forall_and, ← funext_iff,
      ea.injective.eq_iff, eb.injective.eq_iff, ec.injective.eq_iff]
  rw [heq] at hp
  exact hp

/-- A genuine finite rank decomposition supplies the original recursive block
program and its exact primitive-operation cost, with formal polynomial correctness. -/
theorem formal_rectangular_rank_step {a b c R m₁ m₂ m₃ : ℕ}
    (hRank : Tensor.RankAtMost (matrixMultiplicationTensor (K := F) a b c) R)
    (P : MatrixAlgorithm F m₁ m₂ m₃) (hP : FormalCorrect P) :
    ∃ Q : MatrixAlgorithm F (a * m₁) (b * m₂) (c * m₃), FormalCorrect Q ∧
      Q.cost = R * P.cost +
        2 * R * (a * b * m₁ * m₂ + b * c * m₂ * m₃ + a * c * m₁ * m₃) := by
  change Tensor.RankAtMost
    (Tensor.matrixCoefficients (K := F) (Fin a) (Fin b) (Fin c)) R at hRank
  obtain ⟨L, M, N, h⟩ := hRank
  exact ⟨RecursiveBlock.algorithm L M N P,
    recursiveAlgorithm_formalCorrect L M N h P hP,
    RecursiveBlock.algorithm_cost L M N P⟩

/-- A positive rectangular rank seed yields all tensor-power programs with
cost at most `(6R+1)(k+1)R^k`. The entry-count bounds are proved from the seed,
not assumed as additional hypotheses. This includes the scalar zeroth power. -/
theorem formal_rectangular_power_programs {a b c R : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hRank : Tensor.RankAtMost (matrixMultiplicationTensor (K := F) a b c) R) :
    ∀ k : ℕ, ∃ P : MatrixAlgorithm F (a ^ k) (b ^ k) (c ^ k),
      FormalCorrect P ∧ P.cost ≤ (6 * R + 1) * (k + 1) * R ^ k := by
  obtain ⟨hab, hbc, hca⟩ := Square.matrix_rankAtMost_entry_counts ha hb hc hRank
  intro k
  induction k with
  | zero =>
    refine ⟨scalarAlgorithm F, scalarAlgorithm_formalCorrect, ?_⟩
    simp
  | succ k ih =>
    obtain ⟨P, hP, hcost⟩ := ih
    obtain ⟨Q, hQ, hQcost⟩ := formal_rectangular_rank_step hRank P hP
    have hwork := rectangular_linear_work_le hab hbc hca k
    have hbound : Q.cost ≤ (6 * R + 1) * (k + 1 + 1) * R ^ (k + 1) := by
      rw [hQcost]
      calc
        _ ≤ R * ((6 * R + 1) * (k + 1) * R ^ k) + 6 * R * R ^ (k + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left R hcost) hwork
        _ = ((6 * R + 1) * (k + 1) + 6 * R) * R ^ (k + 1) := by
          rw [pow_succ]
          ring
        _ ≤ (6 * R + 1) * (k + 1 + 1) * R ^ (k + 1) :=
          Nat.mul_le_mul_right _ (by
            calc
              (6 * R + 1) * (k + 1) + 6 * R ≤
                  (6 * R + 1) * (k + 1) + (6 * R + 1) :=
                Nat.add_le_add_left (by omega) _
              _ = (6 * R + 1) * (k + 1 + 1) := by ring)
    have hresult : ∃ Q : MatrixAlgorithm F (a * a ^ k) (b * b ^ k) (c * c ^ k),
        FormalCorrect Q ∧ Q.cost ≤ (6 * R + 1) * (k + 1 + 1) * R ^ (k + 1) :=
      ⟨Q, hQ, hbound⟩
    rw [pow_succ' a k, pow_succ' b k, pow_succ' c k]
    exact hresult

end BlockIdentities.Arithmetic
