/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.ShapeRankSeeds
public import BlockIdentities.Square.FieldDescent

/-! Shape exponents are invariant under algebraic closure. Descent first fixes
one finite coefficient extension, then amortizes its fixed quadratic overhead. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Arithmetic
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped NNReal
variable {F : Type*} [Field F]

private theorem matrix_map_eq (a b c : ℕ) :
    (fun x y z => algebraMap F (AlgebraicClosure F)
      (matrixMultiplicationTensor (K := F) a b c x y z)) =
      matrixMultiplicationTensor (K := AlgebraicClosure F) a b c := by
  funext x y z
  change (algebraMap F (AlgebraicClosure F))
    (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0) =
    (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0)
  split_ifs <;> simp only [map_one, map_zero]

private theorem matrix_rank_map {a b c R : ℕ}
    (h : Tensor.RankAtMost (matrixMultiplicationTensor (K := F) a b c) R) :
    Tensor.RankAtMost
      (matrixMultiplicationTensor (K := AlgebraicClosure F) a b c) R := by
  have hm := h.map (algebraMap F (AlgebraicClosure F))
  rw [matrix_map_eq] at hm
  exact hm

private theorem powered_seed_size {N a m : ℕ} (hN : 0 < N) {u : ℝ≥0}
    (h : (N : ℝ) ^ (u : ℝ) ≤ a) :
    ((N ^ m : ℕ) : ℝ) ^ (u : ℝ) ≤ ((a ^ m : ℕ) : ℝ) := by
  rw [Nat.cast_pow, ← Real.rpow_pow_comm (by exact_mod_cast hN.le), Nat.cast_pow]
  exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) h m

/-- Mapping finite coefficient identities extends the scalar field. -/
theorem formalShapeOmega_algebraicClosure_le (a b c : ℝ≥0) :
    formalShapeOmega (AlgebraicClosure F) a b c ≤ formalShapeOmega F a b c := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N, hN, hseed⟩ := formalShapeOmega_eventually_rank_seed (F := F) a b c ε hε
  obtain ⟨R, hrank, hR⟩ := hseed N le_rfl
  have hNone : 1 ≤ N := by omega
  exact formalShapeOmega_le_of_rank_seed hN
    (lt_of_lt_of_le Nat.zero_lt_one (one_le_innerSize hNone a))
    (lt_of_lt_of_le Nat.zero_lt_one (one_le_innerSize hNone b))
    (lt_of_lt_of_le Nat.zero_lt_one (one_le_innerSize hNone c))
    (matrix_rank_map hrank) (Nat.le_ceil _) (Nat.le_ceil _) (Nat.le_ceil _) hR

/-- The finite coefficient extension is fixed before the tensor power grows;
its q² overhead is absorbed at arbitrary positive exponent slack. -/
theorem formalShapeOmega_le_algebraicClosure (a b c : ℝ≥0) :
    formalShapeOmega F a b c ≤ formalShapeOmega (AlgebraicClosure F) a b c := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨N, hN, hseed⟩ :=
    formalShapeOmega_eventually_rank_seed (F := AlgebraicClosure F) a b c δ hδ
  obtain ⟨R, hrank, hR⟩ := hseed N le_rfl
  have hNone : 1 ≤ N := by omega
  have hNpos : 0 < N := by omega
  have hNreal : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hmap : Tensor.RankAtMost
      (fun x y z => algebraMap F (AlgebraicClosure F)
        (matrixMultiplicationTensor (K := F)
          (innerSize N a) (innerSize N b) (innerSize N c) x y z)) R := by
    rw [matrix_map_eq]
    exact hrank
  obtain ⟨q, hq, hdescent⟩ := Square.scalar_descent_bound _ R hmap
  have hbase : 1 < (N : ℝ) ^ δ := Real.one_lt_rpow hNreal hδ
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((q : ℝ) ^ 2) hbase
  let m : ℕ := k + 1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hqbudget : (q : ℝ) ^ 2 ≤ ((N : ℝ) ^ δ) ^ m :=
    hk.le.trans (pow_le_pow_right₀ hbase.le (by dsimp [m]; omega))
  have hdesc := rankAtMost_rectangular_of_tensor_power (hdescent m hm)
  have hNm : 2 ≤ N ^ m := hN.trans (le_self_pow hNone (by omega))
  have hsizepos (u : ℝ≥0) : 0 < innerSize N u :=
    lt_of_lt_of_le Nat.zero_lt_one (one_le_innerSize hNone u)
  apply formalShapeOmega_le_of_rank_seed hNm
    (pow_pos (hsizepos a) _) (pow_pos (hsizepos b) _) (pow_pos (hsizepos c) _)
    hdesc (powered_seed_size hNpos (Nat.le_ceil _))
    (powered_seed_size hNpos (Nat.le_ceil _))
    (powered_seed_size hNpos (Nat.le_ceil _))
  simp only [Nat.cast_mul, Nat.cast_pow]
  calc
    (q : ℝ) ^ 2 * (R : ℝ) ^ m ≤ ((N : ℝ) ^ δ) ^ m *
        ((N : ℝ) ^ (formalShapeOmega (AlgebraicClosure F) a b c + δ)) ^ m :=
      mul_le_mul hqbudget (pow_le_pow_left₀ (Nat.cast_nonneg _) hR m)
        (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) _)
    _ = ((N : ℝ) ^ (formalShapeOmega (AlgebraicClosure F) a b c + ε)) ^ m := by
      rw [← mul_pow, ← Real.rpow_add (lt_trans zero_lt_one hNreal)]
      congr 2
      dsimp only [δ]
      ring
    _ = ((N : ℝ) ^ m) ^ (formalShapeOmega (AlgebraicClosure F) a b c + ε) :=
      Real.rpow_pow_comm (Nat.cast_nonneg N) _ _

/-- Algebraic closure preserves every fixed rectangular shape over every field. -/
theorem formalShapeOmega_algebraicClosure (a b c : ℝ≥0) :
    formalShapeOmega (AlgebraicClosure F) a b c = formalShapeOmega F a b c :=
  le_antisymm (formalShapeOmega_algebraicClosure_le a b c)
    (formalShapeOmega_le_algebraicClosure a b c)

end BlockIdentities.Arithmetic
