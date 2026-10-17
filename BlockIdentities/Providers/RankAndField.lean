/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Arithmetic.RankLowerBound
public import BlockIdentities.Arithmetic.RankUpperBound
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.FieldExtension

/-! Proof providers for the approved formal/rank and algebraic-closure interfaces.
This module stays outside the production imports until its frozen anchors seal. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Providers

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open BlockIdentities.Arithmetic

/-- Exact finite-rank ratios and formal polynomial algorithms have the same exponent. -/
theorem formalOmega_eq_exactRankExponent (F : Type*) [Field F] :
    formalOmega F = exactRankExponent F :=
  le_antisymm (formalOmega_le_exactRankExponent F) (exactRankExponent_le_formalOmega F)

/-- Extending coefficients of an exact decomposition cannot increase rank. -/
theorem exactMatrixRank_extension_le {F E : Type*} [Field F] [Field E] [Algebra F E]
    (n : ℕ) : exactMatrixRank E n ≤ exactMatrixRank F n := by
  have h := (exactMatrixRank_spec (K := F) n).map (algebraMap F E)
  have heq : (fun x y z => algebraMap F E
      (matrixMultiplicationTensor (K := F) n n n x y z)) =
      matrixMultiplicationTensor (K := E) n n n := by
    funext x y z
    unfold matrixMultiplicationTensor
    split_ifs <;> simp
  rw [heq] at h
  exact exactRank_le h

/-- The coefficient-extension direction requires no algebraicity hypothesis. -/
theorem exactRankExponent_extension_le {F E : Type*} [Field F] [Field E] [Algebra F E] :
    exactRankExponent E ≤ exactRankExponent F := by
  apply le_csInf (exactRankExponentSet_nonempty (K := F))
  rintro τ ⟨n, hn, rfl⟩
  have hbase : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hpos : 0 < (exactMatrixRank E n : ℝ) := by
    exact_mod_cast exactMatrixRank_pos (K := E) (show 0 < n by omega)
  exact (exactRankExponent_le_logb (K := E) hn).trans
    (Real.logb_le_logb_of_le hbase hpos
      (by exact_mod_cast exactMatrixRank_extension_le (F := F) (E := E) n))

/-- Algebraic closure is that of the given base field; all characteristics are allowed. -/
theorem formalOmega_eq_algebraicClosure (F : Type*) [Field F] :
    formalOmega F = formalOmega (AlgebraicClosure F) := by
  rw [formalOmega_eq_exactRankExponent F,
    formalOmega_eq_exactRankExponent (AlgebraicClosure F)]
  exact le_antisymm (exactRankExponent_le_algebraicClosure F)
    (exactRankExponent_extension_le (F := F) (E := AlgebraicClosure F))

end BlockIdentities.Providers
