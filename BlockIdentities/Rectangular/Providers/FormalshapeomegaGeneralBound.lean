/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Frozen.support_angular_constraint
public import BlockIdentities.Rectangular.Frozen.formalShapeOmega_eq_algebraicClosure
public import BlockIdentities.Rectangular.SupportOptimization

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular.Providers
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem formalShapeOmega_general_bound (F : Type*) [Field F] (a b c : ℝ≥0)
    (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 < c) :
  Arithmetic.formalShapeOmega F a b c ≤
      if (c : ℝ) ≤ (a : ℝ) * (b : ℝ) / ((a : ℝ) + (b : ℝ)) then
        (a : ℝ) + (b : ℝ)
      else ((a : ℝ) + (b : ℝ) + (c : ℝ)) / 2 +
        ((a : ℝ) * (b : ℝ) / (c : ℝ) + (a : ℝ) * (c : ℝ) / (b : ℝ) +
          (b : ℝ) * (c : ℝ) / (a : ℝ)) / 4 :=
by
  let v : Axis → ℝ≥0 := ![c, a, b]
  have ha : 0 < a := lt_of_lt_of_le hc (hbc.trans hab)
  have hb : 0 < b := lt_of_lt_of_le hc hbc
  have hv : ∀ i, 0 < v i := by
    intro i
    fin_cases i
    · exact hc
    · exact ha
    · exact hb
  obtain ⟨S, hS⟩ := exists_interior_support (F := F) v hv
  have ht := S.touching
  rw [hS, Fin.sum_univ_three] at ht
  change S.weight 0 * (c : ℝ) + S.weight 1 * (a : ℝ) + S.weight 2 * (b : ℝ) =
    Arithmetic.formalShapeOmega (AlgebraicClosure F) a b c at ht
  have ho := support_objective_le_of_angles S
    (show 0 < (a : ℝ) by exact_mod_cast ha)
    (show 0 < (b : ℝ) by exact_mod_cast hb)
    (show 0 < (c : ℝ) by exact_mod_cast hc) (BlockIdentities.Rectangular.support_angular_constraint S)
  rw [BlockIdentities.Rectangular.formalShapeOmega_eq_algebraicClosure F a b c]
  calc
    Arithmetic.formalShapeOmega (AlgebraicClosure F) a b c =
        (a : ℝ) * S.weight 1 + (b : ℝ) * S.weight 2 + (c : ℝ) * S.weight 0 := by
      nlinarith only [ht]
    _ ≤ _ := ho

end BlockIdentities.Rectangular.Providers
