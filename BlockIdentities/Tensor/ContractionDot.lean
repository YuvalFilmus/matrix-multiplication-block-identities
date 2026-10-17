/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.RankOneContractions
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! An explicit rank-two dot restriction from a nonzero contraction minor. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators

variable {K X Y Z : Type*} [Field K]

/-- The two-dimensional dot product, with a scalar first coordinate. -/
def dotTwoTensor : Tensor K (Fin 1) (Fin 2) (Fin 2) :=
  fun _ y z => if y = z then 1 else 0

/-- A chosen two-by-two minor of a first-leg contraction. -/
def firstContractionMinor [Fintype X] (T : Tensor K X Y Z) (a : X → K)
    (y₁ y₂ : Y) (z₁ z₂ : Z) : K :=
  contractFirst T a y₁ z₁ * contractFirst T a y₂ z₂ -
    contractFirst T a y₁ z₂ * contractFirst T a y₂ z₁

private theorem restrict_two_rows [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq Y] [DecidableEq Z]
    (T : Tensor K X Y Z) (a : X → K) (y₁ y₂ : Y) (z : Z) (u v : K) :
    Tensor.restrict (fun _ : Fin 1 => a)
      (fun (_ : Fin 1) y => u * (if y = y₁ then 1 else 0) +
        v * (if y = y₂ then 1 else 0))
      (fun (_ : Fin 1) w => if w = z then 1 else 0) T 0 0 0 =
      u * contractFirst T a y₁ z + v * contractFirst T a y₂ z := by
  classical
  simp only [Tensor.restrict, ite_mul, mul_ite, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_add, add_mul,
    Finset.sum_add_distrib, contractFirst, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro x hx <;> ring

/-- The inverse of a nonzero two-by-two minor provides actual local maps to a
rank-two dot product. No coordinate distinctness premises are required. -/
theorem dotTwo_isRestriction_of_first_minor
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (a : X → K) (y₁ y₂ : Y) (z₁ z₂ : Z)
    (hminor : firstContractionMinor T a y₁ y₂ z₁ z₂ ≠ 0) :
    IsRestriction (dotTwoTensor (K := K)) T := by
  classical
  let A := contractFirst T a y₁ z₁
  let B := contractFirst T a y₁ z₂
  let C := contractFirst T a y₂ z₁
  let D := contractFirst T a y₂ z₂
  let Δ := firstContractionMinor T a y₁ y₂ z₁ z₂
  let u : Fin 2 → K := fun i => if i = 0 then D / Δ else -C / Δ
  let v : Fin 2 → K := fun i => if i = 0 then -B / Δ else A / Δ
  let select : Fin 2 → Z := fun i => if i = 0 then z₁ else z₂
  let L : Fin 1 → X → K := fun _ => a
  let M : Fin 2 → Y → K := fun i y =>
    u i * (if y = y₁ then 1 else 0) + v i * (if y = y₂ then 1 else 0)
  let R : Fin 2 → Z → K := fun i z => if z = select i then 1 else 0
  refine ⟨L, M, R, ?_⟩
  funext x y z
  have hformula : Tensor.restrict L M R T x y z =
      u y * contractFirst T a y₁ (select z) +
        v y * contractFirst T a y₂ (select z) := by
    exact restrict_two_rows T a y₁ y₂ (select z) (u y) (v y)
  rw [hformula]
  have hΔ : Δ ≠ 0 := hminor
  have hdet : Δ = A * D - B * C := rfl
  dsimp only [A, B, C, D] at hdet
  fin_cases y <;> fin_cases z <;>
    simp [dotTwoTensor, u, v, select, A, B, C, D] <;>
    field_simp [hΔ] <;>
    (try rw [hdet]) <;> ring

end BlockIdentities.Square
