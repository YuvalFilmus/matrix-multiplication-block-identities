/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.Definitions
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

/-! Characteristic-free rank-one factorization from one-leg contraction minors.
The mixed contraction uses a sum of two coordinate selectors; no division by two
is used, including when the selected coordinates coincide. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open OAI.MatrixMultiplication.Foundation
open scoped BigOperators

variable {K X Y Z : Type*} [Field K]

/-- Contract the first leg against a coefficient vector. -/
def contractFirst [Fintype X] (T : Tensor K X Y Z) (a : X → K) (y : Y) (z : Z) : K :=
  ∑ x, a x * T x y z

/-- Contract the second leg against a coefficient vector. -/
def contractSecond [Fintype Y] (T : Tensor K X Y Z) (b : Y → K) (x : X) (z : Z) : K :=
  ∑ y, b y * T x y z

/-- Contract the third leg against a coefficient vector. -/
def contractThird [Fintype Z] (T : Tensor K X Y Z) (c : Z → K) (x : X) (y : Y) : K :=
  ∑ z, c z * T x y z

/-- The explicit cubic coefficient factorization forced by the vanishing minors
of every one-leg contraction, based at any nonzero coefficient. -/
theorem coefficient_factorization_of_contraction_minors
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor K X Y Z)
    (x₀ : X) (y₀ : Y) (z₀ : Z) (hbase : T x₀ y₀ z₀ ≠ 0)
    (hx : ∀ (a : X → K) (y₁ y₂ : Y) (z₁ z₂ : Z),
      contractFirst T a y₁ z₁ * contractFirst T a y₂ z₂ =
        contractFirst T a y₁ z₂ * contractFirst T a y₂ z₁)
    (hy : ∀ (b : Y → K) (x₁ x₂ : X) (z₁ z₂ : Z),
      contractSecond T b x₁ z₁ * contractSecond T b x₂ z₂ =
        contractSecond T b x₁ z₂ * contractSecond T b x₂ z₁)
    (hz : ∀ (c : Z → K) (x₁ x₂ : X) (y₁ y₂ : Y),
      contractThird T c x₁ y₁ * contractThird T c x₂ y₂ =
        contractThird T c x₁ y₂ * contractThird T c x₂ y₁)
    (x : X) (y : Y) (z : Z) :
    T x y z = T x y₀ z₀ * T x₀ y z₀ * T x₀ y₀ z / (T x₀ y₀ z₀) ^ 2 := by
  classical
  have h₀ := hx (Pi.single x₀ 1) y₀ y z₀ z
  have h₁ := hx (Pi.single x 1) y₀ y z₀ z
  have hsum := hx (fun i => (Pi.single x₀ (1 : K) : X → K) i +
    (Pi.single x (1 : K) : X → K) i) y₀ y z₀ z
  have hsecond := hy (Pi.single y₀ 1) x₀ x z₀ z
  have hthird := hz (Pi.single z₀ 1) x₀ x y₀ y
  simp only [contractFirst, contractSecond, contractThird, Pi.single_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    add_mul, Finset.sum_add_distrib] at h₀ h₁ hsum hsecond hthird
  have hmixed : T x₀ y₀ z₀ * T x y z + T x y₀ z₀ * T x₀ y z =
      T x₀ y₀ z * T x y z₀ + T x y₀ z * T x₀ y z₀ := by
    linear_combination hsum - h₀ - h₁
  have hfactor : (T x₀ y₀ z₀) ^ 2 * T x y z =
      T x y₀ z₀ * T x₀ y z₀ * T x₀ y₀ z := by
    linear_combination
      T x₀ y₀ z₀ * hmixed - T x y₀ z₀ * h₀ +
        T x₀ y₀ z * hthird + T x₀ y z₀ * hsecond
  apply (eq_div_iff (pow_ne_zero 2 hbase)).2
  simpa only [mul_comm] using hfactor

/-- Every contraction having matrix rank at most one forces the tensor itself
to have exact rank at most one. The assumptions spell out the minor equations. -/
theorem rankAtMost_one_of_contraction_minors
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor K X Y Z)
    (x₀ : X) (y₀ : Y) (z₀ : Z) (hbase : T x₀ y₀ z₀ ≠ 0)
    (hx : ∀ (a : X → K) (y₁ y₂ : Y) (z₁ z₂ : Z),
      contractFirst T a y₁ z₁ * contractFirst T a y₂ z₂ =
        contractFirst T a y₁ z₂ * contractFirst T a y₂ z₁)
    (hy : ∀ (b : Y → K) (x₁ x₂ : X) (z₁ z₂ : Z),
      contractSecond T b x₁ z₁ * contractSecond T b x₂ z₂ =
        contractSecond T b x₁ z₂ * contractSecond T b x₂ z₁)
    (hz : ∀ (c : Z → K) (x₁ x₂ : X) (y₁ y₂ : Y),
      contractThird T c x₁ y₁ * contractThird T c x₂ y₂ =
        contractThird T c x₁ y₂ * contractThird T c x₂ y₁) :
    Tensor.RankAtMost T 1 := by
  refine ⟨fun _ x => T x y₀ z₀, fun _ y => T x₀ y z₀,
    fun _ z => T x₀ y₀ z / (T x₀ y₀ z₀) ^ 2, ?_⟩
  funext x y z
  simp only [Fin.sum_univ_one, Tensor.rankOne]
  rw [← mul_div_assoc]
  exact coefficient_factorization_of_contraction_minors T x₀ y₀ z₀ hbase hx hy hz x y z

/-- Contraposition supplies raw nonzero minor data in at least one orientation. -/
theorem exists_contraction_minor_of_not_rankAtMost_one
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor K X Y Z)
    (x₀ : X) (y₀ : Y) (z₀ : Z) (hbase : T x₀ y₀ z₀ ≠ 0)
    (hT : ¬ Tensor.RankAtMost T 1) :
    (∃ (a : X → K) (y₁ y₂ : Y) (z₁ z₂ : Z),
      contractFirst T a y₁ z₁ * contractFirst T a y₂ z₂ ≠
        contractFirst T a y₁ z₂ * contractFirst T a y₂ z₁) ∨
    (∃ (b : Y → K) (x₁ x₂ : X) (z₁ z₂ : Z),
      contractSecond T b x₁ z₁ * contractSecond T b x₂ z₂ ≠
        contractSecond T b x₁ z₂ * contractSecond T b x₂ z₁) ∨
    (∃ (c : Z → K) (x₁ x₂ : X) (y₁ y₂ : Y),
      contractThird T c x₁ y₁ * contractThird T c x₂ y₂ ≠
        contractThird T c x₁ y₂ * contractThird T c x₂ y₁) := by
  classical
  by_contra h
  push Not at h
  exact hT (rankAtMost_one_of_contraction_minors T x₀ y₀ z₀ hbase h.1 h.2.1 h.2.2)

end BlockIdentities.Square
