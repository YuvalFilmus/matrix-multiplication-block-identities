/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.ContractionDot
public import BlockIdentities.Tensor.CyclicClasses
public import BlockIdentities.Tensor.ClassIdentities

/-! Three cyclic copies of a non-rank-one tensor supply two scalar copies.
The finite restriction uses three oriented dots directly, with no matrix-factor
balancing theorem or asymptotic value premise. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators

variable {K : Type*} [Field K]

private theorem dotTriple_supplies_two :
    ClassDegenerates
      (classOf (dotTwoTensor (K := K)) * cycleClass (classOf (dotTwoTensor (K := K))) *
        cycleClass (cycleClass (classOf (dotTwoTensor (K := K)))))
      (2 : TensorClass K) := by
  classical
  let D := dotTwoTensor (K := K)
  let P := Tensor.product (Tensor.product D (Tensor.cyclic D))
    (Tensor.cyclic (Tensor.cyclic D))
  let fx : Fin 2 → (Fin 1 × Fin 2) × Fin 2 := fun i => ((0, i), i)
  let fy : Fin 2 → (Fin 2 × Fin 2) × Fin 1 := fun j => ((j, j), 0)
  let fz : Fin 2 → (Fin 2 × Fin 1) × Fin 2 := fun k => ((k, 0), k)
  have heq : (diagonal (K := K) 2).coeff = Tensor.pullback fx fy fz P := by
    funext i j k
    change Fin 2 at i j k
    by_cases hij : i = j <;> by_cases hjk : j = k <;>
      simp_all [diagonal, Tensor.pullback, P, D, Tensor.product,
        Tensor.cyclic, dotTwoTensor, fx, fy, fz]
  have hres := IsRestriction.pullback P fx fy fz
  rw [← heq] at hres
  have hle : classOf (diagonal (K := K) 2).coeff ≤ classOf P :=
    (classOf_le_iff _ _).mpr hres
  have hdiag : classOf (diagonal (K := K) 2).coeff = (2 : TensorClass K) :=
    (classOf_coeff (diagonal (K := K) 2)).trans (tensorClass_diagonal_eq 2)
  rw [hdiag] at hle
  have h := ClassDegenerates.of_le hle
  simpa only [P, D, classOf_product, ← cycleClass_classOf] using h

/-- The actual finite rank-two subrank supplied by the cyclic source tensor.
One shared dot is first obtained in whichever orientation has a nonzero minor;
cyclic invariance then supplies all three orientations from separate copies. -/
theorem cyclic_cube_supplies_two {A : FiniteTensor K} (hA : Nonzero A)
    (hcycle : cycleClass (tensorClass A) = tensorClass A)
    (hrank : ¬ Tensor.RankAtMost A.coeff 1) :
    ClassDegenerates (tensorClass A ^ 3) (2 : TensorClass K) := by
  classical
  rcases Function.ne_iff.mp hA with ⟨x₀, hx⟩
  rcases Function.ne_iff.mp hx with ⟨y₀, hy⟩
  rcases Function.ne_iff.mp hy with ⟨z₀, hbase⟩
  let a := tensorClass A
  let d := classOf (dotTwoTensor (K := K))
  have hdot : ClassDegenerates a d := by
    rcases exists_contraction_minor_of_not_rankAtMost_one A.coeff x₀ y₀ z₀ hbase hrank with
      hx | hy | hz
    · obtain ⟨b, y₁, y₂, z₁, z₂, hb⟩ := hx
      have hm : firstContractionMinor A.coeff b y₁ y₂ z₁ z₂ ≠ 0 := sub_ne_zero.mpr hb
      have h := ClassDegenerates.of_le ((classOf_le_iff _ _).mpr
        (dotTwo_isRestriction_of_first_minor A.coeff b y₁ y₂ z₁ z₂ hm))
      simpa only [a, d, classOf_coeff] using h
    · obtain ⟨b, x₁, x₂, z₁, z₂, hb⟩ := hy
      have hm : firstContractionMinor (Tensor.cyclic A.coeff) b z₁ z₂ x₁ x₂ ≠ 0 := by
        apply sub_ne_zero.mpr
        simpa only [contractFirst, contractSecond, Tensor.cyclic, mul_comm] using hb
      have h := ClassDegenerates.of_le ((classOf_le_iff _ _).mpr
        (dotTwo_isRestriction_of_first_minor (Tensor.cyclic A.coeff) b z₁ z₂ x₁ x₂ hm))
      simpa only [← cycleClass_classOf, classOf_coeff, hcycle, a, d] using h
    · obtain ⟨b, x₁, x₂, y₁, y₂, hb⟩ := hz
      have hm : firstContractionMinor (Tensor.cyclic (Tensor.cyclic A.coeff))
          b x₁ x₂ y₁ y₂ ≠ 0 := by
        apply sub_ne_zero.mpr
        simpa only [contractFirst, contractThird, Tensor.cyclic] using hb
      have h := ClassDegenerates.of_le ((classOf_le_iff _ _).mpr
        (dotTwo_isRestriction_of_first_minor (Tensor.cyclic (Tensor.cyclic A.coeff))
          b x₁ x₂ y₁ y₂ hm))
      simpa only [← cycleClass_classOf, classOf_coeff, hcycle, a, d] using h
  have hproduct := (hdot.mul hdot.cycle).mul hdot.cycle.cycle
  have hpow : ClassDegenerates (tensorClass A ^ 3)
      ((d * cycleClass d) * cycleClass (cycleClass d)) := by
    simpa only [a, hcycle, pow_succ, pow_zero, one_mul] using hproduct
  exact hpow.trans dotTriple_supplies_two

end BlockIdentities.Square
