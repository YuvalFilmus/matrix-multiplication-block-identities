/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Arithmetic.FormalPolynomial
public import BlockIdentities.Arithmetic.BilinearJets
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor

/-! Shared mixed-coefficient generators for all registers of a formal program.
Each multiplication adds two generators, with no division or characteristic
assumption. Additions and subtractions merely change output weights. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Arithmetic

open OAI.MatrixMultiplication.Arithmetic
open OAI.MatrixMultiplication.Foundation
open scoped BigOperators

variable {F X Y Z : Type*} [Field F]

private theorem zero_rank (k : ℕ) : Tensor.RankAtMost (0 : Tensor F X Y Z) k := by
  refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, ?_⟩
  funext x y z
  simp [Tensor.rankOne]

private theorem add_rank {T S : Tensor F X Y Z} {k l : ℕ}
    (hT : Tensor.RankAtMost T k) (hS : Tensor.RankAtMost S l) :
    Tensor.RankAtMost (T + S) (k + l) := by
  rcases hT with ⟨a, b, c, rfl⟩
  rcases hS with ⟨d, e, f, rfl⟩
  have h := Tensor.rankAtMost_sum_rankOne (Sum.elim a d) (Sum.elim b e) (Sum.elim c f)
  convert h using 1
  · funext x y z
    simp only [Pi.add_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  · simp only [Fintype.card_sum, Fintype.card_fin]

private theorem mono_rank {T : Tensor F X Y Z} {k l : ℕ}
    (hT : Tensor.RankAtMost T k) (hkl : k ≤ l) : Tensor.RankAtMost T l := by
  have h := add_rank hT (zero_rank (X := X) (Y := Y) (Z := Z) (l - k))
  simpa only [add_zero, Nat.add_sub_of_le hkl] using h

/-- Extend every output weight by a linear combination at the new register.
The same left/right generators work simultaneously for every register. -/
private theorem cons_linear_rank {r k : ℕ} {T : Tensor F X Y (Fin r)}
    (hT : Tensor.RankAtMost T k) (w : Fin r → F) :
    Tensor.RankAtMost (fun (x : X) (y : Y) (z : Fin (r + 1)) =>
      Fin.cases (motive := fun _ => F) (∑ i, w i * T x y i) (fun i => T x y i) z) k := by
  rcases hT with ⟨a, b, c, rfl⟩
  refine ⟨a, b, fun q => Fin.cases (motive := fun _ => F) (∑ i, w i * c q i) (c q), ?_⟩
  funext x y z
  refine Fin.cases ?_ (fun i => rfl) z
  simp only [Fin.cases_zero, Tensor.rankOne, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem cons_zero_rank {r k : ℕ} {T : Tensor F X Y (Fin r)}
    (hT : Tensor.RankAtMost T k) :
    Tensor.RankAtMost (fun (x : X) (y : Y) (z : Fin (r + 1)) => Fin.cases (motive := fun _ => F) 0 (fun i => T x y i) z) k := by
  simpa using cons_linear_rank hT (fun _ => 0)

private theorem cons_add_rank {r k : ℕ} {T : Tensor F X Y (Fin r)}
    (hT : Tensor.RankAtMost T k) (i j : Fin r) :
    Tensor.RankAtMost
      (fun (x : X) (y : Y) (z : Fin (r + 1)) => Fin.cases (motive := fun _ => F) (T x y i + T x y j) (fun l => T x y l) z) k := by
  classical
  simpa [Finset.sum_add_distrib, add_mul, ite_mul] using
    cons_linear_rank hT (fun l => (if l = i then 1 else 0) + (if l = j then 1 else 0))

private theorem cons_sub_rank {r k : ℕ} {T : Tensor F X Y (Fin r)}
    (hT : Tensor.RankAtMost T k) (i j : Fin r) :
    Tensor.RankAtMost
      (fun (x : X) (y : Y) (z : Fin (r + 1)) => Fin.cases (motive := fun _ => F) (T x y i - T x y j) (fun l => T x y l) z) k := by
  classical
  simpa [Finset.sum_sub_distrib, sub_mul, ite_mul] using
    cons_linear_rank hT (fun l => (if l = i then 1 else 0) - (if l = j then 1 else 0))

private theorem cons_scaled_rank {r k : ℕ} {T : Tensor F X Y (Fin r)}
    (hT : Tensor.RankAtMost T k) (i j : Fin r) (u v : F) :
    Tensor.RankAtMost
      (fun (x : X) (y : Y) (z : Fin (r + 1)) => Fin.cases (motive := fun _ => F) (u * T x y i + v * T x y j) (fun l => T x y l) z) k := by
  classical
  simpa [Finset.sum_add_distrib, add_mul, mul_assoc, ite_mul] using
    cons_linear_rank hT (fun l => (if l = i then u else 0) + (if l = j then v else 0))

/-- All register mixed coefficients share at most twice the arithmetic-gate count
many rank-one generators; output weights are allowed to depend on the register. -/
theorem program_mixedJet_rankAtMost {r : ℕ} (p : Program F (X ⊕ Y) r) :
    Tensor.RankAtMost (fun x y i => mixedJet (polynomialOutputs p i) x y) (2 * p.cost) := by
  classical
  induction p with
  | nil =>
    refine ⟨Fin.elim0, Fin.elim0, Fin.elim0, ?_⟩
    funext x y i
    exact Fin.elim0 i
  | @step r p g ih =>
    cases g with
    | constant c =>
      have h := cons_zero_rank ih
      convert h using 1
      · funext x y z
        refine Fin.cases ?_ (fun i => rfl) z
        simp [polynomialOutputs, evalProgramIn, evalGateIn]
      · simp [Program.cost, Gate.cost]
    | input j =>
      have h := cons_zero_rank ih
      convert h using 1
      · funext x y z
        refine Fin.cases ?_ (fun i => rfl) z
        simp [polynomialOutputs, evalProgramIn, evalGateIn]
      · simp [Program.cost, Gate.cost]
    | add i j =>
      have h := mono_rank (cons_add_rank ih i j) (Nat.le_add_right (2 * p.cost) 2)
      convert h using 1
      · funext x y z
        refine Fin.cases ?_ (fun l => rfl) z
        simp [polynomialOutputs, evalProgramIn, evalGateIn]
      · change 2 * (p.cost + 1) = 2 * p.cost + 2
        omega
    | sub i j =>
      have h := mono_rank (cons_sub_rank ih i j) (Nat.le_add_right (2 * p.cost) 2)
      convert h using 1
      · funext x y z
        refine Fin.cases ?_ (fun l => rfl) z
        simp [polynomialOutputs, evalProgramIn, evalGateIn]
      · change 2 * (p.cost + 1) = 2 * p.cost + 2
        omega
    | mul i j =>
      let f := polynomialOutputs p i
      let g := polynomialOutputs p j
      let T : Tensor F X Y (Fin (r + 1)) := fun x y z =>
        Fin.cases (zeroJet f * mixedJet g x y + zeroJet g * mixedJet f x y)
          (fun l => mixedJet (polynomialOutputs p l) x y) z
      have hT : Tensor.RankAtMost T (2 * p.cost) :=
        cons_scaled_rank ih j i (zeroJet f) (zeroJet g)
      let U : Tensor F X Y (Fin (r + 1)) :=
        Tensor.rankOne (leftJet f) (rightJet g) (Fin.cases 1 (fun _ => 0))
      let V : Tensor F X Y (Fin (r + 1)) :=
        Tensor.rankOne (leftJet g) (rightJet f) (Fin.cases 1 (fun _ => 0))
      have hU : Tensor.RankAtMost U 1 := Tensor.rankOne_rankAtMost _ _ _
      have hV : Tensor.RankAtMost V 1 := Tensor.rankOne_rankAtMost _ _ _
      have h := add_rank (add_rank hT hU) hV
      convert h using 1
      · funext x y z
        refine Fin.cases ?_ (fun l => ?_) z
        · simp only [polynomialOutputs, evalProgramIn, evalGateIn, Fin.cases_zero]
          change mixedJet (f * g) x y = _
          rw [mixedJet_mul]
          simp [T, U, V, Tensor.rankOne]
          ring
        · simp [T, U, V, Tensor.rankOne, polynomialOutputs, evalProgramIn]
      · change 2 * (p.cost + 1) = (2 * p.cost + 1) + 1
        omega

/-- Pulling out any output family preserves the shared-generator rank bound. -/
theorem program_outputs_mixedJet_rankAtMost {r : ℕ} (p : Program F (X ⊕ Y) r)
    {Output : Type*} (output : Output → Fin r) :
    Tensor.RankAtMost (fun x y o => mixedJet (polynomialOutputs p (output o)) x y)
      (2 * p.cost) :=
  (program_mixedJet_rankAtMost p).pullback id id output

private theorem mixedJet_sum {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial (X ⊕ Y) F) (x : X) (y : Y) :
    mixedJet (∑ i, f i) x y = ∑ i, mixedJet (f i) x y := by
  simp [mixedJet, map_sum]

/-- A formally correct matrix program supplies an exact coefficient rank bound. -/
theorem matrix_rankAtMost_of_formalCorrect {n : ℕ}
    (P : MatrixAlgorithm F n n n) (hP : FormalCorrect P) :
    Tensor.RankAtMost (Tensor.matrixCoefficients (K := F) (Fin n) (Fin n) (Fin n))
      (2 * P.cost) := by
  classical
  have h := program_outputs_mixedJet_rankAtMost P.program
    (fun z : Fin n × Fin n => P.output z.2 z.1)
  convert h using 1
  · funext x y z
    rw [hP z.2 z.1, mixedJet_sum]
    rw [Finset.sum_eq_single y.1]
    · simp only [mixedJet_X_left_mul_X_right]
      by_cases hxy : x.2 = y.1 <;>
        by_cases hxz : x.1 = z.2 <;>
        by_cases hyz : y.2 = z.1 <;>
        simp [Tensor.matrixCoefficients, Prod.ext_iff, hxy, hxz, hyz, eq_comm]
    · intro j _ hj
      have hne : y ≠ (j, z.1) := by
        intro he
        exact hj (congrArg Prod.fst he).symm
      simp [mixedJet_X_left_mul_X_right, hne]
    · simp
  · rfl

end BlockIdentities.Arithmetic
