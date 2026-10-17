/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Arithmetic.FormalComposition

/-! Universal ring-valued correctness and finite recursive linear expressions. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Arithmetic

open OAI.MatrixMultiplication.Arithmetic
open scoped BigOperators

variable {F Input R : Type*} [Field F] [CommRing R]

/-- Substituting arbitrary ring values into formal outputs evaluates the program. -/
theorem eval₂_polynomialOutputs (φ : F →+* R) {r : ℕ}
    (p : Program F Input r) (inputs : Input → R) (i : Fin r) :
    MvPolynomial.eval₂Hom φ inputs (polynomialOutputs p i) =
      evalProgramIn φ p inputs i := by
  simpa only [polynomialOutputs, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X'] using
    map_evalProgramIn MvPolynomial.C (MvPolynomial.eval₂Hom φ inputs) p MvPolynomial.X i

/-- Formal correctness specializes to arbitrary input values in any commutative
ring, with constants transported along the given ring homomorphism. -/
theorem FormalCorrect.evalProgramIn {a b c : ℕ} {P : MatrixAlgorithm F a b c}
    (hP : FormalCorrect P) (φ : F →+* R) (inputs : MatrixInput a b c → R)
    (i : Fin a) (k : Fin c) :
    evalProgramIn φ P.program inputs (P.output i k) =
      ∑ j : Fin b, inputs (.inl (i, j)) * inputs (.inr (j, k)) := by
  have h := congrArg (MvPolynomial.eval₂Hom φ inputs) (hP i k)
  rw [eval₂_polynomialOutputs] at h
  simpa only [map_sum, map_mul, MvPolynomial.eval₂Hom_X'] using h

/-- Matrix-shaped arbitrary-ring specialization of formal correctness. -/
theorem FormalCorrect.matrix_evalProgramIn {a b c : ℕ} {P : MatrixAlgorithm F a b c}
    (hP : FormalCorrect P) (φ : F →+* R)
    (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin b) (Fin c) R)
    (i : Fin a) (k : Fin c) :
    BlockIdentities.Arithmetic.evalProgramIn φ P.program (matrixInputs A B) (P.output i k) = (A * B) i k := by
  simpa only [matrixInputs, Matrix.mul_apply] using
    hP.evalProgramIn φ (matrixInputs A B) i k

/-- An existing matrix algorithm used as a family retains universal correctness. -/
theorem evalFamilyIn_ofMatrix {a b c : ℕ} (φ : F →+* R)
    (P : MatrixAlgorithm F a b c) (hP : FormalCorrect P)
    (inputs : MatrixInput a b c → R) (o : Fin a × Fin c) :
    evalFamilyIn φ (RecursiveBlock.Family.ofMatrix P) inputs o =
      ∑ j, inputs (.inl (o.1, j)) * inputs (.inr (j, o.2)) :=
  hP.evalProgramIn φ inputs o.1 o.2

/-- The recursive-block linear-expression sum has ring-valued semantics. -/
theorem evalExpressionIn_recursive_sumFin (φ : F →+* R) (n : ℕ)
    (f : Fin n → Expression F Input) (inputs : Input → R) :
    evalExpressionIn φ inputs (RecursiveBlock.LinearExpression.sumFin n f) =
      ∑ i, evalExpressionIn φ inputs (f i) := by
  induction n with
  | zero => simp [RecursiveBlock.LinearExpression.sumFin, evalExpressionIn]
  | succ n ih =>
    simp only [RecursiveBlock.LinearExpression.sumFin, evalExpressionIn, ih,
      Fin.sum_univ_succ]

/-- Recursive linear combinations evaluate by applying the coefficient map. -/
theorem evalExpressionIn_recursive_linear {Term : Type*} [Fintype Term]
    (φ : F →+* R) (a : Term → F) (wire : Term → Input) (inputs : Input → R) :
    evalExpressionIn φ inputs (RecursiveBlock.LinearExpression.linear a wire) =
      ∑ i, φ (a i) * inputs (wire i) := by
  rw [RecursiveBlock.LinearExpression.linear, evalExpressionIn_recursive_sumFin]
  exact (Fintype.equivFin Term).symm.sum_comp
    (fun i => φ (a i) * inputs (wire i))

/-- The input-family linear preprocessing works over arbitrary ring inputs. -/
theorem evalFamilyIn_recursive_input_left {n₁ n₂ n₃ r m₁ m₂ m₃ : ℕ}
    (φ : F →+* R) (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (inputs : MatrixInput (n₁ * m₁) (n₂ * m₂) (n₃ * m₃) → R)
    (q : Fin r) (s : Fin m₁) (t : Fin m₂) :
    evalFamilyIn φ (RecursiveBlock.inputFamily a b) inputs (q, .inl (s, t)) =
      ∑ x, φ (a q x) * inputs (.inl (RecursiveBlock.join x.1 s,
        RecursiveBlock.join x.2 t)) := by
  simp only [RecursiveBlock.inputFamily, evalFamilyIn_expressions,
    RecursiveBlock.inputExpressions, evalExpressionIn_recursive_linear]

/-- The right input-family linear preprocessing works over arbitrary ring inputs. -/
theorem evalFamilyIn_recursive_input_right {n₁ n₂ n₃ r m₁ m₂ m₃ : ℕ}
    (φ : F →+* R) (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (inputs : MatrixInput (n₁ * m₁) (n₂ * m₂) (n₃ * m₃) → R)
    (q : Fin r) (t : Fin m₂) (u : Fin m₃) :
    evalFamilyIn φ (RecursiveBlock.inputFamily a b) inputs (q, .inr (t, u)) =
      ∑ y, φ (b q y) * inputs (.inr (RecursiveBlock.join y.1 t,
        RecursiveBlock.join y.2 u)) := by
  simp only [RecursiveBlock.inputFamily, evalFamilyIn_expressions,
    RecursiveBlock.inputExpressions, evalExpressionIn_recursive_linear]

/-- The output-family linear recombination works over arbitrary ring inputs. -/
theorem evalFamilyIn_recursive_output {n₁ n₃ r m₁ m₃ : ℕ}
    (φ : F →+* R) (c : Fin r → Fin n₃ × Fin n₁ → F)
    (inputs : Fin r × (Fin m₁ × Fin m₃) → R)
    (i : Fin n₁) (k : Fin n₃) (s : Fin m₁) (u : Fin m₃) :
    evalFamilyIn φ (RecursiveBlock.outputFamily c) inputs
      (RecursiveBlock.join i s, RecursiveBlock.join k u) =
      ∑ q, φ (c q (k, i)) * inputs (q, (s, u)) := by
  simp only [RecursiveBlock.outputFamily, evalFamilyIn_expressions,
    RecursiveBlock.outputExpressions, evalExpressionIn_recursive_linear,
    RecursiveBlock.join, Equiv.symm_apply_apply]

/-- An exact coefficient rank identity yields its bilinear contraction identity
in every commutative target ring, with the coefficients transported by φ. -/
theorem recursive_rank_bilinear_identity {n₁ n₂ n₃ r : ℕ}
    (φ : F →+* R)
    (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (c : Fin r → Fin n₃ × Fin n₁ → F)
    (h : OAI.MatrixMultiplication.Foundation.Tensor.matrixCoefficients
      (K := F) (Fin n₁) (Fin n₂) (Fin n₃) =
      fun x y z => ∑ q, OAI.MatrixMultiplication.Foundation.Tensor.rankOne
        (a q) (b q) (c q) x y z)
    (left : Fin n₁ × Fin n₂ → R) (right : Fin n₂ × Fin n₃ → R)
    (i : Fin n₁) (k : Fin n₃) :
    (∑ q, φ (c q (k, i)) * (∑ x, φ (a q x) * left x) *
      (∑ y, φ (b q y) * right y)) =
      ∑ j, left (i, j) * right (j, k) := by
  classical
  let T := OAI.MatrixMultiplication.Foundation.Tensor.matrixCoefficients
    (K := R) (Fin n₁) (Fin n₂) (Fin n₃)
  have hR : T = fun x y z => ∑ q,
      OAI.MatrixMultiplication.Foundation.Tensor.rankOne
        (fun x => φ (a q x)) (fun y => φ (b q y)) (fun z => φ (c q z)) x y z := by
    funext x y z
    have hx := congrArg φ (congrFun (congrFun (congrFun h x) y) z)
    by_cases hc : x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1
    · simpa [T, OAI.MatrixMultiplication.Foundation.Tensor.matrixCoefficients,
        OAI.MatrixMultiplication.Foundation.Tensor.rankOne, hc] using hx
    · simpa [T, OAI.MatrixMultiplication.Foundation.Tensor.matrixCoefficients,
        OAI.MatrixMultiplication.Foundation.Tensor.rankOne, hc] using hx
  rw [← OAI.MatrixMultiplication.Foundation.Tensor.contract_matrixCoefficients left right i k]
  change _ = OAI.MatrixMultiplication.Foundation.Tensor.contract T left right (k, i)
  rw [hR]
  simp only [OAI.MatrixMultiplication.Foundation.Tensor.contract,
    OAI.MatrixMultiplication.Foundation.Tensor.rankOne, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ q, ∑ y, ∑ x, φ (c q (k, i)) * (φ (a q x) * left x) *
        (φ (b q y) * right y)) =
        ∑ q, ∑ x, ∑ y, φ (c q (k, i)) * (φ (a q x) * left x) *
          (φ (b q y) * right y) := by
      apply Finset.sum_congr rfl
      intro q _
      exact Finset.sum_comm
    _ = ∑ x, ∑ q, ∑ y, φ (c q (k, i)) * (φ (a q x) * left x) *
        (φ (b q y) * right y) := Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ q, φ (a q x) * φ (b q y) * φ (c q (k, i)) *
        left x * right y := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro q _
      ring

/-- Ring-valued semantics of all inner recursive products. -/
theorem evalFamilyIn_recursiveProducts {n₁ n₂ n₃ r m₁ m₂ m₃ : ℕ}
    (φ : F →+* R) (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (p : MatrixAlgorithm F m₁ m₂ m₃) (hp : FormalCorrect p)
    (inputs : MatrixInput (n₁ * m₁) (n₂ * m₂) (n₃ * m₃) → R)
    (q : Fin r) (s : Fin m₁) (u : Fin m₃) :
    evalFamilyIn φ (RecursiveBlock.recursiveProducts a b p) inputs (q, (s, u)) =
      ∑ t : Fin m₂,
        (∑ x, φ (a q x) * inputs (.inl (RecursiveBlock.join x.1 s,
          RecursiveBlock.join x.2 t))) *
        (∑ y, φ (b q y) * inputs (.inr (RecursiveBlock.join y.1 t,
          RecursiveBlock.join y.2 u))) := by
  rw [RecursiveBlock.recursiveProducts, evalFamilyIn_compose, evalFamilyIn_copies,
    evalFamilyIn_ofMatrix φ p hp]
  simp only [evalFamilyIn_recursive_input_left, evalFamilyIn_recursive_input_right]

/-- The finite coefficient identity reconstructs a full block matrix product
in the arbitrary commutative target ring. -/
theorem recursive_ring_block_identity {n₁ n₂ n₃ r m₁ m₂ m₃ : ℕ}
    (φ : F →+* R)
    (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (c : Fin r → Fin n₃ × Fin n₁ → F)
    (h : OAI.MatrixMultiplication.Foundation.Tensor.matrixCoefficients
      (K := F) (Fin n₁) (Fin n₂) (Fin n₃) =
      fun x y z => ∑ q, OAI.MatrixMultiplication.Foundation.Tensor.rankOne
        (a q) (b q) (c q) x y z)
    (inputs : MatrixInput (n₁ * m₁) (n₂ * m₂) (n₃ * m₃) → R)
    (i : Fin n₁) (k : Fin n₃) (s : Fin m₁) (u : Fin m₃) :
    (∑ q, φ (c q (k, i)) * (∑ t : Fin m₂,
      (∑ x, φ (a q x) * inputs (.inl (RecursiveBlock.join x.1 s,
        RecursiveBlock.join x.2 t))) *
      (∑ y, φ (b q y) * inputs (.inr (RecursiveBlock.join y.1 t,
        RecursiveBlock.join y.2 u))))) =
      ∑ j : Fin (n₂ * m₂), inputs (.inl (RecursiveBlock.join i s, j)) *
        inputs (.inr (j, RecursiveBlock.join k u)) := by
  let L (q : Fin r) (t : Fin m₂) : R :=
    ∑ x, φ (a q x) * inputs (.inl (RecursiveBlock.join x.1 s, RecursiveBlock.join x.2 t))
  let B (q : Fin r) (t : Fin m₂) : R :=
    ∑ y, φ (b q y) * inputs (.inr (RecursiveBlock.join y.1 t, RecursiveBlock.join y.2 u))
  change (∑ q, φ (c q (k, i)) * (∑ t : Fin m₂, L q t * B q t)) = _
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hlocal (t : Fin m₂) : (∑ q, φ (c q (k, i)) * L q t * B q t) =
      ∑ j, inputs (.inl (RecursiveBlock.join i s, RecursiveBlock.join j t)) *
        inputs (.inr (RecursiveBlock.join j t, RecursiveBlock.join k u)) :=
    recursive_rank_bilinear_identity φ a b c h
      (fun x => inputs (.inl (RecursiveBlock.join x.1 s, RecursiveBlock.join x.2 t)))
      (fun y => inputs (.inr (RecursiveBlock.join y.1 t, RecursiveBlock.join y.2 u))) i k
  simp_rw [← mul_assoc, hlocal]
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type _).symm.trans
    (finProdFinEquiv.sum_comp (fun j =>
      inputs (.inl (RecursiveBlock.join i s, j)) *
        inputs (.inr (j, RecursiveBlock.join k u))))

/-- The existing finite recursive-block algorithm is formally polynomial-correct
when its inner algorithm is, using an exact coefficient rank decomposition. -/
theorem recursiveAlgorithm_formalCorrect {n₁ n₂ n₃ r m₁ m₂ m₃ : ℕ}
    (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (c : Fin r → Fin n₃ × Fin n₁ → F)
    (h : OAI.MatrixMultiplication.Foundation.Tensor.matrixCoefficients
      (K := F) (Fin n₁) (Fin n₂) (Fin n₃) =
      fun x y z => ∑ q, OAI.MatrixMultiplication.Foundation.Tensor.rankOne
        (a q) (b q) (c q) x y z)
    (p : MatrixAlgorithm F m₁ m₂ m₃) (hp : FormalCorrect p) :
    FormalCorrect (RecursiveBlock.algorithm a b c p) := by
  intro i k
  obtain ⟨⟨i, s⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨k, u⟩, rfl⟩ := finProdFinEquiv.surjective k
  change evalFamilyIn MvPolynomial.C
    ((RecursiveBlock.recursiveProducts a b p).compose (RecursiveBlock.outputFamily c))
    MvPolynomial.X (RecursiveBlock.join i s, RecursiveBlock.join k u) = _
  rw [evalFamilyIn_compose, evalFamilyIn_recursive_output]
  simp_rw [evalFamilyIn_recursiveProducts MvPolynomial.C a b p hp]
  exact recursive_ring_block_identity MvPolynomial.C a b c h MvPolynomial.X i k s u

end BlockIdentities.Arithmetic
