/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.FormalBounds
public import BlockIdentities.Tensor.MatrixShapeNonzero
public import BlockIdentities.Tensor.NonzeroSum
public import BlockIdentities.Tensor.PowerClasses
public import BlockIdentities.Tensor.ValueSymmetries
public import BlockIdentities.Tensor.ConvolutionSplittings
public import BlockIdentities.Square.EntropyValueOptimization
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section
noncomputable section
open scoped BigOperators NNReal
namespace BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Arithmetic

/-- Formal polynomial algorithms, with all three manuscript ceiling dimensions. -/
def FormalShapeAdmissibleExponent (F : Type*) [Field F] (a b c : ℝ≥0) (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    ∃ P : MatrixAlgorithm F (innerSize n a) (innerSize n b) (innerSize n c),
      FormalCorrect P ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

def formalShapeOmega (F : Type*) [Field F] (a b c : ℝ≥0) : ℝ :=
  sInf {τ : ℝ | FormalShapeAdmissibleExponent F a b c τ}

/-- Same aspect carrier, sizes and program cost as Navot, with formal correctness. -/
def FormalRectangularAdmissibleExponent (F : Type*) [Field F] (k τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    ∃ P : MatrixAlgorithm F n (innerSize n k) n,
      FormalCorrect P ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

def formalRectangularOmega (F : Type*) [Field F] (k : ℝ) : ℝ :=
  sInf {τ : ℝ | FormalRectangularAdmissibleExponent F k τ}

def formalAlpha (F : Type*) [Field F] : ℝ :=
  sSup {k : ℝ | k ∈ Set.Icc 0 1 ∧ formalRectangularOmega F k = 2}

end BlockIdentities.Arithmetic
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation

/-- Ordered physical tensor legs: 0=X, 1=Y, 2=Z. -/
abbrev Axis := Fin 3

abbrev TensorOf (F : Type*) [Field F] := NonzeroTensor (AlgebraicClosure F)

/-- Dot-product dimension order is (c,a,b), hence matrix argument order (Y,Z,X). -/
def orientedExponent (F : Type*) [Field F] (u : Axis → ℝ≥0) : ℝ :=
  Arithmetic.formalShapeOmega (AlgebraicClosure F) (u 1) (u 2) (u 0)

/-- Exactly the source supporting-vector data, at a strictly interior direction.
Coordinate bounds, value boundedness and rank bounds are theorems, not fields. -/
structure InteriorSupport (F : Type*) [Field F] where
  direction : Axis → ℝ≥0
  direction_pos : ∀ i, 0 < direction i
  weight : Axis → ℝ
  supporting : ∀ u : Axis → ℝ≥0,
    (∑ i, weight i * (u i : ℝ)) ≤ orientedExponent F u
  touching : (∑ i, weight i * (direction i : ℝ)) = orientedExponent F direction

def matrixWeight {F : Type*} [Field F] (S : InteriorSupport F) (D : MatrixShape) : ℝ :=
  (D.a : ℝ) ^ S.weight 1 * (D.b : ℝ) ^ S.weight 2 * (D.c : ℝ) ^ S.weight 0

def logDotDimensions (D : MatrixShape) : Axis → ℝ :=
  ![Real.log (D.c : ℝ), Real.log (D.a : ℝ), Real.log (D.b : ℝ)]

/-- Every auxiliary and extraction length is fixed before internal repetition. -/
def orientedGains {F : Type*} [Field F] (S : InteriorSupport F)
    (T : NonzeroTensor (AlgebraicClosure F)) : Set ℝ :=
  {v | ∃ n h : ℕ, 1 ≤ n ∧ 1 ≤ h ∧ ∃ D E : MatrixShape,
    AsymptoticallyRestricts (product (power T.val n) D.tensor) (copies h E.tensor) ∧
      v = ((h : ℝ) * matrixWeight S E / matrixWeight S D) ^ (1 / (n : ℝ))}

/-- Literal source supremum on its nonzero/interior-support carrier. -/
def orientedValue {F : Type*} [Field F] (S : InteriorSupport F)
    (T : NonzeroTensor (AlgebraicClosure F)) : ℝ := sSup (orientedGains S T)

/-- Standard asymptotic rank: infimum of exact tensor-power rank roots. -/
def tensorAsymptoticRank {K : Type*} [Field K] (T : NonzeroTensor K) : ℝ :=
  sInf {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧
    r = (exactRank (power T.val n).coeff : ℝ) ^ (1 / (n : ℝ))}

/-- Actual three sectors with the intrinsic middle first-coordinate reversal. -/
def generalTriplingSplit {K : Type*} [Field K] (r s : ℕ+) : FiniteTensor K :=
  let C := OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r s
  sharedFirstThree C (fun (x : Fin (r : ℕ)) z y => C x.rev y z) C

end BlockIdentities.Rectangular
