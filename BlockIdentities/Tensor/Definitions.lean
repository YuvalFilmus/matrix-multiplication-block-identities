/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Semiring
public import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialDegenerationComposition
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Basic

/-! Concrete tensor interfaces for the manuscript, with no spectral assumptions. -/

@[expose] public section
noncomputable section

namespace BlockIdentities

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators

abbrev FiniteTensor := TensorSemiring.FiniteTensor

namespace Square

variable {K : Type*} [Field K]

/-- All matrix dimensions in the manuscript are positive. -/
structure MatrixShape where
  a : ℕ
  b : ℕ
  c : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c

def MatrixShape.volume (D : MatrixShape) : ℕ := D.a * D.b * D.c

def matrix (a b c : ℕ) : FiniteTensor K :=
  TensorSemiring.FiniteTensor.ofTensor (matrixMultiplicationTensor (K := K) a b c)

def MatrixShape.tensor (D : MatrixShape) : FiniteTensor K := matrix D.a D.b D.c

def convolution (r b : ℕ+) : FiniteTensor K :=
  TensorSemiring.FiniteTensor.ofTensor (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r b)

def scalarShape : MatrixShape := ⟨1, 1, 1, Nat.zero_lt_one, Nat.zero_lt_one, Nat.zero_lt_one⟩

def dotShape : MatrixShape := ⟨1, 1, 2, Nat.zero_lt_one, Nat.zero_lt_one, by decide⟩

def square (n : ℕ) : FiniteTensor K := matrix n n n

def diagonal (n : ℕ) : FiniteTensor K :=
  ⟨n, n, n, fun i j k => if i = j ∧ j = k then 1 else 0⟩

def product (A B : FiniteTensor K) : FiniteTensor K := TensorSemiring.FiniteTensor.product A B

def power (A : FiniteTensor K) (n : ℕ) : FiniteTensor K :=
  TensorSemiring.FiniteTensor.ofTensor (Tensor.power A.coeff n)

def tensorProductList : List (FiniteTensor K) → FiniteTensor K
  | [] => square 1
  | A :: rest => product A (tensorProductList rest)

def copies (n : ℕ) (A : FiniteTensor K) : FiniteTensor K :=
  TensorSemiring.FiniteTensor.ofTensor (Tensor.directSum (fun _ : Fin n => A.coeff))

/-- A permutation of the three ordered tensor legs, in displayed-coordinate order. -/
inductive LegPermutation where
  | xyz | xzy | yxz | yzx | zxy | zyx
  deriving DecidableEq

def permute (π : LegPermutation) (A : FiniteTensor K) : FiniteTensor K :=
  match π with
  | .xyz => A
  | .xzy => ⟨A.nx, A.nz, A.ny, fun x z y => A.coeff x y z⟩
  | .yxz => ⟨A.ny, A.nx, A.nz, fun y x z => A.coeff x y z⟩
  | .yzx => ⟨A.ny, A.nz, A.nx, fun y z x => A.coeff x y z⟩
  | .zxy => ⟨A.nz, A.nx, A.ny, fun z x y => A.coeff x y z⟩
  | .zyx => ⟨A.nz, A.ny, A.nx, fun z y x => A.coeff x y z⟩

def symmetrize (A : FiniteTensor K) : FiniteTensor K :=
  product (product A (permute .yzx A)) (permute .zxy A)

/-- Actual invertible linear changes of the three variable groups. -/
def Isomorphic (A B : FiniteTensor K) : Prop :=
  ∃ (ex : (Fin A.nx → K) ≃ₗ[K] (Fin B.nx → K))
    (ey : (Fin A.ny → K) ≃ₗ[K] (Fin B.ny → K))
    (ez : (Fin A.nz → K) ≃ₗ[K] (Fin B.nz → K)),
    B.coeff = Tensor.restrict (fun x i => ex (Pi.single i 1) x)
      (fun y j => ey (Pi.single j 1) y) (fun z k => ez (Pi.single k 1) z) A.coeff

/-- Polynomial local maps, a common leading order, and exact coefficient identities. -/
def Degenerates (A B : FiniteTensor K) : Prop :=
  ∃ k Lx Ly Lz : ℕ,
    Nonempty (Tensor.PolynomialRestrictionDegeneration A.coeff B.coeff k Lx Ly Lz)

def BorderRankAtMost (A : FiniteTensor K) (r : ℕ) : Prop :=
  Degenerates (diagonal r) A

def Nonzero (A : FiniteTensor K) : Prop := A.coeff ≠ 0

/-- The full source-copy overhead is subexponential; all positive powers are covered. -/
def AsymptoticallyRestricts (A B : FiniteTensor K) : Prop :=
  ∃ a : ℕ → ℕ, (∀ n, 0 < a n) ∧
    Filter.Tendsto (fun n : ℕ => Real.log (a n : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) ∧
    ∀ n : ℕ, 1 ≤ n → Degenerates (copies (a n) (power A n)) (power B n)

/-- A shared-leg identity, in bases with disjoint second- and third-leg sectors.
The source can first permute its legs. Individual block maps are independent. -/
structure SharedLegIdentity {ι : Type} [Fintype ι]
    (A : FiniteTensor K) (B : ι → FiniteTensor K)
    (D : MatrixShape) (E : ι → MatrixShape) where
  ambient : FiniteTensor K
  blocks : ι → Tensor K (Fin ambient.nx) (Fin ambient.ny) (Fin ambient.nz)
  ySector : Fin ambient.ny → ι
  zSector : Fin ambient.nz → ι
  support : ∀ i x y z, blocks i x y z ≠ 0 → ySector y = i ∧ zSector z = i
  sum_eq : ambient.coeff = ∑ i, blocks i
  sourcePermutation : LegPermutation
  source_degeneration : Degenerates (permute sourcePermutation (product A D.tensor)) ambient
  outputPermutation : ι → LegPermutation
  block_degeneration : ∀ i, Degenerates
    ⟨ambient.nx, ambient.ny, ambient.nz, blocks i⟩
    (permute (outputPermutation i) (product (B i) (E i).tensor))

end Square
end BlockIdentities
