/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.Definitions

/-! The canonical shared-leg sums in the manuscript's convolution proposition.
Each displayed block is its stated convolution tensor on its intrinsic spaces;
only the first leg is shared. This retains the middle block's exact orientation. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation

variable {K X Y₀ Z₀ Y₁ Z₁ Y₂ Z₂ : Type*} [Field K]

/-- Two sectors share X and use disjoint variable groups on the other legs. -/
def sharedFirstPair [Fintype X] [Fintype Y₀] [Fintype Z₀]
    [Fintype Y₁] [Fintype Z₁] (T₀ : Tensor K X Y₀ Z₀) (T₁ : Tensor K X Y₁ Z₁) :
    FiniteTensor K :=
  TensorSemiring.FiniteTensor.ofTensor fun x y z =>
    match y, z with
    | Sum.inl y, Sum.inl z => T₀ x y z
    | Sum.inr y, Sum.inr z => T₁ x y z
    | _, _ => 0

/-- Three sectors with the same shared first leg, on their intrinsic side spaces. -/
def sharedFirstThree [Fintype X] [Fintype Y₀] [Fintype Z₀]
    [Fintype Y₁] [Fintype Z₁] [Fintype Y₂] [Fintype Z₂]
    (T₀ : Tensor K X Y₀ Z₀) (T₁ : Tensor K X Y₁ Z₁) (T₂ : Tensor K X Y₂ Z₂) :
    FiniteTensor K :=
  TensorSemiring.FiniteTensor.ofTensor fun x y z =>
    match y, z with
    | Sum.inl y, Sum.inl z => T₀ x y z
    | Sum.inr (Sum.inl y), Sum.inr (Sum.inl z) => T₁ x y z
    | Sum.inr (Sum.inr y), Sum.inr (Sum.inr z) => T₂ x y z
    | _, _ => 0

/-- Exactly C(r,b+1) + C(r,b-1), sharing only their first variable group. -/
def neighborSplit (r b : ℕ+) (_hb : 2 ≤ (b : ℕ)) : FiniteTensor K :=
  sharedFirstPair
    (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r ((b : ℕ) + 1))
    (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r ((b : ℕ) - 1))

/-- The middle constituent before its individual first-leg reversal. -/
def middleConvolution (r : ℕ+) : FiniteTensor K :=
  let C := OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r r
  TensorSemiring.FiniteTensor.ofTensor (fun (x : Fin (r : ℕ)) z y => C x.rev y z)

/-- The exact shared sum: the middle block retains its independent first-leg
reversal. Its individual isomorphism to C(r,r)^(23) cannot be applied globally. -/
def triplingSplit (r : ℕ+) (_hr : 2 ≤ (r : ℕ)) : FiniteTensor K :=
  let C := OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r r
  sharedFirstThree C (fun (x : Fin (r : ℕ)) z y => C x.rev y z) C

end BlockIdentities.Square
