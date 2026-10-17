/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.ConvolutionSplittings
public import BlockIdentities.Tensor.PolynomialMaps

/-! Denominator-cleared local maps for the characteristic-free neighbor split. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Providers.Neighbor

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open BlockIdentities.Square
open scoped BigOperators

variable {K : Type*} [Field K]

private theorem indicator_product (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (1 : K) else 0) * (if q then 1 else 0) =
      (if p ∧ q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

private abbrev SideY (b : ℕ) := Fin (b + 1) ⊕ Fin (b - 1)
private abbrev SideZ (r b : ℕ) := Fin (r + (b + 1) - 1) ⊕ Fin (r + (b - 1) - 1)

private def rawSource (r b : ℕ) :
    Tensor K (Fin r) (Fin b × Fin 2) (Fin (r + b - 1) × Fin 2) :=
  fun i j k => if k.1 = convolutionOutput i j.1 ∧ k.2 = j.2 then 1 else 0

private def rawTarget (r b : ℕ) : Tensor K (Fin r) (SideY b) (SideZ r b) :=
  fun i y z => match y, z with
  | .inl y, .inl z => OAI.MatrixMultiplication.AuxiliarySeparation.convolution r (b + 1) i y z
  | .inr y, .inr z => OAI.MatrixMultiplication.AuxiliarySeparation.convolution r (b - 1) i y z
  | _, _ => 0

private def leftMap (r : ℕ) : Fin r → Fin r → Polynomial K :=
  fun x i => if i = x then 1 else 0

private def middleMap (b : ℕ) (hb : 2 ≤ b) : SideY b → (Fin b × Fin 2) → Polynomial K
  | .inl p, (j, t) => if t = 0 then
      if hp : p.val < b then if j = ⟨p.val, hp⟩ then Polynomial.X else 0 else 0
    else if p.val = b then if j = ⟨b - 1, by omega⟩ then Polynomial.X else 0 else 0
  | .inr p, (j, t) => if t = 0 then
      if j = ⟨p.val + 1, by have := p.isLt; omega⟩ then -1 else 0
    else if j = ⟨p.val, by have := p.isLt; omega⟩ then 1 else 0

private def rightMap (r b : ℕ) : SideZ r b → (Fin (r + b - 1) × Fin 2) → Polynomial K
  | .inl q, (k, t) => if t = 0 then if k.val = q.val then 1 else 0
    else if k.val + 1 = q.val then 1 else 0
  | .inr q, (k, t) => if t = 0 then 0 else if k.val = q.val then Polynomial.X else 0

private theorem restricted_formula (r b : ℕ) (hb : 2 ≤ b)
    (x : Fin r) (y : SideY b) (z : SideZ r b) :
    Tensor.restrict (leftMap r) (middleMap b hb) (rightMap r b)
      (fun i j k => Polynomial.C (rawSource (K := K) r b i j k)) x y z =
      ∑ j : Fin b,
        (middleMap b hb y (j, 0) * rightMap r b z (convolutionOutput x j, 0) +
          middleMap b hb y (j, 1) * rightMap r b z (convolutionOutput x j, 1)) := by
  classical
  simp [Tensor.restrict, leftMap, rawSource, Fintype.sum_prod_type, ite_mul, mul_ite,
    Fin.sum_univ_two, Finset.sum_add_distrib]

private theorem restricted_plus (r b : ℕ) (hb : 2 ≤ b)
    (x : Fin r) (y : Fin (b + 1)) (z : SideZ r b) :
    Tensor.restrict (leftMap r) (middleMap b hb) (rightMap r b)
      (fun i j k => Polynomial.C (rawSource (K := K) r b i j k)) x (.inl y) z =
      (if hy : y.val < b then Polynomial.X *
        rightMap r b z (convolutionOutput x ⟨y.val, hy⟩, 0) else 0) +
      (if y.val = b then Polynomial.X *
        rightMap r b z (convolutionOutput x ⟨b - 1, by omega⟩, 1) else 0) := by
  rw [restricted_formula]
  by_cases hy : y.val < b <;> by_cases he : y.val = b <;>
    simp [middleMap, hy, he, Finset.sum_add_distrib, ite_mul]

private theorem restricted_minus (r b : ℕ) (hb : 2 ≤ b)
    (x : Fin r) (y : Fin (b - 1)) (z : SideZ r b) :
    Tensor.restrict (leftMap r) (middleMap b hb) (rightMap r b)
      (fun i j k => Polynomial.C (rawSource (K := K) r b i j k)) x (.inr y) z =
      -rightMap r b z (convolutionOutput x ⟨y.val + 1, by have := y.isLt; omega⟩, 0) +
        rightMap r b z (convolutionOutput x ⟨y.val, by have := y.isLt; omega⟩, 1) := by
  rw [restricted_formula]
  simp [middleMap, Finset.sum_add_distrib, ite_mul]

private theorem restricted_vanishes (r b : ℕ) (hb : 2 ≤ b)
    (x : Fin r) (y : SideY b) (z : SideZ r b) :
    (Tensor.restrict (leftMap r) (middleMap b hb) (rightMap r b)
      (fun i j k => Polynomial.C (rawSource (K := K) r b i j k)) x y z).coeff 0 = 0 := by
  rcases y with y | y
  · rw [restricted_plus]
    rcases z with z | z <;>
      simp [rightMap, convolutionOutput, Nat.add_assoc, ite_mul, mul_ite,
        ← pow_two, apply_ite] <;> split_ifs <;> simp_all
  · rw [restricted_minus]
    rcases z with z | z <;>
      simp [rightMap, convolutionOutput, Nat.add_assoc, ite_mul, mul_ite, apply_ite] <;>
      split_ifs <;> simp_all

private theorem restricted_leading (r b : ℕ) (hb : 2 ≤ b)
    (x : Fin r) (y : SideY b) (z : SideZ r b) :
    (Tensor.restrict (leftMap r) (middleMap b hb) (rightMap r b)
      (fun i j k => Polynomial.C (rawSource (K := K) r b i j k)) x y z).coeff 1 =
        rawTarget r b x y z := by
  rcases y with y | y
  · rw [restricted_plus]
    rcases z with z | z <;>
      simp [rightMap, rawTarget, convolutionOutput, Nat.add_assoc,
        OAI.MatrixMultiplication.AuxiliarySeparation.convolution, ite_mul, mul_ite,
        ← pow_two, apply_ite] <;>
      split_ifs <;> have hx := x.isLt <;> have hyy := y.isLt <;> have hz := z.isLt <;>
      simp_all <;> omega
  · rw [restricted_minus]
    rcases z with z | z <;>
      simp [rightMap, rawTarget, convolutionOutput, Nat.add_assoc,
        OAI.MatrixMultiplication.AuxiliarySeparation.convolution, ite_mul, mul_ite, apply_ite] <;>
      split_ifs <;> simp_all

private def rawDegeneration (r b : ℕ) (hb : 2 ≤ b) :
    Tensor.PolynomialRestrictionDegeneration (rawSource (K := K) r b)
      (rawTarget r b) 1 0 1 1 where
  leftMap := leftMap r
  middleMap := middleMap b hb
  rightMap := rightMap r b
  left_degree := by intro x i; simp only [leftMap]; split_ifs <;> simp
  middle_degree := by
    intro y j
    rcases y with y | y <;> simp only [middleMap] <;> split_ifs <;> simp
  right_degree := by
    intro z k
    rcases z with z | z <;> simp only [rightMap] <;> split_ifs <;> simp
  vanishes := by
    intro x y z j hj
    have hj0 : j = 0 := by omega
    subst j
    exact restricted_vanishes r b hb x y z
  leading := restricted_leading r b hb

private def transport {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {k lx ly lz : ℕ}
    (L : Tensor.PolynomialRestrictionDegeneration T S k lx ly lz)
    (A B : FiniteTensor K) (ex : Fin A.nx ≃ X) (ey : Fin A.ny ≃ Y)
    (ez : Fin A.nz ≃ Z) (fx : Fin B.nx → U) (fy : Fin B.ny → V) (fz : Fin B.nz → W)
    (hA : A.coeff = Tensor.pullback ex ey ez T)
    (hB : B.coeff = Tensor.pullback fx fy fz S) :
    Tensor.PolynomialRestrictionDegeneration A.coeff B.coeff k lx ly lz := by
  let ax := fun x i => L.leftMap (fx x) (ex i)
  let ay := fun y j => L.middleMap (fy y) (ey j)
  let az := fun z l => L.rightMap (fz z) (ez l)
  have hbase (x : Fin B.nx) (y : Fin B.ny) (z : Fin B.nz) :
      Tensor.restrict ax ay az (fun i j l => Polynomial.C (A.coeff i j l)) x y z =
      Tensor.restrict L.leftMap L.middleMap L.rightMap
        (fun i j l => Polynomial.C (T i j l)) (fx x) (fy y) (fz z) := by
    simp only [Tensor.restrict, hA, Tensor.pullback, ax, ay, az]
    rw [ex.sum_comp (fun i => ∑ j, ∑ l,
      L.leftMap (fx x) i * L.middleMap (fy y) (ey j) * L.rightMap (fz z) (ez l) *
        Polynomial.C (T i (ey j) (ez l)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [ey.sum_comp (fun j => ∑ l,
      L.leftMap (fx x) i * L.middleMap (fy y) j * L.rightMap (fz z) (ez l) *
        Polynomial.C (T i j (ez l)))]
    apply Finset.sum_congr rfl
    intro j _
    exact ez.sum_comp (fun l => L.leftMap (fx x) i * L.middleMap (fy y) j *
      L.rightMap (fz z) l * Polynomial.C (T i j l))
  refine {
    leftMap := ax
    middleMap := ay
    rightMap := az
    left_degree := fun x i => L.left_degree _ _
    middle_degree := fun y j => L.middle_degree _ _
    right_degree := fun z l => L.right_degree _ _
    vanishes := ?_
    leading := ?_ }
  · intro x y z j hj
    rw [hbase]
    exact L.vanishes _ _ _ j hj
  · intro x y z
    rw [hbase, hB]
    exact L.leading _ _ _

/-- Actual characteristic-free neighboring-length degeneration, with the
shared first leg and both independent side sectors unchanged. -/
theorem convolution_neighbor_degeneration (r b : ℕ+) (hb : 2 ≤ (b : ℕ)) :
    Degenerates (product (Square.convolution (K := K) r b) dotShape.tensor)
      (neighborSplit r b hb) := by
  let A := product (Square.convolution (K := K) r b) dotShape.tensor
  let B := neighborSplit (K := K) r b hb
  letI : Unique (Fin 1 × Fin 1) := {
    default := (0, 0)
    uniq := fun _ => Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _) }
  let ex : Fin A.nx ≃ Fin (r : ℕ) :=
    (Fintype.equivFin _).symm.trans
      (((Fintype.equivFin (Fin (r : ℕ))).symm.prodCongr
        (Fintype.equivFin (Fin 1 × Fin 1)).symm).trans (Equiv.prodUnique _ _))
  let ey : Fin A.ny ≃ Fin (b : ℕ) × Fin 2 :=
    (Fintype.equivFin _).symm.trans
      ((Fintype.equivFin (Fin (b : ℕ))).symm.prodCongr
        ((Fintype.equivFin (Fin 1 × Fin 2)).symm.trans (Equiv.uniqueProd _ _)))
  let ez : Fin A.nz ≃ Fin ((r : ℕ) + (b : ℕ) - 1) × Fin 2 :=
    (Fintype.equivFin _).symm.trans
      ((Fintype.equivFin (Fin ((r : ℕ) + (b : ℕ) - 1))).symm.prodCongr
        ((Fintype.equivFin (Fin 2 × Fin 1)).symm.trans (Equiv.prodUnique _ _)))
  have hA : A.coeff = Tensor.pullback ex ey ez (rawSource (K := K) r b) := by
    funext x y z
    let px : Fin (Fintype.card (Fin (r : ℕ))) × Fin (Fintype.card (Fin 1 × Fin 1)) :=
      (Fintype.equivFin _).symm x
    let py : Fin (Fintype.card (Fin (b : ℕ))) × Fin (Fintype.card (Fin 1 × Fin 2)) :=
      (Fintype.equivFin _).symm y
    let pz : Fin (Fintype.card (Fin ((r : ℕ) + (b : ℕ) - 1))) ×
        Fin (Fintype.card (Fin 2 × Fin 1)) := (Fintype.equivFin _).symm z
    let i := (Fintype.equivFin (Fin (r : ℕ))).symm px.1
    let j := (Fintype.equivFin (Fin (b : ℕ))).symm py.1
    let k := (Fintype.equivFin (Fin ((r : ℕ) + (b : ℕ) - 1))).symm pz.1
    let dx := (Fintype.equivFin (Fin 1 × Fin 1)).symm px.2
    let dy := (Fintype.equivFin (Fin 1 × Fin 2)).symm py.2
    let dz := (Fintype.equivFin (Fin 2 × Fin 1)).symm pz.2
    change (if i.val + j.val = k.val then (1 : K) else 0) *
        (if dx.2 = dy.1 ∧ dy.2 = dz.1 ∧ dz.2 = dx.1 then 1 else 0) =
      (if k = convolutionOutput i j ∧ dz.1 = dy.2 then 1 else 0)
    have hleft : dx.2 = dy.1 := Subsingleton.elim _ _
    have hright : dz.2 = dx.1 := Subsingleton.elim _ _
    have hk : k = convolutionOutput i j ↔ i.val + j.val = k.val := by
      constructor
      · intro h
        exact (congrArg Fin.val h).symm
      · intro h
        exact Fin.ext h.symm
    simp only [hleft, hright, true_and, and_true, hk]
    have hq : (dz.1 = dy.2) = (dy.2 = dz.1) := propext eq_comm
    simp only [hq]
    exact indicator_product _ _
  have htarget : TensorSemiring.FiniteTensor.ofTensor (rawTarget (K := K) r b) = B := by
    dsimp only [B, neighborSplit, sharedFirstPair]
    congr 1
    funext x y z
    rcases y with y | y <;> rcases z with z | z <;> rfl
  have H : Degenerates A (TensorSemiring.FiniteTensor.ofTensor (rawTarget (K := K) r b)) := by
    refine ⟨1, 0, 1, 1, ⟨?_⟩⟩
    exact transport (rawDegeneration (K := K) r b hb) A _ ex ey ez
      (Fintype.equivFin (Fin (r : ℕ))).symm
      (Fintype.equivFin (SideY b)).symm
      (Fintype.equivFin (SideZ r b)).symm hA rfl
  rw [htarget] at H
  exact H

end BlockIdentities.Providers.Neighbor
