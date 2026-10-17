/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.MatrixShapeClasses
public import BlockIdentities.Rectangular.RankBoundSupply
public import BlockIdentities.Tensor.AsymptoticClasses
public import BlockIdentities.Rectangular.AsymptoticRankCopies
public import BlockIdentities.Rectangular.MatrixSupportRank

/-! Finite conversion behind the oriented gain rank bound. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open Filter
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped Topology
variable {K : Type*} [Field K]

/-- Repetition of the original conversion retains its actual subexponential
source-copy overhead. Auxiliary and diagonal-supply matrices are physical
componentwise products; no leg permutation or symmetrization occurs. -/
theorem repeated_gain_conversion {T : FiniteTensor K} {n h : ℕ} {D E : MatrixShape}
    (hconv : AsymptoticallyRestricts (product (power T n) D.tensor) (copies h E.tensor)) :
    ∃ a : ℕ → ℕ, (∀ m, 0 < a m) ∧
      Tendsto (fun m : ℕ => Real.log (a m : ℝ) / (m : ℝ)) atTop (𝓝 0) ∧
      ∀ m : ℕ, 1 ≤ m → ∀ P Q : MatrixShape,
        Degenerates (diagonal (K := K) (h ^ m)) (Q.tensor (K := K)) →
        ClassDegenerates
          ((a m : TensorClass K) * tensorClass T ^ (n * m) *
            tensorClass ((D.power m).product P).tensor)
          (tensorClass (((E.power m).product P).product Q).tensor) := by
  obtain ⟨a, ha, hrate, hc⟩ := (asymptoticallyRestricts_iff_classes _ _).mp hconv
  refine ⟨a, ha, hrate, ?_⟩
  intro m hm P Q hQ
  have hbase := (hc m hm).mul (ClassDegenerates.refl (tensorClass (P.tensor (K := K))))
  simp only [tensorClass_product_eq, tensorClass_power_eq, tensorClass_copies_eq,
    mul_pow, ← pow_mul] at hbase
  have hinput :
      (a m : TensorClass K) * (tensorClass T ^ (n * m) * tensorClass D.tensor ^ m) *
          tensorClass P.tensor =
        (a m : TensorClass K) * tensorClass T ^ (n * m) *
          tensorClass ((D.power m).product P).tensor := by
    rw [tensorClass_matrixShape_product, tensorClass_matrixShape_power]
    ring
  rw [hinput] at hbase
  have hq : ClassDegenerates ((h ^ m : ℕ) : TensorClass K) (tensorClass Q.tensor) := by
    have hx := (classDegenerates_tensorClass_iff _ _).mpr hQ
    simpa only [tensorClass_diagonal_eq] using hx
  have hnext := hq.mul (ClassDegenerates.refl
    (tensorClass (E.tensor (K := K)) ^ m * tensorClass P.tensor))
  have hmiddle :
      (h : TensorClass K) ^ m * tensorClass E.tensor ^ m * tensorClass P.tensor =
        ((h ^ m : ℕ) : TensorClass K) * (tensorClass E.tensor ^ m * tensorClass P.tensor) := by
    rw [Nat.cast_pow]
    ring
  rw [hmiddle] at hbase
  have hout : tensorClass (Q.tensor (K := K)) * (tensorClass E.tensor ^ m * tensorClass P.tensor) =
      tensorClass (((E.power m).product P).product Q).tensor := by
    rw [tensorClass_matrixShape_product, tensorClass_matrixShape_product,
      tensorClass_matrixShape_power]
    ring
  rw [hout] at hnext
  exact hbase.trans hnext

/-- Each finite repeated conversion gives an actual rank comparison, with the
original overhead still visible. The auxiliary matrix is charged its exact rank. -/
theorem repeated_gain_weight_bound {F : Type*} [Field F] (S : InteriorSupport F)
    (T : TensorOf F) {n h : ℕ} {D E : MatrixShape}
    (hconv : AsymptoticallyRestricts (product (power T.val n) D.tensor) (copies h E.tensor)) :
    ∃ a : ℕ → ℕ, (∀ m, 0 < a m) ∧
      Tendsto (fun m : ℕ => Real.log (a m : ℝ) / (m : ℝ)) atTop (𝓝 0) ∧
      ∀ m : ℕ, 1 ≤ m → ∀ P Q : MatrixShape,
        Degenerates (diagonal (K := AlgebraicClosure F) (h ^ m))
          (Q.tensor (K := AlgebraicClosure F)) →
        matrixWeight S (((E.power m).product P).product Q) ≤
          (a m : ℝ) * tensorAsymptoticRank T ^ (n * m) *
            (exactRank (((D.power m).product P).tensor (K := AlgebraicClosure F)).coeff : ℝ) := by
  obtain ⟨a, ha, hrate, hc⟩ := repeated_gain_conversion hconv
  refine ⟨a, ha, hrate, ?_⟩
  intro m hm P Q hQ
  let B : TensorOf F := ((D.power m).product P).nonzeroTensor
  let U : TensorOf F := (T.power (n * m)).product B
  let A : TensorOf F := U.copies (a m) (by have hh := ha m; omega)
  let V : TensorOf F := (((E.power m).product P).product Q).nonzeroTensor
  have hB : B.val = ((D.power m).product P).tensor := rfl
  have hV : V.val = (((E.power m).product P).product Q).tensor := rfl
  have hclass : ClassDegenerates (tensorClass A.val) (tensorClass V.val) := by
    have hh := hc m hm P Q hQ
    change ClassDegenerates
      (tensorClass (copies (a m) (product (power T.val (n * m)) B.val)))
      (tensorClass V.val)
    rw [hB, hV]
    simpa only [tensorClass_copies_eq, tensorClass_product_eq, tensorClass_power_eq,
      mul_assoc] using hh
  have hmono : tensorAsymptoticRank V ≤ tensorAsymptoticRank A :=
    tensorAsymptoticRank_mono_degeneration A V
      ((classDegenerates_tensorClass_iff A.val V.val).mp hclass)
  have hcopy := tensorAsymptoticRank_copies_le U (a m) (by have hh := ha m; omega)
  have hprod := tensorAsymptoticRank_product_le (T.power (n * m)) B
  have hupper : tensorAsymptoticRank U ≤
      tensorAsymptoticRank T ^ (n * m) * (exactRank B.val.coeff : ℝ) := by
    calc
      _ ≤ tensorAsymptoticRank (T.power (n * m)) * tensorAsymptoticRank B := hprod
      _ = tensorAsymptoticRank T ^ (n * m) * tensorAsymptoticRank B := by
        rw [tensorAsymptoticRank_power]
      _ ≤ _ := mul_le_mul_of_nonneg_left (tensorAsymptoticRank_le_exactRank B)
        (pow_nonneg (le_trans zero_le_one (one_le_tensorAsymptoticRank T)) _)
  calc
    _ ≤ tensorAsymptoticRank V := matrixWeight_le_tensorAsymptoticRank S _
    _ ≤ tensorAsymptoticRank A := hmono
    _ ≤ (a m : ℝ) * tensorAsymptoticRank U := hcopy
    _ ≤ (a m : ℝ) * (tensorAsymptoticRank T ^ (n * m) *
        (exactRank B.val.coeff : ℝ)) :=
      mul_le_mul_of_nonneg_left hupper (Nat.cast_nonneg _)
    _ = _ := by rw [hB]; ring

/-- Literal positive matrix shape with physical dot-dimension order (c,a,b). -/
def matrixShapeOfDotDimensions (d : Axis → ℕ) (hd : ∀ i, 1 ≤ d i) : MatrixShape :=
  ⟨d 1, d 2, d 0, lt_of_lt_of_le Nat.zero_lt_one (hd 1),
    lt_of_lt_of_le Nat.zero_lt_one (hd 2), lt_of_lt_of_le Nat.zero_lt_one (hd 0)⟩

/-- The complement of the repeated input matrix, rounded independently on each
physical leg. The scale inequality supplies its positivity. -/
def auxiliaryPaddingShape {F : Type*} [Field F] (S : InteriorSupport F)
    (D : MatrixShape) (L : ℝ) (hL : ∀ i, logDotDimensions D i ≤ L * (S.direction i : ℝ))
    (j : ℕ) : MatrixShape :=
  matrixShapeOfDotDimensions
    (fun i => auxiliaryPadding (L * (S.direction i : ℝ) - logDotDimensions D i) j)
    (fun i => auxiliaryPadding_pos (sub_nonneg.mpr (hL i)) j)

/-- The actual diagonal-supply matrix, including the scalar case h=1. -/
def diagonalSupplyShape {F : Type*} [Field F] (S : InteriorSupport F)
    (h : ℕ) (hh : 1 ≤ h) (ε : ℝ) (hε : 0 < ε) (j : ℕ) : MatrixShape :=
  matrixShapeOfDotDimensions (fun i => diagonalSupplyDimension S h ε i j)
    (fun i => diagonalSupplyDimension_pos S hh hε i j)

/-- Fixed ordered weights commute with logarithmic dimension limits. -/
theorem matrixWeight_log_rate {F : Type*} [Field F] (S : InteriorSupport F)
    (M : ℕ → MatrixShape) (u : Axis → ℝ)
    (hu : ∀ i, Tendsto (fun j : ℕ => logDotDimensions (M j) i / ((j : ℝ) + 1))
      atTop (𝓝 (u i))) :
    Tendsto (fun j : ℕ => Real.log (matrixWeight S (M j)) / ((j : ℝ) + 1))
      atTop (𝓝 (S.weight 1 * u 1 + S.weight 2 * u 2 + S.weight 0 * u 0)) := by
  have h := (((hu 1).const_mul (S.weight 1)).add
    ((hu 2).const_mul (S.weight 2))).add ((hu 0).const_mul (S.weight 0))
  convert h using 1
  funext j
  rw [log_matrixWeight]
  simp only [Fin.sum_univ_succ]
  change (S.weight 0 * logDotDimensions (M j) 0 +
    (S.weight 1 * logDotDimensions (M j) 1 + (S.weight 2 * logDotDimensions (M j) 2 + 0))) /
      ((j : ℝ) + 1) = _
  ring

/-- The replicated output, retained complement, and actual supplied matrix
combine by multiplication of dimensions and addition of logarithmic rates. -/
theorem output_dimension_with_supply_log_rate (d e : ℕ) (he : 1 ≤ e)
    (w q : ℝ) (hw : Real.log (d : ℝ) ≤ w) (Q : ℕ → ℕ)
    (hQ : ∀ j, 1 ≤ Q j)
    (hQrate : Tendsto (fun j : ℕ => Real.log (Q j : ℝ) / ((j : ℝ) + 1))
      atTop (𝓝 q)) :
    Tendsto (fun j : ℕ => Real.log
      ((e ^ (j + 1) * auxiliaryPadding (w - Real.log (d : ℝ)) j * Q j : ℕ) : ℝ) /
        ((j : ℝ) + 1)) atTop (𝓝 (w + Real.log (e : ℝ) - Real.log (d : ℝ) + q)) := by
  have hr := (auxiliary_output_log_rate d e he w hw).add hQrate
  have heq (j : ℕ) : Real.log
      ((e ^ (j + 1) * auxiliaryPadding (w - Real.log (d : ℝ)) j * Q j : ℕ) : ℝ) /
        ((j : ℝ) + 1) =
      Real.log ((e ^ (j + 1) * auxiliaryPadding (w - Real.log (d : ℝ)) j : ℕ) : ℝ) /
        ((j : ℝ) + 1) + Real.log (Q j : ℝ) / ((j : ℝ) + 1) := by
    have hep : 0 < e := lt_of_lt_of_le Nat.zero_lt_one he
    have hpp : 0 < auxiliaryPadding (w - Real.log (d : ℝ)) j :=
      lt_of_lt_of_le Nat.zero_lt_one (auxiliaryPadding_pos (sub_nonneg.mpr hw) j)
    have hqp : 0 < (Q j : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hQ j))
    have hprod : 0 < ((e ^ (j + 1) * auxiliaryPadding (w - Real.log (d : ℝ)) j : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_pos (pow_pos hep _) hpp)
    rw [Nat.cast_mul, Real.log_mul hprod.ne' hqp.ne', add_div]
  simpa only [heq] using hr

/-- The logarithmic comparison still contains the actual copy overhead and
actual finite auxiliary rank. Only common auxiliary rates may later cancel. -/
theorem repeated_gain_log_bound {F : Type*} [Field F] (S : InteriorSupport F)
    (T : TensorOf F) {n h : ℕ} {D E : MatrixShape}
    (hconv : AsymptoticallyRestricts (product (power T.val n) D.tensor) (copies h E.tensor)) :
    ∃ a : ℕ → ℕ, (∀ m, 0 < a m) ∧
      Tendsto (fun m : ℕ => Real.log (a m : ℝ) / (m : ℝ)) atTop (𝓝 0) ∧
      ∀ m : ℕ, 1 ≤ m → ∀ P Q : MatrixShape,
        Degenerates (diagonal (K := AlgebraicClosure F) (h ^ m))
          (Q.tensor (K := AlgebraicClosure F)) →
        Real.log (matrixWeight S (((E.power m).product P).product Q)) / (m : ℝ) ≤
          Real.log (a m : ℝ) / (m : ℝ) + (n : ℝ) * Real.log (tensorAsymptoticRank T) +
            Real.log (exactRank (((D.power m).product P).tensor
              (K := AlgebraicClosure F)).coeff : ℝ) / (m : ℝ) := by
  obtain ⟨a, ha, hrate, hc⟩ := repeated_gain_weight_bound S T hconv
  refine ⟨a, ha, hrate, ?_⟩
  intro m hm P Q hQ
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hapos : 0 < (a m : ℝ) := by exact_mod_cast ha m
  have hrpos : 0 < tensorAsymptoticRank T :=
    lt_of_lt_of_le zero_lt_one (one_le_tensorAsymptoticRank T)
  have hBpos : 0 < (exactRank (((D.power m).product P).tensor
      (K := AlgebraicClosure F)).coeff : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
      (one_le_exactRank_of_nonzero _ (nonzero_matrixShape ((D.power m).product P))))
  have hl := Real.log_le_log (matrixWeight_pos S _) (hc m hm P Q hQ)
  rw [Real.log_mul (mul_pos hapos (pow_pos hrpos _)).ne' hBpos.ne',
    Real.log_mul hapos.ne' (pow_pos hrpos _).ne', Real.log_pow] at hl
  have hd := div_le_div_of_nonneg_right hl hmpos.le
  convert hd using 1 <;> push_cast <;> field_simp [hmpos.ne'] <;> ring

/-- The actual final matrix after retaining the complement and consuming the
diagonal supply. This is the componentwise product from the manuscript. -/
def gainOutputShape {F : Type*} [Field F] (S : InteriorSupport F) (D E : MatrixShape)
    (L : ℝ) (hL : ∀ i, logDotDimensions D i ≤ L * (S.direction i : ℝ))
    (h : ℕ) (hh : 1 ≤ h) (ε : ℝ) (hε : 0 < ε) (j : ℕ) : MatrixShape :=
  ((E.power (j + 1)).product (auxiliaryPaddingShape S D L hL j)).product
    (diagonalSupplyShape S h hh ε hε j)

theorem gainOutputShape_log_dimension_rate {F : Type*} [Field F]
    (S : InteriorSupport F) (D E : MatrixShape) (L : ℝ)
    (hL : ∀ i, logDotDimensions D i ≤ L * (S.direction i : ℝ))
    (h : ℕ) (hh : 1 ≤ h) (ε : ℝ) (hε : 0 < ε) (i : Axis) :
    Tendsto (fun j : ℕ => logDotDimensions (gainOutputShape S D E L hL h hh ε hε j) i /
      ((j : ℝ) + 1)) atTop
      (𝓝 ((L + diagonalSupplyScale S h ε) * (S.direction i : ℝ) +
        logDotDimensions E i - logDotDimensions D i)) := by
  have hr (d e : ℕ) (he : 1 ≤ e) (w : ℝ)
      (hw : Real.log (d : ℝ) ≤ w) (k : Axis) :=
    output_dimension_with_supply_log_rate d e he w
      (diagonalSupplyScale S h ε * (S.direction k : ℝ)) hw
      (diagonalSupplyDimension S h ε k)
      (diagonalSupplyDimension_pos S hh hε k)
      (diagonalSupplyDimension_log_rate S hh hε k)
  fin_cases i
  · have hD : Real.log (D.c : ℝ) ≤ L * (S.direction 0 : ℝ) := by
      simpa [logDotDimensions] using hL 0
    have hx := hr D.c E.c (by have hp := E.c_pos; omega) _ hD 0
    convert hx using 1 <;>
      simp [gainOutputShape, auxiliaryPaddingShape, diagonalSupplyShape,
        matrixShapeOfDotDimensions, MatrixShape.product, MatrixShape.power, logDotDimensions]
    ring
  · have hD : Real.log (D.a : ℝ) ≤ L * (S.direction 1 : ℝ) := by
      simpa [logDotDimensions] using hL 1
    have hx := hr D.a E.a (by have hp := E.a_pos; omega) _ hD 1
    convert hx using 1 <;>
      simp [gainOutputShape, auxiliaryPaddingShape, diagonalSupplyShape,
        matrixShapeOfDotDimensions, MatrixShape.product, MatrixShape.power, logDotDimensions]
    ring
  · have hD : Real.log (D.b : ℝ) ≤ L * (S.direction 2 : ℝ) := by
      simpa [logDotDimensions] using hL 2
    have hx := hr D.b E.b (by have hp := E.b_pos; omega) _ hD 2
    convert hx using 1 <;>
      simp [gainOutputShape, auxiliaryPaddingShape, diagonalSupplyShape,
        matrixShapeOfDotDimensions, MatrixShape.product, MatrixShape.power, logDotDimensions]
    ring

end BlockIdentities.Rectangular
