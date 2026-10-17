/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ConvolutionSharedIdentities
public import BlockIdentities.Tensor.ConvolutionTerminal
public import BlockIdentities.Tensor.ConvolutionRankBound
public import BlockIdentities.Tensor.ValueBorderRank
public import BlockIdentities.Frozen.shared_leg_value_inequality_v2
public import BlockIdentities.Square.ConvolutionPotentialBound

/-! Actual convolution maps supply the normalized value rows and source bound. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
variable (K : Type*) [Field K] [IsAlgClosed K]

/-- Literal normalized ordinary value on positive convolution dimensions. -/
def convolutionNormalizedValue (r b : ℕ+) : ℝ :=
  normalizedValueAtOmega (nonzeroConvolution (K := K) r b)

variable {K}

theorem convolutionNormalizedValue_pos (r b : ℕ+) : 0 < convolutionNormalizedValue K r b := by
  unfold convolutionNormalizedValue normalizedValueAtOmega
  apply Real.rpow_pos_of_pos
  exact lt_of_lt_of_le zero_lt_one (one_le_value _ _)

theorem convolutionNormalizedValue_neighbor (r b : ℕ+) (hb : 2 ≤ (b : ℕ)) :
    convolutionNormalizedValue K r ⟨(b : ℕ) - 1, by omega⟩ +
      convolutionNormalizedValue K r ⟨(b : ℕ) + 1, by omega⟩ ≤
        2 * convolutionNormalizedValue K r b := by
  let B : Fin 2 → NonzeroTensor K := fun i => if i = 0 then
    nonzeroConvolution r ⟨(b : ℕ) + 1, by omega⟩ else
    nonzeroConvolution r ⟨(b : ℕ) - 1, by omega⟩
  have hB : (fun i => (B i).val) = neighborOutput (K := K) r b hb := by
    funext i
    by_cases hi : i = 0 <;> simp [B, neighborOutput, hi, nonzeroConvolution]
  have hI := convolutionNeighborIdentity (K := K) r b hb
  rw [← hB] at hI
  have hv := shared_leg_value_inequality (nonzeroConvolution (K := K) r b) B
    dotShape (fun _ => scalarShape) hI
  simpa [convolutionNormalizedValue, Fin.sum_univ_two, dotShape, scalarShape,
    MatrixShape.volume, B, add_comm] using hv

theorem convolutionNormalizedValue_tripling (r : ℕ+) (hr : 2 ≤ (r : ℕ)) :
    3 * convolutionNormalizedValue K r r ≤
      convolutionNormalizedValue K r ⟨4 * (r : ℕ) - 1, by omega⟩ := by
  have hv := shared_leg_value_inequality
    (nonzeroConvolution (K := K) r ⟨4 * (r : ℕ) - 1, by omega⟩)
    (fun _ : Fin 3 => nonzeroConvolution r r) scalarShape (fun _ => scalarShape)
    (convolutionTriplingIdentity (K := K) r hr)
  simpa [convolutionNormalizedValue, scalarShape, MatrixShape.volume,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hv

theorem convolutionNormalizedValue_diagonal_upper (a : ℕ+) :
    convolutionNormalizedValue K a a ≤
      ((2 * (a : ℕ) - 1 : ℕ) : ℝ) ^ (3 / Arithmetic.formalOmega K) := by
  have hr : 1 ≤ (a : ℕ) + (a : ℕ) - 1 := by
    have ha : 0 < (a : ℕ) := a.property
    omega
  have hv := normalizedValueAtOmega_le_of_borderRankAtMost
    (nonzeroConvolution (K := K) a a) ((a : ℕ) + (a : ℕ) - 1) hr
    (convolution_borderRankAtMost (K := K) a a)
  simpa only [convolutionNormalizedValue, two_mul] using hv

/-- Actual row maps, boundary isomorphisms and the terminal value give the
literal certificate yield. The local natural-index extension is proof-only;
all applications lie in the positive convolution domain. -/
theorem convolution_normalized_diagonal_lower (a : ℕ) (ha : 2 ≤ a) :
    2 * convolutionYield ⟨a, ha⟩ ≤
      normalizedValueAtOmega (nonzeroConvolution (K := K) ⟨a, by omega⟩ ⟨a, by omega⟩) := by
  let x : ℕ → ℕ → ℝ := fun r b => if hr : 0 < r then
    if hb : 0 < b then convolutionNormalizedValue K ⟨r, hr⟩ ⟨b, hb⟩ else 0 else 0
  have hxval (r b : ℕ) (hr : 1 ≤ r) (hb : 1 ≤ b) :
      x r b = convolutionNormalizedValue K ⟨r, by omega⟩ ⟨b, by omega⟩ := by
    simp only [x, dite_eq_left (show 0 < r by omega), dite_eq_left (show 0 < b by omega)]
  have hx : ∀ r b, 1 ≤ r → 1 ≤ b → 0 < x r b := by
    intro r b hr hb
    rw [hxval r b hr hb]
    exact convolutionNormalizedValue_pos _ _
  have hn : ∀ r b, 2 ≤ r → r ≤ b → b ≤ 4 * r - 2 →
      x r (b - 1) + x r (b + 1) ≤ 2 * x r b := by
    intro r b hr hrb _
    rw [hxval r (b - 1) (by omega) (by omega), hxval r (b + 1) (by omega) (by omega),
      hxval r b (by omega) (by omega)]
    exact convolutionNormalizedValue_neighbor ⟨r, by omega⟩ ⟨b, by omega⟩ (show 2 ≤ b by omega)
  have ht : ∀ r, 2 ≤ r → 3 * x r r ≤ x r (4 * r - 1) := by
    intro r hr
    rw [hxval r r (by omega) (by omega), hxval r (4 * r - 1) (by omega) (by omega)]
    exact convolutionNormalizedValue_tripling ⟨r, by omega⟩ hr
  have hb : ∀ r, 3 ≤ r → x r (r - 1) = x (r - 1) r := by
    intro r hr
    rw [hxval r (r - 1) (by omega) (by omega), hxval (r - 1) r (by omega) (by omega)]
    exact normalizedValue_convolution_boundary (K := K) ⟨r, by omega⟩ (show 2 ≤ r by omega)
  have h := convolutionPotential_diagonal_lower x hx hn ht hb ⟨a, ha⟩
  rw [hxval a a (by omega) (by omega), hxval 2 1 (by omega) (by omega)] at h
  have he : convolutionNormalizedValue K 2 1 = 2 := normalizedValue_convolution_two_one
  calc
    2 * convolutionYield ⟨a, ha⟩ =
        convolutionYield ⟨a, ha⟩ * convolutionNormalizedValue K (2 : ℕ+) (1 : ℕ+) := by
      rw [he]
      ring
    _ ≤ _ := h

end BlockIdentities.Square
