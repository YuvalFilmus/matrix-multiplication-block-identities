/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedGainSums
public import BlockIdentities.Rectangular.OrientedValueOperations
public import BlockIdentities.Rectangular.BinomialEntropy

/-! Per-letter binomial entropy from actual independent-copy gain witnesses. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped BigOperators Topology
variable {F : Type*} [Field F]

/-- Logarithmic finite binomial bound, before taking any limit. -/
theorem oriented_binomial_log_bound (S : InteriorSupport F) (T U : TensorOf F)
    (n h g : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) (hg : 1 ≤ g) (D E P Q : MatrixShape)
    (hT : AsymptoticallyRestricts (product (power T.val n) D.tensor) (copies h E.tensor))
    (hU : AsymptoticallyRestricts (product (power U.val n) P.tensor) (copies g Q.tensor))
    {v w : ℝ}
    (hv : v = ((h : ℝ) * matrixWeight S E / matrixWeight S D) ^ (1 / (n : ℝ)))
    (hw : w = ((g : ℝ) * matrixWeight S Q / matrixWeight S P) ^ (1 / (n : ℝ)))
    (N k : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) :
    Real.log ((n * N).choose (n * k) : ℝ) / ((n * N : ℕ) : ℝ) +
      (k : ℝ) / N * Real.log v + ((N - k : ℕ) : ℝ) / N * Real.log w ≤
      Real.log (orientedValue S (T.sum U)) := by
  let x : ℝ := (h : ℝ) * matrixWeight S E / matrixWeight S D
  let y : ℝ := (g : ℝ) * matrixWeight S Q / matrixWeight S P
  have hx : 0 < x := div_pos
    (mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)) (matrixWeight_pos S E))
    (matrixWeight_pos S D)
  have hy : 0 < y := div_pos
    (mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hg)) (matrixWeight_pos S Q))
    (matrixWeight_pos S P)
  let c := (n * N).choose (n * k)
  have hc : 0 < (c : ℝ) := by exact_mod_cast Nat.choose_pos (Nat.mul_le_mul_left n hk)
  let A : ℝ := (((c * h ^ k * g ^ (N - k) : ℕ) : ℝ) *
    matrixWeight S ((E.power k).product (Q.power (N - k))) /
    matrixWeight S ((D.power k).product (P.power (N - k))))
  have hAeq : A = (c : ℝ) * x ^ k * y ^ (N - k) := by
    dsimp only [A, x, y]
    rw [matrixWeight_product, matrixWeight_product, matrixWeight_power,
      matrixWeight_power, matrixWeight_power, matrixWeight_power]
    push_cast
    simp only [div_pow, mul_pow]
    field_simp [(matrixWeight_pos S D).ne', (matrixWeight_pos S P).ne'] <;> ring
  have hApos : 0 < A := by rw [hAeq]; positivity
  have hmem : A ^ (1 / ((n * N : ℕ) : ℝ)) ∈ orientedGains S (T.sum U) :=
    binomial_mem_orientedGains S T U n h g hn hh hg D E P Q hT hU N k hN hk
  have hle : A ^ (1 / ((n * N : ℕ) : ℝ)) ≤ orientedValue S (T.sum U) := by
    change A ^ (1 / ((n * N : ℕ) : ℝ)) ≤ sSup (orientedGains S (T.sum U))
    exact le_csSup (orientedGains_bddAbove S (T.sum U)) hmem
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hApos _) hle
  rw [Real.log_rpow hApos, hAeq,
    Real.log_mul (mul_pos hc (pow_pos hx k)).ne' (pow_pos hy (N - k)).ne',
    Real.log_mul hc.ne' (pow_pos hx k).ne', Real.log_pow, Real.log_pow] at hlog
  have hlogv : Real.log v = (1 / (n : ℝ)) * Real.log x := by
    rw [hv]
    exact Real.log_rpow hx _
  have hlogw : Real.log w = (1 / (n : ℝ)) * Real.log y := by
    rw [hw]
    exact Real.log_rpow hy _
  rw [hlogv, hlogw]
  convert hlog using 1
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  dsimp only [c]
  push_cast
  field_simp [hnreal, hNreal] <;> ring

/-- Repeating a floor type n times preserves its empirical law. The entropy
normalization counts letters n*N, so its limit is H(p), not H(p)/n. -/
theorem oriented_entropy_log_bound (S : InteriorSupport F) (T U : TensorOf F)
    (n h g : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) (hg : 1 ≤ g) (D E P Q : MatrixShape)
    (hT : AsymptoticallyRestricts (product (power T.val n) D.tensor) (copies h E.tensor))
    (hU : AsymptoticallyRestricts (product (power U.val n) P.tensor) (copies g Q.tensor))
    {v w : ℝ}
    (hv : v = ((h : ℝ) * matrixWeight S E / matrixWeight S D) ^ (1 / (n : ℝ)))
    (hw : w = ((g : ℝ) * matrixWeight S Q / matrixWeight S P) ^ (1 / (n : ℝ)))
    (p : Fin 2 → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) :
    finiteEntropy p + p 0 * Real.log v + p 1 * Real.log w ≤
      Real.log (orientedValue S (T.sum U)) := by
  obtain ⟨c, hpositive, hpopulation, hentropy⟩ := exists_binomial_entropy_schedule n hn p hp hpsum
  let N : ℕ → ℕ := fun j => ∑ i, c j i
  have hrest (j : ℕ) : N j - c j 0 = c j 1 := by
    change (∑ i, c j i) - c j 0 = c j 1
    rw [Fin.sum_univ_two]
    omega
  have hk (j : ℕ) : c j 0 ≤ N j := by
    change c j 0 ≤ ∑ i, c j i
    rw [Fin.sum_univ_two]
    omega
  have hleft := (hentropy.add ((hpopulation 0).mul_const (Real.log v))).add
    ((hpopulation 1).mul_const (Real.log w))
  have hevent : ∀ᶠ j : ℕ in atTop,
      Real.log ((n * N j).choose (n * c j 0) : ℝ) / ((n * N j : ℕ) : ℝ) +
        (c j 0 : ℝ) / (N j : ℝ) * Real.log v +
        (c j 1 : ℝ) / (N j : ℝ) * Real.log w ≤
        Real.log (orientedValue S (T.sum U)) := by
    apply Eventually.of_forall
    intro j
    have hfinite := oriented_binomial_log_bound S T U n h g hn hh hg D E P Q hT hU
      hv hw (N j) (c j 0) (hpositive j) (hk j)
    simpa only [hrest] using hfinite
  exact le_of_tendsto_of_tendsto hleft tendsto_const_nhds hevent

/-- The numerical entropy optimizer applies to arbitrary positive gains,
including gains below one. -/
theorem sum_le_orientedValue_of_common_witnesses (S : InteriorSupport F) (T U : TensorOf F)
    (n h g : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) (hg : 1 ≤ g) (D E P Q : MatrixShape)
    (hT : AsymptoticallyRestricts (product (power T.val n) D.tensor) (copies h E.tensor))
    (hU : AsymptoticallyRestricts (product (power U.val n) P.tensor) (copies g Q.tensor))
    {v w : ℝ}
    (hv : v = ((h : ℝ) * matrixWeight S E / matrixWeight S D) ^ (1 / (n : ℝ)))
    (hw : w = ((g : ℝ) * matrixWeight S Q / matrixWeight S P) ^ (1 / (n : ℝ))) :
    v + w ≤ orientedValue S (T.sum U) := by
  have hvpos : 0 < v := orientedGain_pos S T ⟨n, h, hn, hh, D, E, hT, hv⟩
  have hwpos : 0 < w := orientedGain_pos S U ⟨n, g, hn, hg, P, Q, hU, hw⟩
  have hy (i : Fin 2) : 0 < ![v, w] i := by fin_cases i <;> assumption
  have hbound (p : Fin 2 → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) :
      (∑ i, p i * Real.log (![v, w] i)) +
        3 * ((finiteEntropy p + ∑ i, p i * Real.log (1 : ℝ) - Real.log 1) / 3) ≤
        Real.log (orientedValue S (T.sum U)) := by
    have hb := oriented_entropy_log_bound S T U n h g hn hh hg D E P Q hT hU hv hw p hp hpsum
    convert hb using 1 <;> simp [Fin.sum_univ_two] <;> ring
  have hopt := normalizedValue_sum_le_of_entropy_bounds
    (orientedValue S (T.sum U)) ![v, w] (fun _ : Fin 2 => (1 : ℝ)) 1 3
    (lt_of_lt_of_le zero_lt_one (one_le_orientedValue S (T.sum U)))
    hy (by intro i; norm_num) (by norm_num) (by norm_num) hbound
  simpa [Fin.sum_univ_two] using hopt

/-- Independent source words give a sum bound for arbitrary actual gains. -/
theorem add_le_orientedValue_of_gains (S : InteriorSupport F) (T U : TensorOf F)
    {v w : ℝ} (hv : v ∈ orientedGains S T) (hw : w ∈ orientedGains S U) :
    v + w ≤ orientedValue S (T.sum U) := by
  obtain ⟨n, h, hn, hh, D, E, hT, hv⟩ := hv
  obtain ⟨m, g, hm, hg, P, Q, hU, hw⟩ := hw
  have hTrep := oriented_conversion_repeat T n h D E hT m
  have hUrep : AsymptoticallyRestricts (product (power U.val (n * m)) (P.power n).tensor)
      (copies (g ^ n) (Q.power n).tensor) := by
    simpa only [Nat.mul_comm m n] using oriented_conversion_repeat U m g P Q hU n
  have hhpow : 1 ≤ h ^ m := by have := pow_pos (by omega : 0 < h) m; omega
  have hgpow : 1 ≤ g ^ n := by have := pow_pos (by omega : 0 < g) n; omega
  apply sum_le_orientedValue_of_common_witnesses S T U (n * m) (h ^ m) (g ^ n)
    (Nat.mul_le_mul hn hm) hhpow hgpow (D.power m) (E.power m) (P.power n) (Q.power n)
    hTrep hUrep
  · exact hv.trans (oriented_gain_repeat S n h hn hh D E m hm).symm
  · have hnum : (((g ^ n : ℕ) : ℝ) * matrixWeight S (Q.power n) /
        matrixWeight S (P.power n)) ^ (1 / ((n * m : ℕ) : ℝ)) =
        ((g : ℝ) * matrixWeight S Q / matrixWeight S P) ^ (1 / (m : ℝ)) := by
      simpa only [Nat.mul_comm m n] using oriented_gain_repeat S m g hm hg P Q n hn
    exact hw.trans hnum.symm

/-- Superadditivity of the literal oriented value, from actual letter-word
multiplicity and its per-letter entropy rate. -/
theorem orientedValue_sum_le (S : InteriorSupport F) (T U : TensorOf F) :
    orientedValue S T + orientedValue S U ≤ orientedValue S (T.sum U) := by
  have hfixed {v : ℝ} (hv : v ∈ orientedGains S T) :
      v + orientedValue S U ≤ orientedValue S (T.sum U) := by
    have hh : orientedValue S U ≤ orientedValue S (T.sum U) - v := by
      apply csSup_le (orientedGains_nonempty S U)
      intro w hw
      apply (le_sub_iff_add_le).mpr
      simpa only [add_comm] using add_le_orientedValue_of_gains S T U hv hw
    simpa only [add_comm] using (le_sub_iff_add_le).mp hh
  apply (le_sub_iff_add_le).mp
  apply csSup_le (orientedGains_nonempty S T)
  intro v hv
  exact (le_sub_iff_add_le).mpr (hfixed hv)

end BlockIdentities.Rectangular
