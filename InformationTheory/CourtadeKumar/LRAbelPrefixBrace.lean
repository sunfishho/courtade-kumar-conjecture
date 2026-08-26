import InformationTheory.CourtadeKumar.LRScalarEndpoint

/-! The polynomial brace estimate in the audited base Abel-prefix proof. -/

open Set

namespace CourtadeKumar

noncomputable def lrAbelPrefixPoly (N : ℕ) (v : ℝ) : ℝ :=
  (N : ℝ) * (v ^ 4 + v ^ 3 - 3 * v ^ 2 - 2 * v) +
    (v ^ 4 + 4 * v ^ 3 + 5 * v ^ 2 + 2 * v)

noncomputable def lrAbelPrefixBrace (N : ℕ) (v : ℝ) : ℝ :=
  (N : ℝ) * (7 * v ^ 2 + 14 * v + 4) -
    v ^ (2 * N - 2) * lrAbelPrefixPoly N v

lemma lrAbelPrefix_base_poly_pos
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < -3 * v ^ 4 - 6 * v ^ 3 + 15 * v ^ 2 + 30 * v + 8 := by
  have h42 : v ^ 4 ≤ v ^ 2 :=
    pow_le_pow_of_le_one hv.1 hv.2 (by omega)
  have h32 : v ^ 3 ≤ v ^ 2 :=
    pow_le_pow_of_le_one hv.1 hv.2 (by omega)
  have hv2 : 0 ≤ v ^ 2 := pow_nonneg hv.1 _
  nlinarith [h42, h32, hv.1, hv2]

lemma lrAbelPrefix_increment_pos
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < -v ^ 4 - v ^ 3 + 10 * v ^ 2 + 16 * v + 4 := by
  have h42 : v ^ 4 ≤ v ^ 2 :=
    pow_le_pow_of_le_one hv.1 hv.2 (by omega)
  have h32 : v ^ 3 ≤ v ^ 2 :=
    pow_le_pow_of_le_one hv.1 hv.2 (by omega)
  have hv2 : 0 ≤ v ^ 2 := pow_nonneg hv.1 _
  nlinarith [h42, h32, hv.1, hv2]

lemma lrAbelPrefix_unweighted_gap_pos
    {N : ℕ} (hN : 2 ≤ N) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < (N : ℝ) * (7 * v ^ 2 + 14 * v + 4) -
      lrAbelPrefixPoly N v := by
  have hNReal : 2 ≤ (N : ℝ) := by exact_mod_cast hN
  have hbase := lrAbelPrefix_base_poly_pos hv
  have hinc := lrAbelPrefix_increment_pos hv
  unfold lrAbelPrefixPoly
  have hdecomp :
      (N : ℝ) * (7 * v ^ 2 + 14 * v + 4) -
          ((N : ℝ) * (v ^ 4 + v ^ 3 - 3 * v ^ 2 - 2 * v) +
            (v ^ 4 + 4 * v ^ 3 + 5 * v ^ 2 + 2 * v)) =
        (-3 * v ^ 4 - 6 * v ^ 3 + 15 * v ^ 2 + 30 * v + 8) +
          ((N : ℝ) - 2) *
            (-v ^ 4 - v ^ 3 + 10 * v ^ 2 + 16 * v + 4) := by ring
  rw [hdecomp]
  exact add_pos_of_pos_of_nonneg hbase
    (mul_nonneg (sub_nonneg.mpr hNReal) hinc.le)

/-- The brace in the differentiated prefix estimate is nonnegative for every
`N ≥ 2` and every physical `v`. -/
theorem lrAbelPrefixBrace_nonneg
    {N : ℕ} (hN : 2 ≤ N) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) :
    0 ≤ lrAbelPrefixBrace N v := by
  have hNReal : 0 ≤ (N : ℝ) := by positivity
  have hbase : 0 ≤ (N : ℝ) * (7 * v ^ 2 + 14 * v + 4) := by
    exact mul_nonneg hNReal (by nlinarith [hv.1, pow_nonneg hv.1 2])
  have hvpow0 : 0 ≤ v ^ (2 * N - 2) := pow_nonneg hv.1 _
  by_cases hP : lrAbelPrefixPoly N v ≤ 0
  · have hprod : v ^ (2 * N - 2) * lrAbelPrefixPoly N v ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hvpow0 hP
    unfold lrAbelPrefixBrace
    linarith
  · have hPpos : 0 < lrAbelPrefixPoly N v := lt_of_not_ge hP
    have hvpow1 : v ^ (2 * N - 2) ≤ 1 := pow_le_one₀ hv.1 hv.2
    have hprod :
        v ^ (2 * N - 2) * lrAbelPrefixPoly N v ≤
          lrAbelPrefixPoly N v := by
      nlinarith
    have hgap := lrAbelPrefix_unweighted_gap_pos hN hv
    unfold lrAbelPrefixBrace
    linarith

end CourtadeKumar
