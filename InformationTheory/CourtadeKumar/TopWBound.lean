import InformationTheory.CourtadeKumar.TopLogBound
import InformationTheory.CourtadeKumar.TopPhiSeries

/-! The rational replacement of `log 2` in the eight-term `w(R)`
truncation used by the full-cap certificate. -/

open Set
open scoped BigOperators

namespace CourtadeKumar

noncomputable def topWCoeff (j : ℕ) : ℝ :=
  Real.log 2 -
    ∑ m ∈ Finset.range j,
      (1 : ℝ) / (2 * (m + 1) * (2 * (m + 1) - 1))

noncomputable def topW8Series (R : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 8, topWCoeff (j + 1) * R ^ (j + 1)

/-- After the first eight `w` coefficients, the numerator remainder is
nonnegative.  It is the positive coefficient tail weighted by
`R⁹ - Rᵐ`, with `m ≥ 10`. -/
lemma topW8_numerator_remainder_nonneg {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    0 ≤ topWCoeff 9 * R ^ 9 -
      (topPhi (Real.sqrt R) - ∑ n ∈ Finset.range 9,
        R ^ (n + 1) / (2 * (n + 1) * (2 * (n + 1) - 1))) := by
  have hc := (top_hasSum_phiCoefficients_tail 9).mul_left (R ^ 9)
  have hp := topPhi_sqrt_tail_hasSum hR 9
  have hd := hc.sub hp
  have hnonneg : ∀ n : ℕ, 0 ≤
      R ^ 9 * ((1 : ℝ) /
        (2 * (n + 9 + 1) * (2 * (n + 9 + 1) - 1))) -
      R ^ (n + 9 + 1) /
        (2 * (n + 9 + 1) * (2 * (n + 9 + 1) - 1)) := by
    intro n
    have hpow : R ^ (n + 9 + 1) ≤ R ^ 9 :=
      pow_le_pow_of_le_one hR.1.le hR.2.le (by omega)
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have ha : 0 ≤ (1 : ℝ) /
        (2 * (n + 9 + 1) * (2 * (n + 9 + 1) - 1)) := by
      apply one_div_nonneg.mpr
      apply mul_nonneg
      · positivity
      · nlinarith
    calc
      0 ≤ ((1 : ℝ) /
          (2 * (n + 9 + 1) * (2 * (n + 9 + 1) - 1))) *
            (R ^ 9 - R ^ (n + 9 + 1)) := mul_nonneg ha (sub_nonneg.mpr hpow)
      _ = _ := by ring
  have hscalar :
      0 ≤ R ^ 9 *
          (Real.log 2 - ∑ n ∈ Finset.range 9,
            (1 : ℝ) / (2 * (n + 1) * (2 * (n + 1) - 1))) -
        (topPhi (Real.sqrt R) - ∑ n ∈ Finset.range 9,
          R ^ (n + 1) / (2 * (n + 1) * (2 * (n + 1) - 1))) := by
    rw [← hd.tsum_eq]
    exact tsum_nonneg hnonneg
  convert hscalar using 1
  all_goals simp [topWCoeff] <;> ring

/-- The exact analytic channel ratio dominates its first eight positive
`R`-series terms. -/
theorem topW8Series_le_capRatio {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    topW8Series R ≤
      (R * Real.log 2 - topPhi (Real.sqrt R)) / (1 - R) := by
  have hrem := topW8_numerator_remainder_nonneg hR
  have hid :
      R * Real.log 2 - topPhi (Real.sqrt R) -
          (1 - R) * topW8Series R =
        topWCoeff 9 * R ^ 9 -
          (topPhi (Real.sqrt R) - ∑ n ∈ Finset.range 9,
            R ^ (n + 1) / (2 * (n + 1) * (2 * (n + 1) - 1))) := by
    norm_num [topW8Series, topWCoeff, Finset.sum_range_succ]
    ring
  have hnum :
      0 ≤ R * Real.log 2 - topPhi (Real.sqrt R) -
        (1 - R) * topW8Series R := by
    rw [hid]
    exact hrem
  rw [le_div_iff₀ (sub_pos.mpr hR.2)]
  nlinarith

lemma logTwo_ge_certificateLower :
    (6931 : ℝ) / 10000 ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

lemma topWCoeff_ge_certificateCoeff (j : Fin 8) :
    (#[1931 / 10000, 3293 / 30000, 2293 / 30000,
        12301 / 210000, 29903 / 630000, 276433 / 6930000,
        3098629 / 90090000, 1361627 / 45045000] : Array ℚ)[j.val] ≤
      topWCoeff (j.val + 1) := by
  fin_cases j <;>
    norm_num [topWCoeff, Finset.sum_range_succ] <;>
    linarith [logTwo_ge_certificateLower]

/-- Replacing `log 2` by `6931/10000` in the first eight positive-series
coefficients can only decrease the truncation on `R ≥ 0`. -/
theorem topCertW8_le_topW8Series {c z : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    topCertW8 c z ≤ topW8Series (topCertR c z) := by
  have hR : 0 ≤ topCertR c z := by
    have hc2 : c ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc.2)
        (add_nonneg hc.1 zero_le_one)]
    unfold topCertR
    nlinarith [mul_nonneg (sq_nonneg c) hz.1]
  have hdelta : 0 ≤ Real.log 2 - (6931 : ℝ) / 10000 := by
    linarith [logTwo_ge_certificateLower]
  have hsum :
      0 ≤ ∑ j ∈ Finset.range 8, topCertR c z ^ (j + 1) := by
    positivity
  have hid :
      topW8Series (topCertR c z) - topCertW8 c z =
        (Real.log 2 - (6931 : ℝ) / 10000) *
          ∑ j ∈ Finset.range 8, topCertR c z ^ (j + 1) := by
    norm_num [topW8Series, topWCoeff, topCertW8,
      Finset.sum_range_succ]
    ring
  nlinarith [mul_nonneg hdelta hsum]

theorem topFiniteClaim_with_W8Series {c z e : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1)
    (he : topCertEnum c z / topCertR c z ^ 9 ≤ e) :
    (1 : ℝ) / 100 ≤
      topW8Series (topCertR c z) +
        Real.log (topCertX c z) / (2 * c ^ 2 * topCapQ c z) + e := by
  exact topFiniteClaim_of_analytic_bounds hc hz
    (topCertW8_le_topW8Series ⟨hc.1.le, hc.2.le⟩ ⟨hz.1.le, hz.2.le⟩) he

/-- The finite TOP certificate with its polynomial `w` surrogate replaced
by the genuine analytic cap ratio. -/
theorem topFiniteClaim_with_capRatio {c z e : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1)
    (he : topCertEnum c z / topCertR c z ^ 9 ≤ e) :
    (1 : ℝ) / 100 ≤
      (topCertR c z * Real.log 2 - topPhi (Real.sqrt (topCertR c z))) /
          (1 - topCertR c z) +
        Real.log (topCertX c z) / (2 * c ^ 2 * topCapQ c z) + e := by
  exact topFiniteClaim_of_analytic_bounds hc hz
    ((topCertW8_le_topW8Series ⟨hc.1.le, hc.2.le⟩ ⟨hz.1.le, hz.2.le⟩).trans
      (topW8Series_le_capRatio (topCertR_mem_Ioo hc hz))) he

end CourtadeKumar
