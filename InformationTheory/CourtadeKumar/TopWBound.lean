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

end CourtadeKumar
