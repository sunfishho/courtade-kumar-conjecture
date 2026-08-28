import InformationTheory.CourtadeKumar.LRDeterminantPositiveFactors
import InformationTheory.CourtadeKumar.LRSmallSBridgeRemainderIdentification
import InformationTheory.CourtadeKumar.LRAbelElementaryBounds

/-!
# Analytic primitives for the determinant tails

This file formalizes the exact entropy-remainder identity for `W₁` and the
two quantitative lower bounds used in (DA6a) and the deep-tail bridge.  The
proofs use ordinary real analysis plus rational bounds on `log 2`; no
numerical decision procedure is involved.
-/

open Set

namespace CourtadeKumar

/-- The exact radial remainder identity
`W₁ = s/4 + r₀(s) - s r₀'(s)`. -/
theorem lrCertificateW_eq_quarter_add_remainder
    {point : CertificatePoint} (hs : 0 < point.s) :
    lrCertificateW point =
      point.s / 4 + lrLowerFaceR0 point.s -
        point.s * lrLowerFaceR0Prime point.s := by
  unfold lrCertificateW
  rw [lrCertificateOmega_eq_lowerFace_split,
    lrLowerFaceOmegaQ0_zero hs]
  unfold lrLowerFaceOmegaR0 lrCertificateB
  simp only [mul_zero, sub_zero, add_zero, lrLowerFaceR0_zero]
  ring

/-- Structural normalized lower bound obtained by discarding
`r₀(s) ≥ 0`. -/
theorem lrCertificateW_normalized_lower
    {point : CertificatePoint} (hs : point.s ∈ Ioo (0 : ℝ) 1) :
    1 - 4 * lrLowerFaceR0Prime point.s ≤
      4 * lrCertificateW point / point.s := by
  have hr := lrLowerFaceR0_nonneg hs
  have hid := lrCertificateW_eq_quarter_add_remainder
    (point := point) hs.1
  rw [le_div_iff₀ hs.1]
  rw [hid]
  nlinarith

/-- The elementary endpoint comparison used to control
`s * log (4/s)` on a small interval. -/
lemma mul_log_four_div_le_endpoint
    {s a : ℝ} (hs : 0 < s) (ha : 0 < a) (hsa : s ≤ a)
    (hlog : 1 ≤ Real.log (4 / a)) :
    s * Real.log (4 / s) ≤ a * Real.log (4 / a) := by
  have hsNe := hs.ne'
  have haNe := ha.ne'
  let u : ℝ := a / s
  have hu : 1 ≤ u := by
    unfold u
    rw [le_div_iff₀ hs]
    simpa using hsa
  have huPos : 0 < u := zero_lt_one.trans_le hu
  have hfactor : 4 / s = (4 / a) * u := by
    unfold u
    field_simp [hsNe, haNe]
  have hbasePos : 0 < 4 / a := div_pos (by norm_num) ha
  have hlogSplit :
      Real.log (4 / s) = Real.log (4 / a) + Real.log u := by
    rw [hfactor, Real.log_mul hbasePos.ne' huPos.ne']
  have hlogU := Real.log_le_sub_one_of_pos huPos
  have hscaled := mul_le_mul_of_nonneg_left hlogU hs.le
  have hsu : s * u = a := by
    unfold u
    field_simp [hsNe]
  rw [mul_sub, mul_one, hsu] at hscaled
  have hendpoint := mul_le_mul_of_nonneg_right hsa
    (sub_nonneg.mpr hlog)
  rw [hlogSplit]
  nlinarith

/-- The continuation-tail estimate in (DA6a). -/
theorem lrCertificateW_normalized_gt_299_div_320
    {point : CertificatePoint}
    (hs : point.s ∈ Ioc (0 : ℝ) (1 / 128 : ℝ)) :
    299 / 320 < 4 * lrCertificateW point / point.s := by
  have hsUnit : point.s ∈ Ioo (0 : ℝ) 1 :=
    ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  have hsSixteenth : point.s ∈ Ioo (0 : ℝ) (1 / 16 : ℝ) :=
    ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  have hlogEndpoint :
      Real.log (4 / (1 / 128 : ℝ)) = 9 * Real.log 2 := by
    rw [show (4 / (1 / 128 : ℝ)) = 2 ^ 9 by norm_num,
      Real.log_pow]
    norm_num
  have hendpointOne : 1 ≤ Real.log (4 / (1 / 128 : ℝ)) := by
    rw [hlogEndpoint]
    nlinarith [Real.log_two_gt_d9]
  have hmulLog := mul_log_four_div_le_endpoint hs.1
    (by norm_num : (0 : ℝ) < 1 / 128) hs.2 hendpointOne
  rw [hlogEndpoint] at hmulLog
  have hprime := lrLowerFaceR0Prime_upper hsSixteenth
  have hfourPrime : 4 * lrLowerFaceR0Prime point.s < 21 / 320 := by
    have hscaledPrime := mul_le_mul_of_nonneg_left hprime
      (by norm_num : (0 : ℝ) ≤ 4)
    have hscaledLog := mul_le_mul_of_nonneg_left hmulLog
      (by norm_num : (0 : ℝ) ≤ 4 / 3)
    have hlogUpper : Real.log 2 < 7 / 10 := by
      nlinarith [Real.log_two_lt_d9]
    calc
      4 * lrLowerFaceR0Prime point.s ≤
          4 * (point.s / 3 * Real.log (4 / point.s)) :=
        hscaledPrime
      _ = 4 / 3 * (point.s * Real.log (4 / point.s)) := by ring
      _ ≤ 4 / 3 * ((1 / 128 : ℝ) * (9 * Real.log 2)) := hscaledLog
      _ < 21 / 320 := by nlinarith
  have hW := lrCertificateW_normalized_lower hsUnit
  linarith

/-- The sharper deep-tail estimate used for `s ≤ 2⁻¹⁴`. -/
theorem lrCertificateW_normalized_gt_999_div_1000
    {point : CertificatePoint}
    (hs : point.s ∈ Ioc (0 : ℝ) (1 / 16384 : ℝ)) :
    999 / 1000 < 4 * lrCertificateW point / point.s := by
  have hsUnit : point.s ∈ Ioo (0 : ℝ) 1 :=
    ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  have hsSixteenth : point.s ∈ Ioo (0 : ℝ) (1 / 16 : ℝ) :=
    ⟨hs.1, hs.2.trans_lt (by norm_num)⟩
  have hlogEndpoint :
      Real.log (4 / (1 / 16384 : ℝ)) = 16 * Real.log 2 := by
    rw [show (4 / (1 / 16384 : ℝ)) = 2 ^ 16 by norm_num,
      Real.log_pow]
    norm_num
  have hendpointOne : 1 ≤ Real.log (4 / (1 / 16384 : ℝ)) := by
    rw [hlogEndpoint]
    nlinarith [Real.log_two_gt_d9]
  have hmulLog := mul_log_four_div_le_endpoint hs.1
    (by norm_num : (0 : ℝ) < 1 / 16384) hs.2 hendpointOne
  rw [hlogEndpoint] at hmulLog
  have hprime := lrLowerFaceR0Prime_upper hsSixteenth
  have hfourPrime : 4 * lrLowerFaceR0Prime point.s < 1 / 1000 := by
    have hscaledPrime := mul_le_mul_of_nonneg_left hprime
      (by norm_num : (0 : ℝ) ≤ 4)
    have hscaledLog := mul_le_mul_of_nonneg_left hmulLog
      (by norm_num : (0 : ℝ) ≤ 4 / 3)
    calc
      4 * lrLowerFaceR0Prime point.s ≤
          4 * (point.s / 3 * Real.log (4 / point.s)) :=
        hscaledPrime
      _ = 4 / 3 * (point.s * Real.log (4 / point.s)) := by ring
      _ ≤ 4 / 3 * ((1 / 16384 : ℝ) * (16 * Real.log 2)) := hscaledLog
      _ < 1 / 1000 := by
        nlinarith [lr_log_two_lt_three_quarters]
  have hW := lrCertificateW_normalized_lower hsUnit
  linarith

end CourtadeKumar
