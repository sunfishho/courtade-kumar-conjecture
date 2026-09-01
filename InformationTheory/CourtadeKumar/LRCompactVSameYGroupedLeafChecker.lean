import InformationTheory.CourtadeKumar.LRCompactVLambdaGroupedLeafChecker
import InformationTheory.CourtadeKumar.LRCompactVSameYLambda

/-!
# Same-`y` grouped compact-`V` leaves

These leaves replace the independent `D_lower/B_upper` ratio by the sharper
same-endpoint ratio at `(R_hi,v_hi,y_lo)`.  The payload keeps only the checked
range reduction for `log(1+v_hi)` and the adaptive grouped-head choice.
-/

set_option autoImplicit false

namespace CourtadeKumar

structure LRCompactVSameYGroupedLeafCertificate where
  logOnePlusVHi : RationalEnclosure.LogRangeCertificate
  headChoice : LRCompactVLambdaGroupedHeadChoice

namespace LRCompactVSameYGroupedLeafCertificate

def bEndpoint
    (logTerms dTerms : ℕ) (box : CertificateBox)
    (certificate : LRCompactVSameYGroupedLeafCertificate) :
    RationalEnclosure :=
  lrCompactVSameYBEndpointEnclosure logTerms dTerms box
    certificate.logOnePlusVHi

def lambda
    (logTerms dTerms : ℕ) (box : CertificateBox)
    (certificate : LRCompactVSameYGroupedLeafCertificate) : ℚ :=
  lrCompactVSameYLambda
    (certificate.bEndpoint logTerms dTerms box)
    (lrCompactVDirectDEnclosure dTerms box)

def groupedLower
    (logTerms wTerms dTerms : ℕ) (box : CertificateBox)
    (certificate : LRCompactVSameYGroupedLeafCertificate) : ℚ :=
  let wOne := lrCompactVWOneEnclosure logTerms wTerms box
  lrCompactVLambdaGroupedFiniteLower certificate.headChoice.headN
    (certificate.lambda logTerms dTerms box) box wOne

def check
    (logTerms wTerms dTerms : ℕ) (box : CertificateBox)
    (certificate : LRCompactVSameYGroupedLeafCertificate) : Bool :=
  let bEndpoint := certificate.bEndpoint logTerms dTerms box
  let lambda := certificate.lambda logTerms dTerms box
  decide (
    certificate.logOnePlusVHi.check (1 + box.kHi) = true ∧
    LRCompactVDirectDValid.check box = true ∧
    0 < bEndpoint.upper ∧
    lambda * box.sHi * (1 - lrCompactVDirectDYLoQ box) ≤
      1 - box.sHi ∧
    0 ≤ certificate.groupedLower logTerms wTerms dTerms box)

theorem sound
    (logTerms wTerms dTerms : ℕ)
    {box : CertificateBox}
    {certificate : LRCompactVSameYGroupedLeafCertificate}
    (hcheck : certificate.check logTerms wTerms dTerms box = true) :
    ∀ point, box.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point := by
  have hparts :
      certificate.logOnePlusVHi.check (1 + box.kHi) = true ∧
      LRCompactVDirectDValid.check box = true ∧
      0 < (certificate.bEndpoint logTerms dTerms box).upper ∧
      certificate.lambda logTerms dTerms box * box.sHi *
          (1 - lrCompactVDirectDYLoQ box) ≤ 1 - box.sHi ∧
      0 ≤ certificate.groupedLower logTerms wTerms dTerms box := by
    simpa [check] using hcheck
  have hvalid := LRCompactVDirectDValid.of_check hparts.2.1
  have hbox := hvalid.1
  intro point hpoint hphysical
  have hinterior := hphysical.1
  let t := Real.sqrt point.chi
  have ht : t ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 hinterior.2.2.1
    · simpa [t] using
        (Real.sqrt_lt_sqrt_iff hinterior.2.2.1.le).2
          hinterior.2.2.2
  have hsquare : t ^ 2 = point.chi :=
    Real.sq_sqrt hinterior.2.2.1.le
  let bEndpoint := certificate.bEndpoint logTerms dTerms box
  let d := lrCompactVDirectDEnclosure dTerms box
  let lambda := certificate.lambda logTerms dTerms box
  let wOne := lrCompactVWOneEnclosure logTerms wTerms box
  have hwOne : wOne.Contains (lrWKernel point.s 1) := by
    dsimp [wOne]
    exact lrCompactVWOneEnclosure_sound
      logTerms wTerms hbox hpoint hinterior
  have hlambdaQ : (0 : ℚ) ≤ lambda := by
    dsimp [lambda, LRCompactVSameYGroupedLeafCertificate.lambda, d,
      bEndpoint]
    exact lrCompactVSameYLambda_nonnegative hparts.2.2.1
  have hlambda : (0 : ℝ) ≤ lambda := by exact_mod_cast hlambdaQ
  have hfinite := lrCompactVLambdaGroupedFiniteLower_le
    (N := certificate.headChoice.headN)
    hlambdaQ hbox hpoint hinterior hwOne
  have hanalytic := lrCompactVLambdaGroupedFinite_le
    hinterior.1 hinterior.2.1 ht hlambda
    certificate.headChoice.headN
  have hbound :
      (lrCompactVLambdaGroupedFiniteLower
          certificate.headChoice.headN lambda box wOne : ℝ) ≤
        (lrFlowPW point.s point.k t -
          4 * lrWKernel point.s 1 *
            (point.k * t ^ 2 / (1 + point.k))) +
          (lambda : ℝ) * lrFlowC point.s point.k t := by
    exact hfinite.trans (by simpa [hsquare] using hanalytic)
  have hlowerReal :
      (0 : ℝ) ≤ certificate.groupedLower
        logTerms wTerms dTerms box := by
    exact_mod_cast hparts.2.2.2.2
  have hQlambda :
      0 ≤
        (lrFlowPW point.s point.k t -
          4 * lrWKernel point.s 1 *
            (point.k * t ^ 2 / (1 + point.k))) +
          (lambda : ℝ) * lrFlowC point.s point.k t := by
    dsimp [groupedLower, lambda, wOne] at hlowerReal
    exact hlowerReal.trans hbound
  have hBPos : 0 < lrFlowB point.s point.k t := by
    apply lrFlowB_pos hinterior.2.1.1 ht.1.le
    have hsqrtR : Real.sqrt point.s < 1 := by
      simpa using (Real.sqrt_lt_sqrt_iff hinterior.1.1.le).2
        hinterior.1.2
    calc
      Real.sqrt point.s * point.k * t < 1 * point.k * t := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hsqrtR hinterior.2.1.1) ht.1
      _ < 1 := by
        have := mul_lt_mul_of_pos_right hinterior.2.1.2 ht.1
        nlinarith [ht.2]
  have hlambdaB :
      (lambda : ℝ) * lrFlowB point.s point.k t ≤
        lrFlowD point.s point.k t := by
    dsimp [lambda, bEndpoint, d, t,
      LRCompactVSameYGroupedLeafCertificate.lambda]
    exact lrCompactVSameYLambda_mul_flowB_le_flowD
      logTerms dTerms dTerms hvalid hpoint hinterior
        hparts.1 hparts.2.2.1 hparts.2.2.2.1
  have hC0 := lrFlowC_nonneg_of_compact_series
    hinterior.1 hinterior.2.1 ht
  have htotal :
      0 ≤
        lrFlowB point.s point.k t *
          (lrFlowPW point.s point.k t -
            4 * lrWKernel point.s 1 *
              (point.k * t ^ 2 / (1 + point.k))) +
        lrFlowD point.s point.k t *
          lrFlowC point.s point.k t := by
    calc
      0 ≤
          lrFlowB point.s point.k t *
              ((lrFlowPW point.s point.k t -
                4 * lrWKernel point.s 1 *
                  (point.k * t ^ 2 / (1 + point.k))) +
                (lambda : ℝ) * lrFlowC point.s point.k t) +
            (lrFlowD point.s point.k t -
                (lambda : ℝ) * lrFlowB point.s point.k t) *
              lrFlowC point.s point.k t :=
        add_nonneg
          (mul_nonneg hBPos.le hQlambda)
          (mul_nonneg (sub_nonneg.mpr hlambdaB) hC0)
      _ =
          lrFlowB point.s point.k t *
            (lrFlowPW point.s point.k t -
              4 * lrWKernel point.s 1 *
                (point.k * t ^ 2 / (1 + point.k))) +
          lrFlowD point.s point.k t *
            lrFlowC point.s point.k t := by ring
  have hvNe : point.k ≠ -1 := by linarith [hinterior.2.1.1]
  rw [lrCompactVReserveTarget,
    lrLowVReserve_eq_compact_grouped hvNe]
  exact htotal

end LRCompactVSameYGroupedLeafCertificate

end CourtadeKumar
