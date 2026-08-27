import InformationTheory.CourtadeKumar.LRHighShapeMidpointAutoTree

/-!
# Direct-`V` fallback for midpoint leaves

On the positive-`J` chart the exact identity

`N(M/2) = V + 2 W M J`

shows that a nonnegative cancellation-safe `V` enclosure is also a valid
midpoint certificate.  This module packages midpoint and direct-`V`
acceptance as two interchangeable, independently checked leaf modes.
-/

namespace CourtadeKumar

/-- The direct corrected reserve dominates the half-midpoint target on the
relevant interior chart. -/
theorem lrCertificateUTarget_nonnegative_of_VTarget
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hV : 0 ≤ lrCertificateVTarget point) :
    0 ≤ lrCertificateUTarget point := by
  have hxPos : 0 < lrCertificateX point := by
    unfold lrCertificateX
    have hprod : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point < 1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hinterior.2.2.2 hinterior.2.1.1
        _ = lrCertificateE point := one_mul _
        _ < 1 := hinterior.2.1.2
    exact sub_pos.mpr hprod
  have hradPos : 0 < lrCertificateVRadicand point :=
    div_pos (sub_pos.mpr hinterior.2.1.2) hxPos
  have hvPos : 0 < lrCertificateV point := Real.sqrt_pos.2 hradPos
  have hM : 0 < lrCertificateM point := by
    unfold lrCertificateM
    exact div_pos hvPos (by linarith)
  have hR : lrCertificateR point ∈ Set.Ioo (0 : ℝ) 1 := by
    unfold lrCertificateR
    constructor <;> linarith [hinterior.1.1, hinterior.1.2]
  have hW : 0 < lrCertificateW point := by
    rw [lrCertificateW_eq_lrWKernel hinterior.1]
    exact lrWKernel_one_pos hR
  have hcorrection : 0 < 2 * lrCertificateW point *
      lrCertificateM point * lrCertificateJ point := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) hW) hM) hrelevant.2
  have hid := lrCertificateVTarget_eq_halfMidpoint_sub point
  have hhalf : 0 < lrCertificateHalfMidpointNumerator point := by
    nlinarith
  unfold lrCertificateUTarget lrCertificateUDenominator
  exact (div_pos hhalf
    (mul_pos hinterior.1.1 hinterior.2.1.1)).le

inductive LRHighShapeMidpointHybridAcceptData where
  | midpoint (payload : LRHighShapeMidpointCertificate)
  | directV (payload : LRHighShapeVCertificate)

namespace LRHighShapeMidpointHybridAcceptData

def check (terms : ℕ) (box : CertificateBox) :
    LRHighShapeMidpointHybridAcceptData → Bool
  | .midpoint payload =>
      LRHighShapeMidpointCertificate.accepts terms box payload
  | .directV payload => LRHighShapeVCertificate.accepts terms box payload

theorem sound (terms : ℕ) (box : CertificateBox)
    (data : LRHighShapeMidpointHybridAcceptData)
    (hcheck : data.check terms box = true) :
    ∀ point, box.Contains point → LRHighShapeVRelevant point →
      0 ≤ lrCertificateUTarget point := by
  intro point hpoint hrelevant
  cases data with
  | midpoint payload =>
      apply lrHighShapeMidpointSubdivisionCertificate_nonnegative terms
        (certificate := .accept payload) (box := box)
      · simpa [check, SubdivisionCertificate.check] using hcheck
      · exact hpoint
      · exact hrelevant
  | directV payload =>
      have hV := lrHighShapeVSubdivisionCertificate_nonnegative terms
        (certificate := .accept payload) (box := box)
        (by simpa [check, SubdivisionCertificate.check] using hcheck)
        point hpoint hrelevant
      have hpayload : LRHighShapeVCertificate.payloadCheck box payload = true := by
        have hparts :
            LRHighShapeVCertificate.payloadCheck box payload = true ∧
              (payload.enclose terms box).provesNonnegative = true := by
          simpa [check, LRHighShapeVCertificate.accepts,
            checkedEnclosureLeafAccepts] using hcheck
        exact hparts.1
      have hinteriorCheck : lrHighShapeInteriorBoxCheck box = true := by
        have hparts : lrHighShapeInteriorBoxCheck box = true ∧
            payload.check box = true := by
          simpa [LRHighShapeVCertificate.payloadCheck] using hpayload
        exact hparts.1
      exact lrCertificateUTarget_nonnegative_of_VTarget
        (lrHighShapeInteriorBoxCheck_sound hinteriorCheck hpoint)
        hrelevant hV

end LRHighShapeMidpointHybridAcceptData

/-- End-to-end soundness for subdivisions whose accepted leaves may choose
either the midpoint evaluator or the cancellation-safe direct-`V` evaluator. -/
theorem lrHighShapeMidpointHybridSubdivisionCertificate_nonnegative
    (terms : ℕ) {box : CertificateBox}
    {certificate : SubdivisionCertificate
      LRHighShapeMidpointHybridAcceptData LRHighShapeVDiscardData}
    (hcheck : certificate.check
      (LRHighShapeMidpointHybridAcceptData.check terms)
      (lrHighShapeVDiscardCheck terms) box = true) :
    ∀ point, box.Contains point → LRHighShapeVRelevant point →
      0 ≤ lrCertificateUTarget point := by
  have hstruct := subdivisionCertificate_sound
    (Relevant := LRHighShapeVRelevant)
    (Property := fun point => LRHighShapeVRelevant point →
      0 ≤ lrCertificateUTarget point)
    (acceptBox := LRHighShapeMidpointHybridAcceptData.check terms)
    (discardBox := lrHighShapeVDiscardCheck terms)
    (box := box) (certificate := certificate)
    (LRHighShapeMidpointHybridAcceptData.sound terms)
    (lrHighShapeVDiscardCheck_sound terms) hcheck
  intro point hpoint hrelevant
  exact hstruct point hpoint hrelevant hrelevant

end CourtadeKumar
