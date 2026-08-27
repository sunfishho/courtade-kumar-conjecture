import InformationTheory.CourtadeKumar.LRHybridHighShapeAssembly
import InformationTheory.CourtadeKumar.LRHighShapeMidpointVFallback
import InformationTheory.CourtadeKumar.LRHighShapeVMidpointEvaluator
import InformationTheory.CourtadeKumar.LRHighShapeVCenteredEvaluator
import InformationTheory.CourtadeKumar.LRHighShapeCenteredPairEvaluator
import InformationTheory.CourtadeKumar.LRHighShapeVZeroFaceEvaluator
import InformationTheory.CourtadeKumar.LRHighShapeTangentAutoTree

/-!
# Pointwise combined high-shape alternatives

A relevant cancellation-coordinate point is closed by either the corrected
direct reserve `V`, or by the conjunction of the exact half-midpoint and
tangent targets.  Allowing this alternative pointwise is strictly more
flexible than demanding one global proof method on the entire endpoint
chart.
-/

open Set

namespace CourtadeKumar

def LRHighShapeCertificateAlternative (point : CertificatePoint) : Prop :=
  0 ≤ lrCertificateVTarget point ∨
    (0 ≤ lrCertificateUTarget point ∧ 0 ≤ lrCertificateTTarget point)

/-- A leaf either certifies the corrected direct reserve, or certifies the
midpoint and tangent pair using one shared tangent payload. -/
inductive LRHighShapeCombinedAcceptData where
  | directV (payload : LRHighShapeVCertificate)
  | directVMidpoint (payload : LRHighShapeVCertificate)
  | directVCentered (payload : LRHighShapeVCenteredCertificate)
  | directVZeroFace (payload : LRHighShapeVZeroFaceCertificate)
  | midpointTangent (payload : LRHighShapeTangentCertificate)
  | midpointTangentCentered (payload : LRHighShapeCenteredPairCertificate)

namespace LRHighShapeCombinedAcceptData

def check (terms : ℕ) (box : CertificateBox) :
    LRHighShapeCombinedAcceptData → Bool
  | .directV payload => LRHighShapeVCertificate.rawAccepts terms box payload
  | .directVMidpoint payload =>
      LRHighShapeVCertificate.midpointAccepts terms box payload
  | .directVCentered payload =>
      LRHighShapeVCenteredCertificate.accepts terms box payload
  | .directVZeroFace payload =>
      LRHighShapeVZeroFaceCertificate.accepts terms box payload
  | .midpointTangent payload =>
      LRHighShapeMidpointCertificate.accepts terms box payload.base &&
        LRHighShapeTangentCertificate.accepts terms box payload
  | .midpointTangentCentered payload => payload.pairAccepts terms box

theorem sound (terms : ℕ) (box : CertificateBox)
    (data : LRHighShapeCombinedAcceptData)
    (hcheck : data.check terms box = true) :
    ∀ point, box.Contains point → LRHighShapeVRelevant point →
      LRHighShapeCertificateAlternative point := by
  intro point hpoint hrelevant
  cases data with
  | directV payload =>
      exact Or.inl (lrHighShapeVRawSubdivisionCertificate_nonnegative terms
        (certificate := .accept payload) (box := box)
        (by simpa [check, SubdivisionCertificate.check] using hcheck)
        point hpoint hrelevant)
  | directVMidpoint payload =>
      exact Or.inl (lrHighShapeVMidpointSubdivisionCertificate_nonnegative terms
        (certificate := .accept payload) (box := box)
        (by simpa [check, SubdivisionCertificate.check] using hcheck)
        point hpoint hrelevant)
  | directVCentered payload =>
      exact Or.inl (lrHighShapeVCenteredSubdivisionCertificate_nonnegative terms
        (certificate := .accept payload) (box := box)
        (by simpa [check, SubdivisionCertificate.check] using hcheck)
        point hpoint hrelevant)
  | directVZeroFace payload =>
      exact Or.inl (lrHighShapeVZeroFaceSubdivisionCertificate_nonnegative terms
        (certificate := .accept payload) (box := box)
        (by simpa [check, SubdivisionCertificate.check] using hcheck)
        point hpoint hrelevant)
  | midpointTangent payload =>
      have hparts :
          LRHighShapeMidpointCertificate.accepts terms box payload.base = true ∧
            LRHighShapeTangentCertificate.accepts terms box payload = true := by
        simpa [check] using hcheck
      have hU := lrHighShapeMidpointSubdivisionCertificate_nonnegative terms
        (certificate := .accept payload.base) (box := box)
        (by simpa [SubdivisionCertificate.check] using hparts.1)
        point hpoint hrelevant
      have hT := LRHighShapeTangentAutoTree.subdivisionCertificate_nonnegative
        terms (certificate := .accept payload) (box := box)
        (by simpa [SubdivisionCertificate.check] using hparts.2)
        point hpoint hrelevant
      exact Or.inr ⟨hU, hT⟩
  | midpointTangentCentered payload =>
      have hparts : payload.uAccepts terms box = true ∧
          payload.tAccepts terms box = true := by
        simpa [check, LRHighShapeCenteredPairCertificate.pairAccepts] using hcheck
      exact Or.inr ⟨
        (payload.u_pos_of_accepts terms hparts.1 hpoint).le,
        (payload.t_pos_of_accepts terms hparts.2 hpoint).le⟩

end LRHighShapeCombinedAcceptData

/-- Soundness of a subdivision that may choose the direct or paired proof
mode independently at every accepted leaf. -/
theorem lrHighShapeCombinedSubdivisionCertificate_sound
    (terms : ℕ) {box : CertificateBox}
    {certificate : SubdivisionCertificate LRHighShapeCombinedAcceptData
      LRHighShapeVDiscardData}
    (hcheck : certificate.check (LRHighShapeCombinedAcceptData.check terms)
      (lrHighShapeVDiscardCheck terms) box = true) :
    ∀ point, box.Contains point → LRHighShapeVRelevant point →
      LRHighShapeCertificateAlternative point := by
  have hstruct := subdivisionCertificate_sound
    (Relevant := LRHighShapeVRelevant)
    (Property := fun point => LRHighShapeVRelevant point →
      LRHighShapeCertificateAlternative point)
    (acceptBox := LRHighShapeCombinedAcceptData.check terms)
    (discardBox := lrHighShapeVDiscardCheck terms)
    (box := box) (certificate := certificate)
    (LRHighShapeCombinedAcceptData.sound terms)
    (lrHighShapeVDiscardCheck_sound terms) hcheck
  intro point hpoint hrelevant
  exact hstruct point hpoint hrelevant hrelevant

def LRHighShapeNearEndpointCombinedCoordinateTheorem : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    point.s < 1 / 10 →
    LRHighShapeCertificateAlternative point

/-- The compact `V` ledger together with a pointwise choice between direct
`V` and midpoint-plus-tangent closes every exact LR flow numerator. -/
theorem lrFlowNumeratorP_nonneg_target_of_compactV_and_combinedEndpoint
    (ledger : LRCompactVR910ReplayLedger)
    (hcombined : LRHighShapeNearEndpointCombinedCoordinateTheorem)
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t) :
    0 ≤ lrFlowNumeratorP R p v t := by
  by_cases htLow : t ^ 2 ≤ 17 / 20
  · exact lrFlowNumeratorP_nonneg_target_lowShape
      hR hp hv ht htLow htarget
  have htHigh : 17 / 20 ≤ t ^ 2 := by linarith
  rcases lt_trichotomy (lrFlowJ R v t) 0 with hJneg | hJzero | hJpos
  · exact lrFlowNumeratorP_nonneg_of_J_neg_target
      hR hp hv ht htarget hJneg
  · exact lrFlowNumeratorP_nonneg_of_J_eq_zero_physical
      hR hv ht hJzero
  · by_cases hvSmall : v ≤ 1 / 3
    · exact lrHighShapeSmallVNumeratorTheorem
        R p v t hR hp hv ht htHigh hvSmall hJpos htarget
    have hvHigh : 1 / 3 ≤ v := by linarith
    by_cases hcompact : R ≤ 9 / 10
    · have hV := ledger.v_nonnegative R v t hR hcompact hv hvHigh ht
        htHigh hJpos
      exact lrFlowNumeratorP_nonneg_of_J_pos_target_of_V
        hR hp hv ht htarget hJpos hV
    · have hnear : 9 / 10 < R := lt_of_not_ge hcompact
      let point := lrFlowCertificatePoint R v t
      have hinterior : LRHighShapeInterior point := by
        simpa [point] using lrFlowCertificatePoint_highShapeInterior hR hv ht
      have hrelevant : LRHighShapeVRelevant point := by
        simpa [point] using lrFlowCertificatePoint_highShapeVRelevant
          hR hv ht htHigh hvHigh hJpos
      have hsUpper : point.s < 1 / 10 := by
        change 1 - R < 1 / 10
        linarith
      rcases hcombined point hinterior hrelevant hsUpper with hV | hpair
      · have hVFlow : 0 ≤ lrLowVReserve R v t := by
          simpa [point, lrCertificateVTarget_flow hR hv ht] using hV
        exact lrFlowNumeratorP_nonneg_of_J_pos_target_of_V
          hR hp hv ht htarget hJpos hVFlow
      · have hU : 0 ≤ lrHighShapeUCertificateTarget point := by
          rw [← lrCertificateUTarget_eq_highShapeTarget
            hinterior.1 hinterior.2.1
            ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩]
          exact hpair.1
        have hvtPos : 0 < v * t := mul_pos hv.1 ht.1
        have hvtLt : v * t < 1 := calc
          v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
          _ < 1 := by simpa using ht.2
        have hePos : 0 < 1 - v ^ 2 * t ^ 2 := by
          nlinarith [sq_pos_of_pos hvtPos]
        have hhalf := lrFlowHalfMidpoint_nonneg_of_certificateTarget
          hR hv.1 ht.1 hePos hU
        have hTCoordinate :
            0 ≤ lrHighShapeTCertificateTarget point := by
          rw [← lrCertificateTTarget_eq_highShapeTarget
            hinterior.1 hinterior.2.1
            ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩]
          exact hpair.2
        have hT : 0 ≤ lrFlowTReserve R v t := by
          have hRNe : R ≠ 1 := hR.2.ne
          simpa [point, lrHighShapeTCertificateTarget_flow hRNe
            hePos.ne' hv.1 ht.1] using hTCoordinate
        exact lrFlowNumeratorP_nonneg_of_J_pos_target_of_halfMidpoint_T
          hR hp hv ht htarget hJpos hhalf hT

/-- Differential closure from the compact ledger and the pointwise
near-endpoint alternative.  In particular, no global midpoint theorem and
no global tangent theorem are assumed separately. -/
theorem hasDerivAt_lrReserve_exactFlow_of_compactV_and_combinedEndpoint
    (ledger : LRCompactVR910ReplayLedger)
    (hcombined : LRHighShapeNearEndpointCombinedCoordinateTheorem)
    {R p v v' t : ℝ} {vfun : ℝ → ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hvval : vfun R = v) (hvfun : HasDerivAt vfun v' R)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t)
    (hcurve :
      (fun y : ℝ ↦ lrSquareTarget y (vfun y) t) =ᶠ[nhds R]
        (fun y : ℝ ↦ lrSquareObjective y (lrProbabilityToOdds p))) :
    HasDerivAt
        (fun y : ℝ ↦
          lrSquareReserve y (lrProbabilityToOdds p) (vfun y) t)
        (lrFlowNumerator R (lrProbabilityToOdds p) v t /
          (lrFlowB R v t * (1 - R) ^ 2 * t ^ 2)) R ∧
      0 ≤ lrFlowNumerator R (lrProbabilityToOdds p) v t /
        (lrFlowB R v t * (1 - R) ^ 2 * t ^ 2) := by
  have hu := lrProbabilityToOdds_mem_Ioo hp
  have hvt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hroot : lrGShape (Real.sqrt R * t) v =
      lrObjectiveTarget (Real.sqrt R) (lrProbabilityToOdds p) := by
    calc
      lrGShape (Real.sqrt R * t) v = lrSquareTarget R v t := rfl
      _ = lrPrefixEll R p := htarget.symm
      _ = lrObjectiveTarget (Real.sqrt R) (lrProbabilityToOdds p) :=
        lrPrefixEll_eq_lrObjectiveTarget hR hp
  have hderiv := hasDerivAt_lrReserve_exactFlow hR hu.1 hv.1 ht hvt
    hvval hvfun hroot hcurve
  have hpOdds : lrFlowP (lrProbabilityToOdds p) = p := by
    simpa [lrFlowP, lrOddsToProbability] using
      lrOddsToProbability_probabilityToOdds
        (show p < 1 from hp.2.trans (by norm_num))
  have hnumP :=
    lrFlowNumeratorP_nonneg_target_of_compactV_and_combinedEndpoint
      ledger hcombined hR
      (show p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ) from ⟨hp.1, hp.2.le⟩)
      hv ht htarget
  have hnum : 0 ≤ lrFlowNumerator R (lrProbabilityToOdds p) v t := by
    rw [lrFlowNumerator_eq_p, hpOdds]
    exact hnumP
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hshape : Real.sqrt R * v * t < 1 := by
    rw [mul_assoc]
    calc
      Real.sqrt R * (v * t) < 1 * (v * t) :=
        mul_lt_mul_of_pos_right hsqrtLt (mul_pos hv.1 ht.1)
      _ < 1 := by simpa using hvt
  have hB : 0 < lrFlowB R v t := lrFlowB_pos hv.1 ht.1.le hshape
  have hden : 0 < lrFlowB R v t * (1 - R) ^ 2 * t ^ 2 :=
    mul_pos (mul_pos hB (sq_pos_of_pos (sub_pos.mpr hR.2)))
      (sq_pos_of_pos ht.1)
  exact ⟨hderiv, div_nonneg hnum hden.le⟩

end CourtadeKumar
