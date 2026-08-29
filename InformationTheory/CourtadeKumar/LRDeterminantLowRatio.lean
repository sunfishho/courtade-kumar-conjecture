import InformationTheory.CourtadeKumar.LRDeterminantRegionAssembly
import InformationTheory.CourtadeKumar.LRDeterminantThickReserve
import InformationTheory.CourtadeKumar.LRHighShapeVEvaluator
import InformationTheory.CourtadeKumar.LRCompactVCorrelatedReplayLedger

/-!
# Direct closure of the determinant low-ratio strip from the audited `V` reserve

The exceptional strip `1/4 < K = k/s ≤ 1` is not one of the ten
determinant-ledger rows.  In the audited manuscript it is closed by (M44):
the outer-midpoint reserve `V` is nonnegative there.  The original tangent
determinant is

`H_d * V + J * mu' * F`.

Every other factor is nonnegative on the regular relevant chart.  Thus the
low-ratio obligation reduces exactly to the already audited low-`K`
`V` certificate.  The lemmas below kernel-check this reduction and isolate
the two genuine certificate inputs in (M41)--(M44): an analytic first-bracket
certificate below `s = 2^-14` and a finite direct-`V` certificate above it.
-/

namespace CourtadeKumar

/-- The manuscript quantity called `s² V` is exactly the numerator used in
the determinant normalization. -/
theorem lrDeterminantV_nonnegative_of_VTarget
    {point : CertificatePoint}
    (hV : 0 ≤ lrCertificateVTarget point) :
    0 ≤ lrDeterminantV point := by
  unfold lrDeterminantV
  exact div_nonneg (by simpa [lrCertificateVTarget] using hV)
    (sq_nonneg point.s)

/-- Coordinate form of the exact decomposition (M40): the direct `V` target
is the stronger first bracket plus the nonnegative `D-D₁` correction. -/
theorem lrCertificateVTarget_eq_firstBracket_add
    {point : CertificatePoint}
    (hvPlus : 1 + lrCertificateV point ≠ 0) :
    lrCertificateVTarget point =
      lrDeterminantFirstBracket
        (lrCertificateBFlow point) (lrDeterminantD1 point)
        (lrCertificateGShape point) (lrDeterminantPsi point)
        (lrDeterminantDelta point) (lrCertificateW point) +
      (lrCertificateD point - lrDeterminantD1 point) *
        lrDeterminantPsi point := by
  unfold lrCertificateVTarget
  rw [lrCertificateMidpointNumerator_eq_determinant_brackets hvPlus]
  unfold lrDeterminantFirstBracket
  ring

/-- The Wronskian bound also records the elementary sign of `Psi` needed in
(M40). -/
theorem lrDeterminantPsi_nonnegative
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 ≤ lrDeterminantPsi point := by
  have hs : 0 < point.s := hinterior.1.1
  have hR : 0 < lrCertificateR point := by
    unfold lrCertificateR
    linarith [hinterior.1.2]
  have hHd : 0 < lrDeterminantHd point :=
    lrDeterminantHd_pos hinterior
  have hW : 0 ≤ lrCertificateW point :=
    (lrCertificateW_pos hinterior).le
  have hgap : 0 ≤ lrCertificateGap point :=
    lrCertificateGap_nonnegative hinterior
  have hc0 : 0 ≤ lrDeterminantC0 point :=
    lrDeterminantC0_nonnegative hs hHd hR.le hW
  have hT : 0 ≤ lrDeterminantT point :=
    lrDeterminantT_nonnegative hR hgap
  have hlog : 0 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlhs : 0 ≤
      12 * Real.log 2 * lrDeterminantC0 point *
        lrDeterminantT point := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hlog) hc0) hT
  exact hlhs.trans (lrCertificateDeterminantWronskian hinterior)

/-- Therefore the analytic first bracket (M42) really does prove the
direct `V` target asserted in (M44), rather than merely bypassing it through
the determinant ledger. -/
theorem lrCertificateVTarget_nonnegative_of_firstBracket
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hfirst : LRDeterminantFirstBracketAt point) :
    0 ≤ lrCertificateVTarget point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have hid := lrCertificateVTarget_eq_firstBracket_add
    (point := point) (by linarith [hv.1])
  have hcorrection : 0 ≤
      (lrCertificateD point - lrDeterminantD1 point) *
        lrDeterminantPsi point :=
    mul_nonneg (sub_nonneg.mpr (lrDeterminantD1_le_D hinterior))
      (lrDeterminantPsi_nonnegative hinterior)
  rw [hid]
  exact add_nonneg hfirst hcorrection

/-- Direct form of the final sentence after (M44): nonnegativity of the
outer-midpoint `V` reserve makes the original tangent determinant, and hence
the cancellation-coordinate tangent target, nonnegative.  This statement
does not use the low-ratio bounds themselves. -/
theorem lrCertificateTTarget_nonnegative_of_VTarget
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hV : 0 ≤ lrCertificateVTarget point) :
    0 ≤ lrCertificateTTarget point := by
  have hdetV : 0 ≤ lrDeterminantV point :=
    lrDeterminantV_nonnegative_of_VTarget hV
  have hHd : 0 ≤ lrDeterminantHd point :=
    (lrDeterminantHd_pos hinterior).le
  have hmu : 0 ≤ lrDeterminantMuPrime point :=
    lrDeterminantMuPrime_nonnegative (lrCertificateW_pos hinterior).le
  have hF : 0 ≤ lrDeterminantF point :=
    lrDeterminantF_nonnegative hinterior.1.1
      (lrCertificateGap_nonnegative hinterior)
  have horiginal : 0 ≤ lrOriginalTangentDeterminant
      (lrDeterminantHd point) (lrDeterminantV point)
      (lrCertificateJ point) (lrDeterminantMuPrime point)
      (lrDeterminantF point) := by
    unfold lrOriginalTangentDeterminant
    exact add_nonneg (mul_nonneg hHd hdetV)
      (mul_nonneg (mul_nonneg hrelevant.2.le hmu) hF)
  exact lrCertificateTTarget_nonnegative_of_originalDeterminant
    hinterior.1.1 horiginal

/-- A convenient globally quantified `V`-target interface.  It is stronger
than the manuscript's near-endpoint (M44) statement; the faithful near/far
assembly below does not assume this global form. -/
def LRDeterminantLowRatioVTargetTheorem : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantLowRatioRegion point →
    0 ≤ lrCertificateVTarget point

/-- An (M44) `V` certificate closes the complete direct low-ratio tangent
obligation used by `LRDeterminantRegionLedger`. -/
theorem lrDeterminantLowRatioTangentTheorem_of_VTarget
    (hV : LRDeterminantLowRatioVTargetTheorem) :
    LRDeterminantLowRatioTangentTheorem := by
  intro point hinterior hrelevant hregion
  exact lrCertificateTTarget_nonnegative_of_VTarget hinterior hrelevant
    (hV point hinterior hrelevant hregion)

/-- The analytic part of the audited low-ratio proof, corresponding to
(M41)--(M42), proves the stronger first bracket for `s ≤ 2^-14`. -/
def LRDeterminantLowRatioSmallSFirstBracketTheorem : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantLowRatioRegion point →
    point.s ≤ 1 / 16384 →
    LRDeterminantFirstBracketAt point

/-- The finite part of (M44) checks the stronger exact `V` target on the
closed complementary slab `2^-14 ≤ s ≤ 1/10`.  The upper bound is already
part of the near-endpoint calling context and is not needed by this adapter. -/
def LRDeterminantLowRatioFiniteVTargetTheorem : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    LRDeterminantLowRatioRegion point →
    1 / 16384 ≤ point.s →
    point.s ≤ 1 / 10 →
    0 ≤ lrCertificateVTarget point

/-- The exact low-ratio obligation used inside the near-endpoint chart.  The
`s < 1/10` argument is essential: it is present in (M44), even though the
older global `LRDeterminantLowRatioTangentTheorem` interface does not expose
it. -/
def LRDeterminantNearEndpointLowRatioTangentTheorem : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    point.s < 1 / 10 →
    LRDeterminantLowRatioRegion point →
    0 ≤ lrCertificateTTarget point

/-- Complementary input needed only because the existing ledger's low-ratio
field is globally quantified.  In the manuscript this is the compact
`R ≤ 9/10` theorem (M51), since `s = 1-R ≥ 1/10`. -/
def LRDeterminantFarChannelLowRatioTangentTheorem : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    1 / 10 ≤ point.s →
    LRDeterminantLowRatioRegion point →
    0 ≤ lrCertificateTTarget point

/-- The existing compact-channel replay-ledger interface supplies exactly
the far-channel input above when instantiated.  This is the coordinate
transport of (M51), not a claim that the concrete replay booleans already
evaluate to true. -/
theorem lrDeterminantFarChannelLowRatioTangentTheorem_of_compactVReplayLedger
    (ledger : LRCompactVR910ReplayLedger) :
    LRDeterminantFarChannelLowRatioTangentTheorem := by
  intro point hinterior hrelevant hsFar _hregion
  let R := lrCertificateR point
  let v := lrCertificateV point
  let t := lrCertificateT point
  have hR : R ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [R, lrCertificateR]
    constructor <;> linarith [hinterior.1.1, hinterior.1.2]
  have hRUpper : R ≤ 9 / 10 := by
    dsimp [R, lrCertificateR]
    norm_num at hsFar ⊢
    linarith
  have hv : v ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [v] using lrCertificateV_mem_Ioo hinterior
  have hvThird : 1 / 3 ≤ v := by
    simpa [v] using
      lrCertificateV_one_third_le_of_physical hinterior hrelevant.1
  have ht : t ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [t] using lrCertificateT_mem_Ioo hinterior
  have hxPos : 0 < lrCertificateX point := by
    unfold lrCertificateX
    have hprod : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point < 1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hinterior.2.2.2 hinterior.2.1.1
        _ = lrCertificateE point := one_mul _
        _ < 1 := hinterior.2.1.2
    linarith
  have htSq : t ^ 2 = lrCertificateX point := by
    dsimp [t, lrCertificateT]
    exact Real.sq_sqrt hxPos.le
  have htHigh : 17 / 20 ≤ t ^ 2 := by
    rw [htSq]
    unfold lrCertificateX lrCertificateE
    nlinarith [hrelevant.1.2.1]
  have hJ : 0 < lrFlowJ R v t := by
    rw [← lrCertificateJ_eq_flow hinterior.1 hinterior.2.1
      ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩]
    exact hrelevant.2
  have hflow : 0 ≤ lrLowVReserve R v t :=
    ledger.v_nonnegative R v t hR hRUpper hv hvThird ht htHigh hJ
  have hV : 0 ≤ lrCertificateVTarget point := by
    rw [lrCertificateVTarget_eq_lrLowVReserve hinterior.1
      hinterior.2.1 ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩]
    exact hflow
  exact lrCertificateTTarget_nonnegative_of_VTarget hinterior hrelevant hV

/-- Exact audited split at `s = 2^-14`.  The small-`s` branch enters through
the analytic first bracket and the complementary branch enters through the
finite exact-`V` replay.  The two closed inputs overlap at the boundary, so
there is no uncovered slit. -/
theorem lrDeterminantNearEndpointLowRatioTangentTheorem_of_smallSFirstBracket_and_finiteV
    (hsmall : LRDeterminantLowRatioSmallSFirstBracketTheorem)
    (hfinite : LRDeterminantLowRatioFiniteVTargetTheorem) :
    LRDeterminantNearEndpointLowRatioTangentTheorem := by
  intro point hinterior hrelevant hsUpper hregion
  by_cases hs : point.s ≤ 1 / 16384
  · exact lrCertificateTTarget_nonnegative_of_VTarget hinterior hrelevant
      (lrCertificateVTarget_nonnegative_of_firstBracket hinterior
        (hsmall point hinterior hrelevant hregion hs))
  · exact lrCertificateTTarget_nonnegative_of_VTarget hinterior hrelevant
      (hfinite point hinterior hrelevant hregion
        (le_of_lt (lt_of_not_ge hs)) hsUpper.le)

/-- Assemble the stronger historical ledger interface from the exact
near-endpoint (M44) branch and the separate compact-channel (M51) branch. -/
theorem lrDeterminantLowRatioTangentTheorem_of_nearEndpoint_and_farChannel
    (hnear : LRDeterminantNearEndpointLowRatioTangentTheorem)
    (hfar : LRDeterminantFarChannelLowRatioTangentTheorem) :
    LRDeterminantLowRatioTangentTheorem := by
  intro point hinterior hrelevant hregion
  by_cases hs : point.s < 1 / 10
  · exact hnear point hinterior hrelevant hs hregion
  · exact hfar point hinterior hrelevant (le_of_not_gt hs) hregion

/-- Fully faithful assembly of the current ledger field from the three
audited inputs: (M42), finite (M44), and compact-channel (M51). -/
theorem lrDeterminantLowRatioTangentTheorem_of_audited_parts
    (hsmall : LRDeterminantLowRatioSmallSFirstBracketTheorem)
    (hfinite : LRDeterminantLowRatioFiniteVTargetTheorem)
    (hfar : LRDeterminantFarChannelLowRatioTangentTheorem) :
    LRDeterminantLowRatioTangentTheorem := by
  exact lrDeterminantLowRatioTangentTheorem_of_nearEndpoint_and_farChannel
    (lrDeterminantNearEndpointLowRatioTangentTheorem_of_smallSFirstBracket_and_finiteV
      hsmall hfinite)
    hfar

end CourtadeKumar
