import InformationTheory.CourtadeKumar.LRGapBudgetSEFourTailCertificate
import InformationTheory.CourtadeKumar.LRReducedCertificateAssembly

/-!
# Flow-level assembly of the replayed `k >= 4` gap-budget tail

The old near-endpoint tangent interface was noncompact in
`k = e / s`.  The replayed gap-budget theorem closes `k >= 4`, while the
uniform-tail theorem supplies the accompanying half-midpoint numerator.
Consequently the remaining tangent input is confined to the compact core
`k <= 4`.
-/

open Set

namespace CourtadeKumar

/-- The bounded part of the near-endpoint tangent-coordinate obligation. -/
def LRHighShapeNearEndpointCoreTangentCoordinateTheorem : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    point.s < 1 / 10 →
    point.k ≤ 4 →
    0 ≤ lrCertificateTTarget point

/-- The compact tangent theorem and the replayed gap-budget tail together
prove the full near-endpoint tangent theorem used by the LR flow assembly. -/
theorem nearEndpointTangentTheorem_of_coreTangent_and_gapBudgetTail
    (hcore : LRHighShapeNearEndpointCoreTangentCoordinateTheorem) :
    LRHighShapeNearEndpointTangentTheorem := by
  intro R v t hR hv ht htHigh hvHigh hJ hnear
  let point := lrFlowCertificatePoint R v t
  have hinterior : LRHighShapeInterior point := by
    simpa [point] using lrFlowCertificatePoint_highShapeInterior hR hv ht
  have hrelevant : LRHighShapeVRelevant point := by
    simpa [point] using lrFlowCertificatePoint_highShapeVRelevant
      hR hv ht htHigh hvHigh hJ
  have hsUpper : point.s < 1 / 10 := by
    change 1 - R < 1 / 10
    linarith
  have hsPos : 0 < 1 - R := sub_pos.mpr hR.2
  have hRNe : R ≠ 1 := hR.2.ne
  have hvtPos : 0 < v * t := mul_pos hv.1 ht.1
  have hvtLt : v * t < 1 := by
    calc
      v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
      _ < 1 := by simpa using ht.2
  have hePos : 0 < 1 - v ^ 2 * t ^ 2 := by
    nlinarith [sq_pos_of_pos hvtPos]
  by_cases hkTail : 4 ≤ point.k
  · have htail : 4 * (1 - R) ≤ lrUniformTailE v t := by
      change 4 ≤ (1 - v ^ 2 * t ^ 2) / (1 - R) at hkTail
      rw [le_div_iff₀ hsPos] at hkTail
      simpa [lrUniformTailE] using hkTail
    have hhalf :
        0 ≤ lrFlowNumeratorP R (lrFlowM v / 2) v t :=
      (lrUniformTail_halfMidpoint_pos hR
        (show v ∈ Ico (1 / 3 : ℝ) 1 from ⟨hvHigh, hv.2⟩)
        ht htHigh htail).le
    have hbudgetCoordinate : 0 ≤ lrCertificateGapBudget point :=
      LRGapBudgetSEFourTailCertificate.gapBudget_nonnegative_unconditional
        hinterior hrelevant.1 hsUpper hkTail
    have hbudget : 0 ≤ lrFlowGapBudget R v t := by
      rw [← lrCertificateGapBudget_flow hR hv ht hePos]
      simpa [point] using hbudgetCoordinate
    exact lrFlowTReserve_nonneg_of_halfMidpoint_gapBudget
      hR hv hJ hhalf hbudget
  · have hkCore : point.k ≤ 4 := le_of_not_ge hkTail
    have htarget := hcore point hinterior hrelevant hsUpper hkCore
    rw [lrCertificateTTarget_eq_highShapeTarget hinterior.1
      hinterior.2.1
      ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩] at htarget
    rw [show point = lrFlowCertificatePoint R v t by rfl,
      lrHighShapeTCertificateTarget_flow hRNe hePos.ne' hv.1 ht.1] at htarget
    exact htarget

/-- The complete pointwise LR numerator theorem now needs only two bounded
near-endpoint inputs: the post-small-`s` midpoint strip and the tangent core
`k <= 4`. -/
theorem lrFlowNumeratorP_nonneg_target_of_compact_core_certificates
    (ledger : LRCompactVR910ReplayLedger)
    (hmidpoint : LRSmallSBridgeCoreCertificate.LRHighShapeNearEndpointPostSmallSBridgeMidpointCoordinateTheorem)
    (htangent : LRHighShapeNearEndpointCoreTangentCoordinateTheorem)
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htarget : lrPrefixEll R p = lrSquareTarget R v t) :
    0 ≤ lrFlowNumeratorP R p v t :=
  lrFlowNumeratorP_nonneg_target_of_compactV_and_nearEndpoint ledger
    (LRSmallSBridgeCoreCertificate.nearEndpointHalfMidpoint_of_postSmallSBridge
      hmidpoint)
    (nearEndpointTangentTheorem_of_coreTangent_and_gapBudgetTail htangent)
    hR hp hv ht htarget

/-- Differential form of the compact-core reduction, ready for the final
single-ray monotonicity argument. -/
theorem hasDerivAt_lrReserve_exactFlow_of_compact_core_certificates
    (ledger : LRCompactVR910ReplayLedger)
    (hmidpoint : LRSmallSBridgeCoreCertificate.LRHighShapeNearEndpointPostSmallSBridgeMidpointCoordinateTheorem)
    (htangent : LRHighShapeNearEndpointCoreTangentCoordinateTheorem)
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
        (lrFlowB R v t * (1 - R) ^ 2 * t ^ 2) :=
  hasDerivAt_lrReserve_exactFlow_of_compactV_and_nearEndpoint ledger
    (LRSmallSBridgeCoreCertificate.nearEndpointHalfMidpoint_of_postSmallSBridge
      hmidpoint)
    (nearEndpointTangentTheorem_of_coreTangent_and_gapBudgetTail htangent)
    hR hp hv ht hvval hvfun htarget hcurve

end CourtadeKumar
