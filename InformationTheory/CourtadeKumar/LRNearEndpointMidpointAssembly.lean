import InformationTheory.CourtadeKumar.LRSmallSBridgeCoreGeneratedData
import InformationTheory.CourtadeKumar.LRHybridHighShapeAssembly
import InformationTheory.CourtadeKumar.LRHighShapeMidpointTailAssembly

/-!
# Near-endpoint midpoint assembly

After the compact direct-`V` ledger removes `R ≤ 9/10`, the midpoint
certificate is needed only for `s = 1-R < 1/10`.  This file also incorporates
the generated small-`s` bridge, the analytic lower face, and the uniform
`k ≥ 4` tail.  The remaining midpoint input is therefore a bounded strip
`2⁻¹⁴ < s < 1/10` in cancellation coordinates.
-/

open Set

namespace CourtadeKumar
namespace LRSmallSBridgeCoreCertificate

def LRHighShapeNearEndpointPostSmallSBridgeMidpointCoordinateTheorem : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    point.k ≤ 4 →
    (1 / 128 < point.s ∨ 1 / 4 < point.k) →
    1 / 16384 < point.s →
    point.s < 1 / 10 →
    0 ≤ lrCertificateUTarget point

def LRHighShapeNearEndpointMiddleCoreMidpointCoordinateTheorem : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    point.k ≤ 4 →
    (1 / 128 < point.s ∨ 1 / 4 < point.k) →
    point.s < 1 / 10 →
    0 ≤ lrCertificateUTarget point

/-- The generated bridge fills `s ≤ 2⁻¹⁴`; only the post-bridge compact
strip is passed in as a hypothesis. -/
theorem generated_nearEndpointMiddleCoreCoordinate_of_postSmallSBridge
    (hpost :
      LRHighShapeNearEndpointPostSmallSBridgeMidpointCoordinateTheorem) :
    LRHighShapeNearEndpointMiddleCoreMidpointCoordinateTheorem := by
  intro point hinterior hrelevant hk hmiddle hsUpper
  by_cases hsSmall : point.s ≤ 1 / 16384
  · have hkLower : 1 / 4 ≤ point.k := by
      rcases hmiddle with hsLarge | hkLarge
      · exfalso
        nlinarith
      · exact hkLarge.le
    have hbridge := generated_halfMidpoint
      (show point.s ∈ Ioc (0 : ℝ) (1 / 16384) from
        ⟨hinterior.1.1, hsSmall⟩)
      (show point.k ∈ Icc (1 / 4 : ℝ) 4 from ⟨hkLower, hk⟩)
      (show point.chi ∈ Icc (0 : ℝ) 1 from
        ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩)
    have hquot : 0 < lrCertificateHalfMidpointNumerator point / point.s :=
      (show (0 : ℝ) < 13 / 20 by norm_num).trans hbridge
    have hnum : 0 < lrCertificateHalfMidpointNumerator point := by
      rw [div_pos_iff] at hquot
      rcases hquot with h | h
      · exact h.1
      · linarith [hinterior.1.1, h.2]
    unfold lrCertificateUTarget lrCertificateUDenominator
    exact (div_pos hnum
      (mul_pos hinterior.1.1 hinterior.2.1.1)).le
  · exact hpost point hinterior hrelevant hk hmiddle
      (lt_of_not_ge hsSmall) hsUpper

/-- A near-endpoint coordinate theorem supplies the corresponding exact
flow-level middle-core statement. -/
theorem nearEndpointMiddleCoreHalfMidpoint_of_coordinate
    (hcoordinate :
      LRHighShapeNearEndpointMiddleCoreMidpointCoordinateTheorem) :
    ∀ (R v t : ℝ),
      R ∈ Ioo (0 : ℝ) 1 →
      v ∈ Ioo (0 : ℝ) 1 →
      t ∈ Ioo (0 : ℝ) 1 →
      17 / 20 ≤ t ^ 2 →
      1 / 3 ≤ v →
      0 < lrFlowJ R v t →
      lrUniformTailE v t ≤ 4 * (1 - R) →
      (1 / 128 < 1 - R ∨
        1 / 4 < lrUniformTailE v t / (1 - R)) →
      9 / 10 < R →
      0 ≤ lrFlowNumeratorP R (lrFlowM v / 2) v t := by
  intro R v t hR hv ht htHigh hvHigh hJ hcore hmiddle hnear
  let point := lrFlowCertificatePoint R v t
  have hinterior := lrFlowCertificatePoint_highShapeInterior hR hv ht
  have hrelevant := lrFlowCertificatePoint_highShapeVRelevant
    hR hv ht htHigh hvHigh hJ
  have hsPos : 0 < 1 - R := sub_pos.mpr hR.2
  have hk : point.k ≤ 4 := by
    change (1 - v ^ 2 * t ^ 2) / (1 - R) ≤ 4
    rw [div_le_iff₀ hsPos]
    simpa [lrUniformTailE] using hcore
  have hmiddlePoint : 1 / 128 < point.s ∨ 1 / 4 < point.k := by
    simpa [point, lrFlowCertificatePoint, lrUniformTailE] using hmiddle
  have hsUpper : point.s < 1 / 10 := by
    change 1 - R < 1 / 10
    linarith
  have htarget := hcoordinate point hinterior hrelevant hk hmiddlePoint hsUpper
  have hnormalized : 0 ≤ lrHighShapeUCertificateTarget point := by
    rw [← lrCertificateUTarget_eq_highShapeTarget
      hinterior.1 hinterior.2.1
      ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩]
    exact htarget
  have hePos : 0 < 1 - v ^ 2 * t ^ 2 := by
    have hvtPos : 0 < v * t := mul_pos hv.1 ht.1
    have hvtLt : v * t < 1 := calc
      v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
      _ < 1 := by simpa using ht.2
    nlinarith [sq_pos_of_pos hvtPos]
  exact lrFlowHalfMidpoint_nonneg_of_certificateTarget
    hR hv.1 ht.1 hePos hnormalized

/-- End-to-end near-endpoint midpoint theorem.  Its sole input is the
bounded post-small-`s` coordinate strip. -/
theorem nearEndpointHalfMidpoint_of_postSmallSBridge
    (hpost :
      LRHighShapeNearEndpointPostSmallSBridgeMidpointCoordinateTheorem) :
    LRHighShapeNearEndpointHalfMidpointTheorem := by
  have hmiddle := nearEndpointMiddleCoreHalfMidpoint_of_coordinate
    (generated_nearEndpointMiddleCoreCoordinate_of_postSmallSBridge hpost)
  intro R v t hR hv ht htHigh hvHigh hJ hnear
  by_cases htail : 4 * (1 - R) ≤ lrUniformTailE v t
  · exact (lrUniformTail_halfMidpoint_pos hR
      (show v ∈ Ico (1 / 3 : ℝ) 1 from ⟨hvHigh, hv.2⟩)
      ht htHigh htail).le
  have hcore : lrUniformTailE v t ≤ 4 * (1 - R) :=
    le_of_lt (lt_of_not_ge htail)
  by_cases hsSmall : 1 - R ≤ 1 / 128
  · by_cases hkSmall : lrUniformTailE v t / (1 - R) ≤ 1 / 4
    · exact lrLowerFace_halfMidpoint_nonneg hR hv ht hJ hsSmall
        (by simpa [lrUniformTailE] using hkSmall)
    · exact hmiddle R v t hR hv ht htHigh hvHigh hJ hcore
        (Or.inr (lt_of_not_ge hkSmall)) hnear
  · exact hmiddle R v t hR hv ht htHigh hvHigh hJ hcore
      (Or.inl (lt_of_not_ge hsSmall)) hnear

end LRSmallSBridgeCoreCertificate
end CourtadeKumar
