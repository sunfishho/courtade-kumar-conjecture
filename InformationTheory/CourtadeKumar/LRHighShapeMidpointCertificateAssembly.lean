import InformationTheory.CourtadeKumar.LRHighShapeMidpointTailAssembly
import InformationTheory.CourtadeKumar.LRHighShapeVEvaluator

/-!
# End-to-end assembly of high-shape midpoint subdivisions

This module connects the verified midpoint evaluator to the common
high-shape relevance/discard checker, and then transports the resulting
coordinate inequality back to the exact LR half-midpoint numerator.
-/

open Set

namespace CourtadeKumar

/-- A successful midpoint subdivision proves the normalized half-midpoint
target at every relevant point of its root box. -/
theorem lrHighShapeMidpointSubdivisionCertificate_nonnegative
    (terms : ℕ) {box : CertificateBox}
    {certificate : SubdivisionCertificate LRHighShapeMidpointCertificate
      LRHighShapeVDiscardData}
    (hcheck : certificate.check
      (LRHighShapeMidpointCertificate.accepts terms)
      (lrHighShapeVDiscardCheck terms) box = true) :
    ∀ point, box.Contains point → LRHighShapeVRelevant point →
      0 ≤ lrCertificateUTarget point := by
  exact subdivisionCertificate_nonnegative_checked
    (LRHighShapeMidpointCertificate.checkedEvaluatorSound terms)
    (lrHighShapeVDiscardCheck_sound terms) hcheck

/-- An interior analytic flow point is interior in the cancellation chart. -/
theorem lrFlowCertificatePoint_highShapeInterior
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    LRHighShapeInterior (lrFlowCertificatePoint R v t) := by
  let point := lrFlowCertificatePoint R v t
  have hRNe : R ≠ 1 := hR.2.ne
  have hvtPos : 0 < v * t := mul_pos hv.1 ht.1
  have hvtLt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hePos : 0 < 1 - v ^ 2 * t ^ 2 := by
    nlinarith [sq_pos_of_pos hvtPos]
  have heLt : 1 - v ^ 2 * t ^ 2 < 1 := by
    nlinarith [sq_pos_of_pos hvtPos]
  have htSqLt : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
  have hchiPos : 0 < (1 - t ^ 2) / (1 - v ^ 2 * t ^ 2) :=
    div_pos (sub_pos.mpr htSqLt) hePos
  have hchiLt : (1 - t ^ 2) / (1 - v ^ 2 * t ^ 2) < 1 := by
    rw [div_lt_one hePos]
    have hvSqLt : v ^ 2 < 1 := by nlinarith [hv.1, hv.2]
    nlinarith [mul_pos (sub_pos.mpr hvSqLt) (sq_pos_of_pos ht.1)]
  refine ⟨?_, ?_, ?_⟩
  · change 1 - R ∈ Ioo (0 : ℝ) 1
    constructor <;> linarith [hR.1, hR.2]
  · rw [show lrCertificateE point = 1 - v ^ 2 * t ^ 2 by
      exact lrCertificateE_flow hRNe]
    exact ⟨hePos, heLt⟩
  · change (1 - t ^ 2) / (1 - v ^ 2 * t ^ 2) ∈ Ioo (0 : ℝ) 1
    exact ⟨hchiPos, hchiLt⟩

/-- A checked subdivision covering one analytic point proves its exact
unnormalized half-midpoint numerator is nonnegative. -/
theorem lrFlowHalfMidpoint_nonnegative_of_subdivision
    (terms : ℕ) {box : CertificateBox}
    {certificate : SubdivisionCertificate LRHighShapeMidpointCertificate
      LRHighShapeVDiscardData}
    (hcheck : certificate.check
      (LRHighShapeMidpointCertificate.accepts terms)
      (lrHighShapeVDiscardCheck terms) box = true)
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htHigh : 17 / 20 ≤ t ^ 2) (hvHigh : 1 / 3 ≤ v)
    (hJ : 0 < lrFlowJ R v t)
    (hcontains : box.Contains (lrFlowCertificatePoint R v t)) :
    0 ≤ lrFlowNumeratorP R (lrFlowM v / 2) v t := by
  let point := lrFlowCertificatePoint R v t
  have hinterior := lrFlowCertificatePoint_highShapeInterior hR hv ht
  have hrelevant := lrFlowCertificatePoint_highShapeVRelevant
    hR hv ht htHigh hvHigh hJ
  have htarget := lrHighShapeMidpointSubdivisionCertificate_nonnegative
    terms hcheck point hcontains hrelevant
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

/-- Coordinate-level compact-core midpoint statement left for the finite
ledger. -/
def LRHighShapeCoreMidpointCoordinateTheorem : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    point.k ≤ 4 →
    0 ≤ lrCertificateUTarget point

/-- A coordinate proof on `k ≤ 4` supplies the compact midpoint interface
used by the analytic-tail assembly. -/
theorem lrHighShapeCoreHalfMidpointTheorem_of_coordinateTheorem
    (hcoordinate : LRHighShapeCoreMidpointCoordinateTheorem) :
    LRHighShapeCoreHalfMidpointTheorem := by
  intro R v t hR hv ht htHigh hvHigh hJ hcore
  let point := lrFlowCertificatePoint R v t
  have hinterior := lrFlowCertificatePoint_highShapeInterior hR hv ht
  have hrelevant := lrFlowCertificatePoint_highShapeVRelevant
    hR hv ht htHigh hvHigh hJ
  have hsPos : 0 < 1 - R := sub_pos.mpr hR.2
  have hk : point.k ≤ 4 := by
    change (1 - v ^ 2 * t ^ 2) / (1 - R) ≤ 4
    rw [div_le_iff₀ hsPos]
    simpa [lrUniformTailE] using hcore
  have htarget := hcoordinate point hinterior hrelevant hk
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

end CourtadeKumar
