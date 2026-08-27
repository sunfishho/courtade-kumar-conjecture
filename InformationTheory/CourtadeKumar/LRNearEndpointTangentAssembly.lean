import InformationTheory.CourtadeKumar.LRHighShapeTangentAutoTree
import InformationTheory.CourtadeKumar.LRHybridHighShapeAssembly

/-!
# Near-endpoint tangent assembly

The compact direct-`V` ledger removes `R ≤ 9/10`, hence the tangent
certificate is required only in the cancellation chart `s = 1-R < 1/10`.
-/

open Set

namespace CourtadeKumar

def LRHighShapeNearEndpointTangentCoordinateTheorem : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeInterior point →
    LRHighShapeVRelevant point →
    point.s < 1 / 10 →
    0 ≤ lrCertificateTTarget point

/-- Transport the bounded near-endpoint coordinate obligation to the exact
flow-level tangent theorem used by the hybrid assembly. -/
theorem nearEndpointTangentTheorem_of_coordinateTheorem
    (hcoordinate : LRHighShapeNearEndpointTangentCoordinateTheorem) :
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
  have htarget := hcoordinate point hinterior hrelevant hsUpper
  rw [lrCertificateTTarget_eq_highShapeTarget hinterior.1
    hinterior.2.1 ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩] at htarget
  have hRNe : R ≠ 1 := hR.2.ne
  have hvtPos : 0 < v * t := mul_pos hv.1 ht.1
  have hvtLt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hePos : 0 < 1 - v ^ 2 * t ^ 2 := by
    nlinarith [sq_pos_of_pos hvtPos]
  rw [show point = lrFlowCertificatePoint R v t by rfl,
    lrHighShapeTCertificateTarget_flow hRNe hePos.ne' hv.1 ht.1] at htarget
  exact htarget

end CourtadeKumar
