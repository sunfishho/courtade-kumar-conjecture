import InformationTheory.CourtadeKumar.LRHighShapeVEvaluator
import InformationTheory.CourtadeKumar.LRFullFlowAssembly

/-!
# Bridge from cancellation-coordinate `V` to the complete flow interface

The executable high-shape evaluator deliberately does not import the full
low-shape proof.  This small downstream module reconnects its coordinate
theorem to the final flow theorem after both sides have been established.
-/

namespace CourtadeKumar

/-- Once all cancellation-coordinate roots are covered, the exact change of
variables turns their result into the sole high-shape assumption required by
the reduced flow assembly. -/
theorem lrHighShapeVTheorem_of_coordinateTheorem
    (hcoordinate : LRHighShapeVCoordinateTheorem) :
    LRHighShapeVTheorem := by
  intro R v t hR hv ht htHigh hvHigh hJ
  have htarget := hcoordinate (lrFlowCertificatePoint R v t)
    (lrFlowCertificatePoint_highShapeVRelevant
      hR hv ht htHigh hvHigh hJ)
  rw [lrCertificateVTarget_flow hR hv ht] at htarget
  exact htarget

end CourtadeKumar
