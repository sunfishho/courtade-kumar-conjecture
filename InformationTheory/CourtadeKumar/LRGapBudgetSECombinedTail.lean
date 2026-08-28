import InformationTheory.CourtadeKumar.LRGapBudgetSEEndpointRetainedQCertificate

/-!
# Combined bounded-tail derivative certificate

Leaves may use the ordinary open-box evaluator, the basic closed-endpoint
minorant, or the stronger endpoint evaluator retaining `Q(B(s,e))`.  The
choice is checked independently on every leaf; subdivision and physical
discard soundness remain generic.
-/

namespace CourtadeKumar

inductive LRGapBudgetSEDerivativeAcceptData where
  | regular
  | endpoint
  | endpointRetainedQ
  deriving DecidableEq, Repr

namespace LRGapBudgetSEDerivativeAcceptData

def check (terms sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRGapBudgetSEDerivativeAcceptData → Bool
  | .regular =>
      LRGapBudgetSECertificate.autoDerivativeAccepts
        terms sqrtFuel logFuel box ()
  | .endpoint =>
      LRGapBudgetSEEndpointCertificate.autoAccepts
        terms sqrtFuel logFuel box ()
  | .endpointRetainedQ =>
      LRGapBudgetSEEndpointRetainedQCertificate.autoAccepts
        terms sqrtFuel logFuel box ()

theorem sound (terms sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (data : LRGapBudgetSEDerivativeAcceptData)
    (hcheck : data.check terms sqrtFuel logFuel box = true) :
    ∀ point, box.Contains point → LRGapBudgetSETailRelevant point →
      0 ≤ lrGapBudgetSEChiDerivE point.s point.k point.chi := by
  intro point hpoint hrelevant
  cases data with
  | regular =>
      exact LRGapBudgetSECertificate.autoDerivativeAccepts_sound
        terms sqrtFuel logFuel box () hcheck point hpoint
  | endpoint =>
      exact LRGapBudgetSEEndpointCertificate.autoAccepts_sound
        terms sqrtFuel logFuel box () hcheck point hpoint hrelevant
  | endpointRetainedQ =>
      exact LRGapBudgetSEEndpointRetainedQCertificate.autoAccepts_sound
        terms sqrtFuel logFuel box () hcheck point hpoint hrelevant

end LRGapBudgetSEDerivativeAcceptData

abbrev LRGapBudgetSEDerivativeTree :=
  SubdivisionCertificate LRGapBudgetSEDerivativeAcceptData
    LRGapBudgetSEDiscardData

/-- End-to-end soundness for a finite tree mixing all three derivative
leaf modes. -/
theorem lrGapBudgetSECombinedDerivativeSubdivision_sound
    (terms sqrtFuel logFuel : ℕ) {box : CertificateBox}
    {tree : LRGapBudgetSEDerivativeTree}
    (hcheck : tree.check
      (LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel)
      lrGapBudgetSEDiscardCheck box = true) :
    ∀ point, box.Contains point → LRGapBudgetSETailRelevant point →
      0 ≤ lrGapBudgetSEChiDerivE point.s point.k point.chi := by
  have hstruct := subdivisionCertificate_sound
    (Relevant := LRGapBudgetSETailRelevant)
    (Property := fun point => LRGapBudgetSETailRelevant point →
      0 ≤ lrGapBudgetSEChiDerivE point.s point.k point.chi)
    (acceptBox :=
      LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel)
    (discardBox := lrGapBudgetSEDiscardCheck)
    (box := box) (certificate := tree)
    (LRGapBudgetSEDerivativeAcceptData.sound terms sqrtFuel logFuel)
    lrGapBudgetSEDiscardCheck_sound hcheck
  intro point hpoint hrelevant
  exact hstruct point hpoint hrelevant hrelevant

/-- A checked combined tree on the closed bounded root supplies the original
unbounded-coordinate derivative hypothesis used by tail monotonicity. -/
theorem lrCertificateGapBudgetDerivK_nonnegative_of_combinedSETail
    (terms sqrtFuel logFuel : ℕ)
    {tree : LRGapBudgetSEDerivativeTree}
    (hcheck : tree.check
      (LRGapBudgetSEDerivativeAcceptData.check terms sqrtFuel logFuel)
      lrGapBudgetSEDiscardCheck lrGapBudgetSETailRoot = true)
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hphysical : LRHighShapePhysical point)
    (hs : point.s < 1 / 10) (hk : 4 ≤ point.k) :
    0 ≤ lrCertificateGapBudgetDerivK point := by
  apply lrCertificateGapBudgetDerivK_nonneg_of_derivE
    hinterior.1.1.le
    (lrCertificateV_pos_of_highShapeInterior hinterior)
    (lrCertificateX_pos_of_highShapeInterior hinterior)
  exact lrGapBudgetSECombinedDerivativeSubdivision_sound
    terms sqrtFuel logFuel hcheck
    (lrGapBudgetSEPoint point)
    (lrGapBudgetSEPoint_mem_root hinterior hs)
    (lrGapBudgetSEPoint_tailRelevant hinterior hphysical hs hk)

end CourtadeKumar

