import InformationTheory.CourtadeKumar.IntervalADElementary

/-!
# Assembly of subdivision and midpoint certificates

This is the target-independent end-to-end checker theorem.  A concrete
determinant module supplies an executable leaf evaluator and proves its value
and derivative enclosures sound.  Successful Boolean checking of an
untrusted payload tree then proves strict positivity at every relevant point
of the root box.
-/

namespace CourtadeKumar

def midpointLeafAccepts {AcceptData : Type}
    (evaluate : CertificateBox → AcceptData → MidpointCertificate)
    (box : CertificateBox) (data : AcceptData) : Bool :=
  (evaluate box data).check box

/-- A checked midpoint leaf first validates its target-specific arithmetic
payload, then tests the generic midpoint lower bound. -/
def checkedMidpointLeafAccepts {AcceptData : Type}
    (payloadCheck : CertificateBox → AcceptData → Bool)
    (evaluate : CertificateBox → AcceptData → MidpointCertificate)
    (box : CertificateBox) (data : AcceptData) : Bool :=
  payloadCheck box data && (evaluate box data).check box

/-- Soundness contract for a target-specific executable midpoint evaluator. -/
structure MidpointLeafEvaluatorSound
    {AcceptData : Type}
    (target : CertificatePoint → ℝ)
    (evaluate : CertificateBox → AcceptData → MidpointCertificate) where
  value : ∀ box data,
    (evaluate box data).value.Contains (target box.midpoint)
  derivatives : ∀ box data,
    BoxDerivativeEnclosures target box (evaluate box data)

/-- Soundness contract for an evaluator whose transcendental or algebraic
payload must pass a separate executable validity check. -/
structure CheckedMidpointLeafEvaluatorSound
    {AcceptData : Type}
    (target : CertificatePoint → ℝ)
    (payloadCheck : CertificateBox → AcceptData → Bool)
    (evaluate : CertificateBox → AcceptData → MidpointCertificate) where
  value : ∀ box data, payloadCheck box data = true →
    (evaluate box data).value.Contains (target box.midpoint)
  derivatives : ∀ box data, payloadCheck box data = true →
    BoxDerivativeEnclosures target box (evaluate box data)

theorem subdivisionCertificate_strictPositive
    {Relevant : CertificatePoint → Prop}
    {target : CertificatePoint → ℝ}
    {AcceptData DiscardData : Type}
    {evaluate : CertificateBox → AcceptData → MidpointCertificate}
    {discardBox : CertificateBox → DiscardData → Bool}
    (evaluate_sound : MidpointLeafEvaluatorSound target evaluate)
    (discard_sound : ∀ box data, discardBox box data = true →
      ∀ point, box.Contains point → ¬ Relevant point)
    {box : CertificateBox}
    {certificate : SubdivisionCertificate AcceptData DiscardData}
    (hcheck : certificate.check (midpointLeafAccepts evaluate)
      discardBox box = true) :
    ∀ point, box.Contains point → Relevant point → 0 < target point := by
  apply subdivisionCertificate_sound
      (Relevant := Relevant) (Property := fun point ↦ 0 < target point)
      (acceptBox := midpointLeafAccepts evaluate)
      (discardBox := discardBox)
      (box := box) (certificate := certificate) ?_ discard_sound hcheck
  intro leaf data hleaf point hpoint
  exact MidpointCertificate.sound_of_derivativeEnclosures
    (evaluate_sound.value leaf data)
    (evaluate_sound.derivatives leaf data) hleaf hpoint

theorem subdivisionCertificate_nonnegative_of_strictPositive
    {Relevant : CertificatePoint → Prop}
    {target : CertificatePoint → ℝ}
    {AcceptData DiscardData : Type}
    {evaluate : CertificateBox → AcceptData → MidpointCertificate}
    {discardBox : CertificateBox → DiscardData → Bool}
    (evaluate_sound : MidpointLeafEvaluatorSound target evaluate)
    (discard_sound : ∀ box data, discardBox box data = true →
      ∀ point, box.Contains point → ¬ Relevant point)
    {box : CertificateBox}
    {certificate : SubdivisionCertificate AcceptData DiscardData}
    (hcheck : certificate.check (midpointLeafAccepts evaluate)
      discardBox box = true) :
    ∀ point, box.Contains point → Relevant point → 0 ≤ target point := by
  intro point hpoint hRelevant
  exact (subdivisionCertificate_strictPositive evaluate_sound discard_sound
    hcheck point hpoint hRelevant).le

theorem subdivisionCertificate_strictPositive_checked
    {Relevant : CertificatePoint → Prop}
    {target : CertificatePoint → ℝ}
    {AcceptData DiscardData : Type}
    {payloadCheck : CertificateBox → AcceptData → Bool}
    {evaluate : CertificateBox → AcceptData → MidpointCertificate}
    {discardBox : CertificateBox → DiscardData → Bool}
    (evaluate_sound : CheckedMidpointLeafEvaluatorSound target payloadCheck evaluate)
    (discard_sound : ∀ box data, discardBox box data = true →
      ∀ point, box.Contains point → ¬ Relevant point)
    {box : CertificateBox}
    {certificate : SubdivisionCertificate AcceptData DiscardData}
    (hcheck : certificate.check
      (checkedMidpointLeafAccepts payloadCheck evaluate)
      discardBox box = true) :
    ∀ point, box.Contains point → Relevant point → 0 < target point := by
  apply subdivisionCertificate_sound
      (Relevant := Relevant) (Property := fun point ↦ 0 < target point)
      (acceptBox := checkedMidpointLeafAccepts payloadCheck evaluate)
      (discardBox := discardBox)
      (box := box) (certificate := certificate) ?_ discard_sound hcheck
  intro leaf data hleaf point hpoint
  have hparts : payloadCheck leaf data = true ∧
      (evaluate leaf data).check leaf = true := by
    simpa [checkedMidpointLeafAccepts] using hleaf
  exact MidpointCertificate.sound_of_derivativeEnclosures
    (evaluate_sound.value leaf data hparts.1)
    (evaluate_sound.derivatives leaf data hparts.1) hparts.2 hpoint

theorem subdivisionCertificate_nonnegative_checked
    {Relevant : CertificatePoint → Prop}
    {target : CertificatePoint → ℝ}
    {AcceptData DiscardData : Type}
    {payloadCheck : CertificateBox → AcceptData → Bool}
    {evaluate : CertificateBox → AcceptData → MidpointCertificate}
    {discardBox : CertificateBox → DiscardData → Bool}
    (evaluate_sound : CheckedMidpointLeafEvaluatorSound target payloadCheck evaluate)
    (discard_sound : ∀ box data, discardBox box data = true →
      ∀ point, box.Contains point → ¬ Relevant point)
    {box : CertificateBox}
    {certificate : SubdivisionCertificate AcceptData DiscardData}
    (hcheck : certificate.check
      (checkedMidpointLeafAccepts payloadCheck evaluate)
      discardBox box = true) :
    ∀ point, box.Contains point → Relevant point → 0 ≤ target point := by
  intro point hpoint hRelevant
  exact (subdivisionCertificate_strictPositive_checked evaluate_sound discard_sound
    hcheck point hpoint hRelevant).le

end CourtadeKumar
