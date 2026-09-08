import InformationTheory.CourtadeKumar.IntervalCertificateAssemblyCore
import InformationTheory.CourtadeKumar.IntervalDerivativeCertificate

/-!
# Assembly of subdivision and midpoint certificates

This is the target-independent end-to-end checker theorem.  A concrete
determinant module supplies an executable leaf evaluator and proves its value
and derivative enclosures sound.  Successful Boolean checking of an
untrusted payload tree then proves strict positivity at every relevant point
of the root box.
-/

namespace CourtadeKumar

theorem midpointLeafAccepts_eq_coreCheck {AcceptData : Type}
    (evaluate : CertificateBox → AcceptData → MidpointCertificate)
    (box : CertificateBox) (data : AcceptData) :
    midpointLeafAccepts evaluate box data =
      (evaluate box data).coreCheck box := rfl

theorem checkedMidpointLeafAccepts_eq_coreCheck {AcceptData : Type}
    (payloadCheck : CertificateBox → AcceptData → Bool)
    (evaluate : CertificateBox → AcceptData → MidpointCertificate)
    (box : CertificateBox) (data : AcceptData) :
    checkedMidpointLeafAccepts payloadCheck evaluate box data =
      (payloadCheck box data && (evaluate box data).coreCheck box) := rfl

theorem checkedEnclosureLeafAccepts_eq_core {AcceptData : Type}
    (payloadCheck : CertificateBox → AcceptData → Bool)
    (enclose : CertificateBox → AcceptData → RationalEnclosure)
    (box : CertificateBox) (data : AcceptData) :
    checkedEnclosureLeafAccepts payloadCheck enclose box data =
      (payloadCheck box data && (enclose box data).provesNonnegative) := rfl

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

/-- Soundness contract for a direct interval extension whose auxiliary
payload must first pass an executable validity check. -/
structure CheckedEnclosureLeafEvaluatorSound
    {AcceptData : Type}
    (target : CertificatePoint → ℝ)
    (payloadCheck : CertificateBox → AcceptData → Bool)
    (enclose : CertificateBox → AcceptData → RationalEnclosure) where
  value : ∀ box data, payloadCheck box data = true →
    ∀ point, box.Contains point → (enclose box data).Contains (target point)

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

/-- End-to-end soundness for a payload-checked direct interval extension. -/
theorem subdivisionCertificate_nonnegative_checkedEnclosure
    {Relevant : CertificatePoint → Prop}
    {target : CertificatePoint → ℝ}
    {AcceptData DiscardData : Type}
    {payloadCheck : CertificateBox → AcceptData → Bool}
    {enclose : CertificateBox → AcceptData → RationalEnclosure}
    {discardBox : CertificateBox → DiscardData → Bool}
    (enclose_sound : CheckedEnclosureLeafEvaluatorSound
      target payloadCheck enclose)
    (discard_sound : ∀ box data, discardBox box data = true →
      ∀ point, box.Contains point → ¬ Relevant point)
    {box : CertificateBox}
    {certificate : SubdivisionCertificate AcceptData DiscardData}
    (hcheck : certificate.check
      (checkedEnclosureLeafAccepts payloadCheck enclose)
      discardBox box = true) :
    ∀ point, box.Contains point → Relevant point → 0 ≤ target point := by
  apply subdivisionCertificate_sound
      (Relevant := Relevant) (Property := fun point ↦ 0 ≤ target point)
      (acceptBox := checkedEnclosureLeafAccepts payloadCheck enclose)
      (discardBox := discardBox)
      (box := box) (certificate := certificate) ?_ discard_sound hcheck
  intro leaf data hleaf point hpoint
  have hparts : payloadCheck leaf data = true ∧
      (enclose leaf data).provesNonnegative = true := by
    simpa [checkedEnclosureLeafAccepts] using hleaf
  exact RationalEnclosure.nonnegative_of_provesNonnegative hparts.2
    (enclose_sound.value leaf data hparts.1 point hpoint)

end CourtadeKumar
