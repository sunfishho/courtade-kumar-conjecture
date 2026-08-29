import InformationTheory.CourtadeKumar.IntervalCertificateAssembly
import InformationTheory.CourtadeKumar.LRDeterminantDeepTail
import InformationTheory.CourtadeKumar.LRHighShapeVEvaluator

/-!
# Assembly of the bounded part of the determinant deep region

The audited deep row splits at `k = 128`.  Its unbounded part is the analytic
tail proved in `LRDeterminantDeepTail`; the bounded part splits once more at
`k = 1/32` into a low-`k` analytic piece and a compact certificate replay.

This file records that decomposition and the exact kernel-checked interface
for the still-to-be-supplied bounded certificates.  It does not postulate or
claim acceptance of a concrete certificate tree: a compact conclusion is
obtained only from a Boolean tree check together with sound accepted- and
discard-leaf checkers.
-/

namespace CourtadeKumar

/-- The bounded half of the manuscript's deep determinant row. -/
def LRDeterminantBoundedDeepRegion (point : CertificatePoint) : Prop :=
  point.s ≤ 1 / 16384 ∧ point.s ≤ point.k ∧ point.k ≤ 128

/-- The noncompact low-`k` part of the bounded deep row. -/
def LRDeterminantBoundedDeepLowKRegion (point : CertificatePoint) : Prop :=
  point.s ≤ 1 / 16384 ∧ point.s ≤ point.k ∧ point.k ≤ 1 / 32

/-- The compact part of the bounded deep row.  The redundant inequality
`s ≤ k` is retained so that this is literally a subregion of the deep row. -/
def LRDeterminantBoundedDeepCompactRegion
    (point : CertificatePoint) : Prop :=
  point.s ≤ 1 / 16384 ∧ point.s ≤ point.k ∧
    1 / 32 ≤ point.k ∧ point.k ≤ 128

def LRDeterminantBoundedDeepCertificateTheorem : Prop :=
  LRDeterminantRegionCertificateTheorem LRDeterminantBoundedDeepRegion

def LRDeterminantBoundedDeepLowKCertificateTheorem : Prop :=
  LRDeterminantRegionCertificateTheorem LRDeterminantBoundedDeepLowKRegion

def LRDeterminantBoundedDeepCompactCertificateTheorem : Prop :=
  LRDeterminantRegionCertificateTheorem
    LRDeterminantBoundedDeepCompactRegion

/-- The two bounded subregions cover the bounded deep row, including their
common boundary `k = 1/32`. -/
theorem lrDeterminantBoundedDeep_lowK_or_compact
    {point : CertificatePoint}
    (hregion : LRDeterminantBoundedDeepRegion point) :
    LRDeterminantBoundedDeepLowKRegion point ∨
      LRDeterminantBoundedDeepCompactRegion point := by
  rcases hregion with ⟨hsDeep, hsk, hkUpper⟩
  by_cases hkLow : point.k ≤ 1 / 32
  · exact Or.inl ⟨hsDeep, hsk, hkLow⟩
  · exact Or.inr ⟨hsDeep, hsk, (lt_of_not_ge hkLow).le, hkUpper⟩

/-- A certificate for the larger audited low-`k` row automatically supplies
the low-`k` part of the bounded deep row. -/
theorem lrDeterminantBoundedDeepLowK_certificate_of_lowKRegion
    (hlowK : LRDeterminantRegionCertificateTheorem
      LRDeterminantLowKRegion) :
    LRDeterminantBoundedDeepLowKCertificateTheorem := by
  intro point hinterior hrelevant hregion
  exact hlowK point hinterior hrelevant
    ⟨hregion.1.trans (by norm_num), hregion.2.1,
      hregion.2.2.trans (by norm_num)⟩

/-- Rational root box for the compact replay.  The root includes harmless
boundary faces; the region theorem is used only under the open-chart
hypotheses. -/
def lrDeterminantBoundedDeepCompactRoot : CertificateBox where
  sLo := 0
  sHi := 1 / 16384
  kLo := 1 / 32
  kHi := 128
  chiLo := 0
  chiHi := 1

/-- Every interior point in the compact subregion belongs to the rational
root box used by its certificate tree. -/
theorem lrDeterminantBoundedDeepCompactRoot_contains
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hregion : LRDeterminantBoundedDeepCompactRegion point) :
    lrDeterminantBoundedDeepCompactRoot.Contains point := by
  rcases hregion with ⟨hsDeep, _hsk, hkLower, hkUpper⟩
  have hbounds :
      (0 : ℝ) ≤ point.s ∧ point.s ≤ 1 / 16384 ∧
      1 / 32 ≤ point.k ∧ point.k ≤ 128 ∧
      0 ≤ point.chi ∧ point.chi ≤ 1 :=
    ⟨hinterior.1.1.le, hsDeep, hkLower, hkUpper,
      hinterior.2.2.1.le, hinterior.2.2.2.le⟩
  simpa [lrDeterminantBoundedDeepCompactRoot,
    CertificateBox.Contains] using hbounds

/-- Contract required of an accepted compact leaf.  This implication form
allows the rational root box to contain boundary or nonphysical points. -/
def LRDeterminantBoundedDeepCompactLeafProperty
    (point : CertificatePoint) : Prop :=
  LRHighShapeInterior point →
  LRHighShapeVRelevant point →
  LRDeterminantAdmittedTarget point

/-- A sound accepted-leaf checker and a successful finite subdivision check
produce the compact-region theorem.  Discard leaves use the already verified
physical/nonpositive-`J` checker. -/
theorem lrDeterminantBoundedDeepCompact_certificate_of_checkedTree
    (terms : ℕ)
    {AcceptData : Type}
    {acceptBox : CertificateBox → AcceptData → Bool}
    (accept_sound : ∀ box data, acceptBox box data = true →
      ∀ point, box.Contains point →
        LRDeterminantBoundedDeepCompactLeafProperty point)
    {certificate :
      SubdivisionCertificate AcceptData LRHighShapeVDiscardData}
    (hcheck : certificate.check acceptBox
      (lrHighShapeVDiscardCheck terms)
      lrDeterminantBoundedDeepCompactRoot = true) :
    LRDeterminantBoundedDeepCompactCertificateTheorem := by
  intro point hinterior hrelevant hregion
  have hproperty : LRDeterminantBoundedDeepCompactLeafProperty point :=
    subdivisionCertificate_sound
      (Relevant := LRHighShapeVRelevant)
      (Property := LRDeterminantBoundedDeepCompactLeafProperty)
      accept_sound (lrHighShapeVDiscardCheck_sound terms) hcheck point
      (lrDeterminantBoundedDeepCompactRoot_contains hinterior hregion)
      hrelevant
  exact hproperty hinterior hrelevant

/-- Scalar target for a compact checker which encloses the full cleared
singular determinant directly. -/
noncomputable def lrDeterminantBoundedDeepClearedTarget
    (point : CertificatePoint) : ℝ :=
  lrDeterminantClearedSingular
    (lrCertificateBFlow point) (lrDeterminantD1 point)
    (lrCertificateGShape point) (lrDeterminantPsi point)
    (lrDeterminantDelta point) (lrCertificateW point)
    (lrDeterminantC0 point) (lrCertificateX point)
    (lrDeterminantT point)

/-- Direct-enclosure specialization of the compact-tree interface. -/
theorem lrDeterminantBoundedDeepCompact_certificate_of_checkedEnclosure
    (terms : ℕ)
    {AcceptData : Type}
    {payloadCheck : CertificateBox → AcceptData → Bool}
    {enclose : CertificateBox → AcceptData → RationalEnclosure}
    (enclose_sound : CheckedEnclosureLeafEvaluatorSound
      lrDeterminantBoundedDeepClearedTarget payloadCheck enclose)
    {certificate :
      SubdivisionCertificate AcceptData LRHighShapeVDiscardData}
    (hcheck : certificate.check
      (checkedEnclosureLeafAccepts payloadCheck enclose)
      (lrHighShapeVDiscardCheck terms)
      lrDeterminantBoundedDeepCompactRoot = true) :
    LRDeterminantBoundedDeepCompactCertificateTheorem := by
  intro point hinterior hrelevant hregion
  have hnonnegative : 0 ≤ lrDeterminantBoundedDeepClearedTarget point :=
    subdivisionCertificate_nonnegative_checkedEnclosure
      enclose_sound (lrHighShapeVDiscardCheck_sound terms) hcheck point
      (lrDeterminantBoundedDeepCompactRoot_contains hinterior hregion)
      hrelevant
  right
  simpa [LRDeterminantClearedSingularAt,
    lrDeterminantBoundedDeepClearedTarget] using hnonnegative

/-- The low-`k` theorem and compact replay assemble into the entire bounded
part of the deep row. -/
theorem lrDeterminantBoundedDeepRegion_certificate_of_low_and_compact
    (hlow : LRDeterminantBoundedDeepLowKCertificateTheorem)
    (hcompact : LRDeterminantBoundedDeepCompactCertificateTheorem) :
    LRDeterminantBoundedDeepCertificateTheorem := by
  intro point hinterior hrelevant hregion
  rcases lrDeterminantBoundedDeep_lowK_or_compact hregion with
    hlowRegion | hcompactRegion
  · exact hlow point hinterior hrelevant hlowRegion
  · exact hcompact point hinterior hrelevant hcompactRegion

/-- The bounded certificate and the proved analytic `k ≥ 128` tail give the
full determinant deep-region theorem. -/
theorem lrDeterminantDeepRegion_certificate_of_boundedDeep
    (hbounded : LRDeterminantBoundedDeepCertificateTheorem) :
    LRDeterminantRegionCertificateTheorem LRDeterminantDeepRegion := by
  intro point hinterior hrelevant hdeep
  rcases hdeep with ⟨hsDeep, hsk⟩
  by_cases hkBounded : point.k ≤ 128
  · exact hbounded point hinterior hrelevant
      ⟨hsDeep, hsk, hkBounded⟩
  · exact lrDeterminantAdmittedTarget_deepTail
      hinterior hrelevant hsDeep (lt_of_not_ge hkBounded).le

/-- End-to-end logical assembly from the two bounded inputs and the existing
analytic tail. -/
theorem lrDeterminantDeepRegion_certificate_of_low_and_compact
    (hlow : LRDeterminantBoundedDeepLowKCertificateTheorem)
    (hcompact : LRDeterminantBoundedDeepCompactCertificateTheorem) :
    LRDeterminantRegionCertificateTheorem LRDeterminantDeepRegion :=
  lrDeterminantDeepRegion_certificate_of_boundedDeep
    (lrDeterminantBoundedDeepRegion_certificate_of_low_and_compact
      hlow hcompact)

/-- End-to-end form for the future audited compact replay: a low-`k`
certificate, sound leaf checker, and accepted tree produce exactly the `deep`
field required by the determinant region ledger. -/
theorem lrDeterminantDeepRegion_certificate_of_checkedTree
    (terms : ℕ)
    (hlow : LRDeterminantBoundedDeepLowKCertificateTheorem)
    {AcceptData : Type}
    {acceptBox : CertificateBox → AcceptData → Bool}
    (accept_sound : ∀ box data, acceptBox box data = true →
      ∀ point, box.Contains point →
        LRDeterminantBoundedDeepCompactLeafProperty point)
    {certificate :
      SubdivisionCertificate AcceptData LRHighShapeVDiscardData}
    (hcheck : certificate.check acceptBox
      (lrHighShapeVDiscardCheck terms)
      lrDeterminantBoundedDeepCompactRoot = true) :
    LRDeterminantRegionCertificateTheorem LRDeterminantDeepRegion :=
  lrDeterminantDeepRegion_certificate_of_low_and_compact hlow
    (lrDeterminantBoundedDeepCompact_certificate_of_checkedTree terms
      accept_sound hcheck)

end CourtadeKumar
