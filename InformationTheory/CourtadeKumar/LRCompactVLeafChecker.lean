import InformationTheory.CourtadeKumar.LRCompactVWOneSeries

/-!
# Executable checked leaves for the compact `V` certificate

An accepted leaf now consists only of checked logarithm range reductions for
`B`.  The `P₀` and `W_R(1)` enclosures, all finite heads, both tails, and the
sign-sensitive grouped lower bound are recomputed exactly by Lean.
-/

namespace CourtadeKumar

/-- Untrusted data retained at one accepted compact leaf. -/
structure LRCompactVLeafCertificate where
  b : LRCompactVBCertificate

namespace LRCompactVLeafCertificate

def pZeroEnclosure
    (logTerms pZeroTerms : ℕ) (box : CertificateBox) :
    RationalEnclosure :=
  lrCompactVPZeroEnclosure logTerms pZeroTerms box

def wOneEnclosure
    (logTerms wTerms : ℕ) (box : CertificateBox) :
    RationalEnclosure :=
  lrCompactVWOneEnclosure logTerms wTerms box

def groupedLower
    (logTerms pZeroTerms wTerms N : ℕ)
    (box : CertificateBox) (certificate : LRCompactVLeafCertificate) : ℚ :=
  lrCompactVGroupedLower N box
    (certificate.b.evaluate logTerms box)
    (pZeroEnclosure logTerms pZeroTerms box)
    (wOneEnclosure logTerms wTerms box)

/-- The kernel-executable accepted-leaf test. -/
def check
    (logTerms pZeroTerms wTerms N : ℕ)
    (box : CertificateBox) (certificate : LRCompactVLeafCertificate) : Bool :=
  decide (
    certificate.b.check box = true ∧
    0 ≤ certificate.groupedLower
      logTerms pZeroTerms wTerms N box)

theorem sound
    (logTerms pZeroTerms wTerms N : ℕ)
    {box : CertificateBox} {certificate : LRCompactVLeafCertificate}
    (hcheck : certificate.check
      logTerms pZeroTerms wTerms N box = true) :
    ∀ point, box.Contains point → LRCompactVInterior point →
      0 ≤ lrCompactVReserveTarget point := by
  have hparts :
      certificate.b.check box = true ∧
      0 ≤ certificate.groupedLower
        logTerms pZeroTerms wTerms N box := by
    simpa [check] using hcheck
  have hboxCheck : LRCompactVBoxValid.check box = true := by
    have hbparts :
        LRCompactVBoxValid.check box = true ∧
        certificate.b.logOnePlusV.check
          (lrCompactVOnePlusVEnclosure box) = true ∧
        certificate.b.logOneSubRY.check
          (lrCompactVOneSubRYEnclosure box) = true := by
      simpa [LRCompactVBCertificate.check] using hparts.1
    exact hbparts.1
  have hbox := LRCompactVBoxValid.of_check hboxCheck
  intro point hpoint hinterior
  have hb := certificate.b.sound logTerms hpoint hinterior hparts.1
  have hpZero := lrCompactVPZeroEnclosure_sound
    logTerms pZeroTerms hbox hpoint hinterior
  have hwOne := lrCompactVWOneEnclosure_sound
    logTerms wTerms hbox hpoint hinterior
  have htarget :=
    lrCompactVCertificateTarget_nonnegative_of_groupedLower
      hbox hpoint hinterior hb hpZero hwOne hparts.2
  exact lrCompactVReserveTarget_nonneg_of_certificateTarget
    hinterior htarget

end LRCompactVLeafCertificate

/-- End-to-end structural soundness for a compact subdivision tree.  The
discard predicate remains a separate physical-domain certificate. -/
theorem lrCompactVSubdivisionCertificate_sound
    (logTerms pZeroTerms wTerms N : ℕ)
    {Relevant : CertificatePoint → Prop} {DiscardData : Type}
    {discardBox : CertificateBox → DiscardData → Bool}
    (hrelevant : ∀ point, Relevant point → LRCompactVInterior point)
    (discardSound : ∀ box data, discardBox box data = true →
      ∀ point, box.Contains point → ¬ Relevant point)
    {box : CertificateBox}
    {certificate :
      SubdivisionCertificate LRCompactVLeafCertificate DiscardData}
    (hcheck : certificate.check
      (LRCompactVLeafCertificate.check
        logTerms pZeroTerms wTerms N)
      discardBox box = true) :
    ∀ point, box.Contains point → Relevant point →
      0 ≤ lrCompactVReserveTarget point := by
  have hstruct := subdivisionCertificate_sound
    (Relevant := Relevant)
    (Property := fun point ↦ Relevant point →
      0 ≤ lrCompactVReserveTarget point)
    (acceptBox := LRCompactVLeafCertificate.check
      logTerms pZeroTerms wTerms N)
    (discardBox := discardBox) (box := box) (certificate := certificate)
    (fun leaf data hleaf point hpoint hrel ↦
      data.sound logTerms pZeroTerms wTerms N hleaf
        point hpoint (hrelevant point hrel))
    discardSound hcheck
  intro point hpoint hrel
  exact hstruct point hpoint hrel hrel

end CourtadeKumar
