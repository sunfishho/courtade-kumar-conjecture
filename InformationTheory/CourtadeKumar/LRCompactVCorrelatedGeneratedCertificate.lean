import InformationTheory.CourtadeKumar.LRCompactVCorrelatedLeafChecker
import InformationTheory.CourtadeKumar.LRCompactVGeneratedCertificate

/-!
# Replayable correlated compact `V` certificates

This generator is used on the five audited slabs from `R=17/20` through
`R=9/10`.  Failure to close a box before the fuel limit is represented by a
Boolean failure; it cannot produce a theorem.
-/

namespace CourtadeKumar

namespace LRCompactVCorrelatedLeafCertificate

def auto (logFuel : ℕ) (box : CertificateBox) :
    LRCompactVCorrelatedLeafCertificate :=
  { b := LRCompactVBCertificate.auto logFuel box
    logOneSubY := RationalEnclosure.autoLogIntervalCertificate logFuel
      (lrCompactVOneSubYEnclosure box) }

end LRCompactVCorrelatedLeafCertificate

def generateLRCompactVCorrelatedCertificate
    (logTerms pZeroTerms wTerms N logFuel : ℕ) :
    ℕ → CertificateBox →
      SubdivisionCertificate
        LRCompactVCorrelatedLeafCertificate LRCompactVDiscardCertificate
  | 0, box =>
      .accept (LRCompactVCorrelatedLeafCertificate.auto logFuel box)
  | fuel + 1, box =>
      let discard := LRCompactVDiscardCertificate.auto logFuel box
      if discard.check logTerms box then
        .discard discard
      else
        let accept := LRCompactVCorrelatedLeafCertificate.auto logFuel box
        if accept.check logTerms pZeroTerms wTerms N box then
          .accept accept
        else
          let axis := lrCompactVSplitAxis box
          let cut := lrCompactVSplitCut box axis
          .split axis cut
            (generateLRCompactVCorrelatedCertificate
              logTerms pZeroTerms wTerms N logFuel fuel
              (box.lower axis cut))
            (generateLRCompactVCorrelatedCertificate
              logTerms pZeroTerms wTerms N logFuel fuel
              (box.upper axis cut))

theorem lrCompactVCorrelatedSubdivisionCertificate_sound
    (logTerms pZeroTerms wTerms N : ℕ)
    {box : CertificateBox}
    {certificate : SubdivisionCertificate
      LRCompactVCorrelatedLeafCertificate LRCompactVDiscardCertificate}
    (hcheck : certificate.check
      (LRCompactVCorrelatedLeafCertificate.check
        logTerms pZeroTerms wTerms N)
      (LRCompactVDiscardCertificate.check logTerms) box = true) :
    ∀ point, box.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point := by
  have hstruct := subdivisionCertificate_sound
    (Relevant := LRCompactVPhysical)
    (Property := fun point => LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point)
    (acceptBox := LRCompactVCorrelatedLeafCertificate.check
      logTerms pZeroTerms wTerms N)
    (discardBox := LRCompactVDiscardCertificate.check logTerms)
    (box := box) (certificate := certificate)
    (fun leaf data hleaf point hpoint hphysical =>
      data.sound logTerms pZeroTerms wTerms N hleaf
        point hpoint hphysical)
    (fun leaf data hleaf => data.excludes_physical logTerms hleaf)
    hcheck
  intro point hpoint hphysical
  exact hstruct point hpoint hphysical hphysical

theorem generatedLRCompactVCorrelatedCertificate_sound
    (logTerms pZeroTerms wTerms N logFuel fuel : ℕ)
    {box : CertificateBox}
    (hcheck : (generateLRCompactVCorrelatedCertificate
      logTerms pZeroTerms wTerms N logFuel fuel box).check
        (LRCompactVCorrelatedLeafCertificate.check
          logTerms pZeroTerms wTerms N)
        (LRCompactVDiscardCertificate.check logTerms) box = true) :
    ∀ point, box.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point :=
  lrCompactVCorrelatedSubdivisionCertificate_sound
    logTerms pZeroTerms wTerms N hcheck

def lrCompactVR1720R78Root : CertificateBox :=
  lrCompactVSlabRoot (17 / 20) (7 / 8)

def lrCompactVR78R113128Root : CertificateBox :=
  lrCompactVSlabRoot (7 / 8) (113 / 128)

def lrCompactVR113128R227256Root : CertificateBox :=
  lrCompactVSlabRoot (113 / 128) (227 / 256)

def lrCompactVR227256R9211024Root : CertificateBox :=
  lrCompactVSlabRoot (227 / 256) (921 / 1024)

def lrCompactVR9211024R910Root : CertificateBox :=
  lrCompactVSlabRoot (921 / 1024) (9 / 10)

theorem generatedLRCompactVCorrelatedSlab_sound
    (logTerms pZeroTerms wTerms N logFuel fuel : ℕ)
    (RLo RHi : ℚ)
    (hcheck : (generateLRCompactVCorrelatedCertificate
      logTerms pZeroTerms wTerms N logFuel fuel
        (lrCompactVSlabRoot RLo RHi)).check
        (LRCompactVCorrelatedLeafCertificate.check
          logTerms pZeroTerms wTerms N)
        (LRCompactVDiscardCertificate.check logTerms)
        (lrCompactVSlabRoot RLo RHi) = true) :
    ∀ (R v t : ℝ),
      R ∈ Set.Ioo (0 : ℝ) 1 →
      (RLo : ℝ) ≤ R → R ≤ (RHi : ℝ) →
      v ∈ Set.Ioo (0 : ℝ) 1 → 1 / 3 ≤ v →
      t ∈ Set.Ioo (0 : ℝ) 1 → 17 / 20 ≤ t ^ 2 →
      0 < lrFlowJ R v t →
      0 ≤ lrLowVReserve R v t := by
  have hroot := generatedLRCompactVCorrelatedCertificate_sound
    logTerms pZeroTerms wTerms N logFuel fuel hcheck
  intro R v t hR hRLo hRHi hv hvLo ht hxLo hJ
  let point := lrCompactVFlowPoint R v t
  have htAbsUpper : |t| ≤ 1 := by
    rw [abs_of_pos ht.1]
    exact ht.2.le
  have hcontains : (lrCompactVSlabRoot RLo RHi).Contains point := by
    unfold lrCompactVSlabRoot point lrCompactVFlowPoint
      CertificateBox.Contains
    norm_num
    exact ⟨hRLo, hRHi, hvLo, hv.2.le, hxLo, htAbsUpper⟩
  have hphysical : LRCompactVPhysical point :=
    lrCompactVFlowPoint_physical hR hv ht hJ
  have hreserve := hroot point hcontains hphysical
  simpa [point, lrCompactVReserveTarget_flow ht.1] using hreserve

end CourtadeKumar
