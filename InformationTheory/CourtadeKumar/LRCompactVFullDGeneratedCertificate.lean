import InformationTheory.CourtadeKumar.LRCompactVGeneratedCertificate
import InformationTheory.CourtadeKumar.LRCompactVFullDLeafChecker

/-!
# Generated full-`D` compact certificates

This is the replayable generator used for the two audited middle channel
slabs.  Insufficient fuel again yields a Boolean failure, never a proof.
-/

namespace CourtadeKumar

namespace LRCompactVFullDLeafCertificate

def auto (logFuel : ℕ) (box : CertificateBox) :
    LRCompactVFullDLeafCertificate :=
  { b := LRCompactVBCertificate.auto logFuel box
    logOneSubY := RationalEnclosure.autoLogIntervalCertificate logFuel
      (lrCompactVOneSubYEnclosure box) }

end LRCompactVFullDLeafCertificate

def generateLRCompactVFullDCertificate
    (logTerms pZeroTerms wTerms N logFuel : ℕ) :
    ℕ → CertificateBox →
      SubdivisionCertificate
        LRCompactVFullDLeafCertificate LRCompactVDiscardCertificate
  | 0, box =>
      .accept (LRCompactVFullDLeafCertificate.auto logFuel box)
  | fuel + 1, box =>
      let discard := LRCompactVDiscardCertificate.auto logFuel box
      if discard.check logTerms box then
        .discard discard
      else
        let accept := LRCompactVFullDLeafCertificate.auto logFuel box
        if accept.check logTerms pZeroTerms wTerms N box then
          .accept accept
        else
          let axis := lrCompactVSplitAxis box
          let cut := lrCompactVSplitCut box axis
          .split axis cut
            (generateLRCompactVFullDCertificate
              logTerms pZeroTerms wTerms N logFuel fuel
              (box.lower axis cut))
            (generateLRCompactVFullDCertificate
              logTerms pZeroTerms wTerms N logFuel fuel
              (box.upper axis cut))

theorem lrCompactVFullDSubdivisionCertificate_sound
    (logTerms pZeroTerms wTerms N : ℕ)
    {box : CertificateBox}
    {certificate : SubdivisionCertificate
      LRCompactVFullDLeafCertificate LRCompactVDiscardCertificate}
    (hcheck : certificate.check
      (LRCompactVFullDLeafCertificate.check
        logTerms pZeroTerms wTerms N)
      (LRCompactVDiscardCertificate.check logTerms) box = true) :
    ∀ point, box.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point := by
  have hstruct := subdivisionCertificate_sound
    (Relevant := LRCompactVPhysical)
    (Property := fun point ↦ LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point)
    (acceptBox := LRCompactVFullDLeafCertificate.check
      logTerms pZeroTerms wTerms N)
    (discardBox := LRCompactVDiscardCertificate.check logTerms)
    (box := box) (certificate := certificate)
    (fun leaf data hleaf point hpoint hphysical ↦
      data.sound logTerms pZeroTerms wTerms N hleaf
        point hpoint hphysical.1)
    (fun leaf data hleaf ↦ data.excludes_physical logTerms hleaf)
    hcheck
  intro point hpoint hphysical
  exact hstruct point hpoint hphysical hphysical

theorem generatedLRCompactVFullDCertificate_sound
    (logTerms pZeroTerms wTerms N logFuel fuel : ℕ)
    {box : CertificateBox}
    (hcheck : (generateLRCompactVFullDCertificate
      logTerms pZeroTerms wTerms N logFuel fuel box).check
        (LRCompactVFullDLeafCertificate.check
          logTerms pZeroTerms wTerms N)
        (LRCompactVDiscardCertificate.check logTerms) box = true) :
    ∀ point, box.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point :=
  lrCompactVFullDSubdivisionCertificate_sound
    logTerms pZeroTerms wTerms N hcheck

def lrCompactVSlabRoot (RLo RHi : ℚ) : CertificateBox where
  sLo := RLo
  sHi := RHi
  kLo := 1 / 3
  kHi := 1
  chiLo := 17 / 20
  chiHi := 1

def lrCompactVR34R1316Root : CertificateBox :=
  lrCompactVSlabRoot (3 / 4) (13 / 16)

def lrCompactVR1316R1720Root : CertificateBox :=
  lrCompactVSlabRoot (13 / 16) (17 / 20)

theorem generatedLRCompactVFullDSlab_sound
    (logTerms pZeroTerms wTerms N logFuel fuel : ℕ)
    (RLo RHi : ℚ)
    (hcheck : (generateLRCompactVFullDCertificate
      logTerms pZeroTerms wTerms N logFuel fuel
        (lrCompactVSlabRoot RLo RHi)).check
        (LRCompactVFullDLeafCertificate.check
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
  have hroot := generatedLRCompactVFullDCertificate_sound
    logTerms pZeroTerms wTerms N logFuel fuel hcheck
  intro R v t hR hRLo hRHi hv hvLo ht hxLo hJ
  let point := lrCompactVFlowPoint R v t
  have htAbsUpper : |t| ≤ 1 := by
    rw [abs_of_pos ht.1]
    exact ht.2.le
  have hcontains : (lrCompactVSlabRoot RLo RHi).Contains point := by
    unfold lrCompactVSlabRoot point lrCompactVFlowPoint CertificateBox.Contains
    norm_num
    exact ⟨hRLo, hRHi, hvLo, hv.2.le, hxLo, htAbsUpper⟩
  have hphysical : LRCompactVPhysical point :=
    lrCompactVFlowPoint_physical hR hv ht hJ
  have hreserve := hroot point hcontains hphysical
  simpa [point, lrCompactVReserveTarget_flow ht.1] using hreserve

end CourtadeKumar
