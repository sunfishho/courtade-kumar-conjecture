import InformationTheory.CourtadeKumar.LRCompactVAutoCertificate

/-!
# Fuel-bounded compact subdivision generator

This executable Lean program constructs a candidate subdivision tree.  It
tries the checked physical discard first, then the checked grouped lower
bound, and otherwise bisects the widest weighted coordinate.  Generation is
not trusted: the ordinary subdivision checker replays the returned tree.
-/

namespace CourtadeKumar

/-- Weighted longest-axis rule used by the audited compact replay. -/
def lrCompactVSplitAxis (box : CertificateBox) : CertificateAxis :=
  let rWidth := 8 * (box.sHi - box.sLo)
  let vWidth := 9 * (box.kHi - box.kLo)
  let xWidth := 40 * (box.chiHi - box.chiLo)
  if vWidth ≤ rWidth ∧ xWidth ≤ rWidth then .s
  else if xWidth ≤ vWidth then .k
  else .chi

def lrCompactVSplitCut
    (box : CertificateBox) (axis : CertificateAxis) : ℚ :=
  match axis with
  | .s => (box.sLo + box.sHi) / 2
  | .k => (box.kLo + box.kHi) / 2
  | .chi => (box.chiLo + box.chiHi) / 2

/-- Construct a candidate compact certificate.  At exhausted fuel an
unaccepted leaf is returned; the later Boolean replay then evaluates to
`false`, so insufficient fuel cannot create a false proof. -/
def generateLRCompactVCertificate
    (logTerms pZeroTerms wTerms N logFuel : ℕ) :
    ℕ → CertificateBox →
      SubdivisionCertificate
        LRCompactVLeafCertificate LRCompactVDiscardCertificate
  | 0, box =>
      .accept (LRCompactVLeafCertificate.auto logFuel box)
  | fuel + 1, box =>
      let discard := LRCompactVDiscardCertificate.auto logFuel box
      if discard.check logTerms box then
        .discard discard
      else
        let accept := LRCompactVLeafCertificate.auto logFuel box
        if accept.check logTerms pZeroTerms wTerms N box then
          .accept accept
        else
          let axis := lrCompactVSplitAxis box
          let cut := lrCompactVSplitCut box axis
          .split axis cut
            (generateLRCompactVCertificate
              logTerms pZeroTerms wTerms N logFuel fuel
              (box.lower axis cut))
            (generateLRCompactVCertificate
              logTerms pZeroTerms wTerms N logFuel fuel
              (box.upper axis cut))

/-- Successful replay of a generated tree proves the compact physical
reserve.  The hypothesis is a kernel-reducible Boolean equality. -/
theorem generatedLRCompactVCertificate_sound
    (logTerms pZeroTerms wTerms N logFuel fuel : ℕ)
    {box : CertificateBox}
    (hcheck : (generateLRCompactVCertificate
      logTerms pZeroTerms wTerms N logFuel fuel box).check
        (LRCompactVLeafCertificate.check
          logTerms pZeroTerms wTerms N)
        (LRCompactVDiscardCertificate.check logTerms) box = true) :
    ∀ point, box.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point := by
  exact lrCompactVPhysicalSubdivisionCertificate_sound
    logTerms pZeroTerms wTerms N hcheck

/-- Root box for the audited compact slab `R≤3/4`. -/
def lrCompactVR34Root : CertificateBox where
  sLo := 0
  sHi := 3 / 4
  kLo := 1 / 3
  kHi := 1
  chiLo := 17 / 20
  chiHi := 1

/-- A successful generated replay on the audited root proves the `V`
reserve throughout the `R≤3/4` high-shape slab. -/
theorem generatedLRCompactVR34_sound
    (logTerms pZeroTerms wTerms N logFuel fuel : ℕ)
    (hcheck : (generateLRCompactVCertificate
      logTerms pZeroTerms wTerms N logFuel fuel lrCompactVR34Root).check
        (LRCompactVLeafCertificate.check
          logTerms pZeroTerms wTerms N)
        (LRCompactVDiscardCertificate.check logTerms)
        lrCompactVR34Root = true) :
    ∀ (R v t : ℝ),
      R ∈ Set.Ioo (0 : ℝ) 1 → R ≤ 3 / 4 →
      v ∈ Set.Ioo (0 : ℝ) 1 → 1 / 3 ≤ v →
      t ∈ Set.Ioo (0 : ℝ) 1 → 17 / 20 ≤ t ^ 2 →
      0 < lrFlowJ R v t →
      0 ≤ lrLowVReserve R v t := by
  have hroot := generatedLRCompactVCertificate_sound
    logTerms pZeroTerms wTerms N logFuel fuel hcheck
  intro R v t hR hRUpper hv hvLower ht htLower hJ
  let point := lrCompactVFlowPoint R v t
  have htSqUpper : t ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2.le)]
  have htAbsUpper : |t| ≤ 1 := by
    rw [abs_of_pos ht.1]
    exact ht.2.le
  have hcontains : lrCompactVR34Root.Contains point := by
    unfold lrCompactVR34Root point lrCompactVFlowPoint CertificateBox.Contains
    norm_num
    exact ⟨hR.1.le, hRUpper, hvLower, hv.2.le, htLower, htAbsUpper⟩
  have hphysical : LRCompactVPhysical point :=
    lrCompactVFlowPoint_physical hR hv ht hJ
  have hreserve := hroot point hcontains hphysical
  simpa [point, lrCompactVReserveTarget_flow ht.1] using hreserve

end CourtadeKumar
