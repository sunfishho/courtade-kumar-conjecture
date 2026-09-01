import InformationTheory.CourtadeKumar.LRCompactVHybridDirectDLeafChecker
import InformationTheory.CourtadeKumar.LRDeterminantAutoCertificateCore

/-!
# Generated hybrid direct-`D` compact certificates

This generator uses the stronger maximum of the tail-enhanced and direct-head
`P_W` bounds together with the cancellation-free direct enclosure of `D`.
The accepted-leaf payload contains only the two logarithm certificates needed
for `B`; unlike the older full-`D` generator, it carries no certificate for
`log (1-y)`.

Generation remains untrusted.  The ordinary recursive Boolean checker replays
the resulting subdivision tree, and the soundness theorem below interprets
only a successful replay.
-/

set_option autoImplicit false

namespace CourtadeKumar

namespace LRCompactVBCertificate

def hybridDirectDAuto (logFuel : ℕ) (box : CertificateBox) :
    LRCompactVBCertificate :=
  { logOnePlusV := RationalEnclosure.autoLogIntervalCertificate logFuel
      (lrCompactVOnePlusVEnclosure box)
    logOneSubRY := RationalEnclosure.autoLogIntervalCertificate logFuel
      (lrCompactVOneSubRYEnclosure box) }

end LRCompactVBCertificate

namespace LRCompactVHybridDirectDLeafCertificate

def auto (logFuel : ℕ) (box : CertificateBox) :
    LRCompactVHybridDirectDLeafCertificate :=
  { b := LRCompactVBCertificate.hybridDirectDAuto logFuel box }

end LRCompactVHybridDirectDLeafCertificate

namespace LRCompactVDiscardCertificate

def hybridDirectDAuto (logFuel : ℕ) (box : CertificateBox) :
    LRCompactVDiscardCertificate :=
  { b := LRCompactVBCertificate.hybridDirectDAuto logFuel box
    logOneSubY := RationalEnclosure.autoLogIntervalCertificate logFuel
      (lrCompactVOneSubYEnclosure box) }

end LRCompactVDiscardCertificate

/-- Weighted longest-axis rule inherited from the audited compact replay. -/
def lrCompactVHybridDirectDSplitAxis
    (box : CertificateBox) : CertificateAxis :=
  let rWidth := 8 * (box.sHi - box.sLo)
  let vWidth := 9 * (box.kHi - box.kLo)
  let xWidth := 40 * (box.chiHi - box.chiLo)
  if vWidth ≤ rWidth ∧ xWidth ≤ rWidth then .s
  else if xWidth ≤ vWidth then .k
  else .chi

def lrCompactVHybridDirectDSplitCut
    (box : CertificateBox) (axis : CertificateAxis) : ℚ :=
  match axis with
  | .s => (box.sLo + box.sHi) / 2
  | .k => (box.kLo + box.kHi) / 2
  | .chi => (box.chiLo + box.chiHi) / 2

def lrCompactVHybridDirectDSlabRoot (RLo RHi : ℚ) : CertificateBox where
  sLo := RLo
  sHi := RHi
  kLo := 1 / 3
  kHi := 1
  chiLo := 17 / 20
  chiHi := 1

structure LRCompactVHybridDirectDChildScore where
  closed : ℕ
  lower : ℚ

structure LRCompactVHybridDirectDSplitScore where
  closed : ℕ
  minimum : ℚ
  total : ℚ

/-- Discards receive a large sentinel only for split selection.  This value
does not enter the certificate checker or any soundness theorem. -/
def lrCompactVHybridDirectDDiscardScore : ℚ := 10 ^ (100 : ℕ)

def lrCompactVHybridDirectDChildScore
    (logTerms pZeroTerms wTerms dTerms N logFuel : ℕ)
    (box : CertificateBox) : LRCompactVHybridDirectDChildScore :=
  let discard := LRCompactVDiscardCertificate.hybridDirectDAuto logFuel box
  if discard.check logTerms box then
    { closed := 1, lower := lrCompactVHybridDirectDDiscardScore }
  else
    let accept := LRCompactVHybridDirectDLeafCertificate.auto logFuel box
    { closed := if accept.check
        logTerms pZeroTerms wTerms dTerms N box then 1 else 0
      lower := accept.groupedLower
        logTerms pZeroTerms wTerms dTerms N box }

def lrCompactVHybridDirectDSplitScore
    (logTerms pZeroTerms wTerms dTerms N logFuel : ℕ)
    (box : CertificateBox) (axis : CertificateAxis) :
    LRCompactVHybridDirectDSplitScore :=
  let cut := lrCompactVHybridDirectDSplitCut box axis
  let lower := lrCompactVHybridDirectDChildScore
    logTerms pZeroTerms wTerms dTerms N logFuel (box.lower axis cut)
  let upper := lrCompactVHybridDirectDChildScore
    logTerms pZeroTerms wTerms dTerms N logFuel (box.upper axis cut)
  { closed := lower.closed + upper.closed
    minimum := min lower.lower upper.lower
    total := lower.lower + upper.lower }

/-- Strict lexicographic comparison used by the one-step lookahead rule:
first close as many children as possible, then maximize the weaker child,
then maximize the sum of both lower scores. -/
def LRCompactVHybridDirectDSplitScore.better
    (candidate incumbent : LRCompactVHybridDirectDSplitScore) : Bool :=
  decide (
    incumbent.closed < candidate.closed ∨
    (candidate.closed = incumbent.closed ∧
      (incumbent.minimum < candidate.minimum ∨
       (candidate.minimum = incumbent.minimum ∧
        incumbent.total < candidate.total))))

/-- One-step exact lookahead.  Exact ties retain the order `R`, `v`, `x`. -/
def lrCompactVHybridDirectDLookaheadSplitAxis
    (logTerms pZeroTerms wTerms dTerms N logFuel : ℕ)
    (box : CertificateBox) : CertificateAxis :=
  let sScore := lrCompactVHybridDirectDSplitScore
    logTerms pZeroTerms wTerms dTerms N logFuel box .s
  let kScore := lrCompactVHybridDirectDSplitScore
    logTerms pZeroTerms wTerms dTerms N logFuel box .k
  let chiScore := lrCompactVHybridDirectDSplitScore
    logTerms pZeroTerms wTerms dTerms N logFuel box .chi
  let preferK := kScore.better sScore
  let firstAxis := if preferK then .k else .s
  let firstScore := if preferK then kScore else sScore
  if chiScore.better firstScore then .chi else firstAxis

def generateLRCompactVHybridDirectDCertificate
    (logTerms pZeroTerms wTerms dTerms N logFuel : ℕ) :
    ℕ → CertificateBox →
      SubdivisionCertificate
        LRCompactVHybridDirectDLeafCertificate LRCompactVDiscardCertificate
  | 0, box =>
      .accept (LRCompactVHybridDirectDLeafCertificate.auto logFuel box)
  | fuel + 1, box =>
      let discard := LRCompactVDiscardCertificate.hybridDirectDAuto
        logFuel box
      if discard.check logTerms box then
        .discard discard
      else
        let accept :=
          LRCompactVHybridDirectDLeafCertificate.auto logFuel box
        if accept.check
            logTerms pZeroTerms wTerms dTerms N box then
          .accept accept
        else
          let axis := lrCompactVHybridDirectDSplitAxis box
          let cut := lrCompactVHybridDirectDSplitCut box axis
          .split axis cut
            (generateLRCompactVHybridDirectDCertificate
              logTerms pZeroTerms wTerms dTerms N logFuel fuel
              (box.lower axis cut))
            (generateLRCompactVHybridDirectDCertificate
              logTerms pZeroTerms wTerms dTerms N logFuel fuel
              (box.upper axis cut))

def generateLRCompactVHybridDirectDLookaheadCertificate
    (logTerms pZeroTerms wTerms dTerms N logFuel : ℕ) :
    ℕ → CertificateBox →
      SubdivisionCertificate
        LRCompactVHybridDirectDLeafCertificate LRCompactVDiscardCertificate
  | 0, box =>
      .accept (LRCompactVHybridDirectDLeafCertificate.auto logFuel box)
  | fuel + 1, box =>
      let discard := LRCompactVDiscardCertificate.hybridDirectDAuto
        logFuel box
      if discard.check logTerms box then
        .discard discard
      else
        let accept :=
          LRCompactVHybridDirectDLeafCertificate.auto logFuel box
        if accept.check
            logTerms pZeroTerms wTerms dTerms N box then
          .accept accept
        else
          let axis := lrCompactVHybridDirectDLookaheadSplitAxis
            logTerms pZeroTerms wTerms dTerms N logFuel box
          let cut := lrCompactVHybridDirectDSplitCut box axis
          .split axis cut
            (generateLRCompactVHybridDirectDLookaheadCertificate
              logTerms pZeroTerms wTerms dTerms N logFuel fuel
              (box.lower axis cut))
            (generateLRCompactVHybridDirectDLookaheadCertificate
              logTerms pZeroTerms wTerms dTerms N logFuel fuel
              (box.upper axis cut))

theorem lrCompactVHybridDirectDSubdivisionCertificate_sound
    (logTerms pZeroTerms wTerms dTerms N : ℕ)
    {box : CertificateBox}
    {certificate : SubdivisionCertificate
      LRCompactVHybridDirectDLeafCertificate LRCompactVDiscardCertificate}
    (hcheck : certificate.check
      (LRCompactVHybridDirectDLeafCertificate.check
        logTerms pZeroTerms wTerms dTerms N)
      (LRCompactVDiscardCertificate.check logTerms) box = true) :
    ∀ point, box.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point := by
  have hstruct := subdivisionCertificate_sound
    (Relevant := LRCompactVPhysical)
    (Property := fun point ↦ LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point)
    (acceptBox := LRCompactVHybridDirectDLeafCertificate.check
      logTerms pZeroTerms wTerms dTerms N)
    (discardBox := LRCompactVDiscardCertificate.check logTerms)
    (box := box) (certificate := certificate)
    (fun leaf data hleaf point hpoint hphysical ↦
      data.sound logTerms pZeroTerms wTerms dTerms N hleaf
        point hpoint hphysical)
    (fun leaf data hleaf ↦ data.excludes_physical logTerms hleaf)
    hcheck
  intro point hpoint hphysical
  exact hstruct point hpoint hphysical hphysical

theorem generatedLRCompactVHybridDirectDCertificate_sound
    (logTerms pZeroTerms wTerms dTerms N logFuel fuel : ℕ)
    {box : CertificateBox}
    (hcheck : (generateLRCompactVHybridDirectDCertificate
      logTerms pZeroTerms wTerms dTerms N logFuel fuel box).check
        (LRCompactVHybridDirectDLeafCertificate.check
          logTerms pZeroTerms wTerms dTerms N)
        (LRCompactVDiscardCertificate.check logTerms) box = true) :
    ∀ point, box.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point :=
  lrCompactVHybridDirectDSubdivisionCertificate_sound
    logTerms pZeroTerms wTerms dTerms N hcheck

theorem generatedLRCompactVHybridDirectDLookaheadCertificate_sound
    (logTerms pZeroTerms wTerms dTerms N logFuel fuel : ℕ)
    {box : CertificateBox}
    (hcheck : (generateLRCompactVHybridDirectDLookaheadCertificate
      logTerms pZeroTerms wTerms dTerms N logFuel fuel box).check
        (LRCompactVHybridDirectDLeafCertificate.check
          logTerms pZeroTerms wTerms dTerms N)
        (LRCompactVDiscardCertificate.check logTerms) box = true) :
    ∀ point, box.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point :=
  lrCompactVHybridDirectDSubdivisionCertificate_sound
    logTerms pZeroTerms wTerms dTerms N hcheck

theorem generatedLRCompactVHybridDirectDSlab_sound
    (logTerms pZeroTerms wTerms dTerms N logFuel fuel : ℕ)
    (RLo RHi : ℚ)
    (hcheck : (generateLRCompactVHybridDirectDCertificate
      logTerms pZeroTerms wTerms dTerms N logFuel fuel
        (lrCompactVHybridDirectDSlabRoot RLo RHi)).check
        (LRCompactVHybridDirectDLeafCertificate.check
          logTerms pZeroTerms wTerms dTerms N)
        (LRCompactVDiscardCertificate.check logTerms)
        (lrCompactVHybridDirectDSlabRoot RLo RHi) = true) :
    ∀ (R v t : ℝ),
      R ∈ Set.Ioo (0 : ℝ) 1 →
      (RLo : ℝ) ≤ R → R ≤ (RHi : ℝ) →
      v ∈ Set.Ioo (0 : ℝ) 1 → 1 / 3 ≤ v →
      t ∈ Set.Ioo (0 : ℝ) 1 → 17 / 20 ≤ t ^ 2 →
      0 < lrFlowJ R v t →
      0 ≤ lrLowVReserve R v t := by
  have hroot := generatedLRCompactVHybridDirectDCertificate_sound
    logTerms pZeroTerms wTerms dTerms N logFuel fuel hcheck
  intro R v t hR hRLo hRHi hv hvLo ht hxLo hJ
  let point := lrCompactVFlowPoint R v t
  have htAbsUpper : |t| ≤ 1 := by
    rw [abs_of_pos ht.1]
    exact ht.2.le
  have hcontains :
      (lrCompactVHybridDirectDSlabRoot RLo RHi).Contains point := by
    unfold lrCompactVHybridDirectDSlabRoot point lrCompactVFlowPoint
      CertificateBox.Contains
    norm_num
    exact ⟨hRLo, hRHi, hvLo, hv.2.le, hxLo, htAbsUpper⟩
  have hphysical : LRCompactVPhysical point :=
    lrCompactVFlowPoint_physical hR hv ht hJ
  have hreserve := hroot point hcontains hphysical
  simpa [point, lrCompactVReserveTarget_flow ht.1] using hreserve

end CourtadeKumar
