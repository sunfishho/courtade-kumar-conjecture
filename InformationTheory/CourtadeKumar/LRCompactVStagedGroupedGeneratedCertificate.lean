import InformationTheory.CourtadeKumar.LRCompactVHybridDirectDGeneratedCertificate
import InformationTheory.CourtadeKumar.LRCompactVLambdaGroupedLeafChecker
import InformationTheory.CourtadeKumar.LRCompactVSameYGroupedLeafChecker

/-!
# Generated staged direct/adaptive-grouped compact-`V` certificates

The generator first tries the tight same-`y` grouped ratio, then retains the
independent-ratio checker as a closure-preserving fallback.  Each grouped
checker tries 128 terms before escalating to 192.  A direct proof is tagged
only when neither grouped proof closes the box.  The accepted-leaf tag is
part of the replay data, so the kernel replays exactly one arithmetic proof.

Subdivision keeps the empirically superior primary one-step lookahead.  The
grouped criterion closes the current box but does not perturb split scoring;
benchmarks showed that lambda-driven topology was slower and left more
unresolved volume.
-/

set_option autoImplicit false

namespace CourtadeKumar

namespace LRCompactVLambdaGroupedLeafCertificate

def ofB (headChoice : LRCompactVLambdaGroupedHeadChoice)
    (b : LRCompactVBCertificate) :
    LRCompactVLambdaGroupedLeafCertificate :=
  { b := b, headChoice := headChoice }

def auto (headChoice : LRCompactVLambdaGroupedHeadChoice)
    (logFuel : ℕ) (box : CertificateBox) :
    LRCompactVLambdaGroupedLeafCertificate :=
  ofB headChoice (LRCompactVBCertificate.hybridDirectDAuto logFuel box)

end LRCompactVLambdaGroupedLeafCertificate

namespace LRCompactVSameYGroupedLeafCertificate

def ofB (headChoice : LRCompactVLambdaGroupedHeadChoice)
    (b : LRCompactVBCertificate) :
    LRCompactVSameYGroupedLeafCertificate :=
  { logOnePlusVHi := b.logOnePlusV.upper
    headChoice := headChoice }

end LRCompactVSameYGroupedLeafCertificate

/-- A replay tag selects exactly one accepted-leaf checker. -/
inductive LRCompactVStagedGroupedLeafCertificate where
  | direct (certificate : LRCompactVHybridDirectDLeafCertificate)
  | sameY (certificate : LRCompactVSameYGroupedLeafCertificate)
  | grouped (certificate : LRCompactVLambdaGroupedLeafCertificate)

namespace LRCompactVStagedGroupedLeafCertificate

def check
    (logTerms pZeroTerms wTerms dTerms directN : ℕ)
    (box : CertificateBox)
    (certificate : LRCompactVStagedGroupedLeafCertificate) : Bool :=
  match certificate with
  | .direct data => data.check
      logTerms pZeroTerms wTerms dTerms directN box
  | .sameY data => data.check logTerms wTerms dTerms box
  | .grouped data => data.check logTerms wTerms dTerms box

/-- Try the tighter, smaller-payload same-`y` leaves first, then the
independent-ratio fallback, and finally a successful direct replay.
Returning `none` means that every closure test failed. -/
def selectAdaptiveReplay
    (logTerms wTerms dTerms : ℕ) (directOK : Bool)
    (box : CertificateBox)
    (direct : LRCompactVHybridDirectDLeafCertificate) :
    Option LRCompactVStagedGroupedLeafCertificate :=
  let tightReduced := LRCompactVSameYGroupedLeafCertificate.ofB
    .n128 direct.b
  if tightReduced.check logTerms wTerms dTerms box then
    some (.sameY tightReduced)
  else
    let tightFull := LRCompactVSameYGroupedLeafCertificate.ofB
      .n192 direct.b
    if tightFull.check logTerms wTerms dTerms box then
      some (.sameY tightFull)
    else
      let reduced := LRCompactVLambdaGroupedLeafCertificate.ofB
        .n128 direct.b
      if reduced.check logTerms wTerms dTerms box then
        some (.grouped reduced)
      else
        let full := LRCompactVLambdaGroupedLeafCertificate.ofB
          .n192 direct.b
        if full.check logTerms wTerms dTerms box then
          some (.grouped full)
        else if directOK then
          some (.direct direct)
        else
          none

theorem sound
    (logTerms pZeroTerms wTerms dTerms directN : ℕ)
    {box : CertificateBox}
    {certificate : LRCompactVStagedGroupedLeafCertificate}
    (hcheck : certificate.check
      logTerms pZeroTerms wTerms dTerms directN box = true) :
    ∀ point, box.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point := by
  cases certificate with
  | direct data =>
      exact data.sound
        logTerms pZeroTerms wTerms dTerms directN hcheck
  | sameY data =>
      exact data.sound logTerms wTerms dTerms hcheck
  | grouped data =>
      exact data.sound logTerms wTerms dTerms hcheck

end LRCompactVStagedGroupedLeafCertificate

/-- Direct-topology generation with adaptive grouped replay tags and primary
lookahead splits. -/
def generateLRCompactVStagedGroupedCertificate
    (logTerms pZeroTerms wTerms dTerms directN logFuel : ℕ) :
    ℕ → CertificateBox →
      SubdivisionCertificate
        LRCompactVStagedGroupedLeafCertificate LRCompactVDiscardCertificate
  | 0, box =>
      let direct :=
        LRCompactVHybridDirectDLeafCertificate.auto logFuel box
      let directOK := direct.check
        logTerms pZeroTerms wTerms dTerms directN box
      match LRCompactVStagedGroupedLeafCertificate.selectAdaptiveReplay
          logTerms wTerms dTerms directOK box direct with
      | some leaf => .accept leaf
      | none => .accept (.direct direct)
  | fuel + 1, box =>
      let discard :=
        LRCompactVDiscardCertificate.hybridDirectDAuto logFuel box
      if discard.check logTerms box then
        .discard discard
      else
        let direct : LRCompactVHybridDirectDLeafCertificate :=
          { b := discard.b }
        let directOK := direct.check
          logTerms pZeroTerms wTerms dTerms directN box
        match LRCompactVStagedGroupedLeafCertificate.selectAdaptiveReplay
            logTerms wTerms dTerms directOK box direct with
        | some leaf => .accept leaf
        | none =>
            let axis := lrCompactVHybridDirectDLookaheadSplitAxis
              logTerms pZeroTerms wTerms dTerms directN logFuel box
            let cut := lrCompactVHybridDirectDSplitCut box axis
            .split axis cut
              (generateLRCompactVStagedGroupedCertificate
                logTerms pZeroTerms wTerms dTerms directN logFuel fuel
                (box.lower axis cut))
              (generateLRCompactVStagedGroupedCertificate
                logTerms pZeroTerms wTerms dTerms directN logFuel fuel
                (box.upper axis cut))

theorem lrCompactVStagedGroupedSubdivisionCertificate_sound
    (logTerms pZeroTerms wTerms dTerms directN : ℕ)
    {box : CertificateBox}
    {certificate : SubdivisionCertificate
      LRCompactVStagedGroupedLeafCertificate LRCompactVDiscardCertificate}
    (hcheck : certificate.check
      (LRCompactVStagedGroupedLeafCertificate.check
        logTerms pZeroTerms wTerms dTerms directN)
      (LRCompactVDiscardCertificate.check logTerms) box = true) :
    ∀ point, box.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point := by
  have hstruct := subdivisionCertificate_sound
    (Relevant := LRCompactVPhysical)
    (Property := fun point ↦ LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point)
    (acceptBox := LRCompactVStagedGroupedLeafCertificate.check
      logTerms pZeroTerms wTerms dTerms directN)
    (discardBox := LRCompactVDiscardCertificate.check logTerms)
    (box := box) (certificate := certificate)
    (fun leaf data hleaf point hpoint hphysical ↦
      data.sound logTerms pZeroTerms wTerms dTerms directN hleaf
        point hpoint hphysical)
    (fun leaf data hleaf ↦ data.excludes_physical logTerms hleaf)
    hcheck
  intro point hpoint hphysical
  exact hstruct point hpoint hphysical hphysical

theorem generatedLRCompactVStagedGroupedCertificate_sound
    (logTerms pZeroTerms wTerms dTerms directN logFuel fuel : ℕ)
    {box : CertificateBox}
    (hcheck : (generateLRCompactVStagedGroupedCertificate
      logTerms pZeroTerms wTerms dTerms directN logFuel fuel box).check
        (LRCompactVStagedGroupedLeafCertificate.check
          logTerms pZeroTerms wTerms dTerms directN)
        (LRCompactVDiscardCertificate.check logTerms) box = true) :
    ∀ point, box.Contains point → LRCompactVPhysical point →
      0 ≤ lrCompactVReserveTarget point :=
  lrCompactVStagedGroupedSubdivisionCertificate_sound
    logTerms pZeroTerms wTerms dTerms directN hcheck

end CourtadeKumar
