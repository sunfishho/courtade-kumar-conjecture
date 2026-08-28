import InformationTheory.CourtadeKumar.LRCombinedHighShapeAssembly

/-!
# Generator for the combined high-shape alternative

At each leaf the generator first tries direct `V`.  If that fails, it tries
the midpoint-and-tangent pair.  Its split score adds the certified midpoint
and tangent derivative losses, so subdivision concentrates on whichever
coordinate obstructs the paired proof most strongly.
-/

namespace CourtadeKumar
namespace LRCombinedHighShapeAutoTree

abbrev Tree := SubdivisionCertificate LRHighShapeCombinedAcceptData
  LRHighShapeVDiscardData

def splitScoreS (terms : ℕ) (box : CertificateBox)
    (payload : LRHighShapeTangentCertificate) : ℚ :=
  LRHighShapeMidpointAutoTree.splitScoreS terms box payload.base +
    LRHighShapeTangentAutoTree.splitScoreS terms box payload

def splitScoreK (terms : ℕ) (box : CertificateBox)
    (payload : LRHighShapeTangentCertificate) : ℚ :=
  LRHighShapeMidpointAutoTree.splitScoreK terms box payload.base +
    LRHighShapeTangentAutoTree.splitScoreK terms box payload

def splitScoreChi (terms : ℕ) (box : CertificateBox)
    (payload : LRHighShapeTangentCertificate) : ℚ :=
  LRHighShapeMidpointAutoTree.splitScoreChi terms box payload.base +
    LRHighShapeTangentAutoTree.splitScoreChi terms box payload

def chooseAxis (terms : ℕ) (box : CertificateBox)
    (payload : LRHighShapeTangentCertificate) : CertificateAxis :=
  -- Compute each large AD enclosure once.  Expanding `splitScoreS/K/Chi`
  -- separately would repeat both evaluations three times at every split.
  let uResult := payload.base.evaluateAD terms box
  let tResult := payload.evaluateAD terms box
  let ss :=
    uResult.derivS.maxAbs * RationalEnclosure.radius box.sInterval +
      tResult.derivS.maxAbs * RationalEnclosure.radius box.sInterval
  let sk :=
    uResult.derivK.maxAbs * RationalEnclosure.radius box.kInterval +
      tResult.derivK.maxAbs * RationalEnclosure.radius box.kInterval
  let sc :=
    uResult.derivChi.maxAbs * RationalEnclosure.radius box.chiInterval +
      tResult.derivChi.maxAbs * RationalEnclosure.radius box.chiInterval
  -- A failed box touching an endpoint is first separated in `χ`.  The
  -- derivative scores come from the open chart and are deliberately not
  -- used to steer subdivision across its logarithmic boundary.
  if (box.chiLo = 0 ∨ box.chiHi = 1) ∧
      1 / 256 < box.chiHi - box.chiLo then .chi
  else if ss ≥ sk ∧ ss ≥ sc ∧ box.sLo < box.sHi then .s
  else if sk ≥ sc ∧ box.kLo < box.kHi then .k
  else .chi

def axisCut (box : CertificateBox) : CertificateAxis → ℚ
  | .s => RationalEnclosure.center box.sInterval
  | .k => RationalEnclosure.center box.kInterval
  | .chi => RationalEnclosure.center box.chiInterval

def pairAccepts (terms : ℕ) (box : CertificateBox)
    (payload : LRHighShapeTangentCertificate) : Bool :=
  LRHighShapeMidpointCertificate.accepts terms box payload.base &&
    LRHighShapeTangentCertificate.accepts terms box payload

def autoAccept (terms sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (payload : LRHighShapeTangentCertificate) :
    Option LRHighShapeCombinedAcceptData :=
  if LRHighShapeVCertificate.rawAccepts terms box payload.base then
    some (.directV payload.base)
  else
    let centeredPair := LRHighShapeCenteredPairCertificate.auto
      sqrtFuel logFuel box payload
    let centered : LRHighShapeVCenteredCertificate :=
      { center := centeredPair.center.base, derivative := payload.base }
    if centeredPair.pairAccepts terms box then
      some (.midpointTangentCentered centeredPair)
    else if LRHighShapeVCenteredCertificate.accepts terms box centered then
      some (.directVCentered centered)
    else if LRHighShapeVCertificate.midpointAccepts terms box payload.base then
      some (.directVMidpoint payload.base)
    else if pairAccepts terms box payload then
      some (.midpointTangent payload)
    else
      let zeroFaceCentered :=
        LRHighShapeVZeroFaceSKCenteredCertificate.autoFromBase
        sqrtFuel logFuel box payload.base
      if zeroFaceCentered.accepts terms box then
        some (.directVZeroFaceSKCentered zeroFaceCentered)
      else if zeroFaceCentered.derivative.accepts terms box then
        some (.directVZeroFace zeroFaceCentered.derivative)
      else none

theorem autoAccept_check_of_eq
    (terms sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (payload : LRHighShapeTangentCertificate)
    (data : LRHighShapeCombinedAcceptData)
    (haccept : autoAccept terms sqrtFuel logFuel box payload = some data) :
    data.check terms box = true := by
  let centeredPair := LRHighShapeCenteredPairCertificate.auto
    sqrtFuel logFuel box payload
  let centered : LRHighShapeVCenteredCertificate :=
    { center := centeredPair.center.base, derivative := payload.base }
  let zeroFaceCentered :=
    LRHighShapeVZeroFaceSKCenteredCertificate.autoFromBase
    sqrtFuel logFuel box payload.base
  by_cases hV : LRHighShapeVCertificate.rawAccepts
      terms box payload.base = true
  · simp [autoAccept, hV] at haccept
    cases haccept
    simpa [LRHighShapeCombinedAcceptData.check] using hV
  have hVFalse : LRHighShapeVCertificate.rawAccepts
      terms box payload.base = false := Bool.eq_false_of_not_eq_true hV
  by_cases hPairCentered : centeredPair.pairAccepts terms box = true
  · simp [autoAccept, hVFalse, centeredPair, hPairCentered] at haccept
    cases haccept
    simpa [LRHighShapeCombinedAcceptData.check] using hPairCentered
  have hPairCenteredFalse : centeredPair.pairAccepts terms box = false :=
    Bool.eq_false_of_not_eq_true hPairCentered
  by_cases hVCentered : LRHighShapeVCenteredCertificate.accepts
      terms box centered = true
  · simp [autoAccept, hVFalse, centeredPair, centered,
      hPairCenteredFalse, hVCentered] at haccept
    cases haccept
    simpa [LRHighShapeCombinedAcceptData.check] using hVCentered
  have hVCenteredFalse : LRHighShapeVCenteredCertificate.accepts
      terms box centered = false := Bool.eq_false_of_not_eq_true hVCentered
  by_cases hVMid : LRHighShapeVCertificate.midpointAccepts
      terms box payload.base = true
  · simp [autoAccept, hVFalse, centeredPair, centered,
      hPairCenteredFalse, hVCenteredFalse, hVMid] at haccept
    cases haccept
    simpa [LRHighShapeCombinedAcceptData.check] using hVMid
  have hVMidFalse : LRHighShapeVCertificate.midpointAccepts
      terms box payload.base = false := Bool.eq_false_of_not_eq_true hVMid
  by_cases hpair : pairAccepts terms box payload = true
  · simp [autoAccept, hVFalse, centeredPair, centered,
      hPairCenteredFalse, hVCenteredFalse, hVMidFalse, hpair] at haccept
    cases haccept
    simpa [LRHighShapeCombinedAcceptData.check, pairAccepts] using hpair
  have hpairFalse : pairAccepts terms box payload = false :=
    Bool.eq_false_of_not_eq_true hpair
  by_cases hZeroCentered : zeroFaceCentered.accepts terms box = true
  · simp [autoAccept, hVFalse, centeredPair, centered, zeroFaceCentered,
      hPairCenteredFalse, hVCenteredFalse, hVMidFalse, hpairFalse,
      hZeroCentered] at haccept
    cases haccept
    simpa [LRHighShapeCombinedAcceptData.check] using hZeroCentered
  have hZeroCenteredFalse : zeroFaceCentered.accepts terms box = false :=
    Bool.eq_false_of_not_eq_true hZeroCentered
  by_cases hZero : zeroFaceCentered.derivative.accepts terms box = true
  · simp [autoAccept, hVFalse, centeredPair, centered, zeroFaceCentered,
      hPairCenteredFalse, hVCenteredFalse, hVMidFalse, hpairFalse,
      hZeroCenteredFalse, hZero] at haccept
    cases haccept
    simpa [LRHighShapeCombinedAcceptData.check] using hZero
  · have hZeroFalse : zeroFaceCentered.derivative.accepts terms box = false :=
      Bool.eq_false_of_not_eq_true hZero
    simp [autoAccept, hVFalse, centeredPair, centered, zeroFaceCentered,
      hPairCenteredFalse, hVCenteredFalse, hVMidFalse, hpairFalse,
      hZeroCenteredFalse, hZeroFalse] at haccept

def buildTree (terms sqrtFuel logFuel : ℕ) : ℕ → CertificateBox → Option Tree
  | 0, box =>
      let payload := LRHighShapeTangentCertificate.auto sqrtFuel logFuel box
      match autoAccept terms sqrtFuel logFuel box payload with
      | some data => some (.accept data)
      | none =>
        match LRHighShapeMidpointAutoTree.autoDiscard terms box payload.base with
        | some data => some (.discard data)
        | none => none
  | fuel + 1, box =>
      let payload := LRHighShapeTangentCertificate.auto sqrtFuel logFuel box
      match autoAccept terms sqrtFuel logFuel box payload with
      | some data => some (.accept data)
      | none =>
        match LRHighShapeMidpointAutoTree.autoDiscard terms box payload.base with
        | some data => some (.discard data)
        | none =>
            let axis := chooseAxis terms box payload
            let cut := axisCut box axis
            match buildTree terms sqrtFuel logFuel fuel
                (box.lower axis cut) with
            | none => none
            | some lower =>
                match buildTree terms sqrtFuel logFuel fuel
                    (box.upper axis cut) with
                | none => none
                | some upper => some (.split axis cut lower upper)

def treeNodes : Tree → ℕ
  | .accept _ => 1
  | .discard _ => 1
  | .split _ _ lower upper => 1 + treeNodes lower + treeNodes upper

theorem buildTree_check_of_eq
    (terms sqrtFuel logFuel fuel : ℕ) (box : CertificateBox) (tree : Tree)
    (hbuild : buildTree terms sqrtFuel logFuel fuel box = some tree) :
    tree.check (LRHighShapeCombinedAcceptData.check terms)
      (lrHighShapeVDiscardCheck terms) box = true := by
  induction fuel generalizing box tree with
  | zero =>
      let payload := LRHighShapeTangentCertificate.auto sqrtFuel logFuel box
      change (match autoAccept terms sqrtFuel logFuel box payload with
        | some data => some (.accept data)
        | none =>
          match LRHighShapeMidpointAutoTree.autoDiscard
              terms box payload.base with
          | some data => some (.discard data)
          | none => none) = some tree at hbuild
      generalize haccept : autoAccept terms sqrtFuel logFuel box payload =
        acceptOption
      cases acceptOption with
      | some data =>
          simp only [haccept, Option.some.injEq] at hbuild
          subst tree
          simpa [SubdivisionCertificate.check] using
            autoAccept_check_of_eq terms sqrtFuel logFuel box payload data haccept
      | none =>
          generalize hdiscard : LRHighShapeMidpointAutoTree.autoDiscard
            terms box payload.base = discardOption
          cases discardOption with
          | none =>
              simp only [haccept, hdiscard] at hbuild
              contradiction
          | some data =>
              simp only [haccept, hdiscard, Option.some.injEq] at hbuild
              subst tree
              simpa [SubdivisionCertificate.check] using
                LRHighShapeMidpointAutoTree.autoDiscard_check_of_eq
                  terms box payload.base data hdiscard
  | succ fuel ih =>
      let payload := LRHighShapeTangentCertificate.auto sqrtFuel logFuel box
      change (match autoAccept terms sqrtFuel logFuel box payload with
        | some data => some (.accept data)
        | none =>
          match LRHighShapeMidpointAutoTree.autoDiscard
              terms box payload.base with
          | some data => some (.discard data)
          | none =>
            let axis := chooseAxis terms box payload
            let cut := axisCut box axis
            match buildTree terms sqrtFuel logFuel fuel
                (box.lower axis cut) with
            | none => none
            | some lower =>
              match buildTree terms sqrtFuel logFuel fuel
                  (box.upper axis cut) with
              | none => none
              | some upper => some (.split axis cut lower upper)) =
        some tree at hbuild
      generalize haccept : autoAccept terms sqrtFuel logFuel box payload =
        acceptOption
      cases acceptOption with
      | some data =>
          simp only [haccept, Option.some.injEq] at hbuild
          subst tree
          simpa [SubdivisionCertificate.check] using
            autoAccept_check_of_eq terms sqrtFuel logFuel box payload data haccept
      | none =>
          generalize hdiscard : LRHighShapeMidpointAutoTree.autoDiscard
            terms box payload.base = discardOption
          cases discardOption with
          | some data =>
              simp only [haccept, hdiscard, Option.some.injEq] at hbuild
              subst tree
              simpa [SubdivisionCertificate.check] using
                LRHighShapeMidpointAutoTree.autoDiscard_check_of_eq
                  terms box payload.base data hdiscard
          | none =>
              let axis := chooseAxis terms box payload
              let cut := axisCut box axis
              generalize hlower : buildTree terms sqrtFuel logFuel fuel
                (box.lower axis cut) = lowerOption
              cases lowerOption with
              | none =>
                  simp only [haccept, hdiscard, axis, cut, hlower] at hbuild
                  contradiction
              | some lower =>
                  generalize hupper : buildTree terms sqrtFuel logFuel fuel
                    (box.upper axis cut) = upperOption
                  cases upperOption with
                  | none =>
                      simp only [haccept, hdiscard, axis, cut, hlower,
                        hupper] at hbuild
                      contradiction
                  | some upper =>
                      simp only [haccept, hdiscard, axis, cut, hlower,
                        hupper, Option.some.injEq] at hbuild
                      subst tree
                      simp only [SubdivisionCertificate.check,
                        Bool.and_eq_true]
                      exact ⟨ih _ _ hlower, ih _ _ hupper⟩

theorem alternative_of_buildTree_eq
    (terms sqrtFuel logFuel fuel : ℕ) (box : CertificateBox) (tree : Tree)
    (hbuild : buildTree terms sqrtFuel logFuel fuel box = some tree) :
    ∀ point, box.Contains point → LRHighShapeInterior point →
      LRHighShapeVRelevant point →
      LRHighShapeCertificateAlternative point := by
  exact lrHighShapeCombinedSubdivisionCertificate_sound terms
    (buildTree_check_of_eq terms sqrtFuel logFuel fuel box tree hbuild)

end LRCombinedHighShapeAutoTree
end CourtadeKumar
