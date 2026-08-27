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
  let ss := splitScoreS terms box payload
  let sk := splitScoreK terms box payload
  let sc := splitScoreChi terms box payload
  if ss ≥ sk ∧ ss ≥ sc ∧ box.sLo < box.sHi then .s
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

def buildTree (terms sqrtFuel logFuel : ℕ) : ℕ → CertificateBox → Option Tree
  | 0, box =>
      let payload := LRHighShapeTangentCertificate.auto sqrtFuel logFuel box
      if LRHighShapeVCertificate.accepts terms box payload.base then
        some (.accept (.directV payload.base))
      else if LRHighShapeVCertificate.midpointAccepts
          terms box payload.base then
        some (.accept (.directVMidpoint payload.base))
      else if pairAccepts terms box payload then
        some (.accept (.midpointTangent payload))
      else
        match LRHighShapeMidpointAutoTree.autoDiscard terms box payload.base with
        | some data => some (.discard data)
        | none => none
  | fuel + 1, box =>
      let payload := LRHighShapeTangentCertificate.auto sqrtFuel logFuel box
      if LRHighShapeVCertificate.accepts terms box payload.base then
        some (.accept (.directV payload.base))
      else if LRHighShapeVCertificate.midpointAccepts
          terms box payload.base then
        some (.accept (.directVMidpoint payload.base))
      else if pairAccepts terms box payload then
        some (.accept (.midpointTangent payload))
      else
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
      by_cases hV : LRHighShapeVCertificate.accepts
          terms box payload.base = true
      · simp [buildTree, payload, hV] at hbuild
        subst tree
        simpa [SubdivisionCertificate.check,
          LRHighShapeCombinedAcceptData.check] using hV
      · have hVFalse : LRHighShapeVCertificate.accepts
            terms box payload.base = false :=
          Bool.eq_false_of_not_eq_true hV
        by_cases hVMid : LRHighShapeVCertificate.midpointAccepts
            terms box payload.base = true
        · simp [buildTree, payload, hVFalse, hVMid] at hbuild
          subst tree
          simpa [SubdivisionCertificate.check,
            LRHighShapeCombinedAcceptData.check] using hVMid
        · have hVMidFalse : LRHighShapeVCertificate.midpointAccepts
              terms box payload.base = false :=
            Bool.eq_false_of_not_eq_true hVMid
          by_cases hpair : pairAccepts terms box payload = true
          · simp [buildTree, payload, hVFalse, hVMidFalse, hpair] at hbuild
            subst tree
            simpa [SubdivisionCertificate.check,
              LRHighShapeCombinedAcceptData.check, pairAccepts] using hpair
          · have hpairFalse : pairAccepts terms box payload = false :=
              Bool.eq_false_of_not_eq_true hpair
            generalize hdiscard : LRHighShapeMidpointAutoTree.autoDiscard
              terms box payload.base = discardOption
            cases discardOption with
            | none =>
                simp [buildTree, payload, hVFalse, hVMidFalse,
                  hpairFalse, hdiscard] at hbuild
            | some data =>
                simp [buildTree, payload, hVFalse, hVMidFalse,
                  hpairFalse, hdiscard] at hbuild
                subst tree
                simpa [SubdivisionCertificate.check] using
                  LRHighShapeMidpointAutoTree.autoDiscard_check_of_eq
                    terms box payload.base data hdiscard
  | succ fuel ih =>
      let payload := LRHighShapeTangentCertificate.auto sqrtFuel logFuel box
      by_cases hV : LRHighShapeVCertificate.accepts
          terms box payload.base = true
      · simp [buildTree, payload, hV] at hbuild
        subst tree
        simpa [SubdivisionCertificate.check,
          LRHighShapeCombinedAcceptData.check] using hV
      · have hVFalse : LRHighShapeVCertificate.accepts
            terms box payload.base = false :=
          Bool.eq_false_of_not_eq_true hV
        by_cases hVMid : LRHighShapeVCertificate.midpointAccepts
            terms box payload.base = true
        · simp [buildTree, payload, hVFalse, hVMid] at hbuild
          subst tree
          simpa [SubdivisionCertificate.check,
            LRHighShapeCombinedAcceptData.check] using hVMid
        · have hVMidFalse : LRHighShapeVCertificate.midpointAccepts
              terms box payload.base = false :=
            Bool.eq_false_of_not_eq_true hVMid
          by_cases hpair : pairAccepts terms box payload = true
          · simp [buildTree, payload, hVFalse, hVMidFalse, hpair] at hbuild
            subst tree
            simpa [SubdivisionCertificate.check,
              LRHighShapeCombinedAcceptData.check, pairAccepts] using hpair
          · have hpairFalse : pairAccepts terms box payload = false :=
              Bool.eq_false_of_not_eq_true hpair
            generalize hdiscard : LRHighShapeMidpointAutoTree.autoDiscard
              terms box payload.base = discardOption
            cases discardOption with
            | some data =>
                simp [buildTree, payload, hVFalse, hVMidFalse,
                  hpairFalse, hdiscard] at hbuild
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
                    simp [buildTree, payload, hVFalse, hVMidFalse,
                      hpairFalse, hdiscard, axis, cut, hlower] at hbuild
                | some lower =>
                    generalize hupper : buildTree terms sqrtFuel logFuel fuel
                      (box.upper axis cut) = upperOption
                    cases upperOption with
                    | none =>
                        simp [buildTree, payload, hVFalse, hVMidFalse,
                          hpairFalse, hdiscard, axis, cut, hlower,
                          hupper] at hbuild
                    | some upper =>
                        simp [buildTree, payload, hVFalse, hVMidFalse,
                          hpairFalse, hdiscard, axis, cut, hlower,
                          hupper] at hbuild
                        subst tree
                        simp only [SubdivisionCertificate.check,
                          Bool.and_eq_true]
                        exact ⟨ih _ _ hlower, ih _ _ hupper⟩

theorem alternative_of_buildTree_eq
    (terms sqrtFuel logFuel fuel : ℕ) (box : CertificateBox) (tree : Tree)
    (hbuild : buildTree terms sqrtFuel logFuel fuel box = some tree) :
    ∀ point, box.Contains point → LRHighShapeVRelevant point →
      LRHighShapeCertificateAlternative point := by
  exact lrHighShapeCombinedSubdivisionCertificate_sound terms
    (buildTree_check_of_eq terms sqrtFuel logFuel fuel box tree hbuild)

end LRCombinedHighShapeAutoTree
end CourtadeKumar
