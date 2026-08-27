import InformationTheory.CourtadeKumar.LRHighShapeMidpointVFallback

/-!
# Mixed midpoint/direct-`V` tree generation

The generator first tries the exact half-midpoint leaf, then the
cancellation-safe direct-`V` leaf, then a verified discard.  Only unresolved
boxes are subdivided.  The proof of `buildTree_check_of_eq` verifies every
choice against the ordinary hybrid checker.
-/

namespace CourtadeKumar
namespace LRHighShapeMidpointHybridAutoTree

abbrev Tree := SubdivisionCertificate LRHighShapeMidpointHybridAcceptData
  LRHighShapeVDiscardData

def autoAccept (terms : ℕ) (box : CertificateBox)
    (payload : LRHighShapeMidpointCertificate) :
    Option LRHighShapeMidpointHybridAcceptData :=
  if LRHighShapeMidpointCertificate.accepts terms box payload then
    some (.midpoint payload)
  else if LRHighShapeVCertificate.accepts terms box payload then
    some (.directV payload)
  else none

theorem autoAccept_check_of_eq
    (terms : ℕ) (box : CertificateBox)
    (payload : LRHighShapeMidpointCertificate)
    (data : LRHighShapeMidpointHybridAcceptData)
    (haccept : autoAccept terms box payload = some data) :
    data.check terms box = true := by
  unfold autoAccept at haccept
  split at haccept <;> rename_i hmidpoint
  · cases haccept
    simpa [LRHighShapeMidpointHybridAcceptData.check] using hmidpoint
  split at haccept <;> rename_i hV
  · cases haccept
    simpa [LRHighShapeMidpointHybridAcceptData.check] using hV
  · simp at haccept

def buildTree (terms sqrtFuel logFuel : ℕ) : ℕ → CertificateBox → Option Tree
  | 0, box =>
      let payload := LRHighShapeVCertificate.auto sqrtFuel logFuel box
      match autoAccept terms box payload with
      | some data => some (.accept data)
      | none =>
          match LRHighShapeMidpointAutoTree.autoDiscard terms box payload with
          | some data => some (.discard data)
          | none => none
  | fuel + 1, box =>
      let payload := LRHighShapeVCertificate.auto sqrtFuel logFuel box
      match autoAccept terms box payload with
      | some data => some (.accept data)
      | none =>
          match LRHighShapeMidpointAutoTree.autoDiscard terms box payload with
          | some data => some (.discard data)
          | none =>
              let axis := LRHighShapeMidpointAutoTree.chooseAxis
                terms box payload
              let cut := LRHighShapeMidpointAutoTree.axisCut box axis
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
    tree.check (LRHighShapeMidpointHybridAcceptData.check terms)
      (lrHighShapeVDiscardCheck terms) box = true := by
  induction fuel generalizing box tree with
  | zero =>
      let payload := LRHighShapeVCertificate.auto sqrtFuel logFuel box
      generalize haccept : autoAccept terms box payload = acceptOption
      cases acceptOption with
      | some data =>
          simp [buildTree, payload, haccept] at hbuild
          subst tree
          simpa [SubdivisionCertificate.check] using
            autoAccept_check_of_eq terms box payload data haccept
      | none =>
          generalize hdiscard : LRHighShapeMidpointAutoTree.autoDiscard
            terms box payload = discardOption
          cases discardOption with
          | none => simp [buildTree, payload, haccept, hdiscard] at hbuild
          | some data =>
              simp [buildTree, payload, haccept, hdiscard] at hbuild
              subst tree
              simpa [SubdivisionCertificate.check] using
                LRHighShapeMidpointAutoTree.autoDiscard_check_of_eq
                  terms box payload data hdiscard
  | succ fuel ih =>
      let payload := LRHighShapeVCertificate.auto sqrtFuel logFuel box
      generalize haccept : autoAccept terms box payload = acceptOption
      cases acceptOption with
      | some data =>
          simp [buildTree, payload, haccept] at hbuild
          subst tree
          simpa [SubdivisionCertificate.check] using
            autoAccept_check_of_eq terms box payload data haccept
      | none =>
          generalize hdiscard : LRHighShapeMidpointAutoTree.autoDiscard
            terms box payload = discardOption
          cases discardOption with
          | some data =>
              simp [buildTree, payload, haccept, hdiscard] at hbuild
              subst tree
              simpa [SubdivisionCertificate.check] using
                LRHighShapeMidpointAutoTree.autoDiscard_check_of_eq
                  terms box payload data hdiscard
          | none =>
              let axis := LRHighShapeMidpointAutoTree.chooseAxis
                terms box payload
              let cut := LRHighShapeMidpointAutoTree.axisCut box axis
              generalize hlower : buildTree terms sqrtFuel logFuel fuel
                (box.lower axis cut) = lowerOption
              cases lowerOption with
              | none =>
                  simp [buildTree, payload, haccept, hdiscard, axis, cut,
                    hlower] at hbuild
              | some lower =>
                  generalize hupper : buildTree terms sqrtFuel logFuel fuel
                    (box.upper axis cut) = upperOption
                  cases upperOption with
                  | none =>
                      simp [buildTree, payload, haccept, hdiscard, axis, cut,
                        hlower, hupper] at hbuild
                  | some upper =>
                      simp [buildTree, payload, haccept, hdiscard, axis, cut,
                        hlower, hupper] at hbuild
                      subst tree
                      simp only [SubdivisionCertificate.check,
                        Bool.and_eq_true]
                      exact ⟨ih _ _ hlower, ih _ _ hupper⟩

theorem target_nonnegative_of_buildTree_eq
    (terms sqrtFuel logFuel fuel : ℕ) (box : CertificateBox) (tree : Tree)
    (hbuild : buildTree terms sqrtFuel logFuel fuel box = some tree) :
    ∀ point, box.Contains point → LRHighShapeVRelevant point →
      0 ≤ lrCertificateUTarget point := by
  exact lrHighShapeMidpointHybridSubdivisionCertificate_nonnegative terms
    (buildTree_check_of_eq terms sqrtFuel logFuel fuel box tree hbuild)

end LRHighShapeMidpointHybridAutoTree
end CourtadeKumar
