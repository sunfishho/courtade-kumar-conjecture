import InformationTheory.CourtadeKumar.LRHighShapeMidpointCertificateAssembly
import InformationTheory.CourtadeKumar.LRHighShapeVAutoCertificate

/-!
# Deterministic trees for the high-shape half-midpoint certificate

This module supplies an untrusted, fuel-bounded tree generator for the
already verified high-shape midpoint evaluator.  Accepted leaves carry the
automatically generated square-root and logarithm payload.  Discarded leaves
carry either a physical-domain obstruction or a checked nonpositive-`J`
certificate.

The theorem `buildTree_check_of_eq` is the trusted boundary: whenever the
generator returns a tree, ordinary kernel reduction proves that the complete
subdivision checker accepts it.
-/

namespace CourtadeKumar
namespace LRHighShapeMidpointAutoTree

abbrev Tree := SubdivisionCertificate LRHighShapeMidpointCertificate
  LRHighShapeVDiscardData

/-- Try every verified discard mode in a fixed order. -/
def autoDiscard (terms : ℕ) (box : CertificateBox)
    (payload : LRHighShapeMidpointCertificate) :
    Option LRHighShapeVDiscardData :=
  match lrPhysicalDiscardFirst box with
  | some reason => some (.physical reason)
  | none =>
      if lrHighShapeVDiscardCheck terms box (.jNonpositive payload) then
        some (.jNonpositive payload)
      else none

theorem autoDiscard_check_of_eq
    (terms : ℕ) (box : CertificateBox)
    (payload : LRHighShapeMidpointCertificate)
    (data : LRHighShapeVDiscardData)
    (hdiscard : autoDiscard terms box payload = some data) :
    lrHighShapeVDiscardCheck terms box data = true := by
  unfold autoDiscard at hdiscard
  generalize hphysical : lrPhysicalDiscardFirst box = physicalOption at hdiscard
  cases physicalOption with
  | some reason =>
      cases hdiscard
      simpa [lrHighShapeVDiscardCheck] using
        lrPhysicalDiscardFirst_check_of_eq box reason hphysical
  | none =>
      by_cases hJ :
          lrHighShapeVDiscardCheck terms box (.jNonpositive payload) = true
      · simp [hJ] at hdiscard
        cases hdiscard
        exact hJ
      · simp [hJ] at hdiscard

def splitScoreS (terms : ℕ) (box : CertificateBox)
    (payload : LRHighShapeMidpointCertificate) : ℚ :=
  (payload.evaluate terms box).derivS.maxAbs *
    RationalEnclosure.radius box.sInterval

def splitScoreK (terms : ℕ) (box : CertificateBox)
    (payload : LRHighShapeMidpointCertificate) : ℚ :=
  (payload.evaluate terms box).derivK.maxAbs *
    RationalEnclosure.radius box.kInterval

def splitScoreChi (terms : ℕ) (box : CertificateBox)
    (payload : LRHighShapeMidpointCertificate) : ℚ :=
  (payload.evaluate terms box).derivChi.maxAbs *
    RationalEnclosure.radius box.chiInterval

/-- Bisect the coordinate contributing the largest midpoint loss. -/
def chooseAxis (terms : ℕ) (box : CertificateBox)
    (payload : LRHighShapeMidpointCertificate) : CertificateAxis :=
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

/-- Generate a candidate tree.  Exhausted fuel returns `none`, so an
unresolved leaf can never be mistaken for a proof. -/
def buildTree (terms sqrtFuel logFuel : ℕ) : ℕ → CertificateBox → Option Tree
  | 0, box =>
      let payload := LRHighShapeVCertificate.auto sqrtFuel logFuel box
      if LRHighShapeMidpointCertificate.accepts terms box payload then
        some (.accept payload)
      else
        match autoDiscard terms box payload with
        | some data => some (.discard data)
        | none => none
  | fuel + 1, box =>
      let payload := LRHighShapeVCertificate.auto sqrtFuel logFuel box
      if LRHighShapeMidpointCertificate.accepts terms box payload then
        some (.accept payload)
      else
        match autoDiscard terms box payload with
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

/-- Correctness of the generator: a returned tree passes the verified
midpoint subdivision checker on its exact root box. -/
theorem buildTree_check_of_eq
    (terms sqrtFuel logFuel fuel : ℕ) (box : CertificateBox) (tree : Tree)
    (hbuild : buildTree terms sqrtFuel logFuel fuel box = some tree) :
    tree.check (LRHighShapeMidpointCertificate.accepts terms)
      (lrHighShapeVDiscardCheck terms) box = true := by
  induction fuel generalizing box tree with
  | zero =>
      let payload := LRHighShapeVCertificate.auto sqrtFuel logFuel box
      by_cases haccept :
          LRHighShapeMidpointCertificate.accepts terms box payload = true
      · simp [buildTree, payload, haccept] at hbuild
        subst tree
        simpa [SubdivisionCertificate.check] using haccept
      · have hfalse :
            LRHighShapeMidpointCertificate.accepts terms box payload = false :=
          Bool.eq_false_of_not_eq_true haccept
        generalize hdiscard : autoDiscard terms box payload = discardOption
        cases discardOption with
        | none => simp [buildTree, payload, hfalse, hdiscard] at hbuild
        | some data =>
            simp [buildTree, payload, hfalse, hdiscard] at hbuild
            subst tree
            simpa [SubdivisionCertificate.check] using
              autoDiscard_check_of_eq terms box payload data hdiscard
  | succ fuel ih =>
      let payload := LRHighShapeVCertificate.auto sqrtFuel logFuel box
      by_cases haccept :
          LRHighShapeMidpointCertificate.accepts terms box payload = true
      · simp [buildTree, payload, haccept] at hbuild
        subst tree
        simpa [SubdivisionCertificate.check] using haccept
      · have hfalse :
            LRHighShapeMidpointCertificate.accepts terms box payload = false :=
          Bool.eq_false_of_not_eq_true haccept
        generalize hdiscard : autoDiscard terms box payload = discardOption
        cases discardOption with
        | some data =>
            simp [buildTree, payload, hfalse, hdiscard] at hbuild
            subst tree
            simpa [SubdivisionCertificate.check] using
              autoDiscard_check_of_eq terms box payload data hdiscard
        | none =>
            let axis := chooseAxis terms box payload
            let cut := axisCut box axis
            generalize hlower : buildTree terms sqrtFuel logFuel fuel
              (box.lower axis cut) = lowerOption
            cases lowerOption with
            | none =>
                simp [buildTree, payload, hfalse, hdiscard, axis, cut,
                  hlower] at hbuild
            | some lower =>
                generalize hupper : buildTree terms sqrtFuel logFuel fuel
                  (box.upper axis cut) = upperOption
                cases upperOption with
                | none =>
                    simp [buildTree, payload, hfalse, hdiscard, axis, cut,
                      hlower, hupper] at hbuild
                | some upper =>
                    simp [buildTree, payload, hfalse, hdiscard, axis, cut,
                      hlower, hupper] at hbuild
                    subst tree
                    simp only [SubdivisionCertificate.check,
                      Bool.and_eq_true]
                    exact ⟨ih _ _ hlower, ih _ _ hupper⟩

/-- A successful generated tree proves the exact normalized half-midpoint
target throughout its relevant part of the root box. -/
theorem target_nonnegative_of_buildTree_eq
    (terms sqrtFuel logFuel fuel : ℕ) (box : CertificateBox) (tree : Tree)
    (hbuild : buildTree terms sqrtFuel logFuel fuel box = some tree) :
    ∀ point, box.Contains point → LRHighShapeVRelevant point →
      0 ≤ lrCertificateUTarget point := by
  exact lrHighShapeMidpointSubdivisionCertificate_nonnegative terms
    (buildTree_check_of_eq terms sqrtFuel logFuel fuel box tree hbuild)

end LRHighShapeMidpointAutoTree
end CourtadeKumar
