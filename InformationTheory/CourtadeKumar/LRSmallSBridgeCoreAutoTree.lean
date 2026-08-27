import InformationTheory.CourtadeKumar.LRSmallSBridgeCoreInterval

/-!
# Deterministic tree generation for the frozen small-`s` replay

This generator is untrusted convenience code.  It chooses a split from the
verified interval expression; only the resulting call to the sound Boolean
checker enters any theorem.
-/

namespace CourtadeKumar
namespace LRSmallSBridgeCoreCertificate

def splitScoreS (terms : ℕ) (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate) : ℚ :=
  (certificate.evaluate terms box).derivS.maxAbs *
    RationalEnclosure.radius box.sInterval

def splitScoreK (terms : ℕ) (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate) : ℚ :=
  (certificate.evaluate terms box).derivK.maxAbs *
    RationalEnclosure.radius box.kInterval

def splitScoreChi (terms : ℕ) (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate) : ℚ :=
  (certificate.evaluate terms box).derivChi.maxAbs *
      RationalEnclosure.radius box.chiInterval +
    (if box.chiLo = 0 then
      RationalEnclosure.radius
        (qChiEndpointAD terms box certificate).value
    else 0)

def chooseAxis (terms : ℕ) (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate) : CertificateAxis :=
  if box.chiLo = 0 ∧ 1 / 4 < box.chiHi then .chi
  else
    let ss := splitScoreS terms box certificate
    let sk := splitScoreK terms box certificate
    let sc := splitScoreChi terms box certificate
    if ss ≥ sk ∧ ss ≥ sc ∧ box.sLo < box.sHi then .s
    else if sk ≥ sc ∧ box.kLo < box.kHi then .k
    else .chi

def axisCut (box : CertificateBox) : CertificateAxis → ℚ
  | .s => RationalEnclosure.center box.sInterval
  | .k => RationalEnclosure.center box.kInterval
  | .chi => RationalEnclosure.center box.chiInterval

def buildTree (terms sqrtFuel logFuel : ℕ) :
    ℕ → CertificateBox → Option (SubdivisionCertificate Unit Unit)
  | 0, box =>
      if autoAccepts terms sqrtFuel logFuel box () then
        some (.accept ())
      else none
  | fuel + 1, box =>
      if autoAccepts terms sqrtFuel logFuel box () then
        some (.accept ())
      else
        let payload := auto sqrtFuel logFuel box
        let axis := chooseAxis terms box payload
        let cut := axisCut box axis
        match buildTree terms sqrtFuel logFuel fuel (box.lower axis cut),
            buildTree terms sqrtFuel logFuel fuel (box.upper axis cut) with
        | some lower, some upper => some (.split axis cut lower upper)
        | _, _ => none

def treeNodes : SubdivisionCertificate Unit Unit → ℕ
  | .accept _ => 1
  | .discard _ => 1
  | .split _ _ lower upper => 1 + treeNodes lower + treeNodes upper

def rootBox (kLo kHi : ℚ) : CertificateBox :=
  { sLo := 0, sHi := 1 / 16384
    kLo := kLo, kHi := kHi
    chiLo := 0, chiHi := 1 }

/-- Correctness of the untrusted tree-building program: whenever it returns
a tree, every leaf in that tree passes the verified Boolean checker. -/
theorem buildTree_check_of_eq
    (terms sqrtFuel logFuel fuel : ℕ) (box : CertificateBox)
    (tree : SubdivisionCertificate Unit Unit)
    (hbuild : buildTree terms sqrtFuel logFuel fuel box = some tree) :
    tree.check (autoAccepts terms sqrtFuel logFuel) noDiscard box = true := by
  induction fuel generalizing box tree with
  | zero =>
      by_cases haccept : autoAccepts terms sqrtFuel logFuel box () = true
      · simp [buildTree, haccept] at hbuild
        subst tree
        simpa [SubdivisionCertificate.check] using haccept
      · have hfalse : autoAccepts terms sqrtFuel logFuel box () = false :=
          Bool.eq_false_of_not_eq_true haccept
        simp [buildTree, hfalse] at hbuild
  | succ fuel ih =>
      by_cases haccept : autoAccepts terms sqrtFuel logFuel box () = true
      · simp [buildTree, haccept] at hbuild
        subst tree
        simpa [SubdivisionCertificate.check] using haccept
      · have hfalse : autoAccepts terms sqrtFuel logFuel box () = false :=
          Bool.eq_false_of_not_eq_true haccept
        let payload := auto sqrtFuel logFuel box
        let axis := chooseAxis terms box payload
        let cut := axisCut box axis
        generalize hlower : buildTree terms sqrtFuel logFuel fuel
          (box.lower axis cut) = lowerOption
        generalize hupper : buildTree terms sqrtFuel logFuel fuel
          (box.upper axis cut) = upperOption
        cases lowerOption with
        | none =>
            simp [buildTree, hfalse, payload, axis, cut, hlower] at hbuild
        | some lower =>
            cases upperOption with
            | none =>
                simp [buildTree, hfalse, payload, axis, cut, hlower,
                  hupper] at hbuild
            | some upper =>
                simp [buildTree, hfalse, payload, axis, cut, hlower,
                  hupper] at hbuild
                subst tree
                simp only [SubdivisionCertificate.check,
                  Bool.and_eq_true]
                exact ⟨ih _ _ hlower, ih _ _ hupper⟩

end LRSmallSBridgeCoreCertificate
end CourtadeKumar
