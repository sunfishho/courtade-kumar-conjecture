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

end LRSmallSBridgeCoreCertificate
end CourtadeKumar
