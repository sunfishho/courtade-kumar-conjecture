import InformationTheory.CourtadeKumar.LRSmallSBridgeCoreIntervalCore
import InformationTheory.CourtadeKumar.LRHighShapeCoordinateAutoCertificate

/-!
# Auto-generation compatibility layer for the frozen small-`s` core

The evaluator and all semantic soundness theorems live in
`LRSmallSBridgeCoreIntervalCore`.  This compatibility module retains the
historical payload-generation and subdivision-tree API.
-/

namespace CourtadeKumar
namespace LRSmallSBridgeCoreCertificate

def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRSmallSBridgeCoreCertificate :=
  let coordinate := LRHighShapeCoordinateCertificate.auto sqrtFuel box
  let v := coordinate.vAD box
  { coordinate := coordinate
    logTwo := RationalEnclosure.autoLogIntervalCertificate logFuel
      (IntervalAD.const 2).value
    logInner := RationalEnclosure.autoLogIntervalCertificate logFuel
      (innerAD box).value
    logOuter := RationalEnclosure.autoLogIntervalCertificate logFuel
      (outerAD box).value
    logK := RationalEnclosure.autoLogIntervalCertificate logFuel
      (kAD box).value
    logChi := RationalEnclosure.autoLogIntervalCertificate logFuel
      (if box.chiLo = 0 then (IntervalAD.const box.chiHi).value
        else (chiAD box).value)
    logOnePlusV := RationalEnclosure.autoLogIntervalCertificate logFuel
      (IntervalAD.add (IntervalAD.const 1) v).value
    logDArg := RationalEnclosure.autoLogIntervalCertificate logFuel
      (dArgAD box).value }

def autoAccepts (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (_unit : Unit) : Bool :=
  check terms box (auto sqrtFuel logFuel box)

def noDiscard (_box : CertificateBox) (_unit : Unit) : Bool := false

theorem autoAccepts_sound
    (terms sqrtFuel logFuel : ℕ) (box : CertificateBox) (_unit : Unit)
    (hcheck : autoAccepts terms sqrtFuel logFuel box () = true) :
    ∀ point, box.Contains point →
      (2 / 3 : ℝ) < lrSmallSBridgeCoreTarget point := by
  intro point hpoint
  exact positive_of_check terms hpoint
    (by simpa [autoAccepts] using hcheck)

/-- End-to-end soundness interface for a generated finite M30 replay. -/
theorem subdivision_sound
    (terms sqrtFuel logFuel : ℕ)
    {box : CertificateBox}
    {tree : SubdivisionCertificate Unit Unit}
    (hcheck : tree.check (autoAccepts terms sqrtFuel logFuel)
      noDiscard box = true) :
    ∀ point, box.Contains point →
      (2 / 3 : ℝ) < lrSmallSBridgeCoreTarget point := by
  intro point hpoint
  exact subdivisionCertificate_sound
    (Relevant := fun _ ↦ True)
    (Property := fun p ↦ (2 / 3 : ℝ) < lrSmallSBridgeCoreTarget p)
    (acceptBox := autoAccepts terms sqrtFuel logFuel)
    (discardBox := noDiscard)
    (fun leaf data h ↦ autoAccepts_sound terms sqrtFuel logFuel leaf data h)
    (fun _ _ h ↦ by simp [noDiscard] at h)
    hcheck point hpoint trivial

end LRSmallSBridgeCoreCertificate

end CourtadeKumar
