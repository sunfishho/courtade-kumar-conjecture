import InformationTheory.CourtadeKumar.LRDeterminantFiniteD9Evaluator

/-!
# Payload-free finite-D9 replay

Generated finite-D9 trees store only their subdivision topology.  Every
accepted or discarded leaf deterministically reconstructs its untrusted
payload and checks it against the production D9 semantics before the generic
subdivision theorem is used.
-/

namespace CourtadeKumar
namespace LRFiniteDeterminantD9PayloadFree

abbrev Tree := SubdivisionCertificate Unit Unit

/-- Prefer the regular interval-AD payload and use the endpoint-safe value
evaluator on leaves touching the singular `chi = 0` face. -/
def autoData (terms sqrtFuel logFuel : Nat) (box : CertificateBox) :
    LRFiniteDeterminantD9HybridAcceptData :=
  let regular := LRFiniteDeterminantD9Certificate.auto sqrtFuel logFuel box
  if checkedEnclosureLeafAccepts
      LRFiniteDeterminantD9Certificate.payloadCheck
      (LRFiniteDeterminantD9Certificate.enclose terms) box regular then
    .regular regular
  else
    .zeroFace
      (LRFiniteDeterminantD9ZeroFaceCertificate.auto sqrtFuel logFuel box)

def payloadCheck (terms sqrtFuel logFuel : Nat)
    (box : CertificateBox) (_data : Unit) : Bool :=
  LRFiniteDeterminantD9HybridAcceptData.payloadCheck box
    (autoData terms sqrtFuel logFuel box)

def enclose (terms sqrtFuel logFuel : Nat)
    (box : CertificateBox) (_data : Unit) : RationalEnclosure :=
  LRFiniteDeterminantD9HybridAcceptData.enclose terms box
    (autoData terms sqrtFuel logFuel box)

def accepts (terms sqrtFuel logFuel : Nat)
    (box : CertificateBox) (data : Unit) : Bool :=
  checkedEnclosureLeafAccepts
    (payloadCheck terms sqrtFuel logFuel)
    (enclose terms sqrtFuel logFuel) box data

noncomputable def evaluatorSound (terms sqrtFuel logFuel : Nat) :
    CheckedEnclosureLeafEvaluatorSound lrFiniteDeterminantD9ReplayTarget
      (payloadCheck terms sqrtFuel logFuel)
      (enclose terms sqrtFuel logFuel) := by
  constructor
  intro box _ hpayload point hpoint
  exact
    (LRFiniteDeterminantD9HybridAcceptData.checkedEvaluatorSound terms).value
      box (autoData terms sqrtFuel logFuel box) hpayload point hpoint

def midpointBase : LRFiniteDeterminantD9HybridAcceptData →
    LRHighShapeVCertificate
  | .regular certificate => certificate.tangent.base
  | .zeroFace certificate => certificate.zero.base

def autoDiscardData (terms sqrtFuel logFuel : Nat)
    (box : CertificateBox) : Option LRHighShapeVDiscardData :=
  let data := autoData terms sqrtFuel logFuel box
  match lrPhysicalDiscardFirst box with
  | some reason => some (.physical reason)
  | none =>
      let payload := midpointBase data
      if lrHighShapeVDiscardCheck terms box (.jNonpositive payload) then
        some (.jNonpositive payload)
      else none

def discardCheck (terms sqrtFuel logFuel : Nat)
    (box : CertificateBox) (_data : Unit) : Bool :=
  match autoDiscardData terms sqrtFuel logFuel box with
  | none => false
  | some data => lrHighShapeVDiscardCheck terms box data

theorem discardCheck_sound (terms sqrtFuel logFuel : Nat)
    (box : CertificateBox) (data : Unit)
    (hcheck : discardCheck terms sqrtFuel logFuel box data = true) :
    ∀ point, box.Contains point → ¬ LRHighShapeVRelevant point := by
  generalize hdata : autoDiscardData terms sqrtFuel logFuel box = result
  cases result with
  | none => simp [discardCheck, hdata] at hcheck
  | some discard =>
      have hverified :
          lrHighShapeVDiscardCheck terms box discard = true := by
        simpa [discardCheck, hdata] using hcheck
      exact lrHighShapeVDiscardCheck_sound terms box discard hverified

/-- Package a kernel-checked payload-free topology as the abstract D9 tree
consumed by the determinant-region adapters. -/
def toRawCheckedTree (terms sqrtFuel logFuel : Nat)
    {root : CertificateBox} (tree : Tree)
    (hcheck : tree.check (accepts terms sqrtFuel logFuel)
      (discardCheck terms sqrtFuel logFuel) root = true) :
    LRFiniteDeterminantRawD9CheckedTree root where
  AcceptData := Unit
  DiscardData := Unit
  payloadCheck := payloadCheck terms sqrtFuel logFuel
  enclose := enclose terms sqrtFuel logFuel
  discardCheck := discardCheck terms sqrtFuel logFuel
  encloseSound := evaluatorSound terms sqrtFuel logFuel
  discardCompatible := discardCheck_sound terms sqrtFuel logFuel
  certificate := tree
  checked := hcheck

end LRFiniteDeterminantD9PayloadFree
end CourtadeKumar
