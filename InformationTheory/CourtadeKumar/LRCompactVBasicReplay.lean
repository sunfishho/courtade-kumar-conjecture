import InformationTheory.CourtadeKumar.LRCompactVPartialCover

/-!
# Frozen compact-V replay with separate precision at each leaf

Search and profile selection are absent from this checker. Each accepted leaf
specifies finite series lengths and logarithm normalization fuel; the existing
production checker validates the resulting bounds. This allows inexpensive
leaves and tighter leaves to share one fixed covering tree.
-/

namespace CourtadeKumar

structure LRCompactVLeafParameters where
  logTerms : Nat
  pZeroTerms : Nat
  wTerms : Nat
  terms : Nat
  logFuel : Nat

namespace LRCompactVLeafParameters

def short : LRCompactVLeafParameters := ⟨4, 8, 8, 8, 16⟩
def accurateLog : LRCompactVLeafParameters := ⟨6, 8, 8, 8, 16⟩
def long : LRCompactVLeafParameters := ⟨8, 12, 12, 12, 16⟩

def check (box : CertificateBox) (parameters : LRCompactVLeafParameters) : Bool :=
  (LRCompactVLeafCertificate.auto parameters.logFuel box).check
    parameters.logTerms parameters.pZeroTerms parameters.wTerms parameters.terms box

theorem sound {box : CertificateBox} {parameters : LRCompactVLeafParameters}
    (hcheck : parameters.check box = true) : LRCompactVBoxSound box := by
  intro point hpoint hphysical
  exact LRCompactVLeafCertificate.sound
    parameters.logTerms parameters.pZeroTerms parameters.wTerms parameters.terms
    hcheck point hpoint hphysical.1

end LRCompactVLeafParameters

/-- An acceptance-only covering tree. Physical discards cannot occur because
the discard payload type is empty. -/
abbrev LRCompactVBasicReplayTree :=
  SubdivisionCertificate LRCompactVLeafParameters Empty

namespace LRCompactVBasicReplayTree

def check (box : CertificateBox) (tree : LRCompactVBasicReplayTree) : Bool :=
  SubdivisionCertificate.check LRCompactVLeafParameters.check
    (fun _ data ↦ nomatch data) box tree

theorem sound {box : CertificateBox} {tree : LRCompactVBasicReplayTree}
    (hcheck : check box tree = true) : LRCompactVBoxSound box := by
  induction tree generalizing box with
  | accept parameters =>
    exact parameters.sound hcheck
  | discard data => exact nomatch data
  | split axis cut lower upper hlo hhi =>
    have hchildren : check (box.lower axis cut) lower = true ∧
        check (box.upper axis cut) upper = true :=
      Bool.and_eq_true_iff.mp hcheck
    exact LRCompactVBoxSound.join axis cut (hlo hchildren.1) (hhi hchildren.2)

end LRCompactVBasicReplayTree
end CourtadeKumar
