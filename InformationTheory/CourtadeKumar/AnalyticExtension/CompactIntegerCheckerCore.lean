import InformationTheory.CourtadeKumar.AnalyticExtension.CompactIntegerCore
import InformationTheory.CourtadeKumar.AnalyticExtension.CompactCheckerCore

/-! Kernel-oriented compact-V arithmetic. Every integer operation rounds outward;
logarithm witnesses retain the existing exact rational checks. -/
namespace CourtadeKumar.LRCompactIntegerCertificate
open LRCompactReducedCertificate (Leaf Tree)

def inputs (b : CertificateBox) (d : Leaf) (L : RationalEnclosure) : Nat → Jet :=
  fun i => Jet.fromRat (d.inputs b L i)
def pointInputs (b : CertificateBox) (d : Leaf) (L : RationalEnclosure) : Nat → Jet :=
  fun i => Jet.fromRat (d.pointInputs b L i)

def checkLeaf (L : RationalEnclosure) (b : CertificateBox) (d : Leaf) : Bool :=
  let whole := sharedTarget (inputs b d L) 24 8
  let point := sharedTarget (pointInputs b d L) 24 8
  d.precheck b && whole.valid && point.valid &&
    decide (0 ≤ point.decode.bounds.value.lower -
      LRCompactReducedCertificate.boxLoss b whole.decode)

def checkTree (L : RationalEnclosure) (b : CertificateBox) (tree : Tree) : Bool :=
  tree.check (checkLeaf L) LRCompactReducedCertificate.discard b

theorem join_checked {L : RationalEnclosure} {b : CertificateBox}
    (axis : CertificateAxis) (cut : ℚ) {left right : Tree}
    (hl : checkTree L (b.lower axis cut) left = true)
    (hr : checkTree L (b.upper axis cut) right = true) :
    checkTree L b (.split axis cut left right) = true :=
  Bool.and_eq_true_iff.mpr ⟨hl,hr⟩

end CourtadeKumar.LRCompactIntegerCertificate
