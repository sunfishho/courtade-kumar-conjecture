import InformationTheory.CourtadeKumar.LRDeterminantLowRatioFiniteVPackedCertificate
import InformationTheory.CourtadeKumar.LRDeterminantLowRatioFiniteVAutoAssembly

/-!
# Packed four-tree assembly for the finite low-ratio replay

This module is the final structural boundary for generated finite-`V`
certificates.  It stores the two direct roots as packed preorder strings and
the two first-bracket roots as ten independently checked packed slab strings.
Conversion to the already-proved four-tree adapter is purely structural; all
interval arithmetic remains inside the ordinary Boolean checks attached to
the component strings.
-/

namespace CourtadeKumar
namespace LRLowRatioFiniteVPackedAssembly

/-- The four packed objects needed by the finite low-ratio theorem.  Each
first-bracket field contains ten separate midpoint trees at the exact fixed
dyadic slab roots. -/
structure FourTreeCertificate
    (terms sqrtFuel logFuel : ℕ) where
  firstQuarterHalf :
    LRDeterminantLowRatioFiniteVPackedCertificate.FirstBracket.PackedTenSlabForest
      terms sqrtFuel logFuel
      LRLowRatioFiniteVMeanValue.firstQuarterHalfRoot
  firstHalfOne :
    LRDeterminantLowRatioFiniteVPackedCertificate.FirstBracket.PackedTenSlabForest
      terms sqrtFuel logFuel
      LRLowRatioFiniteVMeanValue.firstHalfOneRoot
  directQuarterHalf :
    LRDeterminantLowRatioFiniteVPackedCertificate.Direct.PackedCheckedTree
      terms sqrtFuel logFuel
      LRLowRatioFiniteVMeanValue.quarterHalfRoot
  directHalfOne :
    LRDeterminantLowRatioFiniteVPackedCertificate.Direct.PackedCheckedTree
      terms sqrtFuel logFuel
      LRLowRatioFiniteVMeanValue.halfOneRoot

/-- Forget only the packed representation, retaining the four existing
kernel-checked compact tree objects. -/
def FourTreeCertificate.toAutoAssembly
    {terms sqrtFuel logFuel : ℕ}
    (certificate : FourTreeCertificate terms sqrtFuel logFuel) :
    LRLowRatioFiniteVAutoAssembly.FourTreeCertificate
      terms sqrtFuel logFuel where
  firstQuarterHalf := certificate.firstQuarterHalf.toTenSlabForest
  firstHalfOne := certificate.firstHalfOne.toTenSlabForest
  directQuarterHalf := certificate.directQuarterHalf.toAutoTaggedCheckedTree
  directHalfOne := certificate.directHalfOne.toAutoTaggedCheckedTree

/-- Four packed kernel replays discharge the complete finite low-ratio
direct-`V` theorem. -/
noncomputable def finiteVTargetTheorem
    {terms sqrtFuel logFuel : ℕ}
    (certificate : FourTreeCertificate terms sqrtFuel logFuel) :
    LRDeterminantLowRatioFiniteVTargetTheorem :=
  LRLowRatioFiniteVAutoAssembly.finiteVTargetTheorem
    certificate.toAutoAssembly

end LRLowRatioFiniteVPackedAssembly
end CourtadeKumar
