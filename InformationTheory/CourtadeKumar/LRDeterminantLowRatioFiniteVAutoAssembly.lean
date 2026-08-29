import InformationTheory.CourtadeKumar.LRDeterminantLowRatioFiniteVAutoTree
import InformationTheory.CourtadeKumar.LRDeterminantLowRatioFiniteVFirstBracketAutoTree

/-!
# Four-tree assembly for the finite low-ratio direct-`V` replay

This is the final structural boundary between generated compact topology and
the analytic finite-`V` theorem.  A certificate contains two fixed ten-slab
hybrid first-bracket forests and the two direct-`V` compact trees.  Their
individual Boolean replays are already fields of the component types, so the
assembly below performs no interval arithmetic and stores no analytic payload.
-/

namespace CourtadeKumar
namespace LRLowRatioFiniteVAutoAssembly

/-- The exact four compact objects required by the already-proved finite-`V`
adapter.  The two first-bracket fields each contain the ten fixed dyadic
`s` slabs of one `K` band. -/
structure FourTreeCertificate
    (terms sqrtFuel logFuel : ℕ) where
  firstQuarterHalf :
    LRDeterminantLowRatioFiniteVFirstBracketAutoTree.TenSlabForest
      terms sqrtFuel logFuel
      LRLowRatioFiniteVMeanValue.firstQuarterHalfRoot
  firstHalfOne :
    LRDeterminantLowRatioFiniteVFirstBracketAutoTree.TenSlabForest
      terms sqrtFuel logFuel
      LRLowRatioFiniteVMeanValue.firstHalfOneRoot
  directQuarterHalf :
    LRLowRatioFiniteVAutoTree.AutoTaggedCheckedTree terms sqrtFuel logFuel
      LRLowRatioFiniteVMeanValue.quarterHalfRoot
  directHalfOne :
    LRLowRatioFiniteVAutoTree.AutoTaggedCheckedTree terms sqrtFuel logFuel
      LRLowRatioFiniteVMeanValue.halfOneRoot

/-- Four checked compact topologies discharge the complete finite low-ratio
direct-`V` input.  Only the component conversion and analytic four-tree
adapter are composed here. -/
noncomputable def finiteVTargetTheorem
    {terms sqrtFuel logFuel : ℕ}
    (certificate : FourTreeCertificate terms sqrtFuel logFuel) :
    LRDeterminantLowRatioFiniteVTargetTheorem :=
  LRLowRatioFiniteVMeanValue.finiteVTargetTheorem_of_fourTrees
    (LRDeterminantLowRatioFiniteVFirstBracketAutoTree.TenSlabForest.toFirstBracketTree
      certificate.firstQuarterHalf)
    (LRDeterminantLowRatioFiniteVFirstBracketAutoTree.TenSlabForest.toFirstBracketTree
      certificate.firstHalfOne)
    (LRLowRatioFiniteVAutoTree.AutoTaggedCheckedTree.toCheckedTree
      certificate.directQuarterHalf)
    (LRLowRatioFiniteVAutoTree.AutoTaggedCheckedTree.toCheckedTree
      certificate.directHalfOne)

end LRLowRatioFiniteVAutoAssembly
end CourtadeKumar
