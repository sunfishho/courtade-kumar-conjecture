import InformationTheory.CourtadeKumar.LRDeterminantUpperKReplayAutoTree
import InformationTheory.CourtadeKumar.LRDeterminantLowRatioFiniteVMeanValue

/-!
# First-bracket forest adapter for the finite low-ratio replay

The first twenty historical low-ratio roots prove the sharp upper-`K`
`FirstBracket/e` target on ten consecutive dyadic `s` slabs and two `K`
bands.  This module connects those deterministic sharp trees to the abstract
`FirstBracketTree` boundary used by the finite-`V` assembly.

For generated trees without physical discards, accepted leaves contain only
`Unit`: the trusted checker reconstructs every analytic payload from the
current box.  Ten independently checked slab certificates can therefore be
joined by nine structural `s` splits.  The aggregate checker proof merely
combines the ten existing Boolean equalities; it never reevaluates an
arithmetic leaf at the aggregate root.
-/

namespace CourtadeKumar

namespace LRLowRatioFiniteVMeanValue

namespace FirstBracketTree

/-- A deterministic sharp upper-`K` tree has exactly the semantic interface
required by the lower finite-`V` first-bracket band. -/
def ofAutoSharpCenteredCheckedTree
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (tree : LRUpperKReplayCertificate.AutoSharpCenteredCheckedTree
      terms sqrtFuel logFuel root) :
    FirstBracketTree root where
  target_nonnegative := by
    intro coordinate hcoordinate hinterior hrelevant
    exact
      LRUpperKReplayCertificate.AutoSharpCenteredCheckedTree.target_nonnegative
        tree hcoordinate ⟨hinterior, hrelevant⟩

end FirstBracketTree

namespace FirstBracketForest

/-! ## Unit-leaf, no-discard checked trees -/

/-- The historical first-bracket trees contain no physical-discard leaves. -/
def unitNoDiscard (_box : CertificateBox) (_data : Unit) : Bool := false

/-- A sharp auto tree specialized to `Unit` accept and discard data.

This non-dependent view is the convenient boundary for concatenating
independently generated slabs: all ten certificates then have literally the
same accept and discard datatypes. -/
structure UnitAutoSharpTree
    (terms sqrtFuel logFuel : ℕ) (root : CertificateBox) where
  certificate : SubdivisionCertificate Unit Unit
  checked : certificate.check
    (LRUpperKReplayCertificate.autoSharpCenteredAccepts
      terms sqrtFuel logFuel) unitNoDiscard root = true

namespace UnitAutoSharpTree

/-- Package a unit/no-discard tree in the general sharp checked-tree
interface.  Discard soundness is vacuous because `unitNoDiscard` is false. -/
def toAutoSharpCenteredCheckedTree
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (tree : UnitAutoSharpTree terms sqrtFuel logFuel root) :
    LRUpperKReplayCertificate.AutoSharpCenteredCheckedTree
      terms sqrtFuel logFuel root where
  DiscardData := Unit
  discardCheck := unitNoDiscard
  discardSound := by
    intro box data hfalse
    simp [unitNoDiscard] at hfalse
  certificate := tree.certificate
  checked := tree.checked

end UnitAutoSharpTree

/-! ## Exact dyadic split paths -/

abbrev firstBracketSCut0 : ℚ := 1 / 8192
abbrev firstBracketSCut1 : ℚ := 1 / 4096
abbrev firstBracketSCut2 : ℚ := 1 / 2048
abbrev firstBracketSCut3 : ℚ := 1 / 1024
abbrev firstBracketSCut4 : ℚ := 1 / 512
abbrev firstBracketSCut5 : ℚ := 1 / 256
abbrev firstBracketSCut6 : ℚ := 1 / 128
abbrev firstBracketSCut7 : ℚ := 1 / 64
abbrev firstBracketSCut8 : ℚ := 1 / 32

/-- Remaining root after removing the first dyadic `s` slab. -/
abbrev firstBracketTail1Root (root : CertificateBox) : CertificateBox :=
  root.upper .s firstBracketSCut0

abbrev firstBracketTail2Root (root : CertificateBox) : CertificateBox :=
  (firstBracketTail1Root root).upper .s firstBracketSCut1

abbrev firstBracketTail3Root (root : CertificateBox) : CertificateBox :=
  (firstBracketTail2Root root).upper .s firstBracketSCut2

abbrev firstBracketTail4Root (root : CertificateBox) : CertificateBox :=
  (firstBracketTail3Root root).upper .s firstBracketSCut3

abbrev firstBracketTail5Root (root : CertificateBox) : CertificateBox :=
  (firstBracketTail4Root root).upper .s firstBracketSCut4

abbrev firstBracketTail6Root (root : CertificateBox) : CertificateBox :=
  (firstBracketTail5Root root).upper .s firstBracketSCut5

abbrev firstBracketTail7Root (root : CertificateBox) : CertificateBox :=
  (firstBracketTail6Root root).upper .s firstBracketSCut6

abbrev firstBracketTail8Root (root : CertificateBox) : CertificateBox :=
  (firstBracketTail7Root root).upper .s firstBracketSCut7

/-- Exact slabs `[2⁻¹⁴,2⁻¹³]`, ..., `[2⁻⁵,2⁻⁴]`, expressed as
the actual child-box paths used by the generic subdivision checker. -/
abbrev firstBracketSlab0Root (root : CertificateBox) : CertificateBox :=
  root.lower .s firstBracketSCut0

abbrev firstBracketSlab1Root (root : CertificateBox) : CertificateBox :=
  (firstBracketTail1Root root).lower .s firstBracketSCut1

abbrev firstBracketSlab2Root (root : CertificateBox) : CertificateBox :=
  (firstBracketTail2Root root).lower .s firstBracketSCut2

abbrev firstBracketSlab3Root (root : CertificateBox) : CertificateBox :=
  (firstBracketTail3Root root).lower .s firstBracketSCut3

abbrev firstBracketSlab4Root (root : CertificateBox) : CertificateBox :=
  (firstBracketTail4Root root).lower .s firstBracketSCut4

abbrev firstBracketSlab5Root (root : CertificateBox) : CertificateBox :=
  (firstBracketTail5Root root).lower .s firstBracketSCut5

abbrev firstBracketSlab6Root (root : CertificateBox) : CertificateBox :=
  (firstBracketTail6Root root).lower .s firstBracketSCut6

abbrev firstBracketSlab7Root (root : CertificateBox) : CertificateBox :=
  (firstBracketTail7Root root).lower .s firstBracketSCut7

abbrev firstBracketSlab8Root (root : CertificateBox) : CertificateBox :=
  (firstBracketTail8Root root).lower .s firstBracketSCut8

abbrev firstBracketSlab9Root (root : CertificateBox) : CertificateBox :=
  (firstBracketTail8Root root).upper .s firstBracketSCut8

/-! ## Ten-slab structural forest -/

/-- Ten independently checked dyadic `s` slabs with common evaluator
parameters.  The common parameters and unit discard type are precisely what
allow the certificates to be joined into one ordinary subdivision tree. -/
structure TenSlabForest
    (terms sqrtFuel logFuel : ℕ) (root : CertificateBox) where
  slab0 : UnitAutoSharpTree terms sqrtFuel logFuel
    (firstBracketSlab0Root root)
  slab1 : UnitAutoSharpTree terms sqrtFuel logFuel
    (firstBracketSlab1Root root)
  slab2 : UnitAutoSharpTree terms sqrtFuel logFuel
    (firstBracketSlab2Root root)
  slab3 : UnitAutoSharpTree terms sqrtFuel logFuel
    (firstBracketSlab3Root root)
  slab4 : UnitAutoSharpTree terms sqrtFuel logFuel
    (firstBracketSlab4Root root)
  slab5 : UnitAutoSharpTree terms sqrtFuel logFuel
    (firstBracketSlab5Root root)
  slab6 : UnitAutoSharpTree terms sqrtFuel logFuel
    (firstBracketSlab6Root root)
  slab7 : UnitAutoSharpTree terms sqrtFuel logFuel
    (firstBracketSlab7Root root)
  slab8 : UnitAutoSharpTree terms sqrtFuel logFuel
    (firstBracketSlab8Root root)
  slab9 : UnitAutoSharpTree terms sqrtFuel logFuel
    (firstBracketSlab9Root root)

namespace TenSlabForest

/-- Join the ten slab topologies by the nine historical dyadic `s` cuts. -/
def certificate
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (forest : TenSlabForest terms sqrtFuel logFuel root) :
    SubdivisionCertificate Unit Unit :=
  .split .s firstBracketSCut0 forest.slab0.certificate
    (.split .s firstBracketSCut1 forest.slab1.certificate
      (.split .s firstBracketSCut2 forest.slab2.certificate
        (.split .s firstBracketSCut3 forest.slab3.certificate
          (.split .s firstBracketSCut4 forest.slab4.certificate
            (.split .s firstBracketSCut5 forest.slab5.certificate
              (.split .s firstBracketSCut6 forest.slab6.certificate
                (.split .s firstBracketSCut7 forest.slab7.certificate
                  (.split .s firstBracketSCut8 forest.slab8.certificate
                    forest.slab9.certificate))))))))

/-- The aggregate check is purely structural: it unfolds only the nine split
nodes and combines the ten already checked slab equalities. -/
theorem certificate_check
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (forest : TenSlabForest terms sqrtFuel logFuel root) :
    (certificate forest).check
      (LRUpperKReplayCertificate.autoSharpCenteredAccepts
        terms sqrtFuel logFuel) unitNoDiscard root = true := by
  simp only [certificate, SubdivisionCertificate.check, Bool.and_eq_true]
  exact
    ⟨forest.slab0.checked,
      ⟨forest.slab1.checked,
        ⟨forest.slab2.checked,
          ⟨forest.slab3.checked,
            ⟨forest.slab4.checked,
              ⟨forest.slab5.checked,
                ⟨forest.slab6.checked,
                  ⟨forest.slab7.checked,
                    ⟨forest.slab8.checked, forest.slab9.checked⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The ten-slab forest as one unit/no-discard checked tree at its aggregate
root. -/
def toUnitAutoSharpTree
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (forest : TenSlabForest terms sqrtFuel logFuel root) :
    UnitAutoSharpTree terms sqrtFuel logFuel root where
  certificate := certificate forest
  checked := certificate_check forest

/-- Final conversion consumed by
`lowerFiniteVBand_of_firstBracketTrees`. -/
def toFirstBracketTree
    {terms sqrtFuel logFuel : ℕ} {root : CertificateBox}
    (forest : TenSlabForest terms sqrtFuel logFuel root) :
    FirstBracketTree root :=
  FirstBracketTree.ofAutoSharpCenteredCheckedTree
    (UnitAutoSharpTree.toAutoSharpCenteredCheckedTree
      (toUnitAutoSharpTree forest))

end TenSlabForest

end FirstBracketForest

end LRLowRatioFiniteVMeanValue

end CourtadeKumar
