import InformationTheory.CourtadeKumar.LRCompactVCenteredMonotoneConfigCore
import InformationTheory.CourtadeKumar.KernelCheckedBoolCommand
import InformationTheory.CourtadeKumar.LRCompactVFixedDyadicIntervalSound
import InformationTheory.CourtadeKumar.LRCompactVWOneEndpointEnclosure

/-!
# Shared endpoint-tight `W_R(1)` seed for the adjacent compact region

The centered monotone terminal evaluator uses one fixed-dyadic enclosure of
`W_R(1)` on its eight adjacent strips.  This module records the common root
box and proves the single seed sound once.  The upper endpoint comes from the
lower-`R` endpoint Abel enclosure; antitonicity then makes it valid throughout
the root box.  The lower endpoint is a conservative outward rounding of the
ordinary box-wide Abel lower bound.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace LRCompactVFixedDyadic
namespace NatInterval

/-- A fixed-dyadic interval outwardly covers an exact rational enclosure. -/
def CoversEnclosure (interval : NatInterval) (bits : ℕ)
    (exact : RationalEnclosure) : Prop :=
  decodeNat bits interval.lower ≤ exact.lower ∧
    exact.upper ≤ decodeNat bits interval.upper

/-- Coverage of a sound rational enclosure transports to fixed-dyadic real
containment. -/
theorem contains_of_coversEnclosure
    {interval : NatInterval} {bits : ℕ} {exact : RationalEnclosure}
    {value : ℝ} (hcover : interval.CoversEnclosure bits exact)
    (hexact : exact.Contains value) :
    interval.Contains bits value := by
  rcases hcover with ⟨hcoverLower, hcoverUpper⟩
  have hcoverLowerReal :
      (decodeNat bits interval.lower : ℝ) ≤ (exact.lower : ℝ) := by
    exact_mod_cast hcoverLower
  have hcoverUpperReal :
      (exact.upper : ℝ) ≤ (decodeNat bits interval.upper : ℝ) := by
    exact_mod_cast hcoverUpper
  constructor
  · exact hcoverLowerReal.trans hexact.1
  · exact hexact.2.trans hcoverUpperReal

end NatInterval
end LRCompactVFixedDyadic

namespace LRCompactVCenteredMonotoneSharedW

open LRCompactVFixedDyadic

/-- Backwards-compatible name for the common adjacent parent box. -/
abbrev adjacentRootBox : CertificateBox :=
  LRCompactVCenteredMonotoneConfig.rootBox

/-- Backwards-compatible name for the common fixed-dyadic precision. -/
abbrev sharedWBits : ℕ := LRCompactVCenteredMonotoneConfig.bits

/-- Backwards-compatible name for the shared endpoint-kernel enclosure. -/
abbrev sharedWSeed : NatInterval := LRCompactVCenteredMonotoneConfig.wOne

theorem adjacentRootBox_valid : LRCompactVBoxValid adjacentRootBox := by
  norm_num [adjacentRootBox, LRCompactVCenteredMonotoneConfig.rootBox,
    LRCompactVBoxValid]

theorem adjacentRootBox_sLo_pos : (0 : ℚ) < adjacentRootBox.sLo := by
  norm_num [adjacentRootBox, LRCompactVCenteredMonotoneConfig.rootBox]

/-- Closed exact-arithmetic check for the two outward endpoint inequalities. -/
def sharedWSeedCoverCheck : Bool :=
  decide (decodeNat sharedWBits sharedWSeed.lower ≤
      (lrCompactVWOneEndpointEnclosure 34 72 adjacentRootBox).lower) &&
    decide ((lrCompactVWOneEndpointEnclosure 34 72 adjacentRootBox).upper ≤
      decodeNat sharedWBits sharedWSeed.upper)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
#kernel_checked_bool sharedWSeedCoverCheck_reduction sharedWSeedCoverCheck

theorem sharedWSeed_coversEndpointEnclosure :
    sharedWSeed.CoversEnclosure sharedWBits
      (lrCompactVWOneEndpointEnclosure 34 72 adjacentRootBox) := by
  simpa only [NatInterval.CoversEnclosure, sharedWSeedCoverCheck,
    Bool.and_eq_true, decide_eq_true_eq] using
    sharedWSeedCoverCheck_reduction

/-- The common 96-bit seed contains `W_R(1)` at every interior point of the
adjacent root, hence can be reused unchanged by all eight child strips. -/
theorem sharedWSeed_contains
    {point : CertificatePoint}
    (hpoint : adjacentRootBox.Contains point)
    (hinterior : LRCompactVInterior point) :
    sharedWSeed.Contains sharedWBits (lrWKernel point.s 1) := by
  apply NatInterval.contains_of_coversEnclosure
    sharedWSeed_coversEndpointEnclosure
  exact lrCompactVWOneEndpointEnclosure_sound 34 72
    adjacentRootBox_valid adjacentRootBox_sLo_pos hpoint hinterior

end LRCompactVCenteredMonotoneSharedW
end CourtadeKumar
