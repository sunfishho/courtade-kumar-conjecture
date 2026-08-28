import InformationTheory.CourtadeKumar.LRGapBudgetSEFourBoundaryReplay
import InformationTheory.CourtadeKumar.LRGapBudgetSEGeneratedTailCertificate

/-!
# Complete replayed gap-budget certificate on the `k >= 4` tail

The checked boundary certificate proves the gap budget at `k = 4`.  The
checked derivative certificate proves that the budget is nondecreasing in
`k`.  This file supplies the exact physical-domain transport needed to join
those two results with the analytic monotonicity theorem.
-/

open Set

namespace CourtadeKumar
namespace LRGapBudgetSEFourTailCertificate

/-- The analytic interior persists when `k` is decreased along the segment
from a physical endpoint to the boundary value `4`. -/
theorem interior_on_four_segment
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hphysical : LRHighShapePhysical point)
    {q : ℝ} (hq : q ∈ Icc (4 : ℝ) point.k) :
    LRHighShapeInterior { point with k := q } := by
  change point.s ∈ Ioo (0 : ℝ) 1 ∧
    point.s * q ∈ Ioo (0 : ℝ) 1 ∧
    point.chi ∈ Ioo (0 : ℝ) 1
  refine ⟨hinterior.1, ?_, hinterior.2.2⟩
  constructor
  · exact mul_pos hinterior.1.1 (lt_of_lt_of_le (by norm_num) hq.1)
  · exact (mul_le_mul_of_nonneg_left hq.2 hinterior.1.1.le).trans_lt
      hphysical.1

/-- Each physical inequality persists when `k` is decreased along the
segment from the endpoint to `4`. -/
theorem physical_on_four_segment
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hphysical : LRHighShapePhysical point)
    {q : ℝ} (hq : q ∈ Icc (4 : ℝ) point.k) :
    LRHighShapePhysical { point with k := q } := by
  change point.s * q < 1 ∧
    point.chi * (point.s * q) ≤ 3 / 20 ∧
    0 ≤ 8 - point.s * q * (9 - point.chi)
  have heMono : point.s * q ≤ point.s * point.k :=
    mul_le_mul_of_nonneg_left hq.2 hinterior.1.1.le
  have hchiMono : point.chi * (point.s * q) ≤
      point.chi * (point.s * point.k) :=
    mul_le_mul_of_nonneg_left heMono hinterior.2.2.1.le
  have hnine : 0 ≤ 9 - point.chi := by
    linarith [hinterior.2.2.2]
  have hsmallVMono : point.s * q * (9 - point.chi) ≤
      point.s * point.k * (9 - point.chi) :=
    mul_le_mul_of_nonneg_right heMono hnine
  exact ⟨heMono.trans_lt hphysical.1,
    hchiMono.trans hphysical.2.1,
    by linarith [hphysical.2.2, hsmallVMono]⟩

/-- The physical constraint at a tail point implies the precise relevance
constraint required by the independently replayed `k = 4` boundary tree. -/
theorem four_boundary_relevant
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hphysical : LRHighShapePhysical point)
    (hk : 4 ≤ point.k) :
    LRGapBudgetSEFourBoundary.Relevant point.s point.chi := by
  have heFour : 4 * point.s ≤ point.s * point.k := by
    calc
      4 * point.s = point.s * 4 := by ring
      _ ≤ point.s * point.k :=
        mul_le_mul_of_nonneg_left hk hinterior.1.1.le
  have hchiFour : point.chi * (4 * point.s) ≤
      point.chi * (point.s * point.k) :=
    mul_le_mul_of_nonneg_left heFour hinterior.2.2.1.le
  unfold LRGapBudgetSEFourBoundary.Relevant
  calc
    4 * point.chi * point.s = point.chi * (4 * point.s) := by ring
    _ ≤ point.chi * (point.s * point.k) := hchiFour
    _ ≤ 3 / 20 := hphysical.2.1

/-- The replayed boundary tree proves the original-coordinate budget at
`k = 4`. -/
theorem gapBudget_four_nonnegative
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hphysical : LRHighShapePhysical point)
    (hs : point.s < 1 / 10) (hk : 4 ≤ point.k) :
    0 ≤ lrCertificateGapBudget { point with k := 4 } := by
  have hboundary := LRGapBudgetSEFourBoundaryReplay.gap_nonnegative
    ⟨hinterior.1.1, hs⟩
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩
    (four_boundary_relevant hinterior hphysical hk)
  have hinteriorFour := interior_on_four_segment hinterior hphysical
    (q := (4 : ℝ)) ⟨le_rfl, hk⟩
  rw [lrCertificateGapBudget_eq_SEChi
    (lrCertificateV_pos_of_highShapeInterior hinteriorFour)]
  simpa [lrCertificateE, mul_comm] using hboundary

/-- Fully replayed nonnegativity of the gap budget throughout the physical
high-shape tail `k >= 4`.  Both finite certificates are kernel checked. -/
theorem gapBudget_nonnegative_unconditional
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hphysical : LRHighShapePhysical point)
    (hs : point.s < 1 / 10) (hk : 4 ≤ point.k) :
    0 ≤ lrCertificateGapBudget point := by
  apply lrCertificateGapBudget_nonneg_of_four_of_derivK_nonneg hk
  · intro q hq
    exact interior_on_four_segment hinterior hphysical hq
  · exact gapBudget_four_nonnegative hinterior hphysical hs hk
  · intro q hq
    exact CourtadeKumar.LRGapBudgetSEGeneratedTailCertificate.gapBudgetDerivK_nonnegative_unconditional
        (interior_on_four_segment hinterior hphysical
          ⟨hq.1.le, hq.2.le⟩)
        (physical_on_four_segment hinterior hphysical
          ⟨hq.1.le, hq.2.le⟩)
        hs hq.1.le

end LRGapBudgetSEFourTailCertificate
end CourtadeKumar
