import InformationTheory.CourtadeKumar.IntervalMidpointOpenChiCertificate
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalThreeCoordinateBase

/-!
# Open-chart midpoint leaves for the historical upper-`K` evaluator

This module isolates the final analytic bridge needed by a three-coordinate
historical leaf.  The executable evaluator has two jobs:

* its singleton `centerBox` pass encloses the value at the ordinary midpoint;
* its whole-box pass encloses the three exact chart partial derivatives.

Those four enclosure facts are collected in `CenteredEvaluatorSoundness`.
Once that record is supplied, all remaining steps below are independent of
the interval expression used by the evaluator.

The chart is deliberately open only at queried points.  A certificate box may
touch `h = 0`; the mean-value segment is nevertheless contained in `0 < h < 1`
because both the queried point and the ordinary midpoint lie there.
-/

open Set

namespace CourtadeKumar
namespace LRUpperKHistoricalOpenMidpointLeaf

open LRUpperKReplayCertificate
open LRUpperKHistoricalThreeCoordinateBase

/-- The open squared-channel chart on which all three ordinary derivatives
exist. -/
def chiGood (h : ℝ) : Prop := 0 < h ∧ h < 1

/-- The open chart is preserved by every unordered segment between two of
its points. -/
theorem chiGood_segment {a b x : ℝ}
    (ha : chiGood a) (hb : chiGood b) (hx : x ∈ Set.uIcc a b) :
    chiGood x := by
  rcases Set.mem_uIcc.mp hx with hab | hba
  · exact ⟨ha.1.trans_le hab.1, hab.2.trans_lt hb.2⟩
  · exact ⟨hb.1.trans_le hba.1, hba.2.trans_lt ha.2⟩

/-- Restatement of the singleton-center adapter in the namespace used by the
leaf theorem. -/
theorem midpoint_mem_centerBox (box : CertificateBox) :
    (centerBox box).Contains box.midpoint :=
  centerBox_contains_midpoint box

private theorem chi_bounds_of_openChartBoxCheck {box : CertificateBox}
    (hcheck : openChartBoxCheck box = true) :
    (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
      box.chiHi ≤ 1 := by
  have hparts :
      (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
      (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
        box.sHi * box.sHi * box.kHi < 1 ∧
      (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
        box.chiHi ≤ 1 := by
    simpa [openChartBoxCheck] using hcheck
  rcases hparts with
    ⟨_, _, _, _, _, _, hchiLo, hchiOrder, hchiHi⟩
  exact ⟨hchiLo, hchiOrder, hchiHi⟩

/-- If an open-chart box contains one genuinely open queried point, then its
ordinary midpoint is also genuinely open.  This is the key adapter for boxes
whose lower `h` endpoint is zero. -/
theorem midpoint_chiGood_of_openChartBoxCheck
    {box : CertificateBox} {coordinate : CertificatePoint}
    (hdomain : openChartBoxCheck box = true)
    (hcoordinate : box.Contains coordinate)
    (hgood : chiGood coordinate.chi) :
    chiGood box.midpoint.chi := by
  have hbounds := chi_bounds_of_openChartBoxCheck hdomain
  have hchiLo : (0 : ℝ) ≤ box.chiLo := by
    exact_mod_cast hbounds.1
  have hchiHi : (box.chiHi : ℝ) ≤ 1 := by
    exact_mod_cast hbounds.2.2
  have hchiHiPos : (0 : ℝ) < box.chiHi :=
    hgood.1.trans_le hcoordinate.2.2.2.2.2
  have hchiLoLtOne : (box.chiLo : ℝ) < 1 :=
    hcoordinate.2.2.2.2.1.trans_lt hgood.2
  constructor
  · norm_num [CertificateBox.midpoint, RationalEnclosure.center,
      CertificateBox.chiInterval]
    linarith
  · norm_num [CertificateBox.midpoint, RationalEnclosure.center,
      CertificateBox.chiInterval]
    linarith

/-- A relevant decoded point in an open-chart box automatically has
`0 < h < 1`.  The box check supplies `h ≥ 0`; raw interior supplies
`0 < h² < 1`. -/
theorem chiGood_of_decodedInterior
    {box : CertificateBox} {coordinate : CertificatePoint}
    (hdomain : openChartBoxCheck box = true)
    (hcoordinate : box.Contains coordinate)
    (hinterior : LRHighShapeInterior
      (lrDeterminantKChartDecode coordinate)) :
    chiGood coordinate.chi := by
  have hbounds := chi_bounds_of_openChartBoxCheck hdomain
  have hchiLo : (0 : ℝ) ≤ box.chiLo := by
    exact_mod_cast hbounds.1
  have hnonnegative : 0 ≤ coordinate.chi :=
    hchiLo.trans hcoordinate.2.2.2.2.1
  have hsquare : coordinate.chi ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [lrDeterminantKChartDecode] using hinterior.2.2
  constructor
  · by_contra hnot
    have hle : coordinate.chi ≤ 0 := le_of_not_gt hnot
    have hzero : coordinate.chi = 0 := le_antisymm hle hnonnegative
    rw [hzero] at hsquare
    norm_num at hsquare
  · by_contra hnot
    have hge : 1 ≤ coordinate.chi := le_of_not_gt hnot
    have hsquareGe : 1 ≤ coordinate.chi ^ 2 := by nlinarith
    exact (not_lt_of_ge hsquareGe) hsquare.2

/-- Abstract soundness interface for the sharp historical centered evaluator.
The value is checked on the singleton `centerBox`; derivative enclosures are
checked on the original box. -/
structure CenteredEvaluatorSoundness
    (box : CertificateBox) (certificate : MidpointCertificate) : Prop where
  centerValue : ∀ coordinate, (centerBox box).Contains coordinate →
    certificate.value.Contains
      (lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate))
  derivS : ∀ coordinate, box.Contains coordinate →
    certificate.derivS.Contains (targetChartDerivS coordinate)
  derivK : ∀ coordinate, box.Contains coordinate →
    certificate.derivK.Contains (targetChartDerivK coordinate)
  derivH : ∀ coordinate, box.Contains coordinate →
    certificate.derivChi.Contains (targetChartDerivH coordinate)

/-- The center pass encloses the exact ordinary midpoint value. -/
theorem CenteredEvaluatorSoundness.midpointValue
    {box : CertificateBox} {certificate : MidpointCertificate}
    (hsound : CenteredEvaluatorSoundness box certificate) :
    certificate.value.Contains
      (lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode box.midpoint)) :=
  hsound.centerValue box.midpoint (midpoint_mem_centerBox box)

/-- Package evaluator soundness and the three calculus theorems into the
chart-restricted derivative interface consumed by the midpoint rule. -/
noncomputable def derivativeEnclosures
    {box : CertificateBox} {certificate : MidpointCertificate}
    (hdomain : openChartBoxCheck box = true)
    (hsound : CenteredEvaluatorSoundness box certificate) :
    BoxDerivativeEnclosuresOn
      (fun coordinate ↦ lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate))
      box certificate chiGood := by
  refine
    { partialS := targetChartDerivS
      partialK := targetChartDerivK
      partialChi := targetChartDerivH
      derivS := ?_
      derivK := ?_
      derivChi := ?_
      boundS := ?_
      boundK := ?_
      boundChi := ?_ }
  · intro coordinate hcoordinate hgood
    exact hasDerivAt_targetChart_s
      (openChartBoxCheck_sound hdomain hcoordinate hgood.1 hgood.2)
  · intro coordinate hcoordinate hgood
    exact hasDerivAt_targetChart_k
      (openChartBoxCheck_sound hdomain hcoordinate hgood.1 hgood.2)
  · intro coordinate hcoordinate hgood
    exact hasDerivAt_targetChart_h
      (openChartBoxCheck_sound hdomain hcoordinate hgood.1 hgood.2)
  · intro coordinate hcoordinate
    exact hsound.derivS coordinate hcoordinate
  · intro coordinate hcoordinate
    exact hsound.derivK coordinate hcoordinate
  · intro coordinate hcoordinate
    exact hsound.derivH coordinate hcoordinate

/-- A checked historical midpoint leaf is strictly positive at every queried
point of the open chart. -/
theorem positive_of_midpointCheck
    {box : CertificateBox} {certificate : MidpointCertificate}
    (hdomain : openChartBoxCheck box = true)
    (hsound : CenteredEvaluatorSoundness box certificate)
    (hcheck : certificate.check box = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hgood : chiGood coordinate.chi) :
    0 < lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) := by
  exact certificate.soundOn_of_derivativeEnclosures
    hsound.midpointValue
    (derivativeEnclosures hdomain hsound)
    chiGood_segment hcheck
    (midpoint_chiGood_of_openChartBoxCheck hdomain hcoordinate hgood)
    hcoordinate hgood

/-- Non-strict form used by region-cover assembly. -/
theorem nonnegative_of_midpointCheck
    {box : CertificateBox} {certificate : MidpointCertificate}
    (hdomain : openChartBoxCheck box = true)
    (hsound : CenteredEvaluatorSoundness box certificate)
    (hcheck : certificate.check box = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hgood : chiGood coordinate.chi) :
    0 ≤ lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) :=
  (positive_of_midpointCheck hdomain hsound hcheck hcoordinate hgood).le

/-- Final leaf-facing form: the existing centered replay relevance predicate
already contains decoded raw interior, so no separate `h` hypothesis is
needed. -/
theorem nonnegative_of_midpointCheck_of_relevant
    {box : CertificateBox} {certificate : MidpointCertificate}
    (hdomain : openChartBoxCheck box = true)
    (hsound : CenteredEvaluatorSoundness box certificate)
    (hcheck : certificate.check box = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hrelevant : CenteredRelevant coordinate) :
    0 ≤ lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) := by
  exact nonnegative_of_midpointCheck hdomain hsound hcheck hcoordinate
    (chiGood_of_decodedInterior hdomain hcoordinate hrelevant.1)

end LRUpperKHistoricalOpenMidpointLeaf
end CourtadeKumar
