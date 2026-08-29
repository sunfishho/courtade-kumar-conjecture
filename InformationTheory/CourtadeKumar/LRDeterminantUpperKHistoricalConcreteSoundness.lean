import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalConcreteEvaluator
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalSharpNodeSoundness
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalCommonComponents
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalJetCompatibility
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalTargetJetBridge

/-!
# Soundness of the concrete historical upper-`K` checker

This module is the final semantic assembly for one accepted historical leaf.
The executable checker reconstructs its sharp payload and four monotone-corner
checks deterministically.  From those checks we obtain

* the four cancellation-sensitive `A/C` jets;
* the eight ordinary component jets;
* the exact assembled CK target jet; and
* the centered value/whole-box derivative interface consumed by the open-`h`
  midpoint theorem.

The historical corner evaluator is fixed at square-root fuel `40` and
logarithm fuel `48`, so the sound checker exported here uses precisely those
two audited fuel values.
-/

namespace CourtadeKumar
namespace LRUpperKHistoricalConcreteSoundness

open LRUpperKReplayCertificate

/-! ## Boolean-check extraction -/

/-- The five semantic checks hidden inside one concrete payload check. -/
structure PayloadFacts (terms : ℕ) (box : CertificateBox) : Prop where
  sharp : LRUpperKHistoricalACAD.check terms box
    (LRUpperKHistoricalConcreteEvaluator.autoPayload 40 48 box) = true
  aY0Corner :
    LRUpperKHistoricalACValues.aCornerCheck 40 48 box
      (y0AD box).value = true
  cY0Corner :
    LRUpperKHistoricalACValues.cCornerCheck 40 48 box
      (y0AD box).value = true
  aECorner :
    LRUpperKHistoricalACValues.aCornerCheck 40 48 box
      (eAD box).value = true
  cECorner :
    LRUpperKHistoricalACValues.cCornerCheck 40 48 box
      (eAD box).value = true

theorem payloadFacts_of_checked (terms : ℕ) {box : CertificateBox}
    (hcheck : LRUpperKHistoricalConcreteEvaluator.payloadCheck
      terms 40 48 box = true) :
    PayloadFacts terms box := by
  have hparts :
      LRUpperKHistoricalACAD.check terms box
          (LRUpperKHistoricalConcreteEvaluator.autoPayload 40 48 box) = true ∧
        LRUpperKHistoricalConcreteEvaluator.cornerChecks 40 48 box = true := by
    simpa [LRUpperKHistoricalConcreteEvaluator.payloadCheck] using hcheck
  have hcornersLeft :
      ((LRUpperKHistoricalACValues.aCornerCheck 40 48 box
            (y0AD box).value = true ∧
          LRUpperKHistoricalACValues.cCornerCheck 40 48 box
            (y0AD box).value = true) ∧
        LRUpperKHistoricalACValues.aCornerCheck 40 48 box
          (eAD box).value = true) ∧
      LRUpperKHistoricalACValues.cCornerCheck 40 48 box
        (eAD box).value = true := by
    simpa [LRUpperKHistoricalConcreteEvaluator.cornerChecks] using hparts.2
  rcases hcornersLeft with ⟨⟨⟨haY0, hcY0⟩, haE⟩, hcE⟩
  exact
    { sharp := hparts.1
      aY0Corner := haY0
      cY0Corner := hcY0
      aECorner := haE
      cECorner := hcE }

/-! ## The singleton center remains an admissible chart box -/

/-- Taking all three rational midpoints preserves the closed executable chart
conditions.  This is needed because the center payload is checked on a
singleton box, while the concrete leaf stores only the original box check. -/
theorem openChartBoxCheck_centerBox {box : CertificateBox}
    (hcheck : openChartBoxCheck box = true) :
    openChartBoxCheck
      (LRUpperKHistoricalThreeCoordinateBase.centerBox box) = true := by
  have hparts :
      (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
        (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
          box.sHi * box.sHi * box.kHi < 1 ∧
        (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
          box.chiHi ≤ 1 := by
    simpa [openChartBoxCheck] using hcheck
  rcases hparts with
    ⟨hsLo, hsOrder, hsHi, hKLo, hKOrder, hProduct,
      hhLo, hhOrder, hhHi⟩
  let sMid : ℚ := (box.sLo + box.sHi) / 2
  let kMid : ℚ := (box.kLo + box.kHi) / 2
  let hMid : ℚ := (box.chiLo + box.chiHi) / 2
  have hsMidPositive : (0 : ℚ) < sMid := by
    dsimp [sMid]
    linarith
  have hsMidLe : sMid ≤ box.sHi := by
    dsimp [sMid]
    linarith
  have hsMidLtOne : sMid < 1 := hsMidLe.trans_lt hsHi
  have hKMidPositive : (0 : ℚ) < kMid := by
    dsimp [kMid]
    linarith
  have hKMidLe : kMid ≤ box.kHi := by
    dsimp [kMid]
    linarith
  have hsHiNonnegative : (0 : ℚ) ≤ box.sHi :=
    hsLo.le.trans hsOrder
  have hKMidNonnegative : (0 : ℚ) ≤ kMid := hKMidPositive.le
  have hsSquareLe : sMid * sMid ≤ box.sHi * box.sHi :=
    mul_le_mul hsMidLe hsMidLe hsMidPositive.le hsHiNonnegative
  have hMidProduct : sMid * sMid * kMid < 1 := by
    have hle : sMid * sMid * kMid ≤
        box.sHi * box.sHi * box.kHi :=
      mul_le_mul hsSquareLe hKMidLe hKMidNonnegative
        (mul_nonneg hsHiNonnegative hsHiNonnegative)
    exact hle.trans_lt hProduct
  have hhMidNonnegative : (0 : ℚ) ≤ hMid := by
    dsimp [hMid]
    linarith
  have hhMidLeOne : hMid ≤ 1 := by
    dsimp [hMid]
    linarith
  have hcenter :
      (0 : ℚ) < sMid ∧ sMid ≤ sMid ∧ sMid < 1 ∧
        (0 : ℚ) < kMid ∧ kMid ≤ kMid ∧
          sMid * sMid * kMid < 1 ∧
        (0 : ℚ) ≤ hMid ∧ hMid ≤ hMid ∧ hMid ≤ 1 :=
    ⟨hsMidPositive, le_rfl, hsMidLtOne,
      hKMidPositive, le_rfl, hMidProduct,
      hhMidNonnegative, le_rfl, hhMidLeOne⟩
  simpa [openChartBoxCheck,
    LRUpperKHistoricalThreeCoordinateBase.centerBox,
    CertificateBox.sInterval, CertificateBox.kInterval,
    CertificateBox.chiInterval, RationalEnclosure.center,
    sMid, kMid, hMid] using hcenter

/-! ## Full value-and-three-partial soundness -/

/-- The deterministically reconstructed historical evaluator encloses the
genuine target value and all three genuine `(s,K,h)` chart derivatives at
every point of its box. -/
theorem evaluateAD_sound (terms : ℕ) {box : CertificateBox}
    (hdomain : openChartBoxCheck box = true)
    (hcheck : LRUpperKHistoricalConcreteEvaluator.payloadCheck
      terms 40 48 box = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (LRUpperKHistoricalEvaluatorAssembly.evaluateAD terms box
      (LRUpperKHistoricalConcreteEvaluator.autoPayload 40 48 box)).Contains
      (lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate))
      (targetChartDerivS coordinate)
      (targetChartDerivK coordinate)
      (LRUpperKHistoricalThreeCoordinateBase.targetChartDerivH
        coordinate) := by
  have hpayload := payloadFacts_of_checked terms hcheck
  have hsharp :=
    LRUpperKHistoricalSharpNodeSoundness.sharpNodeEnclosures_of_checked terms
    hdomain hpayload.sharp hcoordinate
    hpayload.aY0Corner hpayload.cY0Corner
    hpayload.aECorner hpayload.cECorner
  have hcommon :=
    LRUpperKHistoricalCommonComponents.commonComponentsAt_of_checked terms
    hpayload.sharp hcoordinate
  have hePoint :
      0 < lrCertificateE
        (LRUpperKHistoricalTargetJetBridge.rawPoint coordinate) := by
    simpa [LRUpperKHistoricalTargetJetBridge.rawPoint,
      LRUpperKHistoricalCommonComponents.rawAt] using
      hcommon.ePointPositive
  have hvPoint :
      0 < lrCertificateV
        (LRUpperKHistoricalTargetJetBridge.rawPoint coordinate) := by
    simpa [LRUpperKHistoricalTargetJetBridge.rawPoint,
      LRUpperKHistoricalCommonComponents.rawAt] using
      hcommon.vPointPositive
  have hencloses :=
    LRUpperKHistoricalEvaluatorAssembly.evaluateAD_sound_of_sharp_nodes terms
    hcommon.vLowerPositive hcommon.eLowerPositive
    hcommon.bFlow hcommon.d1 hcommon.g0
    hsharp.aY0 hsharp.aE hsharp.cY0 hsharp.cE
    hcommon.v hcommon.kappa hcommon.delta hcommon.w hcommon.e
  have hjet :=
    LRUpperKHistoricalJetCompatibility.evaluateJet_eq_upperKTarget_of_compatible
    coordinate hePoint hvPoint
  exact LRUpperKHistoricalEvaluatorAssembly.contains_upperKTarget_of_encloses
    hencloses hjet

/-! ## Centered midpoint interface -/

/-- The center pass supplies the exact midpoint value, and the whole-box pass
supplies all three derivative enclosures. -/
theorem centeredEvaluatorSoundness (terms : ℕ) {box : CertificateBox}
    (hdomain : openChartBoxCheck box = true)
    (hcenter : LRUpperKHistoricalConcreteEvaluator.payloadCheck terms 40 48
      (LRUpperKHistoricalThreeCoordinateBase.centerBox box) = true)
    (hwhole : LRUpperKHistoricalConcreteEvaluator.payloadCheck
      terms 40 48 box = true) :
    LRUpperKHistoricalOpenMidpointLeaf.CenteredEvaluatorSoundness box
      (LRUpperKHistoricalConcreteEvaluator.evaluation
        terms 40 48 box) := by
  have hcenterDomain := openChartBoxCheck_centerBox hdomain
  refine
    { centerValue := ?_
      derivS := ?_
      derivK := ?_
      derivH := ?_ }
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound terms hcenterDomain hcenter hcoordinate
    simpa [LRUpperKHistoricalConcreteEvaluator.evaluation] using hsound.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound terms hdomain hwhole hcoordinate
    simpa [LRUpperKHistoricalConcreteEvaluator.evaluation] using hsound.2.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound terms hdomain hwhole hcoordinate
    simpa [LRUpperKHistoricalConcreteEvaluator.evaluation] using
      hsound.2.2.1
  · intro coordinate hcoordinate
    have hsound := evaluateAD_sound terms hdomain hwhole hcoordinate
    simpa [LRUpperKHistoricalConcreteEvaluator.evaluation] using
      hsound.2.2.2

/-! ## Final accepted-leaf theorem -/

/-- A successful concrete historical check proves the upper-`K` determinant
target nonnegative at every relevant point of the checked box. -/
theorem nonnegative_of_check (terms : ℕ) {box : CertificateBox}
    (hcheck : LRUpperKHistoricalConcreteEvaluator.check
      terms 40 48 box = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hrelevant : CenteredRelevant coordinate) :
    0 ≤ lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) := by
  have hpartsLeft :
      ((openChartBoxCheck box = true ∧
          LRUpperKHistoricalConcreteEvaluator.payloadCheck terms 40 48
            (LRUpperKHistoricalThreeCoordinateBase.centerBox box) = true) ∧
        LRUpperKHistoricalConcreteEvaluator.payloadCheck
          terms 40 48 box = true) ∧
      (LRUpperKHistoricalConcreteEvaluator.evaluation
        terms 40 48 box).check box = true := by
    simpa [LRUpperKHistoricalConcreteEvaluator.check] using hcheck
  rcases hpartsLeft with ⟨⟨⟨hdomain, hcenter⟩, hwhole⟩, hevaluation⟩
  have hsound := centeredEvaluatorSoundness terms
    hdomain hcenter hwhole
  exact LRUpperKHistoricalOpenMidpointLeaf.nonnegative_of_midpointCheck_of_relevant
    hdomain hsound hevaluation hcoordinate hrelevant

end LRUpperKHistoricalConcreteSoundness
end CourtadeKumar
