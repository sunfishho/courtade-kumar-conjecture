import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalSharpNodeSoundness
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalCommonComponents
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalTargetJetBridge

/-!
# Compatibility of the historical upper-`K` exact jets

The interval soundness modules and the final target bridge deliberately name
their exact jets independently.  This file proves that those two interfaces
use exactly the same twelve jets: eight ordinary nodes and the four sharp
`A/C` nodes.

Only the quotient presentations of the `e` and `y0` chart velocities need
domain hypotheses.  Positivity of the chart coordinates supplies the two
nonvanishing facts used below; no interval or numerical argument occurs in
this adapter.
-/

namespace CourtadeKumar
namespace LRUpperKHistoricalJetCompatibility

open LRUpperKReplayCertificate
open LRUpperKHistoricalEvaluatorAssembly

noncomputable section

namespace Common

abbrev eJet := LRUpperKHistoricalCommonComponents.eJet
abbrev vJet := LRUpperKHistoricalCommonComponents.vJet
abbrev bJet := LRUpperKHistoricalCommonComponents.bFlowJet
abbrev d1Jet := LRUpperKHistoricalCommonComponents.d1Jet
abbrev g0Jet := LRUpperKHistoricalCommonComponents.g0Jet
abbrev kappaJet := LRUpperKHistoricalCommonComponents.kappaJet
abbrev deltaJet := LRUpperKHistoricalCommonComponents.deltaJet
abbrev wJet := LRUpperKHistoricalCommonComponents.wJet

end Common

namespace Sharp

abbrev aY0Jet := LRUpperKHistoricalSharpNodeSoundness.aY0Jet
abbrev aEJet := LRUpperKHistoricalSharpNodeSoundness.aEJet
abbrev cY0Jet := LRUpperKHistoricalSharpNodeSoundness.cY0Jet
abbrev cEJet := LRUpperKHistoricalSharpNodeSoundness.cEJet

end Sharp

namespace Target

abbrev rawPoint := LRUpperKHistoricalTargetJetBridge.rawPoint
abbrev chartES := LRUpperKHistoricalTargetJetBridge.chartES
abbrev chartEK := LRUpperKHistoricalTargetJetBridge.chartEK
abbrev chartY0S := LRUpperKHistoricalTargetJetBridge.chartY0S
abbrev chartY0K := LRUpperKHistoricalTargetJetBridge.chartY0K
abbrev chartY0H := LRUpperKHistoricalTargetJetBridge.chartY0H

abbrev eJet := LRUpperKHistoricalTargetJetBridge.eJet
abbrev vJet := LRUpperKHistoricalTargetJetBridge.vJet
abbrev bJet := LRUpperKHistoricalTargetJetBridge.bJet
abbrev d1Jet := LRUpperKHistoricalTargetJetBridge.d1Jet
abbrev g0Jet := LRUpperKHistoricalTargetJetBridge.g0Jet
abbrev aY0Jet := LRUpperKHistoricalTargetJetBridge.aY0Jet
abbrev aEJet := LRUpperKHistoricalTargetJetBridge.aEJet
abbrev cY0Jet := LRUpperKHistoricalTargetJetBridge.cY0Jet
abbrev cEJet := LRUpperKHistoricalTargetJetBridge.cEJet
abbrev kappaJet := LRUpperKHistoricalTargetJetBridge.kappaJet
abbrev deltaJet := LRUpperKHistoricalTargetJetBridge.deltaJet
abbrev wJet := LRUpperKHistoricalTargetJetBridge.wJet

end Target

/-! ## Compatibility of the ordinary component jets -/

theorem eJet_eq_target (coordinate : CertificatePoint) :
    Common.eJet coordinate = Target.eJet coordinate := by
  rfl

theorem vJet_eq_target (coordinate : CertificatePoint) :
    Common.vJet coordinate = Target.vJet coordinate := by
  rfl

theorem bJet_eq_target (coordinate : CertificatePoint) :
    Common.bJet coordinate = Target.bJet coordinate := by
  apply Jet3.ext
  · rfl
  · rfl
  · rfl
  · simp [Common.bJet, Target.bJet,
      LRUpperKHistoricalCommonComponents.bFlowJet,
      LRUpperKHistoricalTargetJetBridge.bJet,
      LRUpperKHistoricalCommonComponents.bFlowDerivH,
      LRUpperKHistoricalCommonComponents.vDerivH,
      LRUpperKHistoricalCommonComponents.xDerivH,
      LRUpperKHistoricalCommonComponents.rawAt,
      LRUpperKHistoricalTargetJetBridge.chartVH,
      LRUpperKHistoricalTargetJetBridge.chartXH,
      LRUpperKHistoricalTargetJetBridge.rawPoint,
      lrCertificateBFlowDeriv, lrCertificateBFlowValueDeriv,
      lrCertificateBDeriv]

theorem d1Jet_eq_target (coordinate : CertificatePoint) :
    Common.d1Jet coordinate = Target.d1Jet coordinate := by
  apply Jet3.ext
  · rfl
  · rfl
  · rfl
  · simp [Common.d1Jet, Target.d1Jet,
      LRUpperKHistoricalCommonComponents.d1Jet,
      LRUpperKHistoricalTargetJetBridge.d1Jet,
      LRUpperKReplayCertificate.d1Deriv,
      LRUpperKReplayCertificate.yDeriv, lrCertificateBDeriv]

theorem g0Jet_eq_target (coordinate : CertificatePoint) :
    Common.g0Jet coordinate = Target.g0Jet coordinate := by
  rfl

theorem kappaJet_eq_target (coordinate : CertificatePoint) :
    Common.kappaJet coordinate = Target.kappaJet coordinate := by
  rfl

theorem deltaJet_eq_target (coordinate : CertificatePoint) :
    Common.deltaJet coordinate = Target.deltaJet coordinate := by
  rfl

theorem wJet_eq_target (coordinate : CertificatePoint) :
    Common.wJet coordinate = Target.wJet coordinate := by
  rfl

/-! ## The two quotient chart velocities -/

theorem two_e_div_s_eq_chartES (coordinate : CertificatePoint)
    (hs : coordinate.s ≠ 0) :
    2 * lrCertificateE (Target.rawPoint coordinate) / coordinate.s =
      Target.chartES coordinate := by
  simp only [Target.rawPoint, Target.chartES,
    LRUpperKHistoricalTargetJetBridge.rawPoint,
    LRUpperKHistoricalTargetJetBridge.chartES,
    lrCertificateE, lrDeterminantKChartDecode]
  field_simp [hs] <;> ring

theorem e_div_K_eq_chartEK (coordinate : CertificatePoint)
    (hK : coordinate.k ≠ 0) :
    lrCertificateE (Target.rawPoint coordinate) / coordinate.k =
      Target.chartEK coordinate := by
  simp only [Target.rawPoint, Target.chartEK,
    LRUpperKHistoricalTargetJetBridge.rawPoint,
    LRUpperKHistoricalTargetJetBridge.chartEK,
    lrCertificateE, lrDeterminantKChartDecode]
  field_simp [hK] <;> ring

theorem two_y0_div_s_eq_chartY0S (coordinate : CertificatePoint)
    (hs : coordinate.s ≠ 0) :
    2 * lrCertificateY0 (Target.rawPoint coordinate) / coordinate.s =
      Target.chartY0S coordinate := by
  calc
    2 * lrCertificateY0 (Target.rawPoint coordinate) / coordinate.s =
        (Target.rawPoint coordinate).chi *
          (2 * lrCertificateE (Target.rawPoint coordinate) /
            coordinate.s) := by
      simp only [lrCertificateY0]
      ring
    _ = (Target.rawPoint coordinate).chi * Target.chartES coordinate := by
      rw [two_e_div_s_eq_chartES coordinate hs]
    _ = Target.chartY0S coordinate := by
      rfl

theorem y0_div_K_eq_chartY0K (coordinate : CertificatePoint)
    (hK : coordinate.k ≠ 0) :
    lrCertificateY0 (Target.rawPoint coordinate) / coordinate.k =
      Target.chartY0K coordinate := by
  calc
    lrCertificateY0 (Target.rawPoint coordinate) / coordinate.k =
        (Target.rawPoint coordinate).chi *
          (lrCertificateE (Target.rawPoint coordinate) / coordinate.k) := by
      simp only [lrCertificateY0]
      ring
    _ = (Target.rawPoint coordinate).chi * Target.chartEK coordinate := by
      rw [e_div_K_eq_chartEK coordinate hK]
    _ = Target.chartY0K coordinate := by
      rfl

/-! ## Compatibility of the four sharp jets -/

theorem aY0Jet_eq_target (coordinate : CertificatePoint)
    (hs : coordinate.s ≠ 0) (hK : coordinate.k ≠ 0) :
    Sharp.aY0Jet coordinate = Target.aY0Jet coordinate := by
  apply Jet3.ext
  · rfl
  · change
      aPrimitiveDeriv coordinate.s
          (lrCertificateY0 (Target.rawPoint coordinate)) 1
          (2 * lrCertificateY0 (Target.rawPoint coordinate) / coordinate.s) =
        aPrimitiveDeriv coordinate.s
          (lrCertificateY0 (Target.rawPoint coordinate)) 1
          (Target.chartY0S coordinate)
    rw [two_y0_div_s_eq_chartY0S coordinate hs]
  · change
      aPrimitiveDeriv coordinate.s
          (lrCertificateY0 (Target.rawPoint coordinate)) 0
          (lrCertificateY0 (Target.rawPoint coordinate) / coordinate.k) =
        aPrimitiveDeriv coordinate.s
          (lrCertificateY0 (Target.rawPoint coordinate)) 0
          (Target.chartY0K coordinate)
    rw [y0_div_K_eq_chartY0K coordinate hK]
  · rfl

theorem cY0Jet_eq_target (coordinate : CertificatePoint)
    (hs : coordinate.s ≠ 0) (hK : coordinate.k ≠ 0) :
    Sharp.cY0Jet coordinate = Target.cY0Jet coordinate := by
  apply Jet3.ext
  · rfl
  · change
      cPrimitiveDeriv coordinate.s
          (lrCertificateY0 (Target.rawPoint coordinate)) 1
          (2 * lrCertificateY0 (Target.rawPoint coordinate) / coordinate.s) =
        cPrimitiveDeriv coordinate.s
          (lrCertificateY0 (Target.rawPoint coordinate)) 1
          (Target.chartY0S coordinate)
    rw [two_y0_div_s_eq_chartY0S coordinate hs]
  · change
      cPrimitiveDeriv coordinate.s
          (lrCertificateY0 (Target.rawPoint coordinate)) 0
          (lrCertificateY0 (Target.rawPoint coordinate) / coordinate.k) =
        cPrimitiveDeriv coordinate.s
          (lrCertificateY0 (Target.rawPoint coordinate)) 0
          (Target.chartY0K coordinate)
    rw [y0_div_K_eq_chartY0K coordinate hK]
  · rfl

theorem aEJet_eq_target (coordinate : CertificatePoint)
    (hs : coordinate.s ≠ 0) (hK : coordinate.k ≠ 0) :
    Sharp.aEJet coordinate = Target.aEJet coordinate := by
  apply Jet3.ext
  · rfl
  · change
      aPrimitiveDeriv coordinate.s
          (lrCertificateE (Target.rawPoint coordinate)) 1
          (2 * lrCertificateE (Target.rawPoint coordinate) / coordinate.s) =
        aPrimitiveDeriv coordinate.s
          (lrCertificateE (Target.rawPoint coordinate)) 1
          (Target.chartES coordinate)
    rw [two_e_div_s_eq_chartES coordinate hs]
  · change
      aPrimitiveDeriv coordinate.s
          (lrCertificateE (Target.rawPoint coordinate)) 0
          (lrCertificateE (Target.rawPoint coordinate) / coordinate.k) =
        aPrimitiveDeriv coordinate.s
          (lrCertificateE (Target.rawPoint coordinate)) 0
          (Target.chartEK coordinate)
    rw [e_div_K_eq_chartEK coordinate hK]
  · rfl

theorem cEJet_eq_target (coordinate : CertificatePoint)
    (hs : coordinate.s ≠ 0) (hK : coordinate.k ≠ 0) :
    Sharp.cEJet coordinate = Target.cEJet coordinate := by
  apply Jet3.ext
  · rfl
  · change
      cPrimitiveDeriv coordinate.s
          (lrCertificateE (Target.rawPoint coordinate)) 1
          (2 * lrCertificateE (Target.rawPoint coordinate) / coordinate.s) =
        cPrimitiveDeriv coordinate.s
          (lrCertificateE (Target.rawPoint coordinate)) 1
          (Target.chartES coordinate)
    rw [two_e_div_s_eq_chartES coordinate hs]
  · change
      cPrimitiveDeriv coordinate.s
          (lrCertificateE (Target.rawPoint coordinate)) 0
          (lrCertificateE (Target.rawPoint coordinate) / coordinate.k) =
        cPrimitiveDeriv coordinate.s
          (lrCertificateE (Target.rawPoint coordinate)) 0
          (Target.chartEK coordinate)
    rw [e_div_K_eq_chartEK coordinate hK]
  · rfl

/-! ## Bundled adapters for the evaluator assembly -/

/-- Rewrites the exact jet assembled from the two soundness interfaces to the
component convention consumed by the target bridge. -/
theorem evaluateJet_eq_targetComponents (coordinate : CertificatePoint)
    (hs : coordinate.s ≠ 0) (hK : coordinate.k ≠ 0) :
    evaluateJet
        (Common.bJet coordinate) (Common.d1Jet coordinate)
        (Common.g0Jet coordinate)
        (Sharp.aY0Jet coordinate) (Sharp.aEJet coordinate)
        (Sharp.cY0Jet coordinate) (Sharp.cEJet coordinate)
        (Common.vJet coordinate) (Common.kappaJet coordinate)
        (Common.deltaJet coordinate) (Common.wJet coordinate)
        (Common.eJet coordinate) =
      evaluateJet
        (Target.bJet coordinate) (Target.d1Jet coordinate)
        (Target.g0Jet coordinate)
        (Target.aY0Jet coordinate) (Target.aEJet coordinate)
        (Target.cY0Jet coordinate) (Target.cEJet coordinate)
        (Target.vJet coordinate) (Target.kappaJet coordinate)
        (Target.deltaJet coordinate) (Target.wJet coordinate)
        (Target.eJet coordinate) := by
  rw [bJet_eq_target, d1Jet_eq_target, g0Jet_eq_target,
    aY0Jet_eq_target coordinate hs hK,
    aEJet_eq_target coordinate hs hK,
    cY0Jet_eq_target coordinate hs hK,
    cEJet_eq_target coordinate hs hK,
    vJet_eq_target, kappaJet_eq_target, deltaJet_eq_target,
    wJet_eq_target, eJet_eq_target]

/-- The exact jet assembled from the sound ordinary and sharp nodes is the
genuine upper-`K` target jet. -/
theorem evaluateJet_eq_upperKTarget (coordinate : CertificatePoint)
    (hs : coordinate.s ≠ 0) (hK : coordinate.k ≠ 0)
    (hv : lrCertificateV (Target.rawPoint coordinate) ≠ 0)
    (honePlus : 1 + lrCertificateV (Target.rawPoint coordinate) ≠ 0)
    (he : lrCertificateE (Target.rawPoint coordinate) ≠ 0) :
    evaluateJet
        (Common.bJet coordinate) (Common.d1Jet coordinate)
        (Common.g0Jet coordinate)
        (Sharp.aY0Jet coordinate) (Sharp.aEJet coordinate)
        (Sharp.cY0Jet coordinate) (Sharp.cEJet coordinate)
        (Common.vJet coordinate) (Common.kappaJet coordinate)
        (Common.deltaJet coordinate) (Common.wJet coordinate)
        (Common.eJet coordinate) =
      upperKTargetJet coordinate := by
  rw [evaluateJet_eq_targetComponents coordinate hs hK]
  exact LRUpperKHistoricalTargetJetBridge.evaluateJet_eq_upperKTarget
    coordinate hv honePlus he

/-- Positivity of the decoded physical `e` and `v` already implies every
nonvanishing fact required by the quotient-form compatibility and the final
target bridge.  This is the compact adapter consumed by concrete soundness. -/
theorem evaluateJet_eq_upperKTarget_of_compatible
    (coordinate : CertificatePoint)
    (hePositive : 0 < lrCertificateE (Target.rawPoint coordinate))
    (hvPositive : 0 < lrCertificateV (Target.rawPoint coordinate)) :
    evaluateJet
        (Common.bJet coordinate) (Common.d1Jet coordinate)
        (Common.g0Jet coordinate)
        (Sharp.aY0Jet coordinate) (Sharp.aEJet coordinate)
        (Sharp.cY0Jet coordinate) (Sharp.cEJet coordinate)
        (Common.vJet coordinate) (Common.kappaJet coordinate)
        (Common.deltaJet coordinate) (Common.wJet coordinate)
        (Common.eJet coordinate) =
      upperKTargetJet coordinate := by
  have hs : coordinate.s ≠ 0 := by
    intro hsZero
    have heZero : lrCertificateE (Target.rawPoint coordinate) = 0 := by
      simp [Target.rawPoint,
        LRUpperKHistoricalTargetJetBridge.rawPoint,
        lrCertificateE, lrDeterminantKChartDecode, hsZero]
    exact hePositive.ne' heZero
  have hK : coordinate.k ≠ 0 := by
    intro hKZero
    have heZero : lrCertificateE (Target.rawPoint coordinate) = 0 := by
      simp [Target.rawPoint,
        LRUpperKHistoricalTargetJetBridge.rawPoint,
        lrCertificateE, lrDeterminantKChartDecode, hKZero]
    exact hePositive.ne' heZero
  exact evaluateJet_eq_upperKTarget coordinate hs hK
    hvPositive.ne' (add_pos (by norm_num) hvPositive).ne' hePositive.ne'

end
end LRUpperKHistoricalJetCompatibility
end CourtadeKumar
