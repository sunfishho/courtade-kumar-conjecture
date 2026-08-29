import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalEvaluatorAssembly
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalDomainAdapters
import InformationTheory.CourtadeKumar.LRDeterminantUpperKReplayEvaluator

/-!
# Common semantic components for the historical upper-`K` evaluator

The sharp historical evaluator changes only the four cancellation-sensitive
`A/C` nodes.  All its remaining nodes are the ordinary, already checked nodes
from `LRUpperKReplayCertificate.sharpEvaluateSKAD_sound`.

This file gives those common nodes a public interface.  At any point of a box
whose sharp payload check succeeds, `commonComponentsAt_of_checked` returns
simultaneous kernel-level `IntervalAD` enclosures of the exact value and all
three `(s,K,h)` partials of

* `e`, `v`, `B`, and `D1`;
* `g0(v)`, `kappa(v)`, `delta`, and `W`; and
* the positive interval lower bounds and positive point values of `e` and `v`.

The proof is the ordinary-node portion of the production sharp evaluator,
factored without adding any analytic or numerical hypothesis.
-/

namespace CourtadeKumar
namespace LRUpperKHistoricalCommonComponents

open LRUpperKReplayCertificate
open LRUpperKHistoricalEvaluatorAssembly

/-! ## Exact chart data -/

noncomputable def rawAt (coordinate : CertificatePoint) : CertificatePoint :=
  lrDeterminantKChartDecode coordinate

noncomputable def eDerivS (coordinate : CertificatePoint) : ℝ :=
  (rawAt coordinate).k + (rawAt coordinate).s * coordinate.k

noncomputable def eDerivK (coordinate : CertificatePoint) : ℝ :=
  (rawAt coordinate).s * coordinate.s

noncomputable def xDerivS (coordinate : CertificatePoint) : ℝ :=
  -((rawAt coordinate).chi * eDerivS coordinate)

noncomputable def xDerivK (coordinate : CertificatePoint) : ℝ :=
  -((rawAt coordinate).chi * eDerivK coordinate)

noncomputable def xDerivH (coordinate : CertificatePoint) : ℝ :=
  -(2 * coordinate.chi * lrCertificateE (rawAt coordinate))

noncomputable def vDerivS (coordinate : CertificatePoint) : ℝ :=
  lrCertificateVDeriv (rawAt coordinate)
    (eDerivS coordinate) (xDerivS coordinate)

noncomputable def vDerivK (coordinate : CertificatePoint) : ℝ :=
  lrCertificateVDeriv (rawAt coordinate)
    (eDerivK coordinate) (xDerivK coordinate)

noncomputable def vDerivH (coordinate : CertificatePoint) : ℝ :=
  lrCertificateVDeriv (rawAt coordinate) 0 (xDerivH coordinate)

noncomputable def yDerivS (coordinate : CertificatePoint) : ℝ :=
  LRUpperKReplayCertificate.yDeriv (rawAt coordinate) 1
    (eDerivS coordinate)

noncomputable def yDerivK (coordinate : CertificatePoint) : ℝ :=
  LRUpperKReplayCertificate.yDeriv (rawAt coordinate) 0
    (eDerivK coordinate)

noncomputable def bFlowDerivS (coordinate : CertificatePoint) : ℝ :=
  lrCertificateBFlowDeriv (rawAt coordinate) 1
    (eDerivS coordinate) (vDerivS coordinate)

noncomputable def bFlowDerivK (coordinate : CertificatePoint) : ℝ :=
  lrCertificateBFlowDeriv (rawAt coordinate) 0
    (eDerivK coordinate) (vDerivK coordinate)

noncomputable def bFlowDerivH (coordinate : CertificatePoint) : ℝ :=
  vDerivH coordinate / (1 + lrCertificateV (rawAt coordinate))

noncomputable def d1DerivS (coordinate : CertificatePoint) : ℝ :=
  LRUpperKReplayCertificate.d1Deriv (rawAt coordinate) 1
    (eDerivS coordinate)

noncomputable def d1DerivK (coordinate : CertificatePoint) : ℝ :=
  LRUpperKReplayCertificate.d1Deriv (rawAt coordinate) 0
    (eDerivK coordinate)

noncomputable def deltaDerivS (coordinate : CertificatePoint) : ℝ :=
  LRUpperKReplayCertificate.deltaDeriv (rawAt coordinate)
    (xDerivS coordinate) (vDerivS coordinate)

noncomputable def deltaDerivK (coordinate : CertificatePoint) : ℝ :=
  LRUpperKReplayCertificate.deltaDeriv (rawAt coordinate)
    (xDerivK coordinate) (vDerivK coordinate)

noncomputable def deltaDerivH (coordinate : CertificatePoint) : ℝ :=
  LRUpperKReplayCertificate.deltaDeriv (rawAt coordinate)
    (xDerivH coordinate) (vDerivH coordinate)

/-! ## Exact real jets for the ordinary nodes -/

noncomputable def eJet (coordinate : CertificatePoint) : Jet3 where
  value := lrCertificateE (rawAt coordinate)
  derivS := eDerivS coordinate
  derivK := eDerivK coordinate
  derivH := 0

noncomputable def vJet (coordinate : CertificatePoint) : Jet3 where
  value := lrCertificateV (rawAt coordinate)
  derivS := vDerivS coordinate
  derivK := vDerivK coordinate
  derivH := vDerivH coordinate

noncomputable def bFlowJet (coordinate : CertificatePoint) : Jet3 where
  value := lrCertificateBFlow (rawAt coordinate)
  derivS := bFlowDerivS coordinate
  derivK := bFlowDerivK coordinate
  derivH := bFlowDerivH coordinate

noncomputable def d1Jet (coordinate : CertificatePoint) : Jet3 where
  value := lrDeterminantD1 (rawAt coordinate)
  derivS := d1DerivS coordinate
  derivK := d1DerivK coordinate
  derivH := 0

noncomputable def g0Jet (coordinate : CertificatePoint) : Jet3 where
  value := lrCertificateG0 (lrCertificateV (rawAt coordinate))
  derivS := lrCertificateG0Prime (lrCertificateV (rawAt coordinate)) *
    vDerivS coordinate
  derivK := lrCertificateG0Prime (lrCertificateV (rawAt coordinate)) *
    vDerivK coordinate
  derivH := lrCertificateG0Prime (lrCertificateV (rawAt coordinate)) *
    vDerivH coordinate

noncomputable def kappaJet (coordinate : CertificatePoint) : Jet3 where
  value := kappaV (lrCertificateV (rawAt coordinate))
  derivS := kappaDeriv (lrCertificateV (rawAt coordinate))
    (vDerivS coordinate)
  derivK := kappaDeriv (lrCertificateV (rawAt coordinate))
    (vDerivK coordinate)
  derivH := kappaDeriv (lrCertificateV (rawAt coordinate))
    (vDerivH coordinate)

noncomputable def deltaJet (coordinate : CertificatePoint) : Jet3 where
  value := lrDeterminantDelta (rawAt coordinate)
  derivS := deltaDerivS coordinate
  derivK := deltaDerivK coordinate
  derivH := deltaDerivH coordinate

noncomputable def wJet (coordinate : CertificatePoint) : Jet3 where
  value := lrCertificateW (rawAt coordinate)
  derivS := lrCertificateOmegaDeriv (rawAt coordinate).s 0 1 0
  derivK := lrCertificateOmegaDeriv (rawAt coordinate).s 0 0 0
  derivH := lrCertificateOmegaDeriv (rawAt coordinate).s 0 0 0

/-! ## Bundled public interface -/

/-- Every ordinary component needed by the sharp historical assembly, at one
queried box point.  `Encloses` means simultaneous containment of the exact
value and the three displayed chart derivatives. -/
structure CommonComponentsAt (terms : ℕ) (box : CertificateBox)
    (payload : LRUpperKHistoricalACAD.Payload)
    (coordinate : CertificatePoint) : Prop where
  eLowerPositive : (0 : ℚ) < (eAD box).value.lower
  vLowerPositive : (0 : ℚ) < (vAD box payload.base).value.lower
  ePointPositive : 0 < lrCertificateE (rawAt coordinate)
  vPointPositive : 0 < lrCertificateV (rawAt coordinate)
  e : Encloses (eAD box) (eJet coordinate)
  v : Encloses (vAD box payload.base) (vJet coordinate)
  bFlow : Encloses (bFlowAD terms box payload.base)
    (bFlowJet coordinate)
  d1 : Encloses (d1AD terms box payload.base) (d1Jet coordinate)
  g0 : Encloses
    (payload.base.g0.evaluate terms (vAD box payload.base))
    (g0Jet coordinate)
  kappa : Encloses (kappaAD box payload.base) (kappaJet coordinate)
  delta : Encloses (deltaAD box payload.base) (deltaJet coordinate)
  w : Encloses (wAD terms box payload.base) (wJet coordinate)

/-! ## Soundness -/

/-- Factor all ordinary nodes out of the production sharp evaluator.  The
only numerical assumption is the same executable sharp payload check already
used by an accepted historical leaf. -/
theorem commonComponentsAt_of_checked (terms : ℕ)
    {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload}
    (hcheck : LRUpperKHistoricalACAD.check terms box payload = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    CommonComponentsAt terms box payload coordinate := by
  have hcheckFacts :=
    LRUpperKHistoricalDomainAdapters.checkFacts_of_checked hcheck
  have hvalid : LRUpperKHistoricalACAD.Valid terms box payload :=
    hcheckFacts.valid
  have hbase : LRUpperKReplayCertificate.Valid box payload.base := hvalid.base
  let raw := lrDeterminantKChartDecode coordinate
  let eS := raw.k + raw.s * coordinate.k
  let eK := raw.s * coordinate.s
  let xS := -(raw.chi * eS)
  let xK := -(raw.chi * eK)
  let xH := -(2 * coordinate.chi * lrCertificateE raw)
  let vS := lrCertificateVDeriv raw eS xS
  let vK := lrCertificateVDeriv raw eK xK
  let vH := lrCertificateVDeriv raw 0 xH

  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains coordinate.s from
      ⟨hcoordinate.1, hcoordinate.2.1⟩)
  have hsRaw : (sAD box).Contains raw.s 1 0 0 := by
    simpa [raw, lrDeterminantKChartDecode] using hs
  have hratio := IntervalAD.contains_variableK
    (show box.kInterval.Contains coordinate.k from
      ⟨hcoordinate.2.2.1, hcoordinate.2.2.2.1⟩)
  have hh := IntervalAD.contains_variableChi
    (show box.chiInterval.Contains coordinate.chi from
      ⟨hcoordinate.2.2.2.2.1, hcoordinate.2.2.2.2.2⟩)
  have hkPositive : (0 : ℚ) < (physicalKAD box).value.lower := by
    simpa [physicalKAD, mulNonnegativeAD] using
      mul_pos hbase.sPositive hbase.ratioPositive
  have hkRaw := mulNonnegativeAD_sound hbase.sPositive.le
    hbase.ratioPositive.le hs hratio
  have hchiRaw := mulNonnegativeAD_sound hbase.hNonnegative
    hbase.hNonnegative hh hh
  have heRaw := LRUpperKHistoricalACAD.eAD_sound hvalid hcoordinate
  have he : (eAD box).Contains (lrCertificateE raw) eS eK 0 := by
    simpa [raw, eS, eK] using heRaw
  have hchi : (physicalChiAD box).Contains raw.chi 0 0
      (2 * coordinate.chi) := by
    convert hchiRaw using 1 <;>
      simp [physicalChiAD, hAD, raw, lrDeterminantKChartDecode,
        pow_two] <;> ring
  have hxRaw := IntervalAD.contains_sub (IntervalAD.contains_const 1)
    (IntervalAD.contains_mul hchi he)
  have hx : (xAD box).Contains (lrCertificateX raw) xS xK xH := by
    convert hxRaw using 1 <;>
      simp [xAD, xS, xK, xH, lrCertificateX] <;> ring
  have hradRaw := IntervalAD.contains_divPositive hbase.xPositive
    (IntervalAD.contains_sub (IntervalAD.contains_const 1) he) hx
  have hrad : (vRadicandAD box).Contains
      (lrCertificateVRadicand raw)
      (lrCertificateVRadicandDeriv raw eS xS)
      (lrCertificateVRadicandDeriv raw eK xK)
      (lrCertificateVRadicandDeriv raw 0 xH) := by
    unfold vRadicandAD lrCertificateVRadicand
      lrCertificateVRadicandDeriv
    convert hradRaw using 1 <;> norm_num
  have hvRaw := IntervalAD.contains_sqrt hbase.vSqrtCheck hrad
  have hv : (vAD box payload.base).Contains
      (lrCertificateV raw) vS vK vH := by
    simpa [vAD, lrCertificateV, lrCertificateVDeriv, vS, vK, vH] using
      hvRaw

  have hsPoint : 0 < coordinate.s := by
    have hlo : (0 : ℝ) < ((sAD box).value.lower : ℝ) := by
      exact_mod_cast hbase.sPositive
    exact hlo.trans_le hs.1.1
  have hKPoint : 0 < coordinate.k := by
    have hlo : (0 : ℝ) < ((ratioAD box).value.lower : ℝ) := by
      exact_mod_cast hbase.ratioPositive
    exact hlo.trans_le hratio.1.1
  have hePoint : 0 < lrCertificateE raw := by
    have hlo : (0 : ℝ) < ((eAD box).value.lower : ℝ) := by
      exact_mod_cast hbase.ePositive
    exact hlo.trans_le he.1.1
  have hvPoint : 0 < lrCertificateV raw := by
    have hlo : (0 : ℝ) < ((vAD box payload.base).value.lower : ℝ) := by
      exact_mod_cast hbase.vPositive
    exact hlo.trans_le hv.1.1

  have hg0 := payload.base.g0.sound terms hbase.g0Check hv
  have hw := payload.base.omegaZero.sound terms
    hbase.omegaZeroCheck hsRaw
  have hkappa := kappaAD_sound hbase hv

  have honePlusV := IntervalAD.contains_add
    (IntervalAD.contains_const 1) hv
  have honePlusVPositive : (0 : ℚ) <
      (onePlusVAD box payload.base).value.lower := by
    change (0 : ℚ) < 1 + (vAD box payload.base).value.lower
    exact add_pos (by norm_num) hbase.vPositive
  have hdeltaRaw := IntervalAD.contains_divPositive honePlusVPositive
    (IntervalAD.contains_sub (IntervalAD.contains_const 1)
      (IntervalAD.contains_mul hv hx)) honePlusV
  let deltaH := deltaDeriv raw xH vH
  have hdelta : (deltaAD box payload.base).Contains
      (lrDeterminantDelta raw) (deltaDeriv raw xS vS)
      (deltaDeriv raw xK vK) deltaH := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [deltaAD, lrDeterminantDelta] using hdeltaRaw.1
    · simpa [deltaAD, deltaDeriv] using hdeltaRaw.2.1
    · simpa [deltaAD, deltaDeriv] using hdeltaRaw.2.2.1
    · simpa [deltaAD, deltaDeriv, deltaH] using hdeltaRaw.2.2.2

  have hkNamed : (physicalKAD box).Contains raw.k coordinate.k
      coordinate.s 0 := by
    convert hkRaw using 1 <;>
      simp [physicalKAD, sAD, ratioAD, raw,
        lrDeterminantKChartDecode] <;> ring
  have hyNumerator := IntervalAD.contains_sub
    (IntervalAD.contains_add (IntervalAD.contains_const 1) hkNamed) he
  have hbeRaw := IntervalAD.contains_mul hsRaw hyNumerator
  have hBValue :
      lrCertificateB raw.s (lrCertificateE raw) =
        raw.s * (1 + raw.k - lrCertificateE raw) := by
    unfold lrCertificateB lrCertificateE
    ring
  have hBDerivS :
      lrCertificateBDeriv raw.s (lrCertificateE raw) 1 eS =
        (1 + raw.k - lrCertificateE raw) +
          raw.s * (coordinate.k - eS) := by
    dsimp [raw, eS, lrDeterminantKChartDecode,
      lrCertificateBDeriv, lrCertificateE]
    ring
  have hBDerivK :
      lrCertificateBDeriv raw.s (lrCertificateE raw) 0 eK =
        raw.s * (coordinate.s - eK) := by
    dsimp [raw, eK, lrDeterminantKChartDecode,
      lrCertificateBDeriv, lrCertificateE]
    ring
  have hbe : (beAD box).Contains
      (lrCertificateB raw.s (lrCertificateE raw))
      (lrCertificateBDeriv raw.s (lrCertificateE raw) 1 eS)
      (lrCertificateBDeriv raw.s (lrCertificateE raw) 0 eK) 0 := by
    rw [hBValue, hBDerivS, hBDerivK]
    simpa [beAD, yNumeratorAD] using hbeRaw
  have hlogOnePlusCheck : payload.base.logOnePlusV.check
      (onePlusVAD box payload.base).value = true := by
    simpa [onePlusVAD, onePlusVI] using hbase.logOnePlusVCheck
  have hlogOnePlus := IntervalAD.contains_log terms
    hlogOnePlusCheck honePlusV
  have hlogBE := IntervalAD.contains_log terms hbase.logBECheck hbe
  have hbRaw := IntervalAD.contains_sub hlogOnePlus
    (IntervalAD.contains_mul (IntervalAD.contains_const (1 / 2)) hlogBE)
  let bH := vH / (1 + lrCertificateV raw)
  have hb : (bFlowAD terms box payload.base).Contains
      (lrCertificateBFlow raw)
      (lrCertificateBFlowDeriv raw 1 eS vS)
      (lrCertificateBFlowDeriv raw 0 eK vK) bH := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [bFlowAD, onePlusVAD, lrCertificateBFlow,
        lrCertificateBFlowValue] using hbRaw.1
    · simpa [bFlowAD, onePlusVAD, lrCertificateBFlowDeriv,
        lrCertificateBFlowValueDeriv] using hbRaw.2.1
    · simpa [bFlowAD, onePlusVAD, lrCertificateBFlowDeriv,
        lrCertificateBFlowValueDeriv] using hbRaw.2.2.1
    · simpa [bFlowAD, onePlusVAD, bH] using hbRaw.2.2.2

  have hYRaw := IntervalAD.contains_divPositive hkPositive
    hyNumerator hkNamed
  have hYValue :
      lrDeterminantY raw =
        (1 + raw.k - lrCertificateE raw) / raw.k := by
    dsimp [raw, lrDeterminantKChartDecode, lrDeterminantY,
      lrCertificateB, lrCertificateE]
    field_simp [hsPoint.ne', hKPoint.ne']
    ring
  have hYDerivS :
      LRUpperKReplayCertificate.yDeriv raw 1 eS =
        ((coordinate.k - eS) * raw.k -
          (1 + raw.k - lrCertificateE raw) * coordinate.k) /
            raw.k ^ 2 := by
    dsimp [raw, eS, lrDeterminantKChartDecode,
      LRUpperKReplayCertificate.yDeriv,
      lrCertificateBDeriv, lrCertificateB, lrCertificateE]
    field_simp [hsPoint.ne', hKPoint.ne']
    ring
  have hYDerivK :
      LRUpperKReplayCertificate.yDeriv raw 0 eK =
        ((coordinate.s - eK) * raw.k -
          (1 + raw.k - lrCertificateE raw) * coordinate.s) /
            raw.k ^ 2 := by
    dsimp [raw, eK, lrDeterminantKChartDecode,
      LRUpperKReplayCertificate.yDeriv,
      lrCertificateBDeriv, lrCertificateB, lrCertificateE]
    field_simp [hsPoint.ne', hKPoint.ne']
    ring
  have hY : (yAD box).Contains (lrDeterminantY raw)
      (LRUpperKReplayCertificate.yDeriv raw 1 eS)
      (LRUpperKReplayCertificate.yDeriv raw 0 eK) 0 := by
    rw [hYValue, hYDerivS, hYDerivK]
    simpa [yAD, yNumeratorAD] using hYRaw
  have hmeanRaw := IntervalAD.contains_mul
    (IntervalAD.contains_const (1 / 2))
    (IntervalAD.contains_add (IntervalAD.contains_const 1) hY)
  have hmean : (meanYAD box).Contains
      ((1 + lrDeterminantY raw) / 2)
      (LRUpperKReplayCertificate.yDeriv raw 1 eS / 2)
      (LRUpperKReplayCertificate.yDeriv raw 0 eK / 2) 0 := by
    convert hmeanRaw using 1 <;> simp [meanYAD] <;> ring
  have hlogMeanCheck : payload.base.logMeanY.check
      (meanYAD box).value = true := by
    simpa [meanYAD, meanYI, yAD, yI] using hbase.logMeanYCheck
  have hlogMean := IntervalAD.contains_log terms
    hlogMeanCheck hmean
  have hthreeRaw := IntervalAD.contains_add
    (IntervalAD.contains_mul (IntervalAD.contains_const 3) hY)
    (IntervalAD.contains_const 1)
  have hthree : (threeYPlusOneAD box).Contains
      (3 * lrDeterminantY raw + 1)
      (3 * LRUpperKReplayCertificate.yDeriv raw 1 eS)
      (3 * LRUpperKReplayCertificate.yDeriv raw 0 eK) 0 := by
    convert hthreeRaw using 1 <;> simp [threeYPlusOneAD] <;> ring
  have hthreePositive : (0 : ℚ) <
      (threeYPlusOneAD box).value.lower := by
    simpa [threeYPlusOneAD, threeYPlusOneI, yAD, yI] using
      hbase.threeYPlusOnePositive
  have hfrac := IntervalAD.contains_divPositive hthreePositive
    (IntervalAD.contains_sub hY (IntervalAD.contains_const 1)) hthree
  have hd1Raw := IntervalAD.contains_add
    (IntervalAD.contains_mul (IntervalAD.contains_const (1 / 2)) hlogMean)
    hfrac
  have hlogMeanParts :
      (0 : ℚ) < (meanYI box).lower ∧
      payload.base.logMeanY.lower.check (meanYI box).lower = true ∧
      payload.base.logMeanY.upper.check (meanYI box).upper = true := by
    simpa [RationalEnclosure.LogIntervalCertificate.check] using
      hbase.logMeanYCheck
  have hmeanPointPos : 0 < (1 + lrDeterminantY raw) / 2 := by
    have hlo : (0 : ℝ) < ((meanYAD box).value.lower : ℝ) := by
      exact_mod_cast (show (0 : ℚ) < (meanYAD box).value.lower by
        simpa [meanYAD, meanYI, yAD, yI] using hlogMeanParts.1)
    exact hlo.trans_le hmean.1.1
  have hthreePointPos : 0 < 3 * lrDeterminantY raw + 1 := by
    have hlo : (0 : ℝ) <
        ((threeYPlusOneAD box).value.lower : ℝ) := by
      exact_mod_cast (show (0 : ℚ) <
          (threeYPlusOneAD box).value.lower by
        simpa [threeYPlusOneAD, threeYPlusOneI, yAD, yI] using
          hbase.threeYPlusOnePositive)
    exact hlo.trans_le hthree.1.1
  have hd1 : (d1AD terms box payload.base).Contains
      (lrDeterminantD1 raw)
      (LRUpperKReplayCertificate.d1Deriv raw 1 eS)
      (LRUpperKReplayCertificate.d1Deriv raw 0 eK) 0 := by
    unfold d1AD LRUpperKReplayCertificate.d1Deriv lrDeterminantD1
    dsimp only
    convert hd1Raw using 1 <;>
      field_simp [hmeanPointPos.ne', hthreePointPos.ne'] <;> ring

  refine
    { eLowerPositive := hbase.ePositive
      vLowerPositive := hbase.vPositive
      ePointPositive := ?_
      vPointPositive := ?_
      e := ?_
      v := ?_
      bFlow := ?_
      d1 := ?_
      g0 := ?_
      kappa := ?_
      delta := ?_
      w := ?_ }
  · simpa [rawAt, raw] using hePoint
  · simpa [rawAt, raw] using hvPoint
  · simpa [Encloses, eJet, rawAt, eDerivS, eDerivK, raw, eS, eK] using he
  · simpa [Encloses, vJet, rawAt, vDerivS, vDerivK, vDerivH,
      eDerivS, eDerivK, xDerivS, xDerivK, xDerivH,
      raw, eS, eK, xS, xK, xH, vS, vK, vH] using hv
  · simpa [Encloses, bFlowJet, rawAt, bFlowDerivS, bFlowDerivK,
      bFlowDerivH, eDerivS, eDerivK, vDerivS, vDerivK, vDerivH,
      xDerivS, xDerivK, xDerivH,
      raw, eS, eK, xS, xK, xH, vS, vK, vH, bH] using hb
  · simpa [Encloses, d1Jet, rawAt, d1DerivS, d1DerivK,
      eDerivS, eDerivK, raw, eS, eK] using hd1
  · simpa [Encloses, g0Jet, rawAt, vDerivS, vDerivK, vDerivH,
      eDerivS, eDerivK, xDerivS, xDerivK, xDerivH,
      raw, eS, eK, xS, xK, xH, vS, vK, vH] using hg0
  · simpa [Encloses, kappaJet, rawAt, vDerivS, vDerivK, vDerivH,
      eDerivS, eDerivK, xDerivS, xDerivK, xDerivH,
      raw, eS, eK, xS, xK, xH, vS, vK, vH] using hkappa
  · simpa [Encloses, deltaJet, rawAt, deltaDerivS, deltaDerivK,
      deltaDerivH, vDerivS, vDerivK, vDerivH, eDerivS, eDerivK,
      xDerivS, xDerivK, xDerivH,
      raw, eS, eK, xS, xK, xH, vS, vK, vH, deltaH] using hdelta
  · simpa [Encloses, wJet, rawAt, lrCertificateW, raw] using hw

end LRUpperKHistoricalCommonComponents
end CourtadeKumar
