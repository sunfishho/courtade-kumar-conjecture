import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalACAD
import InformationTheory.CourtadeKumar.LRDeterminantUpperKHistoricalQPartialSoundness
import InformationTheory.CourtadeKumar.LRDeterminantUpperKReplayEvaluator

/-!
# Domain adapters for the historical upper-`K` evaluator

The sharp historical evaluator deliberately keeps analytic domain facts out
of its executable payload.  This module recovers those facts from the two
Boolean checks which are already present at every accepted leaf:

* `openChartBoxCheck box`, which controls the rational `(s,K,h)` box; and
* `LRUpperKHistoricalACAD.check terms box payload`, which checks all
  scalar enclosures used by the sharp evaluator.

The resulting records are shaped for direct use by the monotone-corner and
fixed/moving soundness modules.  In particular, they expose

* the two rational `s` endpoints and the queried `s` in `(0,1)`;
* the `e` and `y0` interval endpoints in `[0,1)`;
* the nonnegative lower endpoints of `s`, `e`, `y0`, and all three
  `1-s`, `1-e`, and `1-y0` intervals;
* value containments for `B(s,y0)` and `B(s,e)`; and
* the checked `Q'` facts at `s`, `B(s,y0)`, `e`, and `B(s,e)`.

No additional numerical condition is introduced here.  The optional final
record uses `0 < h < 1` only to strengthen `y0` from the closed domain
`[0,1)` to the open domain `(0,1)` and to recover the decoded raw interior.
-/

open Set

namespace CourtadeKumar
namespace LRUpperKHistoricalDomainAdapters

open LRUpperKReplayCertificate
open LRUpperKHistoricalACAD

/-! ## Small extraction lemmas -/

private theorem openChartBoxCheck_parts {box : CertificateBox}
    (hcheck : openChartBoxCheck box = true) :
    (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
      (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
        box.sHi * box.sHi * box.kHi < 1 ∧
      (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
        box.chiHi ≤ 1 := by
  simpa [openChartBoxCheck] using hcheck

private theorem qInterval_domain_of_check
    {input : RationalEnclosure} {certificate : LRQIntervalCertificate}
    (hcheck : certificate.check input = true) :
    (0 : ℚ) < input.lower ∧ input.lower ≤ input.upper ∧
      input.upper < 1 := by
  have hraw :
      (decide ((0 : ℚ) < input.lower ∧ input.lower ≤ input.upper ∧
          input.upper < 1) = true ∧
        certificate.lower.check input.lower = true) ∧
      certificate.upper.check input.upper = true := by
    simpa [LRQIntervalCertificate.check] using hcheck
  simpa using hraw.1.1

private theorem regularizedScale_domain_of_check
    (terms : ℕ) {input : RationalEnclosure}
    {certificate : LRQRegularizedScaleCertificate}
    (hcheck : certificate.check terms input = true) :
    (0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper ∧
      input.upper < 1 := by
  have hraw :
      decide ((0 : ℚ) ≤ input.lower ∧ input.lower ≤ input.upper ∧
          input.upper < 1) = true ∧
        (if input.upper = 0 then true
         else
          LRQRegularizedScaleCertificate.endpointCheck terms input.upper
              certificate.upper certificate.sqrtUpper &&
            if input.lower = 0 then true
            else LRQRegularizedScaleCertificate.endpointCheck terms input.lower
              certificate.lower certificate.sqrtLower) = true := by
    simpa [LRQRegularizedScaleCertificate.check] using hcheck
  simpa using hraw.1

private theorem oneMinus_lower_nonnegative
    {input : RationalEnclosure} (hupper : input.upper ≤ 1) :
    (0 : ℚ) ≤
      (RationalEnclosure.sub (RationalEnclosure.point 1) input).lower := by
  simp [RationalEnclosure.sub, RationalEnclosure.add,
    RationalEnclosure.neg, RationalEnclosure.point]
  exact hupper

private theorem rat_mem_Ioo_zero_one {q : ℚ}
    (hq0 : (0 : ℚ) < q) (hq1 : q < 1) :
    (q : ℝ) ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · exact_mod_cast hq0
  · exact_mod_cast hq1

private theorem rat_mem_Ico_zero_one {q : ℚ}
    (hq0 : (0 : ℚ) ≤ q) (hq1 : q < 1) :
    (q : ℝ) ∈ Ico (0 : ℝ) 1 := by
  constructor
  · exact_mod_cast hq0
  · exact_mod_cast hq1

/-! ## Facts obtained solely from the checked payload -/

/-- Boolean facts used by the sharp `Q''`, fixed/moving, and `Q(e)` nodes.

The `qPrimeAtEBCheck` field is the value-certificate component expected by
`qSecondAtEBI_sound`; `qPrimeAtEBADCheck` retains the stronger AD check from
which it was extracted.  Likewise `qPrimeAtECheck` is the slope certificate
needed by the scalar `qPrimeEI` node. -/
structure CheckFacts (terms : ℕ) (box : CertificateBox)
    (payload : LRUpperKHistoricalACAD.Payload) : Prop where
  valid : LRUpperKHistoricalACAD.Valid terms box payload
  qPrimeAtSCheck :
    payload.base.omegaZero.qPrimeAtS.value.check
      (sAD box).value = true
  qPrimeAtY0BCheck :
    payload.base.omegaY0.qPrimeAtB.check
      (y0BAd box).value = true
  qPrimeAtEBADCheck :
    payload.base.omegaE.qPrimeAtB.check
      (eBAd box).value = true
  qPrimeAtEBCheck :
    payload.base.omegaE.qPrimeAtB.value.check
      (eBAd box).value = true
  qAtECheck :
    payload.base.omegaE.qAtY.check (eAD box).value = true
  qPrimeAtECheck :
    payload.base.omegaE.qAtY.slope.check (eAD box).value = true

theorem checkFacts_of_checked {terms : ℕ} {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload}
    (hcheck : LRUpperKHistoricalACAD.check terms box payload = true) :
    CheckFacts terms box payload := by
  have hvalid := LRUpperKHistoricalACAD.check_sound hcheck
  have homegaE :
      (payload.base.omegaE.qAtB.check (eBAd box).value = true ∧
        payload.base.omegaE.qAtY.check (eAD box).value = true) ∧
      payload.base.omegaE.qPrimeAtB.check (eBAd box).value = true := by
    simpa [LROmegaADCertificate.check, eBAd] using
      hvalid.base.omegaECheck
  have hqPrimeEBParts :
      payload.base.omegaE.qPrimeAtB.value.check
          (eBAd box).value = true ∧
        lrQSecondCoarseCheck (eBAd box).value = true := by
    simpa [LRQPrimeADCertificate.check] using homegaE.2
  have hqEParts :
      payload.base.omegaE.qAtY.value.check (eAD box).value = true ∧
        payload.base.omegaE.qAtY.slope.check
          (eAD box).value = true := by
    simpa [LRQADCertificate.check] using homegaE.1.2
  exact
    { valid := hvalid
      qPrimeAtSCheck := hvalid.auxiliary.qPrimeAtSCheck
      qPrimeAtY0BCheck := hvalid.auxiliary.qPrimeAtBCheck
      qPrimeAtEBADCheck := homegaE.2
      qPrimeAtEBCheck := hqPrimeEBParts.1
      qAtECheck := homegaE.1.2
      qPrimeAtECheck := hqEParts.2 }

/-! ## Rational endpoint facts -/

/-- Exact endpoint-domain and nonnegative-lower facts needed by the corner
and fixed/moving soundness interfaces. -/
structure EndpointFacts (box : CertificateBox) : Prop where
  sLoPhysical : (box.sLo : ℝ) ∈ Ioo (0 : ℝ) 1
  sHiPhysical : (box.sHi : ℝ) ∈ Ioo (0 : ℝ) 1
  sLowerNonnegative : (0 : ℚ) ≤ (sAD box).value.lower
  ratioLowerPositive : (0 : ℚ) < (ratioAD box).value.lower
  hLowerNonnegative : (0 : ℚ) ≤ (hAD box).value.lower
  eLowerPositive : (0 : ℚ) < (eAD box).value.lower
  eOrdered : (eAD box).value.lower ≤ (eAD box).value.upper
  eUpperLtOne : (eAD box).value.upper < 1
  eLowerPhysical : ((eAD box).value.lower : ℝ) ∈ Ico (0 : ℝ) 1
  eUpperPhysical : ((eAD box).value.upper : ℝ) ∈ Ico (0 : ℝ) 1
  y0LowerNonnegative : (0 : ℚ) ≤ (y0AD box).value.lower
  y0Ordered : (y0AD box).value.lower ≤ (y0AD box).value.upper
  y0UpperLtOne : (y0AD box).value.upper < 1
  y0LowerPhysical : ((y0AD box).value.lower : ℝ) ∈ Ico (0 : ℝ) 1
  y0UpperPhysical : ((y0AD box).value.upper : ℝ) ∈ Ico (0 : ℝ) 1
  oneMinusSLowerNonnegative :
    (0 : ℚ) ≤ (oneMinusSI box).lower
  oneMinusELowerNonnegative :
    (0 : ℚ) ≤ (oneMinusEI box).lower
  oneMinusY0LowerNonnegative :
    (0 : ℚ) ≤ (oneMinusYI box).lower

theorem endpointFacts_of_checked {terms : ℕ} {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload}
    (hdomain : openChartBoxCheck box = true)
    (hcheck : LRUpperKHistoricalACAD.check terms box payload = true) :
    EndpointFacts box := by
  rcases openChartBoxCheck_parts hdomain with
    ⟨hsLo, hsOrder, hsHi, hKLo, _hKOrder, _heHi,
      _hhLo, _hhOrder, _hhHi⟩
  have hvalid := LRUpperKHistoricalACAD.check_sound hcheck
  have heDomain := qInterval_domain_of_check hvalid.base.qECheck
  have hyDomain := regularizedScale_domain_of_check terms
    hvalid.auxiliary.qY0ScaleCheck
  have hsLoLtOne : box.sLo < 1 :=
    lt_of_le_of_lt hsOrder hsHi
  have hsHiPositive : (0 : ℚ) < box.sHi :=
    lt_of_lt_of_le hsLo hsOrder
  have heLowerLtOne : (eAD box).value.lower < 1 :=
    lt_of_le_of_lt heDomain.2.1 heDomain.2.2
  have hyLowerLtOne : (y0AD box).value.lower < 1 :=
    lt_of_le_of_lt hyDomain.2.1 hyDomain.2.2
  have hsUpperLeOne : (sAD box).value.upper ≤ 1 := by
    simpa [sAD, IntervalAD.variableS, CertificateBox.sInterval] using
      hsHi.le
  have heUpperLeOne : (eAD box).value.upper ≤ 1 := heDomain.2.2.le
  have hyUpperLeOne : (y0AD box).value.upper ≤ 1 := hyDomain.2.2.le
  exact
    { sLoPhysical := rat_mem_Ioo_zero_one hsLo hsLoLtOne
      sHiPhysical := rat_mem_Ioo_zero_one hsHiPositive hsHi
      sLowerNonnegative := by
        exact hvalid.base.sPositive.le
      ratioLowerPositive := by
        exact hvalid.base.ratioPositive
      hLowerNonnegative := by
        exact hvalid.base.hNonnegative
      eLowerPositive := heDomain.1
      eOrdered := heDomain.2.1
      eUpperLtOne := heDomain.2.2
      eLowerPhysical :=
        rat_mem_Ico_zero_one heDomain.1.le heLowerLtOne
      eUpperPhysical :=
        rat_mem_Ico_zero_one
          (heDomain.1.le.trans heDomain.2.1) heDomain.2.2
      y0LowerNonnegative := hyDomain.1
      y0Ordered := hyDomain.2.1
      y0UpperLtOne := hyDomain.2.2
      y0LowerPhysical :=
        rat_mem_Ico_zero_one hyDomain.1 hyLowerLtOne
      y0UpperPhysical :=
        rat_mem_Ico_zero_one
          (hyDomain.1.trans hyDomain.2.1) hyDomain.2.2
      oneMinusSLowerNonnegative := by
        simpa [oneMinusSI] using
          oneMinus_lower_nonnegative hsUpperLeOne
      oneMinusELowerNonnegative := by
        simpa [oneMinusEI] using
          oneMinus_lower_nonnegative heUpperLeOne
      oneMinusY0LowerNonnegative := by
        simpa [oneMinusYI] using
          oneMinus_lower_nonnegative hyUpperLeOne }

/-! ## Pointwise value and domain facts -/

/-- Pointwise containments and physical-domain facts for one chart point.
The two `B` fields are exactly the scalar containments consumed by the sharp
`Q''` and moving-coefficient soundness lemmas. -/
structure PointFacts (box : CertificateBox)
    (coordinate : CertificatePoint) : Prop where
  sValue : (sAD box).value.Contains coordinate.s
  sRange : (box.sLo : ℝ) ≤ coordinate.s ∧
    coordinate.s ≤ (box.sHi : ℝ)
  eValue : (eAD box).value.Contains
    (lrCertificateE (lrDeterminantKChartDecode coordinate))
  y0Value : (y0AD box).value.Contains
    (lrCertificateY0 (lrDeterminantKChartDecode coordinate))
  y0BValue : (y0BAd box).value.Contains
    (lrCertificateB
      (lrDeterminantKChartDecode coordinate).s
      (lrCertificateY0 (lrDeterminantKChartDecode coordinate)))
  eBValue : (eBAd box).value.Contains
    (lrCertificateB
      (lrDeterminantKChartDecode coordinate).s
      (lrCertificateE (lrDeterminantKChartDecode coordinate)))
  sPhysical : coordinate.s ∈ Ioo (0 : ℝ) 1
  ePhysical :
    lrCertificateE (lrDeterminantKChartDecode coordinate) ∈
      Ico (0 : ℝ) 1
  y0Physical :
    lrCertificateY0 (lrDeterminantKChartDecode coordinate) ∈
      Ico (0 : ℝ) 1

theorem pointFacts_of_checked {terms : ℕ} {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload}
    {coordinate : CertificatePoint}
    (hdomain : openChartBoxCheck box = true)
    (hcheck : LRUpperKHistoricalACAD.check terms box payload = true)
    (hcoordinate : box.Contains coordinate) :
    PointFacts box coordinate := by
  have hendpoints := endpointFacts_of_checked hdomain hcheck
  have hvalid := LRUpperKHistoricalACAD.check_sound hcheck
  have hsFull := IntervalAD.contains_variableS
    (show box.sInterval.Contains coordinate.s from
      ⟨hcoordinate.1, hcoordinate.2.1⟩)
  have heFull := LRUpperKHistoricalACAD.eAD_sound
    hvalid hcoordinate
  have hyFull := LRUpperKReplayCertificate.y0AD_sound
    hvalid.base hcoordinate
  dsimp only at heFull hyFull
  have hyBFull := lrCertificateBAD_sound hsFull hyFull
  have heBFull := lrCertificateBAD_sound hsFull heFull
  have hsValue : (sAD box).value.Contains coordinate.s := hsFull.1
  have heValue : (eAD box).value.Contains
      (lrCertificateE (lrDeterminantKChartDecode coordinate)) := heFull.1
  have hyValue : (y0AD box).value.Contains
      (lrCertificateY0 (lrDeterminantKChartDecode coordinate)) := hyFull.1
  have hsPhysical : coordinate.s ∈ Ioo (0 : ℝ) 1 :=
    ⟨hendpoints.sLoPhysical.1.trans_le hcoordinate.1,
      hcoordinate.2.1.trans_lt hendpoints.sHiPhysical.2⟩
  have hePhysical :
      lrCertificateE (lrDeterminantKChartDecode coordinate) ∈
        Ico (0 : ℝ) 1 :=
    ⟨hendpoints.eLowerPhysical.1.trans heValue.1,
      heValue.2.trans_lt hendpoints.eUpperPhysical.2⟩
  have hyPhysical :
      lrCertificateY0 (lrDeterminantKChartDecode coordinate) ∈
        Ico (0 : ℝ) 1 :=
    ⟨hendpoints.y0LowerPhysical.1.trans hyValue.1,
      hyValue.2.trans_lt hendpoints.y0UpperPhysical.2⟩
  exact
    { sValue := hsValue
      sRange := ⟨hcoordinate.1, hcoordinate.2.1⟩
      eValue := heValue
      y0Value := hyValue
      y0BValue := by
        simpa [y0BAd, lrDeterminantKChartDecode] using hyBFull.1
      eBValue := by
        simpa [eBAd, lrDeterminantKChartDecode] using heBFull.1
      sPhysical := hsPhysical
      ePhysical := hePhysical
      y0Physical := hyPhysical }

/-! ## One bundled adapter -/

/-- All closed-chart facts needed to invoke the existing corner and
fixed/moving soundness theorems at a queried coordinate. -/
structure Facts (terms : ℕ) (box : CertificateBox)
    (payload : LRUpperKHistoricalACAD.Payload)
    (coordinate : CertificatePoint) : Prop where
  checks : CheckFacts terms box payload
  endpoints : EndpointFacts box
  point : PointFacts box coordinate

theorem facts_of_checked {terms : ℕ} {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload}
    {coordinate : CertificatePoint}
    (hdomain : openChartBoxCheck box = true)
    (hcheck : LRUpperKHistoricalACAD.check terms box payload = true)
    (hcoordinate : box.Contains coordinate) :
    Facts terms box payload coordinate :=
  { checks := checkFacts_of_checked hcheck
    endpoints := endpointFacts_of_checked hdomain hcheck
    point := pointFacts_of_checked hdomain hcheck hcoordinate }

/-! ## Optional open-`h` strengthening -/

/-- When the queried chart coordinate additionally satisfies `0 < h < 1`,
the decoded raw point is interior and `y0=chi*e` is itself in `(0,1)`.
This is the domain form required by ordinary (non-endpoint) derivative
theorems; the closed records above do not assume it. -/
structure OpenHPointFacts (box : CertificateBox)
    (coordinate : CertificatePoint) : Prop extends PointFacts box coordinate where
  hPhysical : coordinate.chi ∈ Ioo (0 : ℝ) 1
  decodedInterior :
    LRHighShapeInterior (lrDeterminantKChartDecode coordinate)
  y0PhysicalOpen :
    lrCertificateY0 (lrDeterminantKChartDecode coordinate) ∈
      Ioo (0 : ℝ) 1

theorem openHPointFacts_of_checked {terms : ℕ} {box : CertificateBox}
    {payload : LRUpperKHistoricalACAD.Payload}
    {coordinate : CertificatePoint}
    (hdomain : openChartBoxCheck box = true)
    (hcheck : LRUpperKHistoricalACAD.check terms box payload = true)
    (hcoordinate : box.Contains coordinate)
    (hh : 0 < coordinate.chi) (hhOne : coordinate.chi < 1) :
    OpenHPointFacts box coordinate := by
  have hpoint := pointFacts_of_checked hdomain hcheck hcoordinate
  have hinterior := openChartBoxCheck_sound hdomain hcoordinate hh hhOne
  have hy0Open :
      lrCertificateY0 (lrDeterminantKChartDecode coordinate) ∈
        Ioo (0 : ℝ) 1 := by
    have hpositive :=
      mul_pos hinterior.2.2.1 hinterior.2.1.1
    have hupper :
        (lrDeterminantKChartDecode coordinate).chi *
            lrCertificateE (lrDeterminantKChartDecode coordinate) < 1 :=
      calc
        (lrDeterminantKChartDecode coordinate).chi *
              lrCertificateE (lrDeterminantKChartDecode coordinate) <
            1 * lrCertificateE (lrDeterminantKChartDecode coordinate) :=
          mul_lt_mul_of_pos_right hinterior.2.2.2 hinterior.2.1.1
        _ < 1 := by simpa using hinterior.2.1.2
    simpa [lrCertificateY0] using And.intro hpositive hupper
  exact
    { toPointFacts := hpoint
      hPhysical := ⟨hh, hhOne⟩
      decodedInterior := hinterior
      y0PhysicalOpen := hy0Open }

end LRUpperKHistoricalDomainAdapters
end CourtadeKumar
