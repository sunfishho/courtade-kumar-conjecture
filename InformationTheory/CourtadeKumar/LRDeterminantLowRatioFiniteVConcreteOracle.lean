import InformationTheory.CourtadeKumar.LRDeterminantUpperKReplayEvaluator
import InformationTheory.CourtadeKumar.LRDeterminantLowRatioFiniteVMeanValue
import InformationTheory.CourtadeKumar.LRHighShapeVZeroFaceSKEvaluator

/-!
# Concrete direct-`V` oracle for the last two finite low-ratio roots

This module implements the executable part of the concrete oracle
requested by `LRLowRatioFiniteVMeanValue.Oracle`.

The value pass is the cancellation-preserving chart expression

`(sharpBase + (D / B) * sharpPsi) / e`,

where the existing sharp upper-`K` payload supplies every node except the
new exact enclosure of `log Y`, and `D = log Y / 2`.  The derivative pass
uses the already verified closed-face direct-`V` evaluator on the decoded
raw hull, transports its two smooth partial derivatives back through
`k = s*K`, and applies the quotient rule for normalization by `B*e`.
This hybrid keeps the narrow historical value expression while avoiding a
second proof of the very large sharp `A/C` derivative assembly.

There is no trusted datum in either payload: all fields are checked Boolean
certificates.  `BasicSoundness` below names the one fact which the current
upper-`K` module previously proved only inside its final theorem:
simultaneous soundness of its `e`, `v`, `Y`, `B`, and `delta` AD nodes.  The
proof is factored here from the existing checked argument, after which
`concreteOracle` is a concrete instance of the abstract mean-value
interface.
-/

namespace CourtadeKumar
namespace LRLowRatioFiniteVConcreteOracle

open LRUpperKReplayCertificate

/-! ## Exact closed-face identities -/

/-- The determinant-bracket identity needs only the displayed nonzero
denominators.  In particular it remains valid on `h = 0` and `h = 1`. -/
theorem normalizedTarget_eq_cancellationTarget_of_ne
    {point : CertificatePoint}
    (hB : lrCertificateBFlow point ≠ 0)
    (he : lrCertificateE point ≠ 0)
    (hvPlus : 1 + lrCertificateV point ≠ 0) :
    LRLowRatioFiniteVMeanValue.normalizedTarget point = LRLowRatioFiniteVMeanValue.cancellationTarget point := by
  have hbrackets :=
    lrCertificateMidpointNumerator_eq_determinant_brackets
      (point := point) hvPlus
  unfold LRLowRatioFiniteVMeanValue.normalizedTarget LRLowRatioFiniteVMeanValue.cancellationTarget lrCertificateVTarget
  rw [hbrackets]
  field_simp [hB, he]
  ring

/-- Closed-face version of `D = log Y / 2`. -/
theorem certificateD_eq_half_log_Y_of_ne
    {point : CertificatePoint}
    (he : lrCertificateE point ≠ 0)
    (hb : lrCertificateB point.s (lrCertificateE point) ≠ 0) :
    lrCertificateD point =
      (1 / 2 : ℝ) * Real.log (lrDeterminantY point) := by
  unfold lrCertificateD lrCertificateA lrCertificateAValue
    lrCertificateBFlow lrCertificateBFlowValue lrDeterminantY
  rw [Real.log_div hb he]
  ring

/-- The compact direct expression is exactly the cancellation target. -/
theorem cancellationTarget_eq_sharp
    (point : CertificatePoint) :
    LRLowRatioFiniteVMeanValue.cancellationTarget point =
      ((lrDeterminantPsi point - lrCertificateGShape point +
            4 * lrDeterminantDelta point * lrCertificateW point) +
          (lrCertificateD point / lrCertificateBFlow point) *
            lrDeterminantPsi point) /
        lrCertificateE point := by
  unfold LRLowRatioFiniteVMeanValue.cancellationTarget
  ring

/-! ## Payload, Boolean checker, and exact interval expression -/

/-- The center-value payload extends the sharp graph only by `log Y`. -/
structure Payload where
  sharp : LRUpperKReplayCertificate.Payload
  logY : RationalEnclosure.LogIntervalCertificate

/-- The whole-box derivative payload combines the sharp denominator graph
with the independently checked closed-face derivative pass. -/
structure DerivativePayload where
  sharp : LRUpperKReplayCertificate.Payload
  derivative : LRHighShapeVZeroFaceCertificate

/-- Decode a chart box to a raw axis-aligned hull.  This hull is used only
for derivative bounds.  The narrow value pass stays in the correlated
chart. -/
def rawHull (box : CertificateBox) : CertificateBox where
  sLo := box.sLo
  sHi := box.sHi
  kLo := (LRUpperKReplayCertificate.physicalKAD box).value.lower
  kHi := (LRUpperKReplayCertificate.physicalKAD box).value.upper
  chiLo := (LRUpperKReplayCertificate.physicalChiAD box).value.lower
  chiHi := (LRUpperKReplayCertificate.physicalChiAD box).value.upper

/-- The monotone raw hull contains the physical point decoded from every
chart point, provided the three chart coordinates have nonnegative lower
endpoints.  This is the common geometric bridge used by both the derivative
oracle and chart-lifted discard certificates. -/
theorem rawHull_contains_decode_of_nonnegative
    {box : CertificateBox} {coordinate : CertificatePoint}
    (hsNonnegative : (0 : ℚ) ≤
      (LRUpperKReplayCertificate.sAD box).value.lower)
    (hKNonnegative : (0 : ℚ) ≤
      (LRUpperKReplayCertificate.ratioAD box).value.lower)
    (hhNonnegative : (0 : ℚ) ≤
      (LRUpperKReplayCertificate.hAD box).value.lower)
    (hcoordinate : box.Contains coordinate) :
    (rawHull box).Contains
      (lrDeterminantKChartDecode coordinate) := by
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains coordinate.s from
      ⟨hcoordinate.1, hcoordinate.2.1⟩)
  have hK := IntervalAD.contains_variableK
    (show box.kInterval.Contains coordinate.k from
      ⟨hcoordinate.2.2.1, hcoordinate.2.2.2.1⟩)
  have hh := IntervalAD.contains_variableChi
    (show box.chiInterval.Contains coordinate.chi from
      ⟨hcoordinate.2.2.2.2.1, hcoordinate.2.2.2.2.2⟩)
  have hk := LRUpperKReplayCertificate.mulNonnegativeAD_sound
    hsNonnegative hKNonnegative hs hK
  have hchi := LRUpperKReplayCertificate.mulNonnegativeAD_sound
    hhNonnegative hhNonnegative hh hh
  exact ⟨hcoordinate.1, hcoordinate.2.1,
    (by simpa [rawHull, LRUpperKReplayCertificate.physicalKAD,
        LRUpperKReplayCertificate.sAD,
        LRUpperKReplayCertificate.ratioAD,
        lrDeterminantKChartDecode] using hk.1.1),
    (by simpa [rawHull, LRUpperKReplayCertificate.physicalKAD,
        LRUpperKReplayCertificate.sAD,
        LRUpperKReplayCertificate.ratioAD,
        lrDeterminantKChartDecode] using hk.1.2),
    (by simpa [rawHull, LRUpperKReplayCertificate.physicalChiAD,
        LRUpperKReplayCertificate.hAD,
        lrDeterminantKChartDecode, pow_two] using hchi.1.1),
    (by simpa [rawHull, LRUpperKReplayCertificate.physicalChiAD,
        LRUpperKReplayCertificate.hAD,
        lrDeterminantKChartDecode, pow_two] using hchi.1.2)⟩

/-- The executable chart-domain check supplies the nonnegativity hypotheses
needed by `rawHull_contains_decode_of_nonnegative`. -/
theorem rawHull_contains_decode_of_chartBoxCheck
    {box : CertificateBox} {coordinate : CertificatePoint}
    (hbox : LRLowRatioFiniteVMeanValue.chartBoxCheck box = true)
    (hcoordinate : box.Contains coordinate) :
    (rawHull box).Contains
      (lrDeterminantKChartDecode coordinate) := by
  have hparts :
      (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
      (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
        box.sHi * box.sHi * box.kHi < 1 ∧
      (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
        box.chiHi ≤ 1 := by
    simpa [LRLowRatioFiniteVMeanValue.chartBoxCheck] using hbox
  rcases hparts with
    ⟨hsPositive, _hsOrder, _hsUpper, hKPositive, _hKOrder,
      _heUpper, hhNonnegative, _hhOrder, _hhUpper⟩
  exact rawHull_contains_decode_of_nonnegative
    (by simpa [LRUpperKReplayCertificate.sAD,
        CertificateBox.sInterval, IntervalAD.variableS] using
      hsPositive.le)
    (by simpa [LRUpperKReplayCertificate.ratioAD,
        CertificateBox.kInterval, IntervalAD.variableK] using
      hKPositive.le)
    (by simpa [LRUpperKReplayCertificate.hAD,
        CertificateBox.chiInterval, IntervalAD.variableChi] using
      hhNonnegative)
    hcoordinate

def DAD (terms : ℕ) (box : CertificateBox) (payload : Payload) : IntervalAD :=
  IntervalAD.mul (IntervalAD.const (1 / 2))
    (IntervalAD.log terms payload.logY (LRUpperKReplayCertificate.yAD box))

/-- Exact cancellation-preserving normalized target requested by the
historical final two roots. -/
def directAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.divPositive
    (IntervalAD.add
      (LRUpperKReplayCertificate.sharpBaseAD terms box payload.sharp)
      (IntervalAD.mul
        (IntervalAD.divPositive (DAD terms box payload)
          (LRUpperKReplayCertificate.bFlowAD terms box payload.sharp))
        (LRUpperKReplayCertificate.sharpPsiAD terms box payload.sharp)))
    (LRUpperKReplayCertificate.eAD box)

/-- Named value projection of `directAD`, useful for keeping the semantic
proof independent of the derivative fields. -/
def directValue (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.div
    (RationalEnclosure.add
      (LRUpperKReplayCertificate.sharpBaseAD terms box payload.sharp).value
      (RationalEnclosure.mul
        (RationalEnclosure.div (DAD terms box payload).value
          (LRUpperKReplayCertificate.bFlowAD terms box payload.sharp).value)
        (LRUpperKReplayCertificate.sharpPsiAD terms box
          payload.sharp).value))
    (LRUpperKReplayCertificate.eAD box).value

theorem directAD_value_eq (terms : ℕ) (box : CertificateBox)
    (payload : Payload) :
    (directAD terms box payload).value = directValue terms box payload := by
  rfl

def payloadCheck (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : Bool :=
  LRUpperKReplayCertificate.payloadCheck box payload.sharp &&
    payload.logY.check (LRUpperKReplayCertificate.yAD box).value &&
    decide ((0 : ℚ) <
      (LRUpperKReplayCertificate.bFlowAD terms box payload.sharp).value.lower)

structure Valid (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : Prop where
  sharpCheck : LRUpperKReplayCertificate.payloadCheck box payload.sharp = true
  sharp : LRUpperKReplayCertificate.Valid box payload.sharp
  logY : payload.logY.check (LRUpperKReplayCertificate.yAD box).value = true
  bFlowPositive : (0 : ℚ) <
    (LRUpperKReplayCertificate.bFlowAD terms box payload.sharp).value.lower

theorem payloadCheck_sound {terms : ℕ} {box : CertificateBox}
    {payload : Payload} (hcheck : payloadCheck terms box payload = true) :
    Valid terms box payload := by
  have hparts :
      (LRUpperKReplayCertificate.payloadCheck box payload.sharp = true ∧
        payload.logY.check (LRUpperKReplayCertificate.yAD box).value = true) ∧
      decide ((0 : ℚ) <
        (LRUpperKReplayCertificate.bFlowAD terms box payload.sharp).value.lower) = true := by
    simpa [payloadCheck] using hcheck
  exact
    { sharpCheck := hparts.1.1
      sharp := LRUpperKReplayCertificate.payloadCheck_sound hparts.1.1
      logY := hparts.1.2
      bFlowPositive := by simpa using hparts.2 }

def derivativePayloadCheck (terms : ℕ) (box : CertificateBox)
    (payload : DerivativePayload) : Bool :=
  LRUpperKReplayCertificate.payloadCheck box payload.sharp &&
    decide ((0 : ℚ) <
      (LRUpperKReplayCertificate.bFlowAD terms box payload.sharp).value.lower) &&
    payload.derivative.skCheck (rawHull box)

structure DerivativeValid (terms : ℕ) (box : CertificateBox)
    (payload : DerivativePayload) : Prop where
  sharpCheck : LRUpperKReplayCertificate.payloadCheck box payload.sharp = true
  sharp : LRUpperKReplayCertificate.Valid box payload.sharp
  bFlowPositive : (0 : ℚ) <
    (LRUpperKReplayCertificate.bFlowAD terms box payload.sharp).value.lower
  derivative : payload.derivative.skCheck (rawHull box) = true

theorem derivativePayloadCheck_sound {terms : ℕ} {box : CertificateBox}
    {payload : DerivativePayload}
    (hcheck : derivativePayloadCheck terms box payload = true) :
    DerivativeValid terms box payload := by
  have hparts :
      (LRUpperKReplayCertificate.payloadCheck box payload.sharp = true ∧
        decide ((0 : ℚ) <
          (LRUpperKReplayCertificate.bFlowAD terms box payload.sharp).value.lower) = true) ∧
      payload.derivative.skCheck (rawHull box) = true := by
    simpa [derivativePayloadCheck] using hcheck
  exact
    { sharpCheck := hparts.1.1
      sharp := LRUpperKReplayCertificate.payloadCheck_sound hparts.1.1
      bFlowPositive := by simpa using hparts.1.2
      derivative := hparts.2 }

/-! ## The minimal missing upper-`K` factorization -/

noncomputable def chartES (coordinate : CertificatePoint) : ℝ :=
  let raw := lrDeterminantKChartDecode coordinate
  raw.k + raw.s * coordinate.k

noncomputable def chartEK (coordinate : CertificatePoint) : ℝ :=
  let raw := lrDeterminantKChartDecode coordinate
  raw.s * coordinate.s

noncomputable def chartXS (coordinate : CertificatePoint) : ℝ :=
  let raw := lrDeterminantKChartDecode coordinate
  0 - raw.chi * chartES coordinate

noncomputable def chartXK (coordinate : CertificatePoint) : ℝ :=
  let raw := lrDeterminantKChartDecode coordinate
  0 - raw.chi * chartEK coordinate

noncomputable def chartXH (coordinate : CertificatePoint) : ℝ :=
  let raw := lrDeterminantKChartDecode coordinate
  0 - 2 * coordinate.chi * lrCertificateE raw

noncomputable def chartVS (coordinate : CertificatePoint) : ℝ :=
  let raw := lrDeterminantKChartDecode coordinate
  lrCertificateVDeriv raw (chartES coordinate) (chartXS coordinate)

noncomputable def chartVK (coordinate : CertificatePoint) : ℝ :=
  let raw := lrDeterminantKChartDecode coordinate
  lrCertificateVDeriv raw (chartEK coordinate) (chartXK coordinate)

noncomputable def chartVH (coordinate : CertificatePoint) : ℝ :=
  let raw := lrDeterminantKChartDecode coordinate
  lrCertificateVDeriv raw 0 (chartXH coordinate)

noncomputable def chartYS (coordinate : CertificatePoint) : ℝ :=
  let raw := lrDeterminantKChartDecode coordinate
  LRUpperKReplayCertificate.yDeriv raw 1 (chartES coordinate)

noncomputable def chartYK (coordinate : CertificatePoint) : ℝ :=
  let raw := lrDeterminantKChartDecode coordinate
  LRUpperKReplayCertificate.yDeriv raw 0 (chartEK coordinate)

noncomputable def chartBS (coordinate : CertificatePoint) : ℝ :=
  let raw := lrDeterminantKChartDecode coordinate
  lrCertificateBFlowDeriv raw 1 (chartES coordinate) (chartVS coordinate)

noncomputable def chartBK (coordinate : CertificatePoint) : ℝ :=
  let raw := lrDeterminantKChartDecode coordinate
  lrCertificateBFlowDeriv raw 0 (chartEK coordinate) (chartVK coordinate)

/-- The five simultaneous enclosures already constructed inside
`LRUpperKReplayCertificate.sharpEvaluateSKAD_sound`.  Naming this record is the least invasive way
to expose precisely what the direct-`V` evaluator needs. -/
structure BasicComponentsAt (terms : ℕ) (box : CertificateBox)
    (sharp : LRUpperKReplayCertificate.Payload) (coordinate : CertificatePoint) where
  vH : ℝ
  bH : ℝ
  deltaH : ℝ
  e : (LRUpperKReplayCertificate.eAD box).Contains
    (lrCertificateE (lrDeterminantKChartDecode coordinate))
    (chartES coordinate) (chartEK coordinate) 0
  v : (LRUpperKReplayCertificate.vAD box sharp).Contains
    (lrCertificateV (lrDeterminantKChartDecode coordinate))
    (chartVS coordinate) (chartVK coordinate) vH
  y : (LRUpperKReplayCertificate.yAD box).Contains
    (lrDeterminantY (lrDeterminantKChartDecode coordinate))
    (chartYS coordinate) (chartYK coordinate) 0
  bFlow : (LRUpperKReplayCertificate.bFlowAD terms box sharp).Contains
    (lrCertificateBFlow (lrDeterminantKChartDecode coordinate))
    (chartBS coordinate) (chartBK coordinate) bH
  delta : (LRUpperKReplayCertificate.deltaAD box sharp).Contains
    (lrDeterminantDelta (lrDeterminantKChartDecode coordinate))
    (LRUpperKReplayCertificate.deltaDeriv (lrDeterminantKChartDecode coordinate)
      (chartXS coordinate) (chartVS coordinate))
    (LRUpperKReplayCertificate.deltaDeriv (lrDeterminantKChartDecode coordinate)
      (chartXK coordinate) (chartVK coordinate)) deltaH
  rawBPositive : 0 < lrCertificateB
    (lrDeterminantKChartDecode coordinate).s
    (lrCertificateE (lrDeterminantKChartDecode coordinate))

/-- Exact outstanding factorization boundary.  Its proof is a prefix of
the already kernel-checked `LRUpperKReplayCertificate.sharpEvaluateSKAD_sound`; no new analytic
lemma or numerical certificate is required. -/
def BasicSoundness (terms : ℕ) : Type :=
  ∀ {box : CertificateBox} {sharp : LRUpperKReplayCertificate.Payload},
    LRUpperKReplayCertificate.payloadCheck box sharp = true →
    ∀ {coordinate : CertificatePoint}, box.Contains coordinate →
      BasicComponentsAt terms box sharp coordinate

/-- Factor the five common nodes out of the existing sharp proof.  This is
source-identical to the corresponding prefix and middle block of
`sharpEvaluateSKAD_sound`; it does not add a new analytic assumption. -/
noncomputable def basicSoundness (terms : ℕ) : BasicSoundness terms := by
  intro box sharp hcheck coordinate hcoordinate
  have hvalid : LRUpperKReplayCertificate.Valid box sharp :=
    LRUpperKReplayCertificate.payloadCheck_sound hcheck
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
  have hkLower : (0 : ℚ) ≤ (physicalKAD box).value.lower := by
    simpa [physicalKAD, mulNonnegativeAD] using
      mul_nonneg hvalid.sPositive.le hvalid.ratioPositive.le
  have hkPositive : (0 : ℚ) < (physicalKAD box).value.lower := by
    simpa [physicalKAD, mulNonnegativeAD] using
      mul_pos hvalid.sPositive hvalid.ratioPositive
  have hkRaw := mulNonnegativeAD_sound hvalid.sPositive.le
    hvalid.ratioPositive.le hs hratio
  have hchiRaw := mulNonnegativeAD_sound hvalid.hNonnegative
    hvalid.hNonnegative hh hh
  have heRaw := mulNonnegativeAD_sound hvalid.sPositive.le hkLower hs hkRaw
  have he : (eAD box).Contains (lrCertificateE raw) eS eK 0 := by
    convert heRaw using 1 <;>
      simp [eAD, physicalKAD, sAD, ratioAD, raw, eS, eK,
        lrCertificateE, lrDeterminantKChartDecode] <;> ring
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
  have hradRaw := IntervalAD.contains_divPositive hvalid.xPositive
    (IntervalAD.contains_sub (IntervalAD.contains_const 1) he) hx
  have hrad : (vRadicandAD box).Contains
      (lrCertificateVRadicand raw)
      (lrCertificateVRadicandDeriv raw eS xS)
      (lrCertificateVRadicandDeriv raw eK xK)
      (lrCertificateVRadicandDeriv raw 0 xH) := by
    unfold vRadicandAD lrCertificateVRadicand
      lrCertificateVRadicandDeriv
    convert hradRaw using 1 <;> norm_num
  have hvRaw := IntervalAD.contains_sqrt hvalid.vSqrtCheck hrad
  have hv : (vAD box sharp).Contains (lrCertificateV raw) vS vK vH := by
    simpa [vAD, lrCertificateV, lrCertificateVDeriv, vS, vK, vH] using
      hvRaw
  have hsPoint : 0 < coordinate.s := by
    have hlo : (0 : ℝ) < ((sAD box).value.lower : ℝ) := by
      exact_mod_cast hvalid.sPositive
    exact hlo.trans_le hs.1.1
  have hKPoint : 0 < coordinate.k := by
    have hlo : (0 : ℝ) < ((ratioAD box).value.lower : ℝ) := by
      exact_mod_cast hvalid.ratioPositive
    exact hlo.trans_le hratio.1.1
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
  have honePlusV := IntervalAD.contains_add
    (IntervalAD.contains_const 1) hv
  have honePlusVPositive : (0 : ℚ) <
      (onePlusVAD box sharp).value.lower := by
    change (0 : ℚ) < 1 + (vAD box sharp).value.lower
    exact add_pos (by norm_num) hvalid.vPositive
  have hdeltaRaw := IntervalAD.contains_divPositive honePlusVPositive
    (IntervalAD.contains_sub (IntervalAD.contains_const 1)
      (IntervalAD.contains_mul hv hx)) honePlusV
  let deltaH := deltaDeriv raw xH vH
  have hdelta : (deltaAD box sharp).Contains
      (lrDeterminantDelta raw) (deltaDeriv raw xS vS)
      (deltaDeriv raw xK vK) deltaH := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [deltaAD, lrDeterminantDelta] using hdeltaRaw.1
    · simpa [deltaAD, deltaDeriv] using hdeltaRaw.2.1
    · simpa [deltaAD, deltaDeriv] using hdeltaRaw.2.2.1
    · simpa [deltaAD, deltaDeriv, deltaH] using hdeltaRaw.2.2.2
  have hlogOnePlusCheck : sharp.logOnePlusV.check
      (onePlusVAD box sharp).value = true := by
    simpa [onePlusVAD, onePlusVI] using hvalid.logOnePlusVCheck
  have hlogOnePlus := IntervalAD.contains_log terms
    hlogOnePlusCheck honePlusV
  have hlogBE := IntervalAD.contains_log terms hvalid.logBECheck hbe
  have hbRaw := IntervalAD.contains_sub hlogOnePlus
    (IntervalAD.contains_mul (IntervalAD.contains_const (1 / 2)) hlogBE)
  let bH := vH / (1 + lrCertificateV raw)
  have hb : (bFlowAD terms box sharp).Contains
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
      yDeriv raw 1 eS =
        ((coordinate.k - eS) * raw.k -
          (1 + raw.k - lrCertificateE raw) * coordinate.k) /
            raw.k ^ 2 := by
    dsimp [raw, eS, lrDeterminantKChartDecode, yDeriv,
      lrCertificateBDeriv, lrCertificateB, lrCertificateE]
    field_simp [hsPoint.ne', hKPoint.ne']
    ring
  have hYDerivK :
      yDeriv raw 0 eK =
        ((coordinate.s - eK) * raw.k -
          (1 + raw.k - lrCertificateE raw) * coordinate.s) /
            raw.k ^ 2 := by
    dsimp [raw, eK, lrDeterminantKChartDecode, yDeriv,
      lrCertificateBDeriv, lrCertificateB, lrCertificateE]
    field_simp [hsPoint.ne', hKPoint.ne']
    ring
  have hY : (yAD box).Contains (lrDeterminantY raw)
      (yDeriv raw 1 eS) (yDeriv raw 0 eK) 0 := by
    rw [hYValue, hYDerivS, hYDerivK]
    simpa [yAD, yNumeratorAD] using hYRaw
  have hlogBEParts : (0 : ℚ) < (beAD box).value.lower := by
    have hparts :
        (0 : ℚ) < (beAD box).value.lower ∧
          sharp.logBE.lower.check (beAD box).value.lower = true ∧
          sharp.logBE.upper.check (beAD box).value.upper = true := by
      simpa [RationalEnclosure.LogIntervalCertificate.check] using
        hvalid.logBECheck
    exact hparts.1
  have hrawBPositive : 0 <
      lrCertificateB raw.s (lrCertificateE raw) := by
    have hlo : (0 : ℝ) < ((beAD box).value.lower : ℝ) := by
      exact_mod_cast hlogBEParts
    exact hlo.trans_le hbe.1.1
  refine
    { vH := vH
      bH := bH
      deltaH := deltaH
      e := ?_
      v := ?_
      y := ?_
      bFlow := ?_
      delta := ?_
      rawBPositive := hrawBPositive }
  · simpa [chartES, chartEK, raw, eS, eK] using he
  · simpa [chartVS, chartVK, chartXS, chartXK, raw, eS, eK, xS, xK, vS, vK] using hv
  · simpa [chartYS, chartYK, chartES, chartEK,
      raw, eS, eK] using hY
  · simpa [chartBS, chartBK, chartES, chartEK, chartVS, chartVK,
      chartXS, chartXK,
      raw, eS, eK, xS, xK, vS, vK] using hb
  · simpa [chartXS, chartXK, chartVS, chartVK, chartES, chartEK,
      raw, eS, eK, xS, xK, vS, vK] using hdelta

/-! ## Sharp direct-value soundness from the factored components -/

theorem directAD_value_sound (terms : ℕ)
    (hbasic : BasicSoundness terms)
    {box : CertificateBox} {payload : Payload}
    (hcheck : payloadCheck terms box payload = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (directAD terms box payload).value.Contains (LRLowRatioFiniteVMeanValue.chartTarget coordinate) := by
  have hvalid := payloadCheck_sound hcheck
  have hcore := hbasic hvalid.sharpCheck hcoordinate
  let raw := lrDeterminantKChartDecode coordinate
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains coordinate.s from
      ⟨hcoordinate.1, hcoordinate.2.1⟩)
  have hsRaw : (LRUpperKReplayCertificate.sAD box).Contains raw.s 1 0 0 := by
    simpa [LRUpperKReplayCertificate.sAD, raw, lrDeterminantKChartDecode] using hs
  have haY0 := LRUpperKReplayCertificate.aY0SKAD_sound terms hvalid.sharp hcoordinate
  have haE := LRUpperKReplayCertificate.aESKAD_sound terms hvalid.sharp hcoordinate
  rcases LRUpperKReplayCertificate.cY0SKAD_sound terms hvalid.sharp hcoordinate with
    ⟨cY0H, hcY0⟩
  have hcE := LRUpperKReplayCertificate.cESKAD_sound terms hvalid.sharp hcoordinate
  have hg0 := payload.sharp.g0.sound terms hvalid.sharp.g0Check hcore.v
  have hw := payload.sharp.omegaZero.sound terms
    hvalid.sharp.omegaZeroCheck hsRaw
  have hkappa := LRUpperKReplayCertificate.kappaAD_sound hvalid.sharp hcore.v
  have haEOver := IntervalAD.contains_divPositive
    hvalid.sharp.vPositive haE hcore.v
  have hcEOver := IntervalAD.contains_divPositive
    hvalid.sharp.vPositive hcE hcore.v
  have hsharpPsiRaw := IntervalAD.contains_add
    (IntervalAD.contains_add hg0 haY0)
    (IntervalAD.contains_add haEOver (IntervalAD.contains_mul hkappa hw))
  have hvPoint : 0 < lrCertificateV raw := by
    have hlo : (0 : ℝ) <
        (((LRUpperKReplayCertificate.vAD box payload.sharp).value.lower : ℚ) : ℝ) := by
      exact_mod_cast hvalid.sharp.vPositive
    exact hlo.trans_le hcore.v.1.1
  have hvPlus : 1 + lrCertificateV raw ≠ 0 := by linarith
  have hsharpPsi : (LRUpperKReplayCertificate.sharpPsiAD terms box payload.sharp).value.Contains
      (lrDeterminantPsi raw) := by
    have hid := LRUpperKReplayCertificate.psi_eq_aPrimitives
      (point := raw) hvPoint.ne' hvPlus
    rw [hid]
    convert hsharpPsiRaw.1 using 1 <;>
      simp [LRUpperKReplayCertificate.sharpPsiAD, lrCertificateW] <;> ring
  have hkapPlusDelta := IntervalAD.contains_add hkappa
    (IntervalAD.contains_mul (IntervalAD.contains_const 4) hcore.delta)
  have hsharpBaseRaw := IntervalAD.contains_add
    (IntervalAD.contains_add hcY0 hcEOver)
    (IntervalAD.contains_mul hkapPlusDelta hw)
  have hsharpBase : (LRUpperKReplayCertificate.sharpBaseAD terms box payload.sharp).value.Contains
      (lrDeterminantPsi raw - lrCertificateGShape raw +
        4 * lrDeterminantDelta raw * lrCertificateW raw) := by
    have hid := LRUpperKReplayCertificate.psi_sub_gShape_eq_cPrimitives
      (point := raw) hvPoint.ne' hvPlus
    rw [hid]
    convert hsharpBaseRaw.1 using 1 <;>
      simp [LRUpperKReplayCertificate.sharpBaseAD, lrCertificateW] <;> ring
  have hlogY := IntervalAD.contains_log terms hvalid.logY hcore.y
  have hDhalf := IntervalAD.contains_mul
    (IntervalAD.contains_const (1 / 2)) hlogY
  have hePoint : lrCertificateE raw ≠ 0 := by
    have hlo : (0 : ℝ) <
        (((LRUpperKReplayCertificate.eAD box).value.lower : ℚ) : ℝ) := by
      exact_mod_cast hvalid.sharp.ePositive
    exact (hlo.trans_le hcore.e.1.1).ne'
  have hD : (DAD terms box payload).value.Contains
      (lrCertificateD raw) := by
    rw [certificateD_eq_half_log_Y_of_ne hePoint hcore.rawBPositive.ne']
    simpa [DAD] using hDhalf.1
  have hBPoint : 0 < lrCertificateBFlow raw := by
    have hlo : (0 : ℝ) <
        (((LRUpperKReplayCertificate.bFlowAD terms box payload.sharp).value.lower : ℚ) : ℝ) := by
      exact_mod_cast hvalid.bFlowPositive
    exact hlo.trans_le hcore.bFlow.1.1
  have hDOverB := RationalEnclosure.contains_div
    hvalid.bFlowPositive hD hcore.bFlow.1
  have hinner := RationalEnclosure.contains_add hsharpBase
    (RationalEnclosure.contains_mul hDOverB hsharpPsi)
  have hresult := RationalEnclosure.contains_div
    hvalid.sharp.ePositive hinner hcore.e.1
  have hcancel : (directAD terms box payload).value.Contains
      (LRLowRatioFiniteVMeanValue.cancellationTarget raw) := by
    rw [cancellationTarget_eq_sharp]
    rw [directAD_value_eq]
    simpa [directValue] using hresult
  have hclosed := normalizedTarget_eq_cancellationTarget_of_ne
    hBPoint.ne' hePoint hvPlus
  rw [LRLowRatioFiniteVMeanValue.chartTarget, hclosed]
  exact hcancel

/-! ## Independent closed-face derivative pass -/

/-- Transport the raw direct-`V` evaluator through `k=s*K`.  The third AD
field is synthetic and deliberately unused. -/
def chartVAD (terms : ℕ) (box : CertificateBox)
    (payload : DerivativePayload) : IntervalAD :=
  let rawResult := payload.derivative.evaluateSKAD terms (rawHull box)
  { value := rawResult.value
    derivS := RationalEnclosure.add rawResult.derivS
      (RationalEnclosure.mul (LRUpperKReplayCertificate.ratioAD box).value rawResult.derivK)
    derivK := RationalEnclosure.mul (LRUpperKReplayCertificate.sAD box).value rawResult.derivK
    derivChi := RationalEnclosure.point 0 }

def normalizedDerivativeAD (terms : ℕ) (box : CertificateBox)
    (payload : DerivativePayload) : IntervalAD :=
  IntervalAD.divPositive (chartVAD terms box payload)
    (LRUpperKReplayCertificate.mulNonnegativeAD
      (LRUpperKReplayCertificate.bFlowAD terms box payload.sharp)
      (LRUpperKReplayCertificate.eAD box))

/-- Linearity of the verified raw direct-`V` derivative in the chart
`s` direction. -/
theorem vTargetCurveDeriv_chartS (coordinate : CertificatePoint) :
    let raw := lrDeterminantKChartDecode coordinate
    lrCertificateVTargetDerivS raw + coordinate.k *
        lrCertificateVTargetDerivK raw =
      lrCertificateVTargetCurveDeriv raw 1 coordinate.k 0 := by
  dsimp only
  simp [lrCertificateVTargetDerivS, lrCertificateVTargetDerivK,
    lrCertificateVTargetCurveDeriv, lrCertificateVTargetDeriv,
    lrCertificateHalfMidpointNumeratorCurveDeriv,
    lrCertificateHalfMidpointNumeratorDeriv,
    lrCertificateHalfMidpointBracketDeriv,
    lrCertificateADeriv, lrCertificateAValueDeriv,
    lrCertificateBFlowDeriv, lrCertificateBFlowValueDeriv,
    lrCertificateDDeriv, lrCertificateMDeriv,
    lrCertificateGShapeDeriv, lrCertificateGShapeValueDeriv,
    lrCertificatePWDeriv, lrCertificatePWValueDeriv,
    lrCertificateOmegaDeriv, lrCertificateBDeriv,
    lrCertificateJDeriv, lrCertificateVDeriv,
    lrCertificateVRadicandDeriv,
    lrCertificateEDerivS, lrCertificateEDerivK,
    lrCertificateXDerivS, lrCertificateXDerivK,
    lrCertificateVDerivS, lrCertificateVDerivK,
    lrCertificateGShapeDerivS, lrCertificateGShapeDerivK,
    lrCertificatePWDerivS, lrCertificatePWDerivK]
  ring

/-- Linearity in the chart `K` direction. -/
theorem vTargetCurveDeriv_chartK (coordinate : CertificatePoint) :
    let raw := lrDeterminantKChartDecode coordinate
    coordinate.s * lrCertificateVTargetDerivK raw =
      lrCertificateVTargetCurveDeriv raw 0 coordinate.s 0 := by
  dsimp only
  simp [lrCertificateVTargetDerivK,
    lrCertificateVTargetCurveDeriv, lrCertificateVTargetDeriv,
    lrCertificateHalfMidpointNumeratorCurveDeriv,
    lrCertificateHalfMidpointNumeratorDeriv,
    lrCertificateHalfMidpointBracketDeriv,
    lrCertificateADeriv, lrCertificateAValueDeriv,
    lrCertificateBFlowDeriv, lrCertificateBFlowValueDeriv,
    lrCertificateDDeriv, lrCertificateMDeriv,
    lrCertificateGShapeDeriv, lrCertificateGShapeValueDeriv,
    lrCertificatePWDeriv, lrCertificatePWValueDeriv,
    lrCertificateOmegaDeriv, lrCertificateBDeriv,
    lrCertificateJDeriv, lrCertificateVDeriv,
    lrCertificateVRadicandDeriv,
    lrCertificateEDerivK, lrCertificateXDerivK,
    lrCertificateVDerivK, lrCertificateGShapeDerivK,
    lrCertificatePWDerivK]
  ring

theorem chartVAD_sound (terms : ℕ)
    (hbasic : BasicSoundness terms)
    {box : CertificateBox} {payload : DerivativePayload}
    (hcheck : derivativePayloadCheck terms box payload = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    let raw := lrDeterminantKChartDecode coordinate
    (chartVAD terms box payload).Contains
      (lrCertificateVTarget raw)
      (lrCertificateVTargetCurveDeriv raw 1 coordinate.k 0)
      (lrCertificateVTargetCurveDeriv raw 0 coordinate.s 0) 0 := by
  dsimp only
  have hvalid := derivativePayloadCheck_sound hcheck
  have _hcore := hbasic hvalid.sharpCheck hcoordinate
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains coordinate.s from
      ⟨hcoordinate.1, hcoordinate.2.1⟩)
  have hK := IntervalAD.contains_variableK
    (show box.kInterval.Contains coordinate.k from
      ⟨hcoordinate.2.2.1, hcoordinate.2.2.2.1⟩)
  have hrawContains := rawHull_contains_decode_of_nonnegative
    hvalid.sharp.sPositive.le hvalid.sharp.ratioPositive.le
    hvalid.sharp.hNonnegative hcoordinate
  have hraw := payload.derivative.evaluateSKAD_sound terms
    hvalid.derivative hrawContains
  have hS := RationalEnclosure.contains_add hraw.2.1
    (RationalEnclosure.contains_mul hK.1 hraw.2.2)
  have hKchart := RationalEnclosure.contains_mul hs.1 hraw.2.2
  refine ⟨hraw.1, ?_, ?_, ?_⟩
  · rw [← vTargetCurveDeriv_chartS coordinate]
    exact hS
  · rw [← vTargetCurveDeriv_chartK coordinate]
    exact hKchart
  · simpa [chartVAD] using
      (RationalEnclosure.contains_point (0 : ℚ))

theorem normalizedDerivativeAD_sound (terms : ℕ)
    (hbasic : BasicSoundness terms)
    {box : CertificateBox} {payload : DerivativePayload}
    (hcheck : derivativePayloadCheck terms box payload = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (normalizedDerivativeAD terms box payload).derivS.Contains
        (LRLowRatioFiniteVMeanValue.chartDerivS coordinate) ∧
      (normalizedDerivativeAD terms box payload).derivK.Contains
        (LRLowRatioFiniteVMeanValue.chartDerivK coordinate) := by
  have hvalid := derivativePayloadCheck_sound hcheck
  have hcore := hbasic hvalid.sharpCheck hcoordinate
  let raw := lrDeterminantKChartDecode coordinate
  have hv := chartVAD_sound terms hbasic hcheck hcoordinate
  have hden := LRUpperKReplayCertificate.mulNonnegativeAD_sound
    hvalid.bFlowPositive.le hvalid.sharp.ePositive.le
    hcore.bFlow hcore.e
  have hdenPositive : (0 : ℚ) <
      (LRUpperKReplayCertificate.mulNonnegativeAD
        (LRUpperKReplayCertificate.bFlowAD terms box payload.sharp)
        (LRUpperKReplayCertificate.eAD box)).value.lower := by
    simpa [LRUpperKReplayCertificate.mulNonnegativeAD] using
      mul_pos hvalid.bFlowPositive hvalid.sharp.ePositive
  have hresult := IntervalAD.contains_divPositive hdenPositive hv hden
  constructor
  · simpa [normalizedDerivativeAD, LRLowRatioFiniteVMeanValue.chartDerivS,
      LRLowRatioFiniteVMeanValue.normalizedTargetCurveDeriv, raw,
      chartES, chartXS, chartVS, chartBS] using
      hresult.2.1
  · simpa [normalizedDerivativeAD, LRLowRatioFiniteVMeanValue.chartDerivK,
      LRLowRatioFiniteVMeanValue.normalizedTargetCurveDeriv, raw,
      chartEK, chartXK, chartVK, chartBK] using
      hresult.2.2.1

/-! ## Concrete oracle constructor and deterministic payload proposal -/

noncomputable def oracle (terms : ℕ) (hbasic : BasicSoundness terms) :
    LRLowRatioFiniteVMeanValue.Oracle where
  Payload := Payload
  DerivativePayload := DerivativePayload
  check := payloadCheck terms
  derivativeCheck := derivativePayloadCheck terms
  value := fun box payload ↦ (directAD terms box payload).value
  derivS := fun box payload ↦
    (normalizedDerivativeAD terms box payload).derivS
  derivK := fun box payload ↦
    (normalizedDerivativeAD terms box payload).derivK
  value_sound := by
    intro box payload hcheck coordinate hcoordinate
    exact directAD_value_sound terms hbasic hcheck hcoordinate
  derivS_sound := by
    intro box payload hcheck coordinate hcoordinate
    exact (normalizedDerivativeAD_sound terms hbasic hcheck hcoordinate).1
  derivK_sound := by
    intro box payload hcheck coordinate hcoordinate
    exact (normalizedDerivativeAD_sound terms hbasic hcheck hcoordinate).2

/-- Fully concrete kernel-sound oracle; the proof argument of `oracle` has
been discharged by the factored upper-`K` component theorem above. -/
noncomputable def concreteOracle (terms : ℕ) :
    LRLowRatioFiniteVMeanValue.Oracle :=
  oracle terms (basicSoundness terms)

def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox) : Payload :=
  let sharp := LRUpperKReplayCertificate.auto sqrtFuel logFuel box
  { sharp := sharp
    logY := RationalEnclosure.autoLogIntervalCertificate logFuel
      (LRUpperKReplayCertificate.yAD box).value }

def autoDerivative (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    DerivativePayload :=
  let sharp := LRUpperKReplayCertificate.auto sqrtFuel logFuel box
  { sharp := sharp
    derivative := LRHighShapeVZeroFaceCertificate.auto sqrtFuel logFuel
      (rawHull box) }

/-- Deterministic proposal for a correlated mean-value leaf.  As elsewhere,
the generated data carry no authority until `M.accepts` reduces to `true`. -/
def autoCentered (terms sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRLowRatioFiniteVMeanValue.CenteredPayload (concreteOracle terms) where
  center := auto sqrtFuel logFuel
    (LRLowRatioFiniteVMeanValue.centerSKBox box)
  derivative := autoDerivative sqrtFuel logFuel box

/-! ## Executable automatic leaf projections -/

/-- The two expensive automatically generated payloads shared by the
mean-value payload check and midpoint evaluation. -/
structure AutoMeanAnalysis where
  center : Payload
  derivative : DerivativePayload

def autoMeanAnalysis (sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : AutoMeanAnalysis where
  center := auto sqrtFuel logFuel
    (LRLowRatioFiniteVMeanValue.centerSKBox box)
  derivative := autoDerivative sqrtFuel logFuel box

def AutoMeanAnalysis.evaluation (analysis : AutoMeanAnalysis) (terms : ℕ)
    (box : CertificateBox) : MidpointSKCertificate :=
  { value := (directAD terms
      (LRLowRatioFiniteVMeanValue.centerSKBox box) analysis.center).value
    derivS :=
      (normalizedDerivativeAD terms box analysis.derivative).derivS
    derivK :=
      (normalizedDerivativeAD terms box analysis.derivative).derivK }

def AutoMeanAnalysis.payloadsCheck (analysis : AutoMeanAnalysis) (terms : ℕ)
    (box : CertificateBox) : Bool :=
  LRLowRatioFiniteVMeanValue.chartBoxCheck box &&
    payloadCheck terms (LRLowRatioFiniteVMeanValue.centerSKBox box)
      analysis.center &&
    derivativePayloadCheck terms box analysis.derivative

/-- The deterministic midpoint evaluation, projected directly from the
concrete oracle's computational fields.  Keeping this definition free of the
oracle's proof fields makes it suitable for external topology generation. -/
def autoEvaluation (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : MidpointSKCertificate :=
  (autoMeanAnalysis sqrtFuel logFuel box).evaluation terms box

/-- The executable domain and payload check for an automatic mean-value
leaf. -/
def autoMeanPayloadCheck (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : Bool :=
  (autoMeanAnalysis sqrtFuel logFuel box).payloadsCheck terms box

/-- Deterministic correlated mean-value acceptance Boolean. -/
def autoMeanAccepts (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : Bool :=
  let analysis := autoMeanAnalysis sqrtFuel logFuel box
  analysis.payloadsCheck terms box &&
    (analysis.evaluation terms box).check box

/-- Deterministic natural whole-box acceptance Boolean. -/
def autoNaturalAccepts (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : Bool :=
  let payload := auto sqrtFuel logFuel box
  payloadCheck terms box payload &&
    (directAD terms box payload).value.provesNonnegative

theorem autoEvaluation_eq (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) :
    autoEvaluation terms sqrtFuel logFuel box =
      LRLowRatioFiniteVMeanValue.evaluate (concreteOracle terms) box
        (autoCentered terms sqrtFuel logFuel box) := by
  rfl

theorem autoMeanPayloadCheck_eq (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) :
    autoMeanPayloadCheck terms sqrtFuel logFuel box =
      LRLowRatioFiniteVMeanValue.payloadCheck (concreteOracle terms) box
        (autoCentered terms sqrtFuel logFuel box) := by
  rfl

theorem autoMeanAccepts_eq (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) :
    autoMeanAccepts terms sqrtFuel logFuel box =
      LRLowRatioFiniteVMeanValue.accepts (concreteOracle terms) box
        (autoCentered terms sqrtFuel logFuel box) := by
  rfl

theorem autoNaturalAccepts_eq (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) :
    autoNaturalAccepts terms sqrtFuel logFuel box =
      LRLowRatioFiniteVMeanValue.leafAccepts (concreteOracle terms) box
        (.natural (auto sqrtFuel logFuel box)) := by
  rfl

end LRLowRatioFiniteVConcreteOracle
end CourtadeKumar
