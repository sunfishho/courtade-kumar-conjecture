import InformationTheory.CourtadeKumar.LRDeterminantFiniteReplayTargets
import InformationTheory.CourtadeKumar.LRDeterminantPositiveFactors
import InformationTheory.CourtadeKumar.LRHighShapeVZeroFaceEvaluator
import InformationTheory.CourtadeKumar.IntervalMidpointSKCertificate

/-!
# Direct `(s,K,h)` evaluator for the upper-`K` determinant replay

The audited upper-corridor replay uses the chart

`k = s*K`, `chi = h^2`

and encloses `FirstBracket / e`.  This file evaluates that formula directly
in the chart rather than first replacing a chart box by an axis-aligned raw
`(s,k,chi)` hull.  Thus the interval expression retains the two useful
correlations `k = s*K` and `chi = h^2`.

The `Q(chi*e)` and `omega_s(chi*e)` nodes use their value-only zero-endpoint
certificates, so a checked leaf may touch the closed face `h = 0`.  Every
other transcendental node is backed by the existing exact rational
square-root and logarithm certificates.
-/

namespace CourtadeKumar

namespace LRUpperKReplayCertificate

/-! ## Exact cancellation identities used by the retained evaluator -/

noncomputable def aPrimitive (s y : ℝ) : ℝ :=
  lrCertificateQ y + lrCertificateOmega s y - lrCertificateOmega s 0

noncomputable def cPrimitive (s y : ℝ) : ℝ :=
  lrCertificateOmega s y - lrCertificateOmega s 0

noncomputable def kappaV (v : ℝ) : ℝ :=
  (1 - v) ^ 2 / (v * (1 + v))

theorem kappaV_identity {v : ℝ} (hv : v ≠ 0) (honePlus : 1 + v ≠ 0) :
    1 + 1 / v - 4 / (1 + v) = kappaV v := by
  unfold kappaV
  field_simp [hv, honePlus]
  ring

/-- Cancellation-aware identity for `Psi`.  It is the exact formula used
by the audited upper-corridor evaluator before interval evaluation. -/
theorem psi_eq_aPrimitives {point : CertificatePoint}
    (hv : lrCertificateV point ≠ 0)
    (honePlus : 1 + lrCertificateV point ≠ 0) :
    lrDeterminantPsi point =
      lrCertificateG0 (lrCertificateV point) +
        aPrimitive point.s (lrCertificateY0 point) +
        aPrimitive point.s (lrCertificateE point) /
          lrCertificateV point +
        kappaV (lrCertificateV point) * lrCertificateW point := by
  rw [← kappaV_identity hv honePlus]
  unfold lrDeterminantPsi lrCertificateGShape lrCertificateGShapeValue
    lrCertificatePW lrCertificatePWValue aPrimitive lrCertificateW
  field_simp [hv, honePlus]
  ring

/-- The more delicate difference `Psi-G` can be formed without first
enclosing either large summand. -/
theorem psi_sub_gShape_eq_cPrimitives {point : CertificatePoint}
    (hv : lrCertificateV point ≠ 0)
    (honePlus : 1 + lrCertificateV point ≠ 0) :
    lrDeterminantPsi point - lrCertificateGShape point =
      cPrimitive point.s (lrCertificateY0 point) +
        cPrimitive point.s (lrCertificateE point) /
          lrCertificateV point +
        kappaV (lrCertificateV point) * lrCertificateW point := by
  rw [psi_eq_aPrimitives hv honePlus]
  unfold lrCertificateGShape lrCertificateGShapeValue aPrimitive
    cPrimitive lrCertificateW
  field_simp [hv]
  ring

/-! ## Chart interval expressions -/

/-- Product AD whose value interval uses the sharp endpoint formula under
separately checked nonnegativity hypotheses. -/
def mulNonnegativeAD (a b : IntervalAD) : IntervalAD :=
  let raw := IntervalAD.mul a b
  { raw with value := RationalEnclosure.mulNonnegative a.value b.value }

theorem mulNonnegativeAD_sound
    {a b : IntervalAD} {av as ak ah bv bs bk bh : ℝ}
    (haLower : (0 : ℚ) ≤ a.value.lower)
    (hbLower : (0 : ℚ) ≤ b.value.lower)
    (ha : a.Contains av as ak ah) (hb : b.Contains bv bs bk bh) :
    (mulNonnegativeAD a b).Contains (av * bv)
      (as * bv + av * bs) (ak * bv + av * bk)
      (ah * bv + av * bh) := by
  have hraw := IntervalAD.contains_mul ha hb
  exact ⟨RationalEnclosure.contains_mulNonnegative
    haLower hbLower ha.1 hb.1, hraw.2⟩

def sAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.variableS box.sInterval

/-- The generic box's second coordinate stores `K`. -/
def ratioAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.variableK box.kInterval

/-- The generic box's third coordinate stores `h`. -/
def hAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.variableChi box.chiInterval

/-- Decoded physical `k = s*K`. -/
def physicalKAD (box : CertificateBox) : IntervalAD :=
  mulNonnegativeAD (sAD box) (ratioAD box)

/-- Decoded physical `chi = h^2`. -/
def physicalChiAD (box : CertificateBox) : IntervalAD :=
  mulNonnegativeAD (hAD box) (hAD box)

/-- Physical cancellation variable `e = s*k = s^2*K`. -/
def eAD (box : CertificateBox) : IntervalAD :=
  mulNonnegativeAD (sAD box) (physicalKAD box)

def xAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.sub (IntervalAD.const 1)
    (IntervalAD.mul (physicalChiAD box) (eAD box))

def vRadicandAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.divPositive
    (IntervalAD.sub (IntervalAD.const 1) (eAD box)) (xAD box)

/-- `y0 = chi*e`, with a nonnegative endpoint value hull so that `h = 0`
is admitted without manufacturing a finite enclosure for `Q' (0)`. -/
def y0AD (box : CertificateBox) : IntervalAD :=
  mulNonnegativeAD (physicalChiAD box) (eAD box)

/-! ## Concrete untrusted payload -/

/-- Exactly the scalar certificates needed by the value-only upper-`K`
formula.  There is no proof field and no trusted floating-point datum. -/
structure Payload where
  vSqrt : RationalEnclosure.SqrtCertificate
  omegaZero : LROmegaZeroADCertificate
  omegaY0 : LROmegaZeroIntervalCertificate
  omegaE : LROmegaADCertificate
  g0 : LRG0ADCertificate
  qY0 : LRQZeroIntervalCertificate
  qE : LRQIntervalCertificate
  logOnePlusV : RationalEnclosure.LogIntervalCertificate
  logBE : RationalEnclosure.LogIntervalCertificate
  logMeanY : RationalEnclosure.LogIntervalCertificate

def vAD (box : CertificateBox) (payload : Payload) : IntervalAD :=
  IntervalAD.sqrt payload.vSqrt (vRadicandAD box)

def onePlusVI (box : CertificateBox) (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.add (RationalEnclosure.point 1)
    (vAD box payload).value

def yNumeratorAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.sub
    (IntervalAD.add (IntervalAD.const 1) (physicalKAD box)) (eAD box)

/-- Cancellation-aware identity `b_s(e) = s*(1+k-e)` in this chart. -/
def beAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.mul (sAD box) (yNumeratorAD box)

/-- Cancellation-aware chart formula
`Y = (1+k-e)/k = b_s(e)/e`.  The former avoids dividing two quantities
of order `s` and is the exact expression used by the retained replay. -/
def yI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.div (yNumeratorAD box).value
    (physicalKAD box).value

def meanYI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.scale (1 / 2)
    (RationalEnclosure.add (RationalEnclosure.point 1) (yI box))

def threeYPlusOneI (box : CertificateBox) : RationalEnclosure :=
  RationalEnclosure.add
    (RationalEnclosure.scale 3 (yI box)) (RationalEnclosure.point 1)

/-- A named validity proposition keeps the Boolean checker and its soundness
proof synchronized without an opaque nest of conjunction projections. -/
structure Valid (box : CertificateBox) (payload : Payload) : Prop where
  sPositive : (0 : ℚ) < (sAD box).value.lower
  ratioPositive : (0 : ℚ) < (ratioAD box).value.lower
  hNonnegative : (0 : ℚ) ≤ (hAD box).value.lower
  xPositive : (0 : ℚ) < (xAD box).value.lower
  vSqrtCheck : IntervalAD.sqrtCheck (vRadicandAD box).value
    payload.vSqrt = true
  vPositive : (0 : ℚ) < (vAD box payload).value.lower
  omegaZeroCheck : payload.omegaZero.check (sAD box) = true
  omegaY0Check : payload.omegaY0.check (sAD box) (y0AD box) = true
  omegaECheck : payload.omegaE.check (sAD box) (eAD box) = true
  g0Check : payload.g0.check (vAD box payload) = true
  qY0Check : payload.qY0.check (y0AD box).value = true
  qECheck : payload.qE.check (eAD box).value = true
  logOnePlusVCheck : payload.logOnePlusV.check
    (onePlusVI box payload) = true
  logBECheck : payload.logBE.check (beAD box).value = true
  logMeanYCheck : payload.logMeanY.check (meanYI box) = true
  ePositive : (0 : ℚ) < (eAD box).value.lower
  threeYPlusOnePositive : (0 : ℚ) < (threeYPlusOneI box).lower

def payloadCheck (box : CertificateBox) (payload : Payload) : Bool :=
  decide
    ((0 : ℚ) < (sAD box).value.lower ∧
      (0 : ℚ) < (ratioAD box).value.lower ∧
      (0 : ℚ) ≤ (hAD box).value.lower ∧
      (0 : ℚ) < (xAD box).value.lower ∧
      IntervalAD.sqrtCheck (vRadicandAD box).value payload.vSqrt = true ∧
      (0 : ℚ) < (vAD box payload).value.lower ∧
      payload.omegaZero.check (sAD box) = true ∧
      payload.omegaY0.check (sAD box) (y0AD box) = true ∧
      payload.omegaE.check (sAD box) (eAD box) = true ∧
      payload.g0.check (vAD box payload) = true ∧
      payload.qY0.check (y0AD box).value = true ∧
      payload.qE.check (eAD box).value = true ∧
      payload.logOnePlusV.check (onePlusVI box payload) = true ∧
      payload.logBE.check (beAD box).value = true ∧
      payload.logMeanY.check (meanYI box) = true ∧
      (0 : ℚ) < (eAD box).value.lower ∧
      (0 : ℚ) < (threeYPlusOneI box).lower)

theorem payloadCheck_sound {box : CertificateBox} {payload : Payload}
    (hcheck : payloadCheck box payload = true) : Valid box payload := by
  simp only [payloadCheck, decide_eq_true_eq] at hcheck
  rcases hcheck with
    ⟨hs, hK, hh, hx, hvSqrt, hv, hw, hwy, hwe, hg0, hqy, hqe,
      hlogV, hlogBE, hlogMean, he, hthree⟩
  exact
    { sPositive := hs
      ratioPositive := hK
      hNonnegative := hh
      xPositive := hx
      vSqrtCheck := hvSqrt
      vPositive := hv
      omegaZeroCheck := hw
      omegaY0Check := hwy
      omegaECheck := hwe
      g0Check := hg0
      qY0Check := hqy
      qECheck := hqe
      logOnePlusVCheck := hlogV
      logBECheck := hlogBE
      logMeanYCheck := hlogMean
      ePositive := he
      threeYPlusOnePositive := hthree }

/-- Exact chart derivatives of `y₀ = h² e`, before rewriting the first
two components into their zero-face regularized quotient forms. -/
theorem y0AD_sound {box : CertificateBox} {payload : Payload}
    (hvalid : Valid box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    let raw := lrDeterminantKChartDecode coordinate
    let eS := raw.k + raw.s * coordinate.k
    let eK := raw.s * coordinate.s
    (y0AD box).Contains (lrCertificateY0 raw)
      (raw.chi * eS) (raw.chi * eK)
      (2 * coordinate.chi * lrCertificateE raw) := by
  dsimp only
  let raw := lrDeterminantKChartDecode coordinate
  have hrawE : lrCertificateE (lrDeterminantKChartDecode coordinate) =
      lrCertificateE raw := by rfl
  let eS := raw.k + raw.s * coordinate.k
  let eK := raw.s * coordinate.s
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains coordinate.s from
      ⟨hcoordinate.1, hcoordinate.2.1⟩)
  have hratio := IntervalAD.contains_variableK
    (show box.kInterval.Contains coordinate.k from
      ⟨hcoordinate.2.2.1, hcoordinate.2.2.2.1⟩)
  have hh := IntervalAD.contains_variableChi
    (show box.chiInterval.Contains coordinate.chi from
      ⟨hcoordinate.2.2.2.2.1, hcoordinate.2.2.2.2.2⟩)
  have hkLower : (0 : ℚ) ≤ (physicalKAD box).value.lower := by
    simpa [physicalKAD, mulNonnegativeAD] using
      mul_nonneg hvalid.sPositive.le hvalid.ratioPositive.le
  have hchiLower : (0 : ℚ) ≤ (physicalChiAD box).value.lower := by
    simpa [physicalChiAD, mulNonnegativeAD] using
      mul_nonneg hvalid.hNonnegative hvalid.hNonnegative
  have hkRaw := mulNonnegativeAD_sound hvalid.sPositive.le
    hvalid.ratioPositive.le hs hratio
  have hchiRaw := mulNonnegativeAD_sound hvalid.hNonnegative
    hvalid.hNonnegative hh hh
  have heRaw := mulNonnegativeAD_sound hvalid.sPositive.le hkLower hs hkRaw
  have he : (eAD box).Contains (lrCertificateE raw) eS eK 0 := by
    convert heRaw using 1 <;>
      simp [raw, eS, eK, lrDeterminantKChartDecode]
  have hchi : (physicalChiAD box).Contains raw.chi 0 0
      (2 * coordinate.chi) := by
    convert hchiRaw using 1 <;>
      simp [raw, lrDeterminantKChartDecode, pow_two]
    ring
  have hyRaw := mulNonnegativeAD_sound hchiLower hvalid.ePositive.le
    hchi he
  convert hyRaw using 1 <;>
    simp only [zero_mul, zero_add, add_zero, mul_zero] <;>
    try ring

/-! ## Endpoint-safe chart derivatives -/

/-- In chart coordinates `y0 = s^2*K*h^2`, hence
`Q'(y0) * partial_s y0 = 2*(y0*Q'(y0))/s` and
`Q'(y0) * partial_K y0 = (y0*Q'(y0))/K`.
The zero-endpoint certificate already encloses `y0*Q'(y0)`, so these two
derivatives stay finite on a box touching `h = 0`.  The `h` derivative is
synthetic and is deliberately not used by the centered `(s,K)` rule. -/
def qZeroY0SKAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRQZeroIntervalCertificate) : IntervalAD :=
  let regularized := certificate.enclosure terms (y0AD box).value
  { value := regularized
    derivS := RationalEnclosure.div
      (RationalEnclosure.scale 2 regularized) (sAD box).value
    derivK := RationalEnclosure.div regularized (ratioAD box).value
    derivChi := RationalEnclosure.point 0 }

def qY0SKAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  qZeroY0SKAD terms box payload.qY0

theorem qZeroY0SKAD_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hvalid : Valid box payload)
    {certificate : LRQZeroIntervalCertificate}
    (hqCheck : certificate.check (y0AD box).value = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    let raw := lrDeterminantKChartDecode coordinate
    let result := qZeroY0SKAD terms box certificate
    result.value.Contains (lrCertificateQ (lrCertificateY0 raw)) ∧
      result.derivS.Contains
        (2 * (lrCertificateY0 raw *
          lrCertificateQPrime (lrCertificateY0 raw)) / coordinate.s) ∧
      result.derivK.Contains
        ((lrCertificateY0 raw *
          lrCertificateQPrime (lrCertificateY0 raw)) / coordinate.k) := by
  dsimp only
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains coordinate.s from
      ⟨hcoordinate.1, hcoordinate.2.1⟩)
  have hratio := IntervalAD.contains_variableK
    (show box.kInterval.Contains coordinate.k from
      ⟨hcoordinate.2.2.1, hcoordinate.2.2.2.1⟩)
  have hh := IntervalAD.contains_variableChi
    (show box.chiInterval.Contains coordinate.chi from
      ⟨hcoordinate.2.2.2.2.1, hcoordinate.2.2.2.2.2⟩)
  have hkLower : (0 : ℚ) ≤ (physicalKAD box).value.lower := by
    simpa [physicalKAD, mulNonnegativeAD] using
      mul_nonneg hvalid.sPositive.le hvalid.ratioPositive.le
  have hchiLower : (0 : ℚ) ≤ (physicalChiAD box).value.lower := by
    simpa [physicalChiAD, mulNonnegativeAD] using
      mul_nonneg hvalid.hNonnegative hvalid.hNonnegative
  have hk := mulNonnegativeAD_sound hvalid.sPositive.le
    hvalid.ratioPositive.le hs hratio
  have hchi := mulNonnegativeAD_sound hvalid.hNonnegative
    hvalid.hNonnegative hh hh
  have he := mulNonnegativeAD_sound hvalid.sPositive.le hkLower hs hk
  have hy0 := mulNonnegativeAD_sound hchiLower hvalid.ePositive.le hchi he
  have hy0Value : (y0AD box).value.Contains
      (lrCertificateY0 (lrDeterminantKChartDecode coordinate)) := by
    simpa [y0AD, physicalChiAD, eAD, physicalKAD, sAD, ratioAD, hAD,
      lrCertificateY0, lrCertificateE, lrDeterminantKChartDecode,
      pow_two] using hy0.1
  let regularized := certificate.enclosure terms (y0AD box).value
  have hvalue := certificate.sound terms hqCheck hy0Value
  have hregularized := certificate.mul_prime_sound terms hqCheck hy0Value
  have hsDiv := RationalEnclosure.contains_div hvalid.sPositive
    (RationalEnclosure.contains_scale 2 hregularized) hs.1
  have hKDiv := RationalEnclosure.contains_div hvalid.ratioPositive
    hregularized hratio.1
  exact ⟨by simpa [qZeroY0SKAD, regularized] using hvalue,
    by simpa [qZeroY0SKAD, regularized] using hsDiv,
    by simpa [qZeroY0SKAD, regularized] using hKDiv⟩

theorem qY0SKAD_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hvalid : Valid box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    let raw := lrDeterminantKChartDecode coordinate
    let result := qY0SKAD terms box payload
    result.value.Contains (lrCertificateQ (lrCertificateY0 raw)) ∧
      result.derivS.Contains
        (2 * (lrCertificateY0 raw *
          lrCertificateQPrime (lrCertificateY0 raw)) / coordinate.s) ∧
      result.derivK.Contains
        ((lrCertificateY0 raw *
          lrCertificateQPrime (lrCertificateY0 raw)) / coordinate.k) := by
  simpa [qY0SKAD] using qZeroY0SKAD_sound terms hvalid
    hvalid.qY0Check hcoordinate

/-- Endpoint-safe chart AD for `omega_s(y0)`.  Its first two derivative
fields are genuine `(s,K)` derivatives; the third field is a harmless
synthetic continuation and is never consumed by the centered rule. -/
def omegaY0SKAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  let s := sAD box
  let y := y0AD box
  let b := lrCertificateBAD s y
  let qPrimeB := payload.omegaY0.qPrimeAtB.enclosure terms
  let qB := IntervalAD.unary
    (payload.omegaY0.qAtB.enclosure terms) qPrimeB b
  let qY := qZeroY0SKAD terms box payload.omegaY0.qAtY
  let qPrimeBAD := IntervalAD.unary qPrimeB
    (lrQSecondCoarseEnclosure b.value) b
  IntervalAD.sub (IntervalAD.sub qB qY)
    (IntervalAD.mul (IntervalAD.mul s
      (IntervalAD.sub (IntervalAD.const 1) y)) qPrimeBAD)

theorem omegaY0SKAD_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hvalid : Valid box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    let raw := lrDeterminantKChartDecode coordinate
    ∃ derivH : ℝ, (omegaY0SKAD terms box payload).Contains
      (lrCertificateOmega raw.s (lrCertificateY0 raw))
      (lrCertificateOmegaDeriv raw.s (lrCertificateY0 raw)
        1 (2 * lrCertificateY0 raw / coordinate.s))
      (lrCertificateOmegaDeriv raw.s (lrCertificateY0 raw)
        0 (lrCertificateY0 raw / coordinate.k)) derivH := by
  dsimp only
  let s := sAD box
  let y := y0AD box
  let b := lrCertificateBAD s y
  let qPrimeB := payload.omegaY0.qPrimeAtB.enclosure terms
  let qB := IntervalAD.unary
    (payload.omegaY0.qAtB.enclosure terms) qPrimeB b
  let qY := qZeroY0SKAD terms box payload.omegaY0.qAtY
  let qPrimeBAD := IntervalAD.unary qPrimeB
    (lrQSecondCoarseEnclosure b.value) b
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains coordinate.s from
      ⟨hcoordinate.1, hcoordinate.2.1⟩)
  have hratio := IntervalAD.contains_variableK
    (show box.kInterval.Contains coordinate.k from
      ⟨hcoordinate.2.2.1, hcoordinate.2.2.2.1⟩)
  have hsPoint : 0 < coordinate.s := by
    have hlo : (0 : ℝ) < ((sAD box).value.lower : ℝ) := by
      exact_mod_cast hvalid.sPositive
    exact hlo.trans_le hs.1.1
  have hKPoint : 0 < coordinate.k := by
    have hlo : (0 : ℝ) < ((ratioAD box).value.lower : ℝ) := by
      exact_mod_cast hvalid.ratioPositive
    exact hlo.trans_le hratio.1.1
  let raw := lrDeterminantKChartDecode coordinate
  have hsRaw : s.Contains raw.s 1 0 0 := by
    simpa [s, raw, lrDeterminantKChartDecode] using hs
  let eS := raw.k + raw.s * coordinate.k
  let eK := raw.s * coordinate.s
  let yS := 2 * lrCertificateY0 raw / coordinate.s
  let yK := lrCertificateY0 raw / coordinate.k
  let yH := 2 * coordinate.chi * lrCertificateE raw
  have hsNe : coordinate.s ≠ 0 := ne_of_gt hsPoint
  have hKNe : coordinate.k ≠ 0 := ne_of_gt hKPoint
  have hyNamed := y0AD_sound hvalid hcoordinate
  have hy0S : raw.chi * eS = yS := by
    dsimp [raw, eS, yS]
    simp [lrCertificateY0, lrCertificateE,
      lrDeterminantKChartDecode]
    field_simp [hsNe]
    ring
  have hy0K : raw.chi * eK = yK := by
    dsimp [raw, eK, yK]
    simp [lrCertificateY0, lrCertificateE,
      lrDeterminantKChartDecode]
    field_simp [hKNe]
  change (y0AD box).Contains (lrCertificateY0 raw)
    (raw.chi * eS) (raw.chi * eK)
    (2 * coordinate.chi * lrCertificateE raw) at hyNamed
  rw [hy0S, hy0K] at hyNamed
  have hy : y.Contains (lrCertificateY0 raw) yS yK yH := by
    simpa [y, yH] using hyNamed
  have hb := lrCertificateBAD_sound hsRaw hy
  have hparts :
      (payload.omegaY0.qAtB.check b.value = true ∧
        payload.omegaY0.qAtY.check y.value = true) ∧
        payload.omegaY0.qPrimeAtB.check b.value = true := by
    simpa [LROmegaZeroIntervalCertificate.check, s, y, b] using
      hvalid.omegaY0Check
  have hqBValue := payload.omegaY0.qAtB.sound terms hparts.1.1 hb.1
  have hqPrimeBValue := payload.omegaY0.qPrimeAtB.sound terms
    hparts.2 hb.1
  have hqB := IntervalAD.contains_unary hqBValue hqPrimeBValue hb
  have hcoarse : lrQSecondCoarseCheck b.value = true := by
    have hraw :
        decide ((0 : ℚ) < b.value.lower ∧ b.value.lower ≤ b.value.upper ∧
          b.value.upper < 1) = true ∧
        payload.omegaY0.qPrimeAtB.lowerEndpoint.primeCheck
          b.value.lower = true ∧
        payload.omegaY0.qPrimeAtB.upperEndpoint.primeCheck
          b.value.upper = true := by
      simpa [LRQPrimeIntervalCertificate.check, and_assoc] using hparts.2
    simpa [lrQSecondCoarseCheck] using hraw.1
  have hqSecondB := lrQSecondCoarseEnclosure_sound hcoarse hb.1
  have hqPrimeB := IntervalAD.contains_unary
    hqPrimeBValue hqSecondB hb
  have hqYParts := qZeroY0SKAD_sound terms hvalid hparts.1.2 hcoordinate
  have hqY : qY.Contains (lrCertificateQ (lrCertificateY0 raw))
      (lrCertificateQPrime (lrCertificateY0 raw) * yS)
      (lrCertificateQPrime (lrCertificateY0 raw) * yK) 0 := by
    refine ⟨hqYParts.1, ?_, ?_, ?_⟩
    · convert hqYParts.2.1 using 1
      all_goals (dsimp [yS]; ring)
    · convert hqYParts.2.2 using 1
      all_goals (dsimp [yK]; ring)
    · simp [qY, qZeroY0SKAD, RationalEnclosure.point,
        RationalEnclosure.Contains]
  have honeMinusY := IntervalAD.contains_sub
    (IntervalAD.contains_const 1) hy
  have hfactor := IntervalAD.contains_mul hsRaw honeMinusY
  have hcorrection := IntervalAD.contains_mul hfactor hqPrimeB
  have hresult := IntervalAD.contains_sub
    (IntervalAD.contains_sub hqB hqY) hcorrection
  let derivH :=
    lrCertificateQPrime (lrCertificateB raw.s (lrCertificateY0 raw)) *
        lrCertificateBDeriv raw.s (lrCertificateY0 raw) 0 yH - 0 -
      ((0 * (1 - lrCertificateY0 raw) + raw.s * (0 - yH)) *
          lrCertificateQPrime
            (lrCertificateB raw.s (lrCertificateY0 raw)) +
        raw.s * (1 - lrCertificateY0 raw) *
          (lrCertificateQSecond
              (lrCertificateB raw.s (lrCertificateY0 raw)) *
            lrCertificateBDeriv raw.s (lrCertificateY0 raw) 0 yH))
  refine ⟨derivH, ?_⟩
  convert hresult using 1 <;>
    simp [lrCertificateOmega, lrCertificateOmegaDeriv,
      lrCertificateBDeriv, raw, yS, yK, yH, derivH]
  ring

/-! ## Exact derivatives of the decoded upper-`K` target -/

/-- Derivative of `Y = b_s(e)/e` along an arbitrary raw-coordinate curve. -/
noncomputable def yDeriv (point : CertificatePoint)
    (s' e' : ℝ) : ℝ :=
  (lrCertificateBDeriv point.s (lrCertificateE point) s' e' *
      lrCertificateE point -
    lrCertificateB point.s (lrCertificateE point) * e') /
    lrCertificateE point ^ 2

/-- Derivative of the audited scalar lower logarithm `D1(Y)`. -/
noncomputable def d1Deriv (point : CertificatePoint)
    (s' e' : ℝ) : ℝ :=
  let Y := lrDeterminantY point
  let Y' := yDeriv point s' e'
  (1 / 2 : ℝ) * ((Y' / 2) / ((1 + Y) / 2)) +
    ((Y' * (3 * Y + 1) - (Y - 1) * (3 * Y')) /
      (3 * Y + 1) ^ 2)

noncomputable def psiDeriv (point : CertificatePoint)
    (s' y0' e' v' : ℝ) : ℝ :=
  let g' := lrCertificateGShapeDeriv point y0' e' v'
  let pw' := lrCertificatePWDeriv point s' y0' e' v'
  let w' := lrCertificateOmegaDeriv point.s 0 s' 0
  g' + pw' -
    ((4 * w') * (1 + lrCertificateV point) -
      4 * lrCertificateW point * v') /
      (1 + lrCertificateV point) ^ 2

noncomputable def deltaDeriv (point : CertificatePoint)
    (x' v' : ℝ) : ℝ :=
  ((-(v' * lrCertificateX point + lrCertificateV point * x')) *
        (1 + lrCertificateV point) -
      (1 - lrCertificateV point * lrCertificateX point) * v') /
    (1 + lrCertificateV point) ^ 2

noncomputable def firstBracketDeriv (point : CertificatePoint)
    (s' y0' e' x' v' : ℝ) : ℝ :=
  let B' := lrCertificateBFlowDeriv point s' e' v'
  let D1' := d1Deriv point s' e'
  let G' := lrCertificateGShapeDeriv point y0' e' v'
  let Psi' := psiDeriv point s' y0' e' v'
  let delta' := deltaDeriv point x' v'
  let W' := lrCertificateOmegaDeriv point.s 0 s' 0
  B' *
      (lrDeterminantPsi point - lrCertificateGShape point +
        4 * lrDeterminantDelta point * lrCertificateW point) +
    lrCertificateBFlow point *
      (Psi' - G' +
        4 * (delta' * lrCertificateW point +
          lrDeterminantDelta point * W')) +
    D1' * lrDeterminantPsi point + lrDeterminantD1 point * Psi'

/-- The exact directional derivative of `FirstBracket/e` in raw
`(s,k,chi)` coordinates.  Chart derivatives below simply substitute the
two decoded chart directions. -/
noncomputable def targetRawDeriv (point : CertificatePoint)
    (s' k' chi' : ℝ) : ℝ :=
  let e' := s' * point.k + point.s * k'
  let y0' := chi' * lrCertificateE point + point.chi * e'
  let x' := -(chi' * lrCertificateE point + point.chi * e')
  let v' := lrCertificateVDeriv point e' x'
  (firstBracketDeriv point s' y0' e' x' v' * lrCertificateE point -
      lrDeterminantFirstBracket
          (lrCertificateBFlow point) (lrDeterminantD1 point)
          (lrCertificateGShape point) (lrDeterminantPsi point)
          (lrDeterminantDelta point) (lrCertificateW point) * e') /
    lrCertificateE point ^ 2

noncomputable def targetChartDerivS (coordinate : CertificatePoint) : ℝ :=
  targetRawDeriv (lrDeterminantKChartDecode coordinate) 1 coordinate.k 0

noncomputable def targetChartDerivK (coordinate : CertificatePoint) : ℝ :=
  targetRawDeriv (lrDeterminantKChartDecode coordinate) 0 coordinate.s 0

/-! The following calculus theorem is independent of interval arithmetic.
It identifies the exact algebraic derivative above with the derivative of
the analytic target on the ordinary open chart. -/

theorem hasDerivAt_targetRaw_curve
    {z s' k' chi' : ℝ} {sfun kfun chifun : ℝ → ℝ}
    (hs : HasDerivAt sfun s' z) (hk : HasDerivAt kfun k' z)
    (hchi : HasDerivAt chifun chi' z)
    (hinterior : LRHighShapeInterior
      (lrCertificateCurve sfun kfun chifun z)) :
    HasDerivAt
      (fun q ↦ lrFiniteDeterminantUpperKReplayTarget
        (lrCertificateCurve sfun kfun chifun q))
      (targetRawDeriv (lrCertificateCurve sfun kfun chifun z)
        s' k' chi') z := by
  let point := lrCertificateCurve sfun kfun chifun z
  let e' := s' * point.k + point.s * k'
  let y0' := chi' * lrCertificateE point + point.chi * e'
  let x' := -(chi' * lrCertificateE point + point.chi * e')
  let v' := lrCertificateVDeriv point e' x'
  have heRaw := hasDerivAt_lrCertificateE_curve (chi := chifun) hs hk
  have he : HasDerivAt
      (fun q ↦ lrCertificateE (lrCertificateCurve sfun kfun chifun q))
      e' z := by
    simpa [point, e', lrCertificateCurve] using heRaw
  have hxRaw := hasDerivAt_lrCertificateX_curve hs hk hchi
  have hx : HasDerivAt
      (fun q ↦ lrCertificateX (lrCertificateCurve sfun kfun chifun q))
      x' z := by
    simpa [point, e', x', lrCertificateCurve] using hxRaw
  have hvRaw := hasDerivAt_lrCertificateV_curve hs hk hchi
    hinterior.2.1 hinterior.2.2
  have hv : HasDerivAt
      (fun q ↦ lrCertificateV (lrCertificateCurve sfun kfun chifun q))
      v' z := by
    simpa [point, e', x', v'] using hvRaw
  have hy0Raw := hchi.mul he
  have hy0 : HasDerivAt
      (fun q ↦ lrCertificateY0
        (lrCertificateCurve sfun kfun chifun q)) y0' z := by
    simpa [lrCertificateY0, point, e', y0', lrCertificateCurve] using
      hy0Raw
  have hy0Mem : lrCertificateY0 point ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hinterior.2.2.1 hinterior.2.1.1
    · calc
        point.chi * lrCertificateE point <
            1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hinterior.2.2.2
            hinterior.2.1.1
        _ < 1 := by simpa using hinterior.2.1.2
  have hvMem := lrCertificateV_mem_Ioo hinterior
  have hgRaw := hasDerivAt_lrCertificateGShapeValue_along
    hy0 he hv hy0Mem hinterior.2.1 hvMem.1
  have hg : HasDerivAt
      (fun q ↦ lrCertificateGShape
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificateGShapeDeriv point y0' e' v') z := by
    simpa [lrCertificateGShape, lrCertificateGShapeDeriv, point] using hgRaw
  have hpwRaw := hasDerivAt_lrCertificatePWValue_along
    hs hy0 he hv hinterior.1 hy0Mem hinterior.2.1 hvMem.1
  have hpw : HasDerivAt
      (fun q ↦ lrCertificatePW
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificatePWDeriv point s' y0' e' v') z := by
    simpa [lrCertificatePW, lrCertificatePWDeriv, point] using hpwRaw
  have hwRaw := hasDerivAt_lrCertificateOmega_zero_along
    hs rfl hinterior.1
  have hw : HasDerivAt
      (fun q ↦ lrCertificateW
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificateOmegaDeriv point.s 0 s' 0) z := by
    simpa [lrCertificateW, point, lrCertificateCurve] using hwRaw
  have hbRaw := hasDerivAt_lrCertificateBFlowValue_along
    hs he hv hinterior.1 hinterior.2.1 hvMem.1
  have hb : HasDerivAt
      (fun q ↦ lrCertificateBFlow
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificateBFlowDeriv point s' e' v') z := by
    simpa [lrCertificateBFlow, lrCertificateBFlowDeriv, point] using hbRaw

  have hbY := hasDerivAt_lrCertificateB_along hs he rfl rfl
  have hYRaw := hbY.div he hinterior.2.1.1.ne'
  have hY : HasDerivAt
      (fun q ↦ lrDeterminantY
        (lrCertificateCurve sfun kfun chifun q))
      (yDeriv point s' e') z := by
    simpa [lrDeterminantY, yDeriv, point] using hYRaw
  have hYOne := lrDeterminantY_one_le hinterior
  have hmeanPos : 0 < (1 + lrDeterminantY point) / 2 := by linarith
  have hthreePos : 0 < 3 * lrDeterminantY point + 1 := by linarith
  have hmean := ((hasDerivAt_const z 1).add hY).div_const 2
  have hlogMean :=
    (Real.hasDerivAt_log hmeanPos.ne').comp z hmean
  have hhalfLog := (hasDerivAt_const z (1 / 2 : ℝ)).mul hlogMean
  have hYMinus := hY.sub_const 1
  have hthree := (hY.mul_const 3).add_const 1
  have hthreeNe : lrDeterminantY point * 3 + 1 ≠ 0 := by linarith
  have hfrac := hYMinus.div hthree hthreeNe
  have hd1Raw := hhalfLog.add hfrac
  have hd1 : HasDerivAt
      (fun q ↦ lrDeterminantD1
        (lrCertificateCurve sfun kfun chifun q))
      (d1Deriv point s' e') z := by
    unfold lrDeterminantD1 d1Deriv
    dsimp only
    convert hd1Raw using 1
    · funext q
      simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply,
        Function.comp_apply]
      ring_nf
    · simp [point]
      field_simp [hmeanPos.ne', hthreePos.ne']

  have honePlusV := (hasDerivAt_const z 1).add hv
  have honePlusVNe :
      1 + lrCertificateV point ≠ 0 := by linarith [hvMem.1]
  have hfourWOver := (hw.mul_const 4).div honePlusV honePlusVNe
  have hpsiRaw := (hg.add hpw).sub hfourWOver
  have hpsi : HasDerivAt
      (fun q ↦ lrDeterminantPsi
        (lrCertificateCurve sfun kfun chifun q))
      (psiDeriv point s' y0' e' v') z := by
    unfold lrDeterminantPsi psiDeriv
    dsimp only
    convert hpsiRaw using 1
    · funext q
      simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply]
      ring_nf
    · dsimp [point]
      field_simp [honePlusVNe]
      ring
  have hdeltaRaw := ((hasDerivAt_const z 1).sub (hv.mul hx)).div
    honePlusV honePlusVNe
  have hdelta : HasDerivAt
      (fun q ↦ lrDeterminantDelta
        (lrCertificateCurve sfun kfun chifun q))
      (deltaDeriv point x' v') z := by
    unfold lrDeterminantDelta deltaDeriv
    convert hdeltaRaw using 1 <;>
      simp [point]
  have hinner := (hpsi.sub hg).add ((hdelta.mul hw).mul_const 4)
  have hfirstRaw := (hb.mul hinner).add (hd1.mul hpsi)
  have hfirst : HasDerivAt
      (fun q ↦ lrDeterminantFirstBracket
        (lrCertificateBFlow (lrCertificateCurve sfun kfun chifun q))
        (lrDeterminantD1 (lrCertificateCurve sfun kfun chifun q))
        (lrCertificateGShape (lrCertificateCurve sfun kfun chifun q))
        (lrDeterminantPsi (lrCertificateCurve sfun kfun chifun q))
        (lrDeterminantDelta (lrCertificateCurve sfun kfun chifun q))
        (lrCertificateW (lrCertificateCurve sfun kfun chifun q)))
      (firstBracketDeriv point s' y0' e' x' v') z := by
    unfold lrDeterminantFirstBracket firstBracketDeriv
    dsimp only
    convert hfirstRaw using 1
    · funext q
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring_nf
    · simp [point]
      ring
  have hresult := hfirst.div he hinterior.2.1.1.ne'
  unfold lrFiniteDeterminantUpperKReplayTarget targetRawDeriv
  dsimp only
  simpa [point, e', y0', x', v'] using hresult

theorem hasDerivAt_targetChart_s {coordinate : CertificatePoint}
    (hinterior : LRHighShapeInterior
      (lrDeterminantKChartDecode coordinate)) :
    HasDerivAt
      (fun s ↦ lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode { coordinate with s := s }))
      (targetChartDerivS coordinate) coordinate.s := by
  have h := hasDerivAt_targetRaw_curve
    (sfun := fun s ↦ s)
    (kfun := fun s ↦ s * coordinate.k)
    (chifun := fun _ ↦ coordinate.chi ^ 2)
    (hasDerivAt_id coordinate.s)
    ((hasDerivAt_id coordinate.s).mul_const coordinate.k)
    (hasDerivAt_const coordinate.s (coordinate.chi ^ 2))
    hinterior
  simpa [targetChartDerivS, lrCertificateCurve,
    lrDeterminantKChartDecode] using h

theorem hasDerivAt_targetChart_k {coordinate : CertificatePoint}
    (hinterior : LRHighShapeInterior
      (lrDeterminantKChartDecode coordinate)) :
    HasDerivAt
      (fun K ↦ lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode { coordinate with k := K }))
      (targetChartDerivK coordinate) coordinate.k := by
  have h := hasDerivAt_targetRaw_curve
    (sfun := fun _ ↦ coordinate.s)
    (kfun := fun K ↦ coordinate.s * K)
    (chifun := fun _ ↦ coordinate.chi ^ 2)
    (hasDerivAt_const coordinate.k coordinate.s)
    ((hasDerivAt_const coordinate.k coordinate.s).mul
      (hasDerivAt_id coordinate.k))
    (hasDerivAt_const coordinate.k (coordinate.chi ^ 2))
    hinterior
  simpa [targetChartDerivK, lrCertificateCurve,
    lrDeterminantKChartDecode] using h

/-! ## Full chart AD used by the midpoint derivative pass -/

def onePlusVAD (box : CertificateBox) (payload : Payload) : IntervalAD :=
  IntervalAD.add (IntervalAD.const 1) (vAD box payload)

def yAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.divPositive (yNumeratorAD box) (physicalKAD box)

def meanYAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.mul (IntervalAD.const (1 / 2))
    (IntervalAD.add (IntervalAD.const 1) (yAD box))

def threeYPlusOneAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.add (IntervalAD.mul (IntervalAD.const 3) (yAD box))
    (IntervalAD.const 1)

def wAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  payload.omegaZero.evaluate terms (sAD box)

def omegaEAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  payload.omegaE.evaluate terms (sAD box) (eAD box)

def pwSKAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.add (omegaY0SKAD terms box payload)
    (IntervalAD.divPositive (omegaEAD terms box payload)
      (vAD box payload))

/-- The regular `Q(e)` AD node is already present inside the checked
`omega_s(e)` payload; reusing it avoids a second independent slope payload. -/
def qEAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  payload.omegaE.qAtY.evaluate terms (eAD box)

def gSKAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  let g0 := payload.g0.evaluate terms (vAD box payload)
  let qY0 := qY0SKAD terms box payload
  let qE := qEAD terms box payload
  IntervalAD.add (IntervalAD.add g0 qY0)
    (IntervalAD.divPositive qE (vAD box payload))

def bFlowAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.sub
    (IntervalAD.log terms payload.logOnePlusV (onePlusVAD box payload))
    (IntervalAD.mul (IntervalAD.const (1 / 2))
      (IntervalAD.log terms payload.logBE (beAD box)))

def d1AD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.add
    (IntervalAD.mul (IntervalAD.const (1 / 2))
      (IntervalAD.log terms payload.logMeanY (meanYAD box)))
    (IntervalAD.divPositive
      (IntervalAD.sub (yAD box) (IntervalAD.const 1))
      (threeYPlusOneAD box))

def psiSKAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.sub
    (IntervalAD.add (gSKAD terms box payload) (pwSKAD terms box payload))
    (IntervalAD.divPositive
      (IntervalAD.mul (IntervalAD.const 4) (wAD terms box payload))
      (onePlusVAD box payload))

def deltaAD (box : CertificateBox) (payload : Payload) : IntervalAD :=
  IntervalAD.divPositive
    (IntervalAD.sub (IntervalAD.const 1)
      (IntervalAD.mul (vAD box payload) (xAD box)))
    (onePlusVAD box payload)

def firstBracketAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  let fourWOver := IntervalAD.divPositive
    (IntervalAD.mul (IntervalAD.const 4) (wAD terms box payload))
    (onePlusVAD box payload)
  let psiSubG := IntervalAD.sub (pwSKAD terms box payload) fourWOver
  let firstInner := IntervalAD.add psiSubG
    (IntervalAD.mul (IntervalAD.const 4)
      (IntervalAD.mul (deltaAD box payload) (wAD terms box payload)))
  IntervalAD.add
    (IntervalAD.mul (bFlowAD terms box payload) firstInner)
    (IntervalAD.mul (d1AD terms box payload) (psiSKAD terms box payload))

def evaluateSKAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.divPositive (firstBracketAD terms box payload) (eAD box)

/-! ## Sharp historical `A/C` evaluator -/

/-- `A_s(y) = Q(y) + omega_s(y) - omega_s(0)`, differentiated through
the cancellation-free representation
`Q(b_s(y)) - s(1-y)Q'(b_s(y)) - omega_s(0)`. -/
noncomputable def aPrimitiveDeriv
    (s y s' y' : ℝ) : ℝ :=
  let b := lrCertificateB s y
  let b' := lrCertificateBDeriv s y s' y'
  lrCertificateQPrime b * b' -
    (s' * (1 - y) * lrCertificateQPrime b +
      s * (-y') * lrCertificateQPrime b +
      s * (1 - y) * (lrCertificateQSecond b * b')) -
    lrCertificateOmegaDeriv s 0 s' 0

noncomputable def cPrimitiveDeriv
    (s y s' y' : ℝ) : ℝ :=
  lrCertificateOmegaDeriv s y s' y' -
    lrCertificateOmegaDeriv s 0 s' 0

noncomputable def kappaDeriv (v v' : ℝ) : ℝ :=
  let numerator := (1 - v) ^ 2
  let numerator' := 2 * (1 - v) * (-v')
  let denominator := v * (1 + v)
  let denominator' := v' * (1 + v) + v * v'
  (numerator' * denominator - numerator * denominator') /
    denominator ^ 2

theorem aPrimitiveDeriv_identity (s y s' y' : ℝ) :
    aPrimitiveDeriv s y s' y' =
      lrCertificateQPrime y * y' +
        lrCertificateOmegaDeriv s y s' y' -
        lrCertificateOmegaDeriv s 0 s' 0 := by
  unfold aPrimitiveDeriv lrCertificateOmegaDeriv
  dsimp only
  ring

def y0BAd (box : CertificateBox) : IntervalAD :=
  lrCertificateBAD (sAD box) (y0AD box)

def y0QBAd (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  let b := y0BAd box
  IntervalAD.unary (payload.omegaY0.qAtB.enclosure terms)
    (payload.omegaY0.qPrimeAtB.enclosure terms) b

def y0QPrimeBAd (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  let b := y0BAd box
  let qPrimeB := payload.omegaY0.qPrimeAtB.enclosure terms
  IntervalAD.unary qPrimeB (lrQSecondCoarseEnclosure b.value) b

/-- Cancellation-free `A_s(y0)`.  No `Q(y0)` node is evaluated, so this
expression remains regular on a box whose `h` interval starts at zero. -/
def aY0SKAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.sub
    (IntervalAD.sub (y0QBAd terms box payload)
      (IntervalAD.mul
        (IntervalAD.mul (sAD box)
          (IntervalAD.sub (IntervalAD.const 1) (y0AD box)))
        (y0QPrimeBAd terms box payload)))
    (wAD terms box payload)

def eBAd (box : CertificateBox) : IntervalAD :=
  lrCertificateBAD (sAD box) (eAD box)

def eQBAd (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  payload.omegaE.qAtB.evaluate terms (eBAd box)

def eQPrimeBAd (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  payload.omegaE.qPrimeAtB.evaluate terms (eBAd box)

def aESKAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.sub
    (IntervalAD.sub (eQBAd terms box payload)
      (IntervalAD.mul
        (IntervalAD.mul (sAD box)
          (IntervalAD.sub (IntervalAD.const 1) (eAD box)))
        (eQPrimeBAd terms box payload)))
    (wAD terms box payload)

def cY0SKAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.sub (omegaY0SKAD terms box payload) (wAD terms box payload)

def cESKAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.sub (omegaEAD terms box payload) (wAD terms box payload)

def kappaAD (box : CertificateBox) (payload : Payload) : IntervalAD :=
  let v := vAD box payload
  let oneMinusV := IntervalAD.sub (IntervalAD.const 1) v
  let onePlusV := IntervalAD.add (IntervalAD.const 1) v
  IntervalAD.divPositive (IntervalAD.mul oneMinusV oneMinusV)
    (mulNonnegativeAD v onePlusV)

def sharpPsiAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.add
    (IntervalAD.add
      (payload.g0.evaluate terms (vAD box payload))
      (aY0SKAD terms box payload))
    (IntervalAD.add
      (IntervalAD.divPositive (aESKAD terms box payload)
        (vAD box payload))
      (IntervalAD.mul (kappaAD box payload) (wAD terms box payload)))

def sharpBaseAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.add
    (IntervalAD.add (cY0SKAD terms box payload)
      (IntervalAD.divPositive (cESKAD terms box payload)
        (vAD box payload)))
    (IntervalAD.mul
      (IntervalAD.add (kappaAD box payload)
        (IntervalAD.mul (IntervalAD.const 4) (deltaAD box payload)))
      (wAD terms box payload))

def sharpFirstBracketAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.add
    (IntervalAD.mul (bFlowAD terms box payload)
      (sharpBaseAD terms box payload))
    (IntervalAD.mul (d1AD terms box payload)
      (sharpPsiAD terms box payload))

def sharpEvaluateSKAD (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : IntervalAD :=
  IntervalAD.divPositive (sharpFirstBracketAD terms box payload) (eAD box)

def sharpEnclose (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  (sharpEvaluateSKAD terms box payload).value

/-- The whole-box AD pass encloses the genuine derivatives in the two
smooth chart coordinates.  Its third derivative field is intentionally
synthetic: only the value interval is used in the `h` direction. -/
theorem evaluateSKAD_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hcheck : payloadCheck box payload = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (evaluateSKAD terms box payload).value.Contains
        (lrFiniteDeterminantUpperKReplayTarget
          (lrDeterminantKChartDecode coordinate)) ∧
      (evaluateSKAD terms box payload).derivS.Contains
        (targetChartDerivS coordinate) ∧
      (evaluateSKAD terms box payload).derivK.Contains
        (targetChartDerivK coordinate) := by
  have hvalid : Valid box payload := by
    exact payloadCheck_sound hcheck
  let raw := lrDeterminantKChartDecode coordinate
  let eS := raw.k + raw.s * coordinate.k
  let eK := raw.s * coordinate.s
  let xS := -(raw.chi * eS)
  let xK := -(raw.chi * eK)
  let xH := -(2 * coordinate.chi * lrCertificateE raw)
  let y0S := raw.chi * eS
  let y0K := raw.chi * eK
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
  have hchiLower : (0 : ℚ) ≤ (physicalChiAD box).value.lower := by
    simpa [physicalChiAD, mulNonnegativeAD] using
      mul_nonneg hvalid.hNonnegative hvalid.hNonnegative
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
  have hy0Raw := mulNonnegativeAD_sound hchiLower hvalid.ePositive.le
    hchi he
  have hy0 : (y0AD box).Contains (lrCertificateY0 raw) y0S y0K
      (2 * coordinate.chi * lrCertificateE raw) := by
    convert hy0Raw using 1 <;>
      simp [y0AD, y0S, y0K, lrCertificateY0] <;> ring
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
  have hv : (vAD box payload).Contains (lrCertificateV raw) vS vK vH := by
    simpa [vAD, lrCertificateV, lrCertificateVDeriv, vS, vK, vH] using hvRaw

  have hsPoint : 0 < coordinate.s := by
    have hlo : (0 : ℝ) < ((sAD box).value.lower : ℝ) := by
      exact_mod_cast hvalid.sPositive
    exact hlo.trans_le hs.1.1
  have hKPoint : 0 < coordinate.k := by
    have hlo : (0 : ℝ) < ((ratioAD box).value.lower : ℝ) := by
      exact_mod_cast hvalid.ratioPositive
    exact hlo.trans_le hratio.1.1
  have hkPoint : 0 < raw.k := by
    dsimp [raw, lrDeterminantKChartDecode]
    exact mul_pos hsPoint hKPoint
  have hePoint : 0 < lrCertificateE raw := by
    have hlo : (0 : ℝ) < ((eAD box).value.lower : ℝ) := by
      exact_mod_cast hvalid.ePositive
    exact hlo.trans_le he.1.1
  have hvPoint : 0 < lrCertificateV raw := by
    have hlo : (0 : ℝ) < ((vAD box payload).value.lower : ℝ) := by
      exact_mod_cast hvalid.vPositive
    exact hlo.trans_le hv.1.1
  have honePlusVPoint : 1 + lrCertificateV raw ≠ 0 := by linarith

  have hy0S : 2 * lrCertificateY0 raw / coordinate.s = y0S := by
    dsimp [raw, eS, y0S]
    simp [lrCertificateY0, lrCertificateE,
      lrDeterminantKChartDecode]
    field_simp [hsPoint.ne']
    ring
  have hy0K : lrCertificateY0 raw / coordinate.k = y0K := by
    dsimp [raw, eK, y0K]
    simp [lrCertificateY0, lrCertificateE,
      lrDeterminantKChartDecode]
    field_simp [hKPoint.ne']

  rcases omegaY0SKAD_sound terms hvalid hcoordinate with
    ⟨omegaY0H, homegaY0Raw⟩
  have homegaY0 : (omegaY0SKAD terms box payload).Contains
      (lrCertificateOmega raw.s (lrCertificateY0 raw))
      (lrCertificateOmegaDeriv raw.s (lrCertificateY0 raw) 1 y0S)
      (lrCertificateOmegaDeriv raw.s (lrCertificateY0 raw) 0 y0K)
      omegaY0H := by
    rw [hy0S, hy0K] at homegaY0Raw
    simpa [raw] using homegaY0Raw
  have homegaE := payload.omegaE.sound terms hvalid.omegaECheck hsRaw he
  have homegaEdiv := IntervalAD.contains_divPositive hvalid.vPositive
    homegaE hv
  have hpwRaw := IntervalAD.contains_add homegaY0 homegaEdiv
  let pwH := omegaY0H +
    (lrCertificateOmegaDeriv raw.s (lrCertificateE raw) 0 0 *
          lrCertificateV raw -
        lrCertificateOmega raw.s (lrCertificateE raw) * vH) /
      lrCertificateV raw ^ 2
  have hpw : (pwSKAD terms box payload).Contains
      (lrCertificatePW raw)
      (lrCertificatePWDeriv raw 1 y0S eS vS)
      (lrCertificatePWDeriv raw 0 y0K eK vK) pwH := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [pwSKAD, omegaEAD, lrCertificatePW,
        lrCertificatePWValue] using hpwRaw.1
    · simpa [pwSKAD, omegaEAD, lrCertificatePWDeriv,
        lrCertificatePWValueDeriv] using hpwRaw.2.1
    · simpa [pwSKAD, omegaEAD, lrCertificatePWDeriv,
        lrCertificatePWValueDeriv] using hpwRaw.2.2.1
    · simpa [pwSKAD, omegaEAD, pwH] using hpwRaw.2.2.2

  have homegaEChecks :
      (payload.omegaE.qAtB.check
          (lrCertificateBAD (sAD box) (eAD box)).value = true ∧
        payload.omegaE.qAtY.check (eAD box).value = true) ∧
      payload.omegaE.qPrimeAtB.check
        (lrCertificateBAD (sAD box) (eAD box)).value = true := by
    simpa [LROmegaADCertificate.check] using hvalid.omegaECheck
  have hqE := payload.omegaE.qAtY.sound terms homegaEChecks.1.2 he
  have hqY0Parts := qY0SKAD_sound terms hvalid hcoordinate
  change
    (qY0SKAD terms box payload).value.Contains
        (lrCertificateQ (lrCertificateY0 raw)) ∧
      (qY0SKAD terms box payload).derivS.Contains
          (2 * (lrCertificateY0 raw *
            lrCertificateQPrime (lrCertificateY0 raw)) / coordinate.s) ∧
      (qY0SKAD terms box payload).derivK.Contains
        (lrCertificateY0 raw *
          lrCertificateQPrime (lrCertificateY0 raw) / coordinate.k)
    at hqY0Parts
  have hqY0 : (qY0SKAD terms box payload).Contains
      (lrCertificateQ (lrCertificateY0 raw))
      (lrCertificateQPrime (lrCertificateY0 raw) * y0S)
      (lrCertificateQPrime (lrCertificateY0 raw) * y0K) 0 := by
    refine ⟨hqY0Parts.1, ?_, ?_, ?_⟩
    · convert hqY0Parts.2.1 using 1
      rw [← hy0S]
      ring
    · convert hqY0Parts.2.2 using 1
      rw [← hy0K]
      ring
    · simp [qY0SKAD, qZeroY0SKAD, RationalEnclosure.point,
        RationalEnclosure.Contains]
  have hg0 := payload.g0.sound terms hvalid.g0Check hv
  have hqEdiv := IntervalAD.contains_divPositive hvalid.vPositive hqE hv
  have hgRaw := IntervalAD.contains_add
    (IntervalAD.contains_add hg0 hqY0) hqEdiv
  let gH := lrCertificateG0Prime (lrCertificateV raw) * vH + 0 +
    (lrCertificateQPrime (lrCertificateE raw) * 0 *
          lrCertificateV raw -
        lrCertificateQ (lrCertificateE raw) * vH) /
      lrCertificateV raw ^ 2
  have hg : (gSKAD terms box payload).Contains
      (lrCertificateGShape raw)
      (lrCertificateGShapeDeriv raw y0S eS vS)
      (lrCertificateGShapeDeriv raw y0K eK vK) gH := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [gSKAD, qEAD, lrCertificateGShape,
        lrCertificateGShapeValue] using hgRaw.1
    · simpa [gSKAD, qEAD, lrCertificateGShapeDeriv,
        lrCertificateGShapeValueDeriv] using hgRaw.2.1
    · simpa [gSKAD, qEAD, lrCertificateGShapeDeriv,
        lrCertificateGShapeValueDeriv] using hgRaw.2.2.1
    · simpa [gSKAD, qEAD, gH] using hgRaw.2.2.2

  have hw := payload.omegaZero.sound terms hvalid.omegaZeroCheck hsRaw
  have honePlusV := IntervalAD.contains_add (IntervalAD.contains_const 1) hv
  have honePlusVPositive : (0 : ℚ) <
      (onePlusVAD box payload).value.lower := by
    have honePositive : (0 : ℚ) < 1 := by norm_num
    have hvLowerPositive : (0 : ℚ) <
        (vAD box payload).value.lower := hvalid.vPositive
    change (0 : ℚ) < 1 + (vAD box payload).value.lower
    exact add_pos honePositive hvLowerPositive
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
  have hlogOnePlusCheck : payload.logOnePlusV.check
      (onePlusVAD box payload).value = true := by
    simpa [onePlusVAD, onePlusVI] using hvalid.logOnePlusVCheck
  have hlogOnePlus := IntervalAD.contains_log terms
    hlogOnePlusCheck honePlusV
  have hlogBE := IntervalAD.contains_log terms hvalid.logBECheck hbe
  have hbRaw := IntervalAD.contains_sub hlogOnePlus
    (IntervalAD.contains_mul (IntervalAD.contains_const (1 / 2)) hlogBE)
  let bH := vH / (1 + lrCertificateV raw)
  have hb : (bFlowAD terms box payload).Contains
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
  have hmeanRaw := IntervalAD.contains_mul
    (IntervalAD.contains_const (1 / 2))
    (IntervalAD.contains_add (IntervalAD.contains_const 1) hY)
  have hmean : (meanYAD box).Contains
      ((1 + lrDeterminantY raw) / 2)
      (yDeriv raw 1 eS / 2) (yDeriv raw 0 eK / 2) 0 := by
    convert hmeanRaw using 1 <;> simp [meanYAD] <;> ring
  have hlogMeanCheck : payload.logMeanY.check
      (meanYAD box).value = true := by
    simpa [meanYAD, meanYI, yAD, yI] using hvalid.logMeanYCheck
  have hlogMean := IntervalAD.contains_log terms
    hlogMeanCheck hmean
  have hthreeRaw := IntervalAD.contains_add
    (IntervalAD.contains_mul (IntervalAD.contains_const 3) hY)
    (IntervalAD.contains_const 1)
  have hthree : (threeYPlusOneAD box).Contains
      (3 * lrDeterminantY raw + 1)
      (3 * yDeriv raw 1 eS) (3 * yDeriv raw 0 eK) 0 := by
    convert hthreeRaw using 1 <;> simp [threeYPlusOneAD] <;> ring
  have hthreePositive : (0 : ℚ) <
      (threeYPlusOneAD box).value.lower := by
    simpa [threeYPlusOneAD, threeYPlusOneI, yAD, yI] using
      hvalid.threeYPlusOnePositive
  have hfrac := IntervalAD.contains_divPositive
    hthreePositive
    (IntervalAD.contains_sub hY (IntervalAD.contains_const 1)) hthree
  have hd1Raw := IntervalAD.contains_add
    (IntervalAD.contains_mul (IntervalAD.contains_const (1 / 2)) hlogMean)
    hfrac
  have hlogMeanParts :
      (0 : ℚ) < (meanYI box).lower ∧
      payload.logMeanY.lower.check (meanYI box).lower = true ∧
      payload.logMeanY.upper.check (meanYI box).upper = true := by
    simpa [RationalEnclosure.LogIntervalCertificate.check] using
      hvalid.logMeanYCheck
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
          hvalid.threeYPlusOnePositive)
    exact hlo.trans_le hthree.1.1
  have hd1 : (d1AD terms box payload).Contains
      (lrDeterminantD1 raw) (d1Deriv raw 1 eS)
      (d1Deriv raw 0 eK) 0 := by
    unfold d1AD d1Deriv lrDeterminantD1
    dsimp only
    convert hd1Raw using 1 <;>
      field_simp [hmeanPointPos.ne', hthreePointPos.ne'] <;> ring

  have hfourW := IntervalAD.contains_mul (IntervalAD.contains_const 4) hw
  have hfourWOver := IntervalAD.contains_divPositive honePlusVPositive
    hfourW honePlusV
  have hpsiRaw := IntervalAD.contains_sub
    (IntervalAD.contains_add hg hpw) hfourWOver
  let psiH := gH + pwH -
    ((4 * lrCertificateOmegaDeriv raw.s 0 0 0) *
          (1 + lrCertificateV raw) -
        4 * lrCertificateW raw * vH) /
      (1 + lrCertificateV raw) ^ 2
  have hpsiHDef :
      psiH = gH + pwH -
        ((4 * lrCertificateOmegaDeriv raw.s 0 0 0) *
              (1 + lrCertificateV raw) -
            4 * lrCertificateW raw * vH) /
          (1 + lrCertificateV raw) ^ 2 := by
    rfl
  have hpsi : (psiSKAD terms box payload).Contains
      (lrDeterminantPsi raw) (psiDeriv raw 1 y0S eS vS)
      (psiDeriv raw 0 y0K eK vK) psiH := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [psiSKAD, lrDeterminantPsi] using hpsiRaw.1
    · simpa [psiSKAD, psiDeriv] using hpsiRaw.2.1
    · simpa [psiSKAD, psiDeriv] using hpsiRaw.2.2.1
    · simpa [psiSKAD, hpsiHDef] using hpsiRaw.2.2.2
  have hdeltaRaw := IntervalAD.contains_divPositive honePlusVPositive
    (IntervalAD.contains_sub (IntervalAD.contains_const 1)
      (IntervalAD.contains_mul hv hx)) honePlusV
  let deltaH := deltaDeriv raw xH vH
  have hdelta : (deltaAD box payload).Contains
      (lrDeterminantDelta raw) (deltaDeriv raw xS vS)
      (deltaDeriv raw xK vK) deltaH := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [deltaAD, lrDeterminantDelta] using hdeltaRaw.1
    · simpa [deltaAD, deltaDeriv] using hdeltaRaw.2.1
    · simpa [deltaAD, deltaDeriv] using hdeltaRaw.2.2.1
    · simpa [deltaAD, deltaDeriv, deltaH] using hdeltaRaw.2.2.2

  have hpsiSubG := IntervalAD.contains_sub hpw hfourWOver
  have hinner := IntervalAD.contains_add hpsiSubG
    (IntervalAD.contains_mul (IntervalAD.contains_const 4)
      (IntervalAD.contains_mul hdelta hw))
  have hfirstRaw := IntervalAD.contains_add
    (IntervalAD.contains_mul hb hinner)
    (IntervalAD.contains_mul hd1 hpsi)
  let firstH :=
    bH * (lrDeterminantPsi raw - lrCertificateGShape raw +
        4 * lrDeterminantDelta raw * lrCertificateW raw) +
      lrCertificateBFlow raw *
        (psiH - gH +
          4 * (deltaH * lrCertificateW raw +
            lrDeterminantDelta raw *
              lrCertificateOmegaDeriv raw.s 0 0 0)) +
      0 * lrDeterminantPsi raw + lrDeterminantD1 raw * psiH
  have hfirst : (firstBracketAD terms box payload).Contains
      (lrDeterminantFirstBracket
        (lrCertificateBFlow raw) (lrDeterminantD1 raw)
        (lrCertificateGShape raw) (lrDeterminantPsi raw)
        (lrDeterminantDelta raw) (lrCertificateW raw))
      (firstBracketDeriv raw 1 y0S eS xS vS)
      (firstBracketDeriv raw 0 y0K eK xK vK) firstH := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · convert hfirstRaw.1 using 1 <;>
        simp [firstBracketAD, lrDeterminantFirstBracket,
          lrDeterminantPsi, lrCertificateW] <;> ring_nf <;> simp
    · convert hfirstRaw.2.1 using 1 <;>
        simp [firstBracketAD, firstBracketDeriv, psiDeriv,
          lrDeterminantPsi, lrCertificateW] <;> ring
    · convert hfirstRaw.2.2.1 using 1 <;>
        simp [firstBracketAD, firstBracketDeriv, psiDeriv,
          lrDeterminantPsi, lrCertificateW] <;> ring
    · convert hfirstRaw.2.2.2 using 1
      simp [firstBracketAD, firstH, hpsiHDef, lrDeterminantPsi,
        lrCertificateW]
      field_simp [honePlusVPoint]
      ring
  have hresult := IntervalAD.contains_divPositive hvalid.ePositive hfirst he
  refine ⟨?_, ?_, ?_⟩
  · simpa [evaluateSKAD, lrFiniteDeterminantUpperKReplayTarget] using hresult.1
  · simpa [evaluateSKAD, targetChartDerivS, targetRawDeriv,
      raw, eS, xS, y0S, vS] using hresult.2.1
  · simpa [evaluateSKAD, targetChartDerivK, targetRawDeriv,
      raw, eK, xK, y0K, vK] using hresult.2.2.1

/-! The two primitive soundness lemmas below expose the exact historical
cancellations.  In particular, `aY0SKAD_sound` never asks for a scalar
enclosure of `Q'` at `y0 = 0`; all differentiated `Q` nodes are evaluated
at `b_s(y0) ≥ s > 0`. -/

theorem aY0SKAD_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hvalid : Valid box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    let raw := lrDeterminantKChartDecode coordinate
    let yS := 2 * lrCertificateY0 raw / coordinate.s
    let yK := lrCertificateY0 raw / coordinate.k
    let yH := 2 * coordinate.chi * lrCertificateE raw
    (aY0SKAD terms box payload).Contains
      (aPrimitive raw.s (lrCertificateY0 raw))
      (aPrimitiveDeriv raw.s (lrCertificateY0 raw) 1 yS)
      (aPrimitiveDeriv raw.s (lrCertificateY0 raw) 0 yK)
      (aPrimitiveDeriv raw.s (lrCertificateY0 raw) 0 yH) := by
  dsimp only
  let raw := lrDeterminantKChartDecode coordinate
  let eS := raw.k + raw.s * coordinate.k
  let eK := raw.s * coordinate.s
  let yS := 2 * lrCertificateY0 raw / coordinate.s
  let yK := lrCertificateY0 raw / coordinate.k
  let yH := 2 * coordinate.chi * lrCertificateE raw
  let s := sAD box
  let y := y0AD box
  let b := y0BAd box
  let qPrimeB := payload.omegaY0.qPrimeAtB.enclosure terms
  let qB := y0QBAd terms box payload
  let qPrimeBAD := y0QPrimeBAd terms box payload
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains coordinate.s from
      ⟨hcoordinate.1, hcoordinate.2.1⟩)
  have hsRaw : s.Contains raw.s 1 0 0 := by
    simpa [s, raw, lrDeterminantKChartDecode] using hs
  have hratio := IntervalAD.contains_variableK
    (show box.kInterval.Contains coordinate.k from
      ⟨hcoordinate.2.2.1, hcoordinate.2.2.2.1⟩)
  have hsPoint : 0 < coordinate.s := by
    have hlo : (0 : ℝ) < ((sAD box).value.lower : ℝ) := by
      exact_mod_cast hvalid.sPositive
    exact hlo.trans_le hs.1.1
  have hKPoint : 0 < coordinate.k := by
    have hlo : (0 : ℝ) < ((ratioAD box).value.lower : ℝ) := by
      exact_mod_cast hvalid.ratioPositive
    exact hlo.trans_le hratio.1.1
  have hsNe : coordinate.s ≠ 0 := ne_of_gt hsPoint
  have hKNe : coordinate.k ≠ 0 := ne_of_gt hKPoint
  have hyNamed := y0AD_sound hvalid hcoordinate
  change (y0AD box).Contains (lrCertificateY0 raw)
    (raw.chi * eS) (raw.chi * eK)
    (2 * coordinate.chi * lrCertificateE raw) at hyNamed
  have hy0S : raw.chi * eS = yS := by
    dsimp [raw, eS, yS]
    simp [lrCertificateY0, lrCertificateE,
      lrDeterminantKChartDecode]
    field_simp [hsNe]
    ring
  have hy0K : raw.chi * eK = yK := by
    dsimp [raw, eK, yK]
    simp [lrCertificateY0, lrCertificateE,
      lrDeterminantKChartDecode]
    field_simp [hKNe]
  rw [hy0S, hy0K] at hyNamed
  have hy : y.Contains (lrCertificateY0 raw) yS yK yH := by
    simpa [y, yH] using hyNamed
  have hb := lrCertificateBAD_sound hsRaw hy
  have hparts :
      (payload.omegaY0.qAtB.check b.value = true ∧
        payload.omegaY0.qAtY.check y.value = true) ∧
        payload.omegaY0.qPrimeAtB.check b.value = true := by
    simpa [LROmegaZeroIntervalCertificate.check, s, y, b,
      y0BAd] using hvalid.omegaY0Check
  have hqBValue := payload.omegaY0.qAtB.sound terms hparts.1.1 hb.1
  have hqPrimeBValue := payload.omegaY0.qPrimeAtB.sound terms
    hparts.2 hb.1
  have hqB : qB.Contains
      (lrCertificateQ
        (lrCertificateB raw.s (lrCertificateY0 raw)))
      (lrCertificateQPrime
          (lrCertificateB raw.s (lrCertificateY0 raw)) *
        lrCertificateBDeriv raw.s (lrCertificateY0 raw) 1 yS)
      (lrCertificateQPrime
          (lrCertificateB raw.s (lrCertificateY0 raw)) *
        lrCertificateBDeriv raw.s (lrCertificateY0 raw) 0 yK)
      (lrCertificateQPrime
          (lrCertificateB raw.s (lrCertificateY0 raw)) *
        lrCertificateBDeriv raw.s (lrCertificateY0 raw) 0 yH) := by
    exact IntervalAD.contains_unary hqBValue hqPrimeBValue hb
  have hcoarse : lrQSecondCoarseCheck b.value = true := by
    have hraw :
        decide ((0 : ℚ) < b.value.lower ∧ b.value.lower ≤ b.value.upper ∧
          b.value.upper < 1) = true ∧
        payload.omegaY0.qPrimeAtB.lowerEndpoint.primeCheck
          b.value.lower = true ∧
        payload.omegaY0.qPrimeAtB.upperEndpoint.primeCheck
          b.value.upper = true := by
      simpa [LRQPrimeIntervalCertificate.check, and_assoc] using hparts.2
    simpa [lrQSecondCoarseCheck] using hraw.1
  have hqSecondB := lrQSecondCoarseEnclosure_sound hcoarse hb.1
  have hqPrimeB : qPrimeBAD.Contains
      (lrCertificateQPrime
        (lrCertificateB raw.s (lrCertificateY0 raw)))
      (lrCertificateQSecond
          (lrCertificateB raw.s (lrCertificateY0 raw)) *
        lrCertificateBDeriv raw.s (lrCertificateY0 raw) 1 yS)
      (lrCertificateQSecond
          (lrCertificateB raw.s (lrCertificateY0 raw)) *
        lrCertificateBDeriv raw.s (lrCertificateY0 raw) 0 yK)
      (lrCertificateQSecond
          (lrCertificateB raw.s (lrCertificateY0 raw)) *
        lrCertificateBDeriv raw.s (lrCertificateY0 raw) 0 yH) := by
    exact IntervalAD.contains_unary hqPrimeBValue hqSecondB hb
  have honeMinusY := IntervalAD.contains_sub
    (IntervalAD.contains_const 1) hy
  have hfactor := IntervalAD.contains_mul hsRaw honeMinusY
  have hcorrection := IntervalAD.contains_mul hfactor hqPrimeB
  have hw := payload.omegaZero.sound terms hvalid.omegaZeroCheck hsRaw
  have hresult := IntervalAD.contains_sub
    (IntervalAD.contains_sub hqB hcorrection) hw
  convert hresult using 1 <;>
    simp [aY0SKAD, y0QBAd, y0QPrimeBAd, y0BAd, qB, qPrimeBAD,
      aPrimitive, aPrimitiveDeriv, lrCertificateOmega,
      lrCertificateW, lrCertificateBDeriv, raw, yS, yK, yH] <;> ring

theorem aESKAD_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hvalid : Valid box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    let raw := lrDeterminantKChartDecode coordinate
    let eS := raw.k + raw.s * coordinate.k
    let eK := raw.s * coordinate.s
    (aESKAD terms box payload).Contains
      (aPrimitive raw.s (lrCertificateE raw))
      (aPrimitiveDeriv raw.s (lrCertificateE raw) 1 eS)
      (aPrimitiveDeriv raw.s (lrCertificateE raw) 0 eK)
      (aPrimitiveDeriv raw.s (lrCertificateE raw) 0 0) := by
  dsimp only
  let raw := lrDeterminantKChartDecode coordinate
  let eS := raw.k + raw.s * coordinate.k
  let eK := raw.s * coordinate.s
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains coordinate.s from
      ⟨hcoordinate.1, hcoordinate.2.1⟩)
  have hsRaw : (sAD box).Contains raw.s 1 0 0 := by
    simpa [raw, lrDeterminantKChartDecode] using hs
  have hratio := IntervalAD.contains_variableK
    (show box.kInterval.Contains coordinate.k from
      ⟨hcoordinate.2.2.1, hcoordinate.2.2.2.1⟩)
  have hkLower : (0 : ℚ) ≤ (physicalKAD box).value.lower := by
    simpa [physicalKAD, mulNonnegativeAD] using
      mul_nonneg hvalid.sPositive.le hvalid.ratioPositive.le
  have hk := mulNonnegativeAD_sound hvalid.sPositive.le
    hvalid.ratioPositive.le hs hratio
  have heRaw := mulNonnegativeAD_sound hvalid.sPositive.le hkLower hs hk
  have he : (eAD box).Contains (lrCertificateE raw) eS eK 0 := by
    convert heRaw using 1 <;>
      simp [eAD, physicalKAD, sAD, ratioAD, raw, eS, eK,
        lrCertificateE, lrDeterminantKChartDecode] <;> ring
  have hb := lrCertificateBAD_sound hsRaw he
  have hparts :
      (payload.omegaE.qAtB.check (eBAd box).value = true ∧
        payload.omegaE.qAtY.check (eAD box).value = true) ∧
      payload.omegaE.qPrimeAtB.check (eBAd box).value = true := by
    simpa [LROmegaADCertificate.check, eBAd] using hvalid.omegaECheck
  have hqB := payload.omegaE.qAtB.sound terms hparts.1.1 hb
  have hqPrimeB := payload.omegaE.qPrimeAtB.sound terms hparts.2 hb
  have honeMinusE := IntervalAD.contains_sub
    (IntervalAD.contains_const 1) he
  have hfactor := IntervalAD.contains_mul hsRaw honeMinusE
  have hcorrection := IntervalAD.contains_mul hfactor hqPrimeB
  have hw := payload.omegaZero.sound terms hvalid.omegaZeroCheck hsRaw
  have hresult := IntervalAD.contains_sub
    (IntervalAD.contains_sub hqB hcorrection) hw
  convert hresult using 1 <;>
    simp [aESKAD, eQBAd, eQPrimeBAd, eBAd, aPrimitive,
      aPrimitiveDeriv, lrCertificateOmega, lrCertificateW,
      lrCertificateBDeriv, raw, eS, eK] <;> ring

theorem cY0SKAD_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hvalid : Valid box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    let raw := lrDeterminantKChartDecode coordinate
    let yS := 2 * lrCertificateY0 raw / coordinate.s
    let yK := lrCertificateY0 raw / coordinate.k
    ∃ derivH : ℝ, (cY0SKAD terms box payload).Contains
      (cPrimitive raw.s (lrCertificateY0 raw))
      (cPrimitiveDeriv raw.s (lrCertificateY0 raw) 1 yS)
      (cPrimitiveDeriv raw.s (lrCertificateY0 raw) 0 yK) derivH := by
  dsimp only
  let raw := lrDeterminantKChartDecode coordinate
  let yS := 2 * lrCertificateY0 raw / coordinate.s
  let yK := lrCertificateY0 raw / coordinate.k
  rcases omegaY0SKAD_sound terms hvalid hcoordinate with
    ⟨omegaH, homega⟩
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains coordinate.s from
      ⟨hcoordinate.1, hcoordinate.2.1⟩)
  have hsRaw : (sAD box).Contains raw.s 1 0 0 := by
    simpa [raw, lrDeterminantKChartDecode] using hs
  have hw := payload.omegaZero.sound terms hvalid.omegaZeroCheck hsRaw
  have hresult := IntervalAD.contains_sub homega hw
  let derivH := omegaH - lrCertificateOmegaDeriv raw.s 0 0 0
  refine ⟨derivH, ?_⟩
  convert hresult using 1 <;>
    simp [cY0SKAD, cPrimitive, cPrimitiveDeriv, raw, yS, yK,
      derivH, lrCertificateW] <;> ring

theorem cESKAD_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hvalid : Valid box payload)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    let raw := lrDeterminantKChartDecode coordinate
    let eS := raw.k + raw.s * coordinate.k
    let eK := raw.s * coordinate.s
    (cESKAD terms box payload).Contains
      (cPrimitive raw.s (lrCertificateE raw))
      (cPrimitiveDeriv raw.s (lrCertificateE raw) 1 eS)
      (cPrimitiveDeriv raw.s (lrCertificateE raw) 0 eK)
      (cPrimitiveDeriv raw.s (lrCertificateE raw) 0 0) := by
  dsimp only
  let raw := lrDeterminantKChartDecode coordinate
  let eS := raw.k + raw.s * coordinate.k
  let eK := raw.s * coordinate.s
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains coordinate.s from
      ⟨hcoordinate.1, hcoordinate.2.1⟩)
  have hsRaw : (sAD box).Contains raw.s 1 0 0 := by
    simpa [raw, lrDeterminantKChartDecode] using hs
  have hratio := IntervalAD.contains_variableK
    (show box.kInterval.Contains coordinate.k from
      ⟨hcoordinate.2.2.1, hcoordinate.2.2.2.1⟩)
  have hkLower : (0 : ℚ) ≤ (physicalKAD box).value.lower := by
    simpa [physicalKAD, mulNonnegativeAD] using
      mul_nonneg hvalid.sPositive.le hvalid.ratioPositive.le
  have hk := mulNonnegativeAD_sound hvalid.sPositive.le
    hvalid.ratioPositive.le hs hratio
  have heRaw := mulNonnegativeAD_sound hvalid.sPositive.le hkLower hs hk
  have he : (eAD box).Contains (lrCertificateE raw) eS eK 0 := by
    convert heRaw using 1 <;>
      simp [eAD, physicalKAD, sAD, ratioAD, raw, eS, eK,
        lrCertificateE, lrDeterminantKChartDecode] <;> ring
  have homega := payload.omegaE.sound terms hvalid.omegaECheck hsRaw he
  have hw := payload.omegaZero.sound terms hvalid.omegaZeroCheck hsRaw
  have hresult := IntervalAD.contains_sub homega hw
  convert hresult using 1 <;>
    simp [cESKAD, omegaEAD, cPrimitive, cPrimitiveDeriv,
      raw, eS, eK, lrCertificateW] <;> ring

theorem kappaAD_sound {box : CertificateBox} {payload : Payload}
    (hvalid : Valid box payload)
    {v vS vK vH : ℝ}
    (hv : (vAD box payload).Contains v vS vK vH) :
    (kappaAD box payload).Contains (kappaV v)
      (kappaDeriv v vS) (kappaDeriv v vK) (kappaDeriv v vH) := by
  let vNode := vAD box payload
  let oneMinusV := IntervalAD.sub (IntervalAD.const 1) vNode
  let onePlusV := IntervalAD.add (IntervalAD.const 1) vNode
  have honeMinus := IntervalAD.contains_sub (IntervalAD.contains_const 1) hv
  have honePlus := IntervalAD.contains_add (IntervalAD.contains_const 1) hv
  have honePlusLower : (0 : ℚ) ≤ onePlusV.value.lower := by
    dsimp [onePlusV, vNode, IntervalAD.add, IntervalAD.const,
      RationalEnclosure.add, RationalEnclosure.point]
    linarith [hvalid.vPositive]
  have hdenom := mulNonnegativeAD_sound hvalid.vPositive.le
    honePlusLower hv honePlus
  have hdenomPositive : (0 : ℚ) <
      (mulNonnegativeAD vNode onePlusV).value.lower := by
    dsimp [mulNonnegativeAD, RationalEnclosure.mulNonnegative,
      onePlusV, vNode, IntervalAD.add, IntervalAD.const,
      RationalEnclosure.add, RationalEnclosure.point]
    exact mul_pos hvalid.vPositive
      (add_pos (by norm_num) hvalid.vPositive)
  have hnumerator := IntervalAD.contains_mul honeMinus honeMinus
  have hresult := IntervalAD.contains_divPositive hdenomPositive
    hnumerator hdenom
  unfold kappaAD kappaV kappaDeriv
  dsimp only
  convert hresult using 1 <;> ring

theorem sharpEvaluateSKAD_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hcheck : payloadCheck box payload = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (sharpEvaluateSKAD terms box payload).value.Contains
        (lrFiniteDeterminantUpperKReplayTarget
          (lrDeterminantKChartDecode coordinate)) ∧
      (sharpEvaluateSKAD terms box payload).derivS.Contains
        (targetChartDerivS coordinate) ∧
      (sharpEvaluateSKAD terms box payload).derivK.Contains
        (targetChartDerivK coordinate) := by
  have hvalid : Valid box payload := by
    exact payloadCheck_sound hcheck
  let raw := lrDeterminantKChartDecode coordinate
  let eS := raw.k + raw.s * coordinate.k
  let eK := raw.s * coordinate.s
  let xS := -(raw.chi * eS)
  let xK := -(raw.chi * eK)
  let xH := -(2 * coordinate.chi * lrCertificateE raw)
  let y0S := raw.chi * eS
  let y0K := raw.chi * eK
  let y0H := 2 * coordinate.chi * lrCertificateE raw
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
  have hchiLower : (0 : ℚ) ≤ (physicalChiAD box).value.lower := by
    simpa [physicalChiAD, mulNonnegativeAD] using
      mul_nonneg hvalid.hNonnegative hvalid.hNonnegative
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
  have hv : (vAD box payload).Contains (lrCertificateV raw) vS vK vH := by
    simpa [vAD, lrCertificateV, lrCertificateVDeriv, vS, vK, vH] using hvRaw
  have hsPoint : 0 < coordinate.s := by
    have hlo : (0 : ℝ) < ((sAD box).value.lower : ℝ) := by
      exact_mod_cast hvalid.sPositive
    exact hlo.trans_le hs.1.1
  have hKPoint : 0 < coordinate.k := by
    have hlo : (0 : ℝ) < ((ratioAD box).value.lower : ℝ) := by
      exact_mod_cast hvalid.ratioPositive
    exact hlo.trans_le hratio.1.1
  have hkPoint : 0 < raw.k := by
    dsimp [raw, lrDeterminantKChartDecode]
    exact mul_pos hsPoint hKPoint
  have hePoint : 0 < lrCertificateE raw := by
    have hlo : (0 : ℝ) < ((eAD box).value.lower : ℝ) := by
      exact_mod_cast hvalid.ePositive
    exact hlo.trans_le he.1.1
  have hvPoint : 0 < lrCertificateV raw := by
    have hlo : (0 : ℝ) < ((vAD box payload).value.lower : ℝ) := by
      exact_mod_cast hvalid.vPositive
    exact hlo.trans_le hv.1.1
  have honePlusVPoint : 1 + lrCertificateV raw ≠ 0 := by linarith
  have hy0S : 2 * lrCertificateY0 raw / coordinate.s = y0S := by
    dsimp [raw, eS, y0S]
    simp [lrCertificateY0, lrCertificateE,
      lrDeterminantKChartDecode]
    field_simp [hsPoint.ne']
    ring
  have hy0K : lrCertificateY0 raw / coordinate.k = y0K := by
    dsimp [raw, eK, y0K]
    simp [lrCertificateY0, lrCertificateE,
      lrDeterminantKChartDecode]
    field_simp [hKPoint.ne']

  have haY0Raw := aY0SKAD_sound terms hvalid hcoordinate
  change (aY0SKAD terms box payload).Contains
    (aPrimitive raw.s (lrCertificateY0 raw))
    (aPrimitiveDeriv raw.s (lrCertificateY0 raw) 1
      (2 * lrCertificateY0 raw / coordinate.s))
    (aPrimitiveDeriv raw.s (lrCertificateY0 raw) 0
      (lrCertificateY0 raw / coordinate.k))
    (aPrimitiveDeriv raw.s (lrCertificateY0 raw) 0
      (2 * coordinate.chi * lrCertificateE raw)) at haY0Raw
  have haY0 : (aY0SKAD terms box payload).Contains
      (aPrimitive raw.s (lrCertificateY0 raw))
      (aPrimitiveDeriv raw.s (lrCertificateY0 raw) 1 y0S)
      (aPrimitiveDeriv raw.s (lrCertificateY0 raw) 0 y0K)
      (aPrimitiveDeriv raw.s (lrCertificateY0 raw) 0 y0H) := by
    rw [hy0S, hy0K] at haY0Raw
    simpa [raw, y0H] using haY0Raw
  have haE := aESKAD_sound terms hvalid hcoordinate
  rcases cY0SKAD_sound terms hvalid hcoordinate with ⟨cY0H, hcY0Raw⟩
  have hcY0 : (cY0SKAD terms box payload).Contains
      (cPrimitive raw.s (lrCertificateY0 raw))
      (cPrimitiveDeriv raw.s (lrCertificateY0 raw) 1 y0S)
      (cPrimitiveDeriv raw.s (lrCertificateY0 raw) 0 y0K) cY0H := by
    rw [hy0S, hy0K] at hcY0Raw
    simpa [raw] using hcY0Raw
  have hcE := cESKAD_sound terms hvalid hcoordinate
  have hg0 := payload.g0.sound terms hvalid.g0Check hv
  have hw := payload.omegaZero.sound terms hvalid.omegaZeroCheck hsRaw
  have hkappa := kappaAD_sound hvalid hv
  have haEOver := IntervalAD.contains_divPositive hvalid.vPositive haE hv
  have hkappaW := IntervalAD.contains_mul hkappa hw
  have hsharpPsiRaw := IntervalAD.contains_add
    (IntervalAD.contains_add hg0 haY0)
    (IntervalAD.contains_add haEOver hkappaW)
  let sharpPsiH :=
    lrCertificateG0Prime (lrCertificateV raw) * vH +
      aPrimitiveDeriv raw.s (lrCertificateY0 raw) 0 y0H +
      ((aPrimitiveDeriv raw.s (lrCertificateE raw) 0 0 *
            lrCertificateV raw -
          aPrimitive raw.s (lrCertificateE raw) * vH) /
        lrCertificateV raw ^ 2 +
        (kappaDeriv (lrCertificateV raw) vH * lrCertificateW raw +
          kappaV (lrCertificateV raw) *
            lrCertificateOmegaDeriv raw.s 0 0 0))
  have hsharpPsi : (sharpPsiAD terms box payload).Contains
      (lrDeterminantPsi raw) (psiDeriv raw 1 y0S eS vS)
      (psiDeriv raw 0 y0K eK vK) sharpPsiH := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hid := psi_eq_aPrimitives
        (point := raw) hvPoint.ne' honePlusVPoint
      rw [hid]
      convert hsharpPsiRaw.1 using 1 <;>
        simp [sharpPsiAD, lrCertificateW] <;> ring
    · convert hsharpPsiRaw.2.1 using 1 <;>
        simp [sharpPsiAD, psiDeriv, aPrimitiveDeriv_identity,
          aPrimitive, kappaV, kappaDeriv, lrCertificateGShapeDeriv,
          lrCertificateGShapeValueDeriv, lrCertificatePWDeriv,
          lrCertificatePWValueDeriv, lrCertificateW] <;>
        field_simp [hvPoint.ne', honePlusVPoint] <;> ring
    · convert hsharpPsiRaw.2.2.1 using 1 <;>
        simp [sharpPsiAD, psiDeriv, aPrimitiveDeriv_identity,
          aPrimitive, kappaV, kappaDeriv, lrCertificateGShapeDeriv,
          lrCertificateGShapeValueDeriv, lrCertificatePWDeriv,
          lrCertificatePWValueDeriv, lrCertificateW] <;>
        field_simp [hvPoint.ne', honePlusVPoint] <;> ring
    · simpa [sharpPsiAD, sharpPsiH] using hsharpPsiRaw.2.2.2

  have hcEOver := IntervalAD.contains_divPositive hvalid.vPositive hcE hv
  have honePlusV := IntervalAD.contains_add (IntervalAD.contains_const 1) hv
  have honePlusVPositive : (0 : ℚ) <
      (onePlusVAD box payload).value.lower := by
    have honePositive : (0 : ℚ) < 1 := by norm_num
    have hvLowerPositive : (0 : ℚ) <
        (vAD box payload).value.lower := hvalid.vPositive
    change (0 : ℚ) < 1 + (vAD box payload).value.lower
    exact add_pos honePositive hvLowerPositive
  have hdeltaRaw := IntervalAD.contains_divPositive honePlusVPositive
    (IntervalAD.contains_sub (IntervalAD.contains_const 1)
      (IntervalAD.contains_mul hv hx)) honePlusV
  let deltaH := deltaDeriv raw xH vH
  have hdelta : (deltaAD box payload).Contains
      (lrDeterminantDelta raw) (deltaDeriv raw xS vS)
      (deltaDeriv raw xK vK) deltaH := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [deltaAD, lrDeterminantDelta] using hdeltaRaw.1
    · simpa [deltaAD, deltaDeriv] using hdeltaRaw.2.1
    · simpa [deltaAD, deltaDeriv] using hdeltaRaw.2.2.1
    · simpa [deltaAD, deltaDeriv, deltaH] using hdeltaRaw.2.2.2
  have hkapPlusDelta := IntervalAD.contains_add hkappa
    (IntervalAD.contains_mul (IntervalAD.contains_const 4) hdelta)
  have hkapDeltaW := IntervalAD.contains_mul hkapPlusDelta hw
  have hsharpBaseRaw := IntervalAD.contains_add
    (IntervalAD.contains_add hcY0 hcEOver) hkapDeltaW
  let sharpBaseH :=
    cY0H +
      ((cPrimitiveDeriv raw.s (lrCertificateE raw) 0 0 *
            lrCertificateV raw -
          cPrimitive raw.s (lrCertificateE raw) * vH) /
        lrCertificateV raw ^ 2) +
      ((kappaDeriv (lrCertificateV raw) vH + 4 * deltaH) *
          lrCertificateW raw +
        (kappaV (lrCertificateV raw) +
            4 * lrDeterminantDelta raw) *
          lrCertificateOmegaDeriv raw.s 0 0 0)
  have hsharpBase : (sharpBaseAD terms box payload).Contains
      (lrDeterminantPsi raw - lrCertificateGShape raw +
        4 * lrDeterminantDelta raw * lrCertificateW raw)
      (psiDeriv raw 1 y0S eS vS -
        lrCertificateGShapeDeriv raw y0S eS vS +
        4 * (deltaDeriv raw xS vS * lrCertificateW raw +
          lrDeterminantDelta raw *
            lrCertificateOmegaDeriv raw.s 0 1 0))
      (psiDeriv raw 0 y0K eK vK -
        lrCertificateGShapeDeriv raw y0K eK vK +
        4 * (deltaDeriv raw xK vK * lrCertificateW raw +
          lrDeterminantDelta raw *
            lrCertificateOmegaDeriv raw.s 0 0 0)) sharpBaseH := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hid := psi_sub_gShape_eq_cPrimitives
        (point := raw) hvPoint.ne' honePlusVPoint
      rw [hid]
      convert hsharpBaseRaw.1 using 1 <;>
        simp [sharpBaseAD, lrCertificateW] <;> ring
    · convert hsharpBaseRaw.2.1 using 1 <;>
        simp [sharpBaseAD, psiDeriv, aPrimitiveDeriv_identity,
          cPrimitive, cPrimitiveDeriv, kappaV, kappaDeriv,
          lrCertificateGShapeDeriv, lrCertificateGShapeValueDeriv,
          lrCertificatePWDeriv, lrCertificatePWValueDeriv,
          lrCertificateW] <;>
        field_simp [hvPoint.ne', honePlusVPoint] <;> ring
    · convert hsharpBaseRaw.2.2.1 using 1 <;>
        simp [sharpBaseAD, psiDeriv, aPrimitiveDeriv_identity,
          cPrimitive, cPrimitiveDeriv, kappaV, kappaDeriv,
          lrCertificateGShapeDeriv, lrCertificateGShapeValueDeriv,
          lrCertificatePWDeriv, lrCertificatePWValueDeriv,
          lrCertificateW] <;>
        field_simp [hvPoint.ne', honePlusVPoint] <;> ring
    · simpa [sharpBaseAD, sharpBaseH] using hsharpBaseRaw.2.2.2

  /- The remaining two factors do not participate in the dangerous
  `Q(y₀)`/`omega(y₀)` cancellation.  Reuse the regular, checked AD
  nodes for `B` and `D₁`, and only combine them with the sharp primitive
  enclosures at the final product rule. -/
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
  have hlogOnePlusCheck : payload.logOnePlusV.check
      (onePlusVAD box payload).value = true := by
    simpa [onePlusVAD, onePlusVI] using hvalid.logOnePlusVCheck
  have hlogOnePlus := IntervalAD.contains_log terms
    hlogOnePlusCheck honePlusV
  have hlogBE := IntervalAD.contains_log terms hvalid.logBECheck hbe
  have hbRaw := IntervalAD.contains_sub hlogOnePlus
    (IntervalAD.contains_mul (IntervalAD.contains_const (1 / 2)) hlogBE)
  let bH := vH / (1 + lrCertificateV raw)
  have hb : (bFlowAD terms box payload).Contains
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
  have hmeanRaw := IntervalAD.contains_mul
    (IntervalAD.contains_const (1 / 2))
    (IntervalAD.contains_add (IntervalAD.contains_const 1) hY)
  have hmean : (meanYAD box).Contains
      ((1 + lrDeterminantY raw) / 2)
      (yDeriv raw 1 eS / 2) (yDeriv raw 0 eK / 2) 0 := by
    convert hmeanRaw using 1 <;> simp [meanYAD] <;> ring
  have hlogMeanCheck : payload.logMeanY.check
      (meanYAD box).value = true := by
    simpa [meanYAD, meanYI, yAD, yI] using hvalid.logMeanYCheck
  have hlogMean := IntervalAD.contains_log terms
    hlogMeanCheck hmean
  have hthreeRaw := IntervalAD.contains_add
    (IntervalAD.contains_mul (IntervalAD.contains_const 3) hY)
    (IntervalAD.contains_const 1)
  have hthree : (threeYPlusOneAD box).Contains
      (3 * lrDeterminantY raw + 1)
      (3 * yDeriv raw 1 eS) (3 * yDeriv raw 0 eK) 0 := by
    convert hthreeRaw using 1 <;> simp [threeYPlusOneAD] <;> ring
  have hthreePositive : (0 : ℚ) <
      (threeYPlusOneAD box).value.lower := by
    simpa [threeYPlusOneAD, threeYPlusOneI, yAD, yI] using
      hvalid.threeYPlusOnePositive
  have hfrac := IntervalAD.contains_divPositive
    hthreePositive
    (IntervalAD.contains_sub hY (IntervalAD.contains_const 1)) hthree
  have hd1Raw := IntervalAD.contains_add
    (IntervalAD.contains_mul (IntervalAD.contains_const (1 / 2)) hlogMean)
    hfrac
  have hlogMeanParts :
      (0 : ℚ) < (meanYI box).lower ∧
      payload.logMeanY.lower.check (meanYI box).lower = true ∧
      payload.logMeanY.upper.check (meanYI box).upper = true := by
    simpa [RationalEnclosure.LogIntervalCertificate.check] using
      hvalid.logMeanYCheck
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
          hvalid.threeYPlusOnePositive)
    exact hlo.trans_le hthree.1.1
  have hd1 : (d1AD terms box payload).Contains
      (lrDeterminantD1 raw) (d1Deriv raw 1 eS)
      (d1Deriv raw 0 eK) 0 := by
    unfold d1AD d1Deriv lrDeterminantD1
    dsimp only
    convert hd1Raw using 1 <;>
      field_simp [hmeanPointPos.ne', hthreePointPos.ne'] <;> ring

  have hfirstRaw := IntervalAD.contains_add
    (IntervalAD.contains_mul hb hsharpBase)
    (IntervalAD.contains_mul hd1 hsharpPsi)
  let firstH :=
    bH * (lrDeterminantPsi raw - lrCertificateGShape raw +
        4 * lrDeterminantDelta raw * lrCertificateW raw) +
      lrCertificateBFlow raw * sharpBaseH +
      0 * lrDeterminantPsi raw + lrDeterminantD1 raw * sharpPsiH
  have hfirst : (sharpFirstBracketAD terms box payload).Contains
      (lrDeterminantFirstBracket
        (lrCertificateBFlow raw) (lrDeterminantD1 raw)
        (lrCertificateGShape raw) (lrDeterminantPsi raw)
        (lrDeterminantDelta raw) (lrCertificateW raw))
      (firstBracketDeriv raw 1 y0S eS xS vS)
      (firstBracketDeriv raw 0 y0K eK xK vK) firstH := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · convert hfirstRaw.1 using 1 <;>
        simp [sharpFirstBracketAD, lrDeterminantFirstBracket,
          lrCertificateW] <;> ring_nf <;> simp
    · convert hfirstRaw.2.1 using 1 <;>
        simp [sharpFirstBracketAD, firstBracketDeriv,
          lrCertificateW] <;> ring
    · convert hfirstRaw.2.2.1 using 1 <;>
        simp [sharpFirstBracketAD, firstBracketDeriv,
          lrCertificateW] <;> ring
    · convert hfirstRaw.2.2.2 using 1 <;>
        simp [sharpFirstBracketAD, firstH, lrCertificateW] <;> ring
  have hresult := IntervalAD.contains_divPositive hvalid.ePositive hfirst he
  refine ⟨?_, ?_, ?_⟩
  · simpa [sharpEvaluateSKAD,
      lrFiniteDeterminantUpperKReplayTarget] using hresult.1
  · simpa [sharpEvaluateSKAD, targetChartDerivS, targetRawDeriv,
      raw, eS, xS, y0S, vS] using hresult.2.1
  · simpa [sharpEvaluateSKAD, targetChartDerivK, targetRawDeriv,
      raw, eK, xK, y0K, vK] using hresult.2.2.1

/-- Value projection of the cancellation-aware AD evaluator.  This is the
concrete leaf-evaluator theorem: every accepted payload check supplies a
kernel proof that the returned rational interval contains the decoded
historical target. -/
theorem sharpEnclose_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hcheck : payloadCheck box payload = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (sharpEnclose terms box payload).Contains
      (lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate)) := by
  simpa [sharpEnclose] using
    (sharpEvaluateSKAD_sound terms hcheck hcoordinate).1

noncomputable def sharpCheckedEvaluatorSound (terms : ℕ) :
    CheckedEnclosureLeafEvaluatorSound
      (fun coordinate ↦ lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate))
      payloadCheck (sharpEnclose terms) := by
  constructor
  intro box payload hpayload coordinate hcoordinate
  exact sharpEnclose_sound terms hpayload hcoordinate

/-! ## Value evaluator -/

def wI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  (payload.omegaZero.evaluate terms (sAD box)).value

def omegaY0I (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  payload.omegaY0.evaluate terms (sAD box) (y0AD box)

def omegaEI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  (payload.omegaE.evaluate terms (sAD box) (eAD box)).value

def pwI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.add (omegaY0I terms box payload)
    (RationalEnclosure.div (omegaEI terms box payload)
      (vAD box payload).value)

def gI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  let v := (vAD box payload).value
  RationalEnclosure.add
    (RationalEnclosure.add
      (payload.g0.evaluate terms (vAD box payload)).value
      (payload.qY0.enclosure terms (y0AD box).value))
    (RationalEnclosure.div (payload.qE.enclosure terms) v)

def bFlowI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.sub
    (payload.logOnePlusV.enclosure terms)
    (RationalEnclosure.scale (1 / 2)
      (payload.logBE.enclosure terms))

def d1I (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.add
    (RationalEnclosure.scale (1 / 2)
      (payload.logMeanY.enclosure terms))
    (RationalEnclosure.div
      (RationalEnclosure.sub (yI box) (RationalEnclosure.point 1))
      (threeYPlusOneI box))

def psiI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.sub
    (RationalEnclosure.add (gI terms box payload) (pwI terms box payload))
    (RationalEnclosure.div
      (RationalEnclosure.scale 4 (wI terms box payload))
      (onePlusVI box payload))

def deltaI (box : CertificateBox) (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.div
    (RationalEnclosure.sub (RationalEnclosure.point 1)
      (RationalEnclosure.mul (vAD box payload).value (xAD box).value))
    (onePlusVI box payload)

def firstBracketI (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  let psi := psiI terms box payload
  -- Expand `psi - G` before interval evaluation.  This exact cancellation
  -- avoids paying the (comparatively wide) enclosure of `G` twice.
  let psiSubG := RationalEnclosure.sub (pwI terms box payload)
    (RationalEnclosure.div
      (RationalEnclosure.scale 4 (wI terms box payload))
      (onePlusVI box payload))
  let firstInner := RationalEnclosure.add
    psiSubG
    (RationalEnclosure.scale 4
      (RationalEnclosure.mul (deltaI box payload)
        (wI terms box payload)))
  RationalEnclosure.add
    (RationalEnclosure.mul (bFlowI terms box payload) firstInner)
    (RationalEnclosure.mul (d1I terms box payload) psi)

/-- Direct interval extension of the exact audited target
`FirstBracket / e`. -/
def enclose (terms : ℕ) (box : CertificateBox)
    (payload : Payload) : RationalEnclosure :=
  RationalEnclosure.div (firstBracketI terms box payload) (eAD box).value

/-! ## Kernel-checked soundness -/

theorem enclose_sound (terms : ℕ) {box : CertificateBox}
    {payload : Payload} (hcheck : payloadCheck box payload = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate) :
    (enclose terms box payload).Contains
      (lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate)) := by
  have hvalid : Valid box payload := by
    exact payloadCheck_sound hcheck

  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains coordinate.s from
      ⟨hcoordinate.1, hcoordinate.2.1⟩)
  have hratio := IntervalAD.contains_variableK
    (show box.kInterval.Contains coordinate.k from
      ⟨hcoordinate.2.2.1, hcoordinate.2.2.2.1⟩)
  have hh := IntervalAD.contains_variableChi
    (show box.chiInterval.Contains coordinate.chi from
      ⟨hcoordinate.2.2.2.2.1, hcoordinate.2.2.2.2.2⟩)
  have hk := mulNonnegativeAD_sound hvalid.sPositive.le
    hvalid.ratioPositive.le hs hratio
  have hchi := mulNonnegativeAD_sound hvalid.hNonnegative
    hvalid.hNonnegative hh hh
  have hkLower : (0 : ℚ) ≤ (physicalKAD box).value.lower := by
    simpa [physicalKAD, mulNonnegativeAD] using
      mul_nonneg hvalid.sPositive.le hvalid.ratioPositive.le
  have hkPositive : (0 : ℚ) < (physicalKAD box).value.lower := by
    simpa [physicalKAD, mulNonnegativeAD] using
      mul_pos hvalid.sPositive hvalid.ratioPositive
  have hchiLower : (0 : ℚ) ≤ (physicalChiAD box).value.lower := by
    simpa [physicalChiAD, mulNonnegativeAD] using
      mul_nonneg hvalid.hNonnegative hvalid.hNonnegative
  have he := mulNonnegativeAD_sound hvalid.sPositive.le hkLower hs hk
  have hy0 := mulNonnegativeAD_sound hchiLower hvalid.ePositive.le hchi he
  have hx := IntervalAD.contains_sub (IntervalAD.contains_const 1)
    (IntervalAD.contains_mul hchi he)
  have hrad := IntervalAD.contains_divPositive hvalid.xPositive
    (IntervalAD.contains_sub (IntervalAD.contains_const 1) he) hx
  have hvAD := IntervalAD.contains_sqrt hvalid.vSqrtCheck hrad

  have heValue : (eAD box).value.Contains
      (lrCertificateE (lrDeterminantKChartDecode coordinate)) := by
    simpa [eAD, physicalKAD, sAD, ratioAD,
      lrCertificateE, lrDeterminantKChartDecode] using he.1
  have hkValue : (physicalKAD box).value.Contains
      (lrDeterminantKChartDecode coordinate).k := by
    simpa [physicalKAD, sAD, ratioAD, lrDeterminantKChartDecode] using hk.1
  have hxValue : (xAD box).value.Contains
      (lrCertificateX (lrDeterminantKChartDecode coordinate)) := by
    simpa [xAD, physicalChiAD, eAD, physicalKAD, sAD, ratioAD, hAD,
      lrCertificateX, lrCertificateE, lrDeterminantKChartDecode,
      pow_two] using hx.1
  have hy0Value : (y0AD box).value.Contains
      (lrCertificateY0 (lrDeterminantKChartDecode coordinate)) := by
    simpa [y0AD, physicalChiAD, eAD, physicalKAD, sAD, ratioAD, hAD,
      lrCertificateY0, lrCertificateE, lrDeterminantKChartDecode,
      pow_two] using hy0.1
  have hv : (vAD box payload).value.Contains
      (lrCertificateV (lrDeterminantKChartDecode coordinate)) := by
    simpa [vAD, vRadicandAD, xAD, physicalChiAD, eAD, physicalKAD,
      sAD, ratioAD, hAD, lrCertificateV, lrCertificateVRadicand,
      lrCertificateX, lrCertificateE, lrDeterminantKChartDecode,
      pow_two] using hvAD.1

  have hwAD := payload.omegaZero.sound terms hvalid.omegaZeroCheck hs
  have hw : (wI terms box payload).Contains
      (lrCertificateW (lrDeterminantKChartDecode coordinate)) := by
    simpa [wI, lrCertificateW, sAD, lrDeterminantKChartDecode] using hwAD.1
  have homegaY0Raw := payload.omegaY0.sound terms
    hvalid.omegaY0Check hs hy0
  have homegaY0 : (omegaY0I terms box payload).Contains
      (lrCertificateOmega
        (lrDeterminantKChartDecode coordinate).s
        (lrCertificateY0 (lrDeterminantKChartDecode coordinate))) := by
    simpa [omegaY0I, lrCertificateY0, lrCertificateE,
      lrDeterminantKChartDecode, pow_two] using homegaY0Raw
  have homegaEAD := payload.omegaE.sound terms hvalid.omegaECheck hs he
  have homegaE : (omegaEI terms box payload).Contains
      (lrCertificateOmega
        (lrDeterminantKChartDecode coordinate).s
        (lrCertificateE (lrDeterminantKChartDecode coordinate))) := by
    simpa [omegaEI, lrCertificateE, lrDeterminantKChartDecode] using
      homegaEAD.1
  have hpw : (pwI terms box payload).Contains
      (lrCertificatePW (lrDeterminantKChartDecode coordinate)) := by
    have hquot := RationalEnclosure.contains_div hvalid.vPositive
      homegaE hv
    have hsum := RationalEnclosure.contains_add homegaY0 hquot
    simpa [pwI, lrCertificatePW, lrCertificatePWValue] using hsum

  have hg0AD := payload.g0.sound terms hvalid.g0Check hvAD
  have hg0 : (payload.g0.evaluate terms (vAD box payload)).value.Contains
      (lrCertificateG0
        (lrCertificateV (lrDeterminantKChartDecode coordinate))) := by
    simpa [vAD, vRadicandAD, xAD, physicalChiAD, eAD, physicalKAD,
      sAD, ratioAD, hAD, lrCertificateV, lrCertificateVRadicand,
      lrCertificateX, lrCertificateE, lrDeterminantKChartDecode,
      pow_two] using hg0AD.1
  have hqY0 := payload.qY0.sound terms hvalid.qY0Check hy0Value
  have hqE := payload.qE.sound terms hvalid.qECheck heValue
  have hg : (gI terms box payload).Contains
      (lrCertificateGShape (lrDeterminantKChartDecode coordinate)) := by
    have hqEdiv := RationalEnclosure.contains_div hvalid.vPositive hqE hv
    have hsum := RationalEnclosure.contains_add
      (RationalEnclosure.contains_add hg0 hqY0) hqEdiv
    simpa [gI, lrCertificateGShape, lrCertificateGShapeValue] using hsum

  have honePlusV := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 1) hv
  have honePlusVPositive : (0 : ℚ) < (onePlusVI box payload).lower := by
    have honePositive : (0 : ℚ) < 1 := by norm_num
    have hvLowerPositive : (0 : ℚ) <
        (vAD box payload).value.lower := hvalid.vPositive
    change (0 : ℚ) < 1 + (vAD box payload).value.lower
    exact add_pos honePositive hvLowerPositive
  have hyNumerator := IntervalAD.contains_sub
    (IntervalAD.contains_add (IntervalAD.contains_const 1) hk) he
  have hbeChart := IntervalAD.contains_mul hs hyNumerator
  have hbe : (beAD box).value.Contains
      (lrCertificateB
        (lrDeterminantKChartDecode coordinate).s
        (lrCertificateE (lrDeterminantKChartDecode coordinate))) := by
    have hformula :
        coordinate.s *
            (1 + (lrDeterminantKChartDecode coordinate).k -
              lrCertificateE (lrDeterminantKChartDecode coordinate)) =
          lrCertificateB
            (lrDeterminantKChartDecode coordinate).s
            (lrCertificateE (lrDeterminantKChartDecode coordinate)) := by
      unfold lrCertificateB lrCertificateE lrDeterminantKChartDecode
      ring
    rw [← hformula]
    simpa [beAD, yNumeratorAD] using hbeChart.1
  have hlogOnePlus := payload.logOnePlusV.sound terms
    hvalid.logOnePlusVCheck honePlusV
  have hlogBE := payload.logBE.sound terms hvalid.logBECheck hbe
  have hb : (bFlowI terms box payload).Contains
      (lrCertificateBFlow (lrDeterminantKChartDecode coordinate)) := by
    have hraw := RationalEnclosure.contains_sub hlogOnePlus
      (RationalEnclosure.contains_scale (1 / 2) hlogBE)
    simpa [bFlowI, lrCertificateBFlow, lrCertificateBFlowValue] using hraw

  have hY : (yI box).Contains
      (lrDeterminantY (lrDeterminantKChartDecode coordinate)) := by
    have hnumerator : (yNumeratorAD box).value.Contains
        (1 + (lrDeterminantKChartDecode coordinate).k -
          lrCertificateE (lrDeterminantKChartDecode coordinate)) := by
      simpa [yNumeratorAD] using hyNumerator.1
    have hraw := RationalEnclosure.contains_div hkPositive
      hnumerator hkValue
    have hsReal : 0 < coordinate.s := by
      have hlower : (0 : ℝ) < ((sAD box).value.lower : ℝ) := by
        exact_mod_cast hvalid.sPositive
      exact hlower.trans_le hs.1.1
    have hkReal : 0 < (lrDeterminantKChartDecode coordinate).k := by
      have hlower : (0 : ℝ) <
          ((physicalKAD box).value.lower : ℝ) := by
        exact_mod_cast hkPositive
      exact hlower.trans_le hkValue.1
    have hformula :
        (1 + (lrDeterminantKChartDecode coordinate).k -
            lrCertificateE (lrDeterminantKChartDecode coordinate)) /
            (lrDeterminantKChartDecode coordinate).k =
          lrDeterminantY (lrDeterminantKChartDecode coordinate) := by
      unfold lrDeterminantY lrCertificateB lrCertificateE
        lrDeterminantKChartDecode
      field_simp [hsReal.ne', hkReal.ne']
      ring
    rw [← hformula]
    exact hraw
  have hmeanRaw := RationalEnclosure.contains_scale (1 / 2)
    (RationalEnclosure.contains_add
      (RationalEnclosure.contains_point 1) hY)
  have hmean : (meanYI box).Contains
      ((1 + lrDeterminantY (lrDeterminantKChartDecode coordinate)) / 2) := by
    convert hmeanRaw using 1 <;> ring
  have hlogMean := payload.logMeanY.sound terms
    hvalid.logMeanYCheck hmean
  have hthreeYPlusOne : (threeYPlusOneI box).Contains
      ((3 : ℝ) * lrDeterminantY
          (lrDeterminantKChartDecode coordinate) + (1 : ℝ)) := by
    simpa using RationalEnclosure.contains_add
      (RationalEnclosure.contains_scale (3 : ℚ) hY)
      (RationalEnclosure.contains_point (1 : ℚ))
  have hfrac := RationalEnclosure.contains_div
    hvalid.threeYPlusOnePositive
    (RationalEnclosure.contains_sub hY
      (RationalEnclosure.contains_point 1))
    hthreeYPlusOne
  have hd1 : (d1I terms box payload).Contains
      (lrDeterminantD1 (lrDeterminantKChartDecode coordinate)) := by
    have hraw := RationalEnclosure.contains_add
      (RationalEnclosure.contains_scale (1 / 2) hlogMean) hfrac
    simpa [d1I, lrDeterminantD1] using hraw

  have hfourW := RationalEnclosure.contains_scale 4 hw
  have hWOver := RationalEnclosure.contains_div honePlusVPositive
    hfourW honePlusV
  have hpsi : (psiI terms box payload).Contains
      (lrDeterminantPsi (lrDeterminantKChartDecode coordinate)) := by
    have hraw := RationalEnclosure.contains_sub
      (RationalEnclosure.contains_add hg hpw) hWOver
    simpa [psiI, lrDeterminantPsi] using hraw
  have hdelta : (deltaI box payload).Contains
      (lrDeterminantDelta (lrDeterminantKChartDecode coordinate)) := by
    have hproduct := RationalEnclosure.contains_mul hv hxValue
    have hnumerator := RationalEnclosure.contains_sub
      (RationalEnclosure.contains_point 1) hproduct
    have hraw := RationalEnclosure.contains_div honePlusVPositive
      hnumerator honePlusV
    simpa [deltaI, lrDeterminantDelta] using hraw

  have hinner := RationalEnclosure.contains_add
    (RationalEnclosure.contains_sub hpw hWOver)
    (RationalEnclosure.contains_scale 4
      (RationalEnclosure.contains_mul hdelta hw))
  have hfirst : (firstBracketI terms box payload).Contains
      (lrDeterminantFirstBracket
        (lrCertificateBFlow (lrDeterminantKChartDecode coordinate))
        (lrDeterminantD1 (lrDeterminantKChartDecode coordinate))
        (lrCertificateGShape (lrDeterminantKChartDecode coordinate))
        (lrDeterminantPsi (lrDeterminantKChartDecode coordinate))
        (lrDeterminantDelta (lrDeterminantKChartDecode coordinate))
        (lrCertificateW (lrDeterminantKChartDecode coordinate))) := by
    have hraw := RationalEnclosure.contains_add
      (RationalEnclosure.contains_mul hb hinner)
      (RationalEnclosure.contains_mul hd1 hpsi)
    have htarget :
        lrCertificateBFlow (lrDeterminantKChartDecode coordinate) *
            ((lrCertificatePW (lrDeterminantKChartDecode coordinate) -
                4 * lrCertificateW (lrDeterminantKChartDecode coordinate) /
                  (1 + lrCertificateV
                    (lrDeterminantKChartDecode coordinate))) +
              4 * (lrDeterminantDelta
                    (lrDeterminantKChartDecode coordinate) *
                  lrCertificateW (lrDeterminantKChartDecode coordinate))) +
          lrDeterminantD1 (lrDeterminantKChartDecode coordinate) *
            lrDeterminantPsi (lrDeterminantKChartDecode coordinate) =
          lrDeterminantFirstBracket
            (lrCertificateBFlow (lrDeterminantKChartDecode coordinate))
            (lrDeterminantD1 (lrDeterminantKChartDecode coordinate))
            (lrCertificateGShape (lrDeterminantKChartDecode coordinate))
            (lrDeterminantPsi (lrDeterminantKChartDecode coordinate))
            (lrDeterminantDelta (lrDeterminantKChartDecode coordinate))
            (lrCertificateW (lrDeterminantKChartDecode coordinate)) := by
      unfold lrDeterminantFirstBracket lrDeterminantPsi
      ring
    rw [← htarget]
    simpa [firstBracketI] using hraw
  have hresult := RationalEnclosure.contains_div hvalid.ePositive
    hfirst heValue
  simpa [enclose, lrFiniteDeterminantUpperKReplayTarget] using hresult

noncomputable def checkedEvaluatorSound (terms : ℕ) :
    CheckedEnclosureLeafEvaluatorSound
      (fun coordinate ↦ lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate))
      payloadCheck (enclose terms) := by
  constructor
  intro box payload hpayload coordinate hcoordinate
  exact enclose_sound terms hpayload hcoordinate

/-! ## Deterministic payload proposal -/

/-- Generate all untrusted endpoint payloads from the exact interval
expression.  Its output has no semantic authority until `payloadCheck`
returns `true`. -/
def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox) : Payload :=
  let s := sAD box
  let e := eAD box
  let y0 := y0AD box
  let vSqrt := RationalEnclosure.autoSqrtCertificate sqrtFuel
    (vRadicandAD box).value
  let seed : Payload :=
    { vSqrt := vSqrt
      omegaZero := LROmegaZeroADCertificate.auto sqrtFuel logFuel s
      omegaY0 := LROmegaZeroIntervalCertificate.auto
        (sqrtFuel + 8) (logFuel + 8) s y0
      omegaE := LROmegaADCertificate.auto sqrtFuel logFuel s e
      g0 := LRG0ADCertificate.auto logFuel
        (IntervalAD.sqrt vSqrt (vRadicandAD box))
      qY0 := LRQZeroIntervalCertificate.auto
        (sqrtFuel + 8) (logFuel + 8) y0.value
      qE := LRQIntervalCertificate.auto sqrtFuel logFuel e.value
      logOnePlusV := RationalEnclosure.autoLogIntervalCertificate logFuel
        (RationalEnclosure.add (RationalEnclosure.point 1)
          (IntervalAD.sqrt vSqrt (vRadicandAD box)).value)
      logBE := RationalEnclosure.autoLogIntervalCertificate logFuel
        (beAD box).value
      logMeanY :=
        { lower := { exponent := 0, mantissa := 0 }
          upper := { exponent := 0, mantissa := 0 } } }
  { seed with logMeanY :=
      RationalEnclosure.autoLogIntervalCertificate logFuel (meanYI box) }

def accepts (terms sqrtFuel logFuel : ℕ) (box : CertificateBox)
    (_unit : Unit) : Bool :=
  checkedEnclosureLeafAccepts payloadCheck (enclose terms) box
    (auto sqrtFuel logFuel box)

/-! ## Audited centered `(s,K)` leaf rule -/

/-- Freeze exactly the two smooth chart coordinates.  The `h` endpoints
are copied unchanged, so the center enclosure still covers the entire
closed `h` interval, including `h = 0`. -/
def centerSKBox (box : CertificateBox) : CertificateBox :=
  let s := RationalEnclosure.center box.sInterval
  let K := RationalEnclosure.center box.kInterval
  { sLo := s, sHi := s, kLo := K, kHi := K,
    chiLo := box.chiLo, chiHi := box.chiHi }

theorem centerSKBox_contains_anchorSK
    {box : CertificateBox} {coordinate : CertificatePoint}
    (hcoordinate : box.Contains coordinate) :
    (centerSKBox box).Contains (box.anchorSK coordinate) := by
  simp only [centerSKBox, CertificateBox.anchorSK,
    CertificateBox.midpoint]
  exact ⟨le_rfl, le_rfl, le_rfl, le_rfl,
    hcoordinate.2.2.2.2.1, hcoordinate.2.2.2.2.2⟩

/-- Closed chart-box conditions sufficient for every point with `h > 0`
to decode to the ordinary raw interior. -/
def openChartBoxCheck (box : CertificateBox) : Bool :=
  decide (
    (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
    (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
      box.sHi * box.sHi * box.kHi < 1 ∧
    (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧ box.chiHi ≤ 1)

theorem openChartBoxCheck_sound {box : CertificateBox}
    (hcheck : openChartBoxCheck box = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hh : 0 < coordinate.chi) (hhOne : coordinate.chi < 1) :
    LRHighShapeInterior (lrDeterminantKChartDecode coordinate) := by
  have hparts :
      (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
      (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
        box.sHi * box.sHi * box.kHi < 1 ∧
      (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
        box.chiHi ≤ 1 := by
    simpa [openChartBoxCheck] using hcheck
  rcases hparts with
    ⟨hsLoQ, hsOrderQ, hsHiQ, hKLoQ, hKOrderQ, heHiQ,
      hhLoQ, hhOrderQ, hhHiQ⟩
  have hsLo : (0 : ℝ) < box.sLo := by exact_mod_cast hsLoQ
  have hsHi : (box.sHi : ℝ) < 1 := by exact_mod_cast hsHiQ
  have hKLo : (0 : ℝ) < box.kLo := by exact_mod_cast hKLoQ
  have heHi : (((box.sHi * box.sHi * box.kHi : ℚ) : ℝ)) < 1 := by
    exact_mod_cast heHiQ
  have hs : coordinate.s ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hsLo.trans_le hcoordinate.1, hcoordinate.2.1.trans_lt hsHi⟩
  have hK : 0 < coordinate.k := hKLo.trans_le hcoordinate.2.2.1
  have hsHiNonneg : (0 : ℝ) ≤ box.sHi :=
    hsLo.le.trans (by exact_mod_cast hsOrderQ)
  have hKHiNonneg : (0 : ℝ) ≤ box.kHi :=
    hKLo.le.trans (by exact_mod_cast hKOrderQ)
  have hkBound : coordinate.s * coordinate.k ≤
      (box.sHi : ℝ) * box.kHi :=
    mul_le_mul hcoordinate.2.1 hcoordinate.2.2.2.1 hK.le hsHiNonneg
  have heBound : coordinate.s * (coordinate.s * coordinate.k) ≤
      (box.sHi : ℝ) * (box.sHi * box.kHi) :=
    mul_le_mul hcoordinate.2.1 hkBound
      (mul_nonneg hs.1.le hK.le) hsHiNonneg
  have he : lrCertificateE (lrDeterminantKChartDecode coordinate) ∈
      Set.Ioo (0 : ℝ) 1 := by
    constructor
    · simp only [lrCertificateE, lrDeterminantKChartDecode]
      exact mul_pos hs.1 (mul_pos hs.1 hK)
    · simp only [lrCertificateE, lrDeterminantKChartDecode]
      calc
        coordinate.s * (coordinate.s * coordinate.k) ≤
            (box.sHi : ℝ) * (box.sHi * box.kHi) := heBound
        _ = ((box.sHi * box.sHi * box.kHi : ℚ) : ℝ) := by
          norm_num <;> ring
        _ < 1 := heHi
  have hsqPos : 0 < coordinate.chi ^ 2 := pow_pos hh 2
  have hsqLt : coordinate.chi ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hhOne)
      (show 0 < 1 + coordinate.chi by linarith)]
  exact ⟨hs, he, by
    simpa [lrDeterminantKChartDecode] using
      (show coordinate.chi ^ 2 ∈ Set.Ioo (0 : ℝ) 1 from
        ⟨hsqPos, hsqLt⟩)⟩

structure CenteredPayload where
  center : Payload
  derivative : Payload

def centeredPayloadCheck (box : CertificateBox)
    (certificate : CenteredPayload) : Bool :=
  openChartBoxCheck box &&
    payloadCheck (centerSKBox box) certificate.center &&
    payloadCheck box certificate.derivative

def evaluateCentered (terms : ℕ) (box : CertificateBox)
    (certificate : CenteredPayload) : MidpointSKCertificate :=
  let derivative := evaluateSKAD terms box certificate.derivative
  { value := enclose terms (centerSKBox box) certificate.center
    derivS := derivative.derivS
    derivK := derivative.derivK }

def centeredAccepts (terms : ℕ) (box : CertificateBox)
    (certificate : CenteredPayload) : Bool :=
  centeredPayloadCheck box certificate &&
    (evaluateCentered terms box certificate).check box

noncomputable def centeredDerivativeEnclosures (terms : ℕ)
    {box : CertificateBox} {certificate : CenteredPayload}
    (hderivative : payloadCheck box certificate.derivative = true)
    (hdomain : openChartBoxCheck box = true) :
    BoxSKDerivativeEnclosuresOn
      (fun coordinate ↦ lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate))
      box (evaluateCentered terms box certificate)
        (fun h ↦ 0 < h ∧ h < 1) := by
  refine
    { partialS := targetChartDerivS
      partialK := targetChartDerivK
      derivS := ?_
      derivK := ?_
      boundS := ?_
      boundK := ?_ }
  · intro coordinate hcoordinate hh
    exact hasDerivAt_targetChart_s
      (openChartBoxCheck_sound hdomain hcoordinate hh.1 hh.2)
  · intro coordinate hcoordinate hh
    exact hasDerivAt_targetChart_k
      (openChartBoxCheck_sound hdomain hcoordinate hh.1 hh.2)
  · intro coordinate hcoordinate
    have h := evaluateSKAD_sound terms hderivative hcoordinate
    simpa [evaluateCentered] using h.2.1
  · intro coordinate hcoordinate
    have h := evaluateSKAD_sound terms hderivative hcoordinate
    simpa [evaluateCentered] using h.2.2

theorem positive_of_centeredAccepts (terms : ℕ)
    {box : CertificateBox} {certificate : CenteredPayload}
    (haccept : centeredAccepts terms box certificate = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hh : 0 < coordinate.chi) (hhOne : coordinate.chi < 1) :
    0 < lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) := by
  have hacceptParts : centeredPayloadCheck box certificate = true ∧
      (evaluateCentered terms box certificate).check box = true := by
    simpa [centeredAccepts] using haccept
  have hpayloadParts :
      (openChartBoxCheck box = true ∧
        payloadCheck (centerSKBox box) certificate.center = true) ∧
      payloadCheck box certificate.derivative = true := by
    simpa [centeredPayloadCheck] using hacceptParts.1
  have hvalue : ∀ anchor, box.Contains anchor →
      (evaluateCentered terms box certificate).value.Contains
        (lrFiniteDeterminantUpperKReplayTarget
          (lrDeterminantKChartDecode (box.anchorSK anchor))) := by
    intro anchor hanchor
    have hcenter := enclose_sound terms hpayloadParts.1.2
      (centerSKBox_contains_anchorSK hanchor)
    simpa [evaluateCentered] using hcenter
  exact (evaluateCentered terms box certificate).soundOn_of_derivativeEnclosures
    hvalue
    (centeredDerivativeEnclosures terms hpayloadParts.2 hpayloadParts.1.1)
    hacceptParts.2 hcoordinate ⟨hh, hhOne⟩

/-! The sharp centered pass has exactly the same checked domain and midpoint
geometry as the baseline pass.  It differs only in the interval expression:
both its frozen `(s,K)` value enclosure and its whole-box derivatives use the
historical `A/C` cancellations.  The `h` interval is still retained in full,
and the analytic mean-value argument only consumes the two genuine `s` and
`K` derivatives. -/

def evaluateSharpCentered (terms : ℕ) (box : CertificateBox)
    (certificate : CenteredPayload) : MidpointSKCertificate :=
  let derivative := sharpEvaluateSKAD terms box certificate.derivative
  { value := sharpEnclose terms (centerSKBox box) certificate.center
    derivS := derivative.derivS
    derivK := derivative.derivK }

def sharpCenteredAccepts (terms : ℕ) (box : CertificateBox)
    (certificate : CenteredPayload) : Bool :=
  centeredPayloadCheck box certificate &&
    (evaluateSharpCentered terms box certificate).check box

noncomputable def sharpCenteredDerivativeEnclosures (terms : ℕ)
    {box : CertificateBox} {certificate : CenteredPayload}
    (hderivative : payloadCheck box certificate.derivative = true)
    (hdomain : openChartBoxCheck box = true) :
    BoxSKDerivativeEnclosuresOn
      (fun coordinate ↦ lrFiniteDeterminantUpperKReplayTarget
        (lrDeterminantKChartDecode coordinate))
      box (evaluateSharpCentered terms box certificate)
        (fun h ↦ 0 < h ∧ h < 1) := by
  refine
    { partialS := targetChartDerivS
      partialK := targetChartDerivK
      derivS := ?_
      derivK := ?_
      boundS := ?_
      boundK := ?_ }
  · intro coordinate hcoordinate hh
    exact hasDerivAt_targetChart_s
      (openChartBoxCheck_sound hdomain hcoordinate hh.1 hh.2)
  · intro coordinate hcoordinate hh
    exact hasDerivAt_targetChart_k
      (openChartBoxCheck_sound hdomain hcoordinate hh.1 hh.2)
  · intro coordinate hcoordinate
    have h := sharpEvaluateSKAD_sound terms hderivative hcoordinate
    simpa [evaluateSharpCentered] using h.2.1
  · intro coordinate hcoordinate
    have h := sharpEvaluateSKAD_sound terms hderivative hcoordinate
    simpa [evaluateSharpCentered] using h.2.2

theorem positive_of_sharpCenteredAccepts (terms : ℕ)
    {box : CertificateBox} {certificate : CenteredPayload}
    (haccept : sharpCenteredAccepts terms box certificate = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hh : 0 < coordinate.chi) (hhOne : coordinate.chi < 1) :
    0 < lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) := by
  have hacceptParts : centeredPayloadCheck box certificate = true ∧
      (evaluateSharpCentered terms box certificate).check box = true := by
    simpa [sharpCenteredAccepts] using haccept
  have hpayloadParts :
      (openChartBoxCheck box = true ∧
        payloadCheck (centerSKBox box) certificate.center = true) ∧
      payloadCheck box certificate.derivative = true := by
    simpa [centeredPayloadCheck] using hacceptParts.1
  have hvalue : ∀ anchor, box.Contains anchor →
      (evaluateSharpCentered terms box certificate).value.Contains
        (lrFiniteDeterminantUpperKReplayTarget
          (lrDeterminantKChartDecode (box.anchorSK anchor))) := by
    intro anchor hanchor
    have hcenter := sharpEnclose_sound terms hpayloadParts.1.2
      (centerSKBox_contains_anchorSK hanchor)
    simpa [evaluateSharpCentered] using hcenter
  exact
    (evaluateSharpCentered terms box certificate).soundOn_of_derivativeEnclosures
      hvalue
      (sharpCenteredDerivativeEnclosures terms hpayloadParts.2
        hpayloadParts.1.1)
      hacceptParts.2 hcoordinate ⟨hh, hhOne⟩

def autoCentered (sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : CenteredPayload :=
  { center := auto sqrtFuel logFuel (centerSKBox box)
    derivative := auto sqrtFuel logFuel box }

def autoCenteredAccepts (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (_unit : Unit) : Bool :=
  centeredAccepts terms box (autoCentered sqrtFuel logFuel box)

def autoSharpCenteredAccepts (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (_unit : Unit) : Bool :=
  sharpCenteredAccepts terms box (autoCentered sqrtFuel logFuel box)

/-! ## Structural wrapper for a centered upper-`K` replay -/

/-- Relevance for the centered tree includes the open raw chart needed by
the analytic mean-value theorem.  The eventual region adapter supplies this
directly from the original high-shape interior point. -/
def CenteredRelevant (coordinate : CertificatePoint) : Prop :=
  LRHighShapeInterior (lrDeterminantKChartDecode coordinate) ∧
    LRHighShapeVRelevant (lrDeterminantKChartDecode coordinate)

structure CenteredCheckedTree (terms : ℕ) (root : CertificateBox) where
  DiscardData : Type
  discardCheck : CertificateBox → DiscardData → Bool
  discardSound : ∀ box data, discardCheck box data = true →
    ∀ coordinate, box.Contains coordinate →
      ¬ LRHighShapeVRelevant (lrDeterminantKChartDecode coordinate)
  certificate : SubdivisionCertificate CenteredPayload DiscardData
  checked : certificate.check (centeredAccepts terms) discardCheck root = true

namespace CenteredCheckedTree

theorem target_nonnegative {terms : ℕ} {root : CertificateBox}
    (tree : CenteredCheckedTree terms root)
    {coordinate : CertificatePoint} (hcoordinate : root.Contains coordinate)
    (hrelevant : CenteredRelevant coordinate) :
    0 ≤ lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate) := by
  have hconditional := subdivisionCertificate_sound
      (Relevant := fun coordinate ↦
        LRHighShapeVRelevant (lrDeterminantKChartDecode coordinate))
      (Property := fun coordinate ↦
        LRHighShapeInterior (lrDeterminantKChartDecode coordinate) →
          0 ≤ lrFiniteDeterminantUpperKReplayTarget
            (lrDeterminantKChartDecode coordinate))
      (acceptBox := centeredAccepts terms)
      (discardBox := tree.discardCheck)
      (box := root) (certificate := tree.certificate) (by
    intro box certificate haccept point hpoint
    have hacceptParts : centeredPayloadCheck box certificate = true ∧
        (evaluateCentered terms box certificate).check box = true := by
      simpa [centeredAccepts] using haccept
    have hpayloadParts :
        (openChartBoxCheck box = true ∧
          payloadCheck (centerSKBox box) certificate.center = true) ∧
        payloadCheck box certificate.derivative = true := by
      simpa [centeredPayloadCheck] using hacceptParts.1
    have hopenParts :
        (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
        (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
          box.sHi * box.sHi * box.kHi < 1 ∧
        (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
          box.chiHi ≤ 1 := by
      simpa [openChartBoxCheck] using hpayloadParts.1.1
    intro hpointInterior
    have hhNonnegative : 0 ≤ point.chi := by
      have hlo : (0 : ℝ) ≤ box.chiLo := by
        exact_mod_cast hopenParts.2.2.2.2.2.2.1
      exact hlo.trans hpoint.2.2.2.2.1
    have hhSqPos : 0 < point.chi ^ 2 := by
      simpa [lrDeterminantKChartDecode] using
        hpointInterior.2.2.1
    have hhSqLt : point.chi ^ 2 < 1 := by
      simpa [lrDeterminantKChartDecode] using
        hpointInterior.2.2.2
    have hhPositive : 0 < point.chi := by nlinarith
    have hhOne : point.chi < 1 := by nlinarith
    exact (positive_of_centeredAccepts terms haccept hpoint
      hhPositive hhOne).le)
      (by
    intro box data hdiscard point hpoint hpointRelevant
    exact (tree.discardSound box data hdiscard point hpoint)
      hpointRelevant)
      tree.checked coordinate hcoordinate hrelevant.2
  exact hconditional hrelevant.1

end CenteredCheckedTree

/-- Region-level adapter for the exact centered upper-`K` replay. -/
theorem regionCertificate_of_centeredCheckedTree
    {terms : ℕ} {root : CertificateBox}
    {Region : CertificatePoint → Prop}
    (root_contains : ∀ {point : CertificatePoint},
      LRHighShapeInterior point → Region point →
        root.Contains (lrDeterminantKChartEncode point))
    (tree : CenteredCheckedTree terms root) :
    LRDeterminantRegionCertificateTheorem Region := by
  intro point hinterior hrelevant hregion
  have hdecoded := lrDeterminantKChartDecode_encode hinterior
  have hchartRelevant : CenteredRelevant
      (lrDeterminantKChartEncode point) := by
    unfold CenteredRelevant
    rw [hdecoded]
    exact ⟨hinterior, hrelevant⟩
  have htarget := tree.target_nonnegative
    (root_contains hinterior hregion) hchartRelevant
  rw [hdecoded] at htarget
  exact lrDeterminantAdmittedTarget_of_upperKReplayTarget hinterior htarget

theorem upperKRegionCertificate_of_centeredCheckedTree
    {terms : ℕ}
    (tree : CenteredCheckedTree terms lrDeterminantUpperKKChartRoot) :
    LRDeterminantRegionCertificateTheorem LRDeterminantUpperKRegion :=
  regionCertificate_of_centeredCheckedTree
    lrDeterminantUpperKKChartRoot_contains_encode tree

end LRUpperKReplayCertificate

end CourtadeKumar
