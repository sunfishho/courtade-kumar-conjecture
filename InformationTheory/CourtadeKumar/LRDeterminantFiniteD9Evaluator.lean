import InformationTheory.CourtadeKumar.LRDeterminantFiniteReplayTargets
import InformationTheory.CourtadeKumar.LRHighShapeTangentAutoTree
import InformationTheory.CourtadeKumar.LRHighShapeVZeroFaceEvaluator

/-!
# A verified direct enclosure for the raw finite D9 determinant target

This module develops the actual accepted-leaf arithmetic missing from
`LRFiniteDeterminantRawD9CheckedTree`.  It reuses the checked high-shape
coordinate, kernel, logarithmic-coefficient, shape, gap, and half-slope AD
nodes.  The only additional transcendental payload is the logarithm in

`D1 = log ((1 + Y) / 2) / 2 + (Y - 1) / (3 * Y + 1)`.

The evaluator uses the two exact cancellations

`s * Hd = halfSlope`,  `R * T = gap`.

Consequently its interval expression is the exact D9 target but introduces
neither division by `s` nor division by `R`.  No open-chart hypothesis is
placed in the payload checker.  Because the regular derivative payload for
`Q(chi*e)` can reject a leaf touching `chi = 0`, the second half of this
module supplies a value-only zero-face evaluator and combines the two sound
leaf rules in one hybrid checked-tree interface.
-/

namespace CourtadeKumar

/-- Untrusted scalar data for a direct D9 enclosure.  All fields are checked
by executable Boolean predicates before their semantic theorems are used. -/
structure LRFiniteDeterminantD9Certificate where
  tangent : LRHighShapeTangentCertificate
  logD1Mean : RationalEnclosure.LogIntervalCertificate

namespace LRFiniteDeterminantD9Certificate

def yAD (box : CertificateBox) : IntervalAD :=
  let k := lrCertificateKAD box
  let e := lrCertificateEAD box
  IntervalAD.divPositive
    (IntervalAD.sub (IntervalAD.add (IntervalAD.const 1) k) e) k

def d1MeanAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.mul
    (IntervalAD.add (IntervalAD.const 1) (yAD box))
    (IntervalAD.const (1 / 2))

def d1DenominatorAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.add
    (IntervalAD.mul (IntervalAD.const 3) (yAD box))
    (IntervalAD.const 1)

def d1AD (terms : ℕ) (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9Certificate) : IntervalAD :=
  let y := yAD box
  let logMean := IntervalAD.log terms certificate.logD1Mean (d1MeanAD box)
  IntervalAD.add
    (IntervalAD.mul (IntervalAD.const (1 / 2)) logMean)
    (IntervalAD.divPositive
      (IntervalAD.sub y (IntervalAD.const 1))
      (d1DenominatorAD box))

def onePlusVAD (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9Certificate) : IntervalAD :=
  IntervalAD.add (IntervalAD.const 1)
    (certificate.tangent.base.kernel.coordinate.vAD box)

/-- The exact cancellation-coordinate formula
`Psi = G + P_W - 4 W / (1 + v)`. -/
def psiAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9Certificate) : IntervalAD :=
  let base := certificate.tangent.base
  let coordinate := base.kernel.coordinate
  let g := base.gShape.evaluate terms box coordinate
  let pw := base.kernel.pwAD terms box
  let w := base.kernel.wAD terms box
  IntervalAD.sub (IntervalAD.add g pw)
    (IntervalAD.divPositive
      (IntervalAD.mul (IntervalAD.const 4) w)
      (onePlusVAD box certificate))

/-- The exact coefficient `delta = (1 - v*x) / (1 + v)`. -/
def deltaAD (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9Certificate) : IntervalAD :=
  let v := certificate.tangent.base.kernel.coordinate.vAD box
  IntervalAD.divPositive
    (IntervalAD.sub (IntervalAD.const 1)
      (IntervalAD.mul v (lrCertificateXAD box)))
    (onePlusVAD box certificate)

def firstBracketAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9Certificate) : IntervalAD :=
  let base := certificate.tangent.base
  let coordinate := base.kernel.coordinate
  let b := (base.ab.evaluate terms box coordinate).b
  let g := base.gShape.evaluate terms box coordinate
  let w := base.kernel.wAD terms box
  let psi := psiAD terms box certificate
  let d1 := d1AD terms box certificate
  let delta := deltaAD box certificate
  IntervalAD.add
    (IntervalAD.mul b
      (IntervalAD.add (IntervalAD.sub psi g)
        (IntervalAD.mul
          (IntervalAD.mul (IntervalAD.const 4) delta) w)))
    (IntervalAD.mul d1 psi)

/-- Direct interval-AD extension of D9.  It retains `s*Hd` as the already
computed half-slope and `R*T` as the already computed gap. -/
def evaluateAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9Certificate) : IntervalAD :=
  let tangentValues := certificate.tangent.evaluateAll terms box
  let base := certificate.tangent.base
  let coordinate := base.kernel.coordinate
  let b := (base.ab.evaluate terms box coordinate).b
  let w := base.kernel.wAD terms box
  let d1 := d1AD terms box certificate
  let first := firstBracketAD terms box certificate
  let factor := IntervalAD.sub
    (IntervalAD.mul b (lrCertificateXAD box)) d1
  IntervalAD.add
    (IntervalAD.mul
      (IntervalAD.mul (IntervalAD.const 3) tangentValues.halfSlope) first)
    (IntervalAD.mul
      (IntervalAD.mul
        (IntervalAD.mul (IntervalAD.const 4) w) tangentValues.gap)
      factor)

def enclose (terms : ℕ) (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9Certificate) : RationalEnclosure :=
  (certificate.evaluateAD terms box).value

/-- This checker does not require the whole closed leaf to lie in the open
chi chart.  Positivity of `s`, `k`, `R`, the D1 denominator, and `1+v` is
instead checked directly on the rational enclosures.  Its reused `Q` AD
payload may still fail closed at `chi = 0`. -/
def payloadCheck (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9Certificate) : Bool :=
  decide (
    certificate.tangent.check box = true ∧
    (0 : ℚ) < (lrCertificateSAD box).value.lower ∧
    (0 : ℚ) < (lrCertificateKAD box).value.lower ∧
    (0 : ℚ) < (lrCertificateRAD box).value.lower ∧
    certificate.logD1Mean.check (d1MeanAD box).value = true ∧
    (0 : ℚ) < (d1DenominatorAD box).value.lower ∧
    (0 : ℚ) < (onePlusVAD box certificate).value.lower)

theorem yAD_value_sound
    {box : CertificateBox} {point : CertificatePoint}
    (hpoint : box.Contains point)
    (hsLower : (0 : ℚ) < (lrCertificateSAD box).value.lower)
    (hkLower : (0 : ℚ) < (lrCertificateKAD box).value.lower) :
    (yAD box).value.Contains (lrDeterminantY point) := by
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have hk := IntervalAD.contains_variableK
    (show box.kInterval.Contains point.k from
      ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩)
  have he := lrCertificateEAD_sound hpoint
  have hnum := IntervalAD.contains_sub
    (IntervalAD.contains_add (IntervalAD.contains_const 1) hk) he
  have hy := IntervalAD.contains_divPositive hkLower hnum hk
  have hsLowerReal : (0 : ℝ) < ((lrCertificateSAD box).value.lower : ℝ) := by
    exact_mod_cast hsLower
  have hkLowerReal : (0 : ℝ) < ((lrCertificateKAD box).value.lower : ℝ) := by
    exact_mod_cast hkLower
  have hsPos : 0 < point.s := hsLowerReal.trans_le hs.1.1
  have hkPos : 0 < point.k := hkLowerReal.trans_le hk.1.1
  have hyEq :
      (((1 : ℚ) : ℝ) + point.k - lrCertificateE point) / point.k =
        lrDeterminantY point := by
    unfold lrDeterminantY lrCertificateB lrCertificateE
    field_simp [hsPos.ne', hkPos.ne']
    ring
  unfold yAD
  dsimp only
  rw [hyEq] at hy
  exact hy.1

theorem d1AD_value_sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRFiniteDeterminantD9Certificate}
    (hpoint : box.Contains point)
    (hsLower : (0 : ℚ) < (lrCertificateSAD box).value.lower)
    (hkLower : (0 : ℚ) < (lrCertificateKAD box).value.lower)
    (hlog : certificate.logD1Mean.check (d1MeanAD box).value = true)
    (hden : (0 : ℚ) < (d1DenominatorAD box).value.lower) :
    (certificate.d1AD terms box).value.Contains
      (lrDeterminantD1 point) := by
  have hk := IntervalAD.contains_variableK
    (show box.kInterval.Contains point.k from
      ⟨hpoint.2.2.1, hpoint.2.2.2.1⟩)
  have he := lrCertificateEAD_sound hpoint
  have hnum := IntervalAD.contains_sub
    (IntervalAD.contains_add (IntervalAD.contains_const 1) hk) he
  have hy := IntervalAD.contains_divPositive hkLower hnum hk
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have hsLowerReal : (0 : ℝ) < ((lrCertificateSAD box).value.lower : ℝ) := by
    exact_mod_cast hsLower
  have hkLowerReal : (0 : ℝ) < ((lrCertificateKAD box).value.lower : ℝ) := by
    exact_mod_cast hkLower
  have hsPos : 0 < point.s := hsLowerReal.trans_le hs.1.1
  have hkPos : 0 < point.k := hkLowerReal.trans_le hk.1.1
  have hyEq :
      (((1 : ℚ) : ℝ) + point.k - lrCertificateE point) / point.k =
        lrDeterminantY point := by
    unfold lrDeterminantY lrCertificateB lrCertificateE
    field_simp [hsPos.ne', hkPos.ne']
    ring
  have hmean := IntervalAD.contains_mul
    (IntervalAD.contains_add (IntervalAD.contains_const 1) hy)
    (IntervalAD.contains_const (1 / 2))
  have hlogMean := IntervalAD.contains_log terms hlog hmean
  have hdenominator := IntervalAD.contains_add
    (IntervalAD.contains_mul (IntervalAD.contains_const 3) hy)
    (IntervalAD.contains_const 1)
  have hfraction := IntervalAD.contains_divPositive hden
    (IntervalAD.contains_sub hy (IntervalAD.contains_const 1))
    hdenominator
  have hd1 := IntervalAD.contains_add
    (IntervalAD.contains_mul (IntervalAD.contains_const (1 / 2)) hlogMean)
    hfraction
  rw [hyEq] at hd1
  unfold d1AD d1MeanAD d1DenominatorAD
  dsimp only
  simpa [lrDeterminantD1] using hd1.1

theorem evaluate_value_sound
    (terms : ℕ) {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRFiniteDeterminantD9Certificate}
    (hpoint : box.Contains point)
    (hcheck : certificate.payloadCheck box = true) :
    (certificate.enclose terms box).Contains
      (lrFiniteDeterminantD9ReplayTarget point) := by
  have hparts :
      certificate.tangent.check box = true ∧
      (0 : ℚ) < (lrCertificateSAD box).value.lower ∧
      (0 : ℚ) < (lrCertificateKAD box).value.lower ∧
      (0 : ℚ) < (lrCertificateRAD box).value.lower ∧
      certificate.logD1Mean.check (d1MeanAD box).value = true ∧
      (0 : ℚ) < (d1DenominatorAD box).value.lower ∧
      (0 : ℚ) < (onePlusVAD box certificate).value.lower := by
    simpa [payloadCheck] using hcheck
  have htangentParts :
      certificate.tangent.base.check box = true ∧
      certificate.tangent.qBY0.check
        (lrCertificateBAD (lrCertificateSAD box)
          (lrCertificateY0AD box)).value = true ∧
      certificate.tangent.qBE.check
        (lrCertificateBAD (lrCertificateSAD box)
          (lrCertificateEAD box)).value = true ∧
      certificate.tangent.qS.check (lrCertificateSAD box).value = true ∧
      certificate.tangent.logTwoPlusV.check
        (IntervalAD.add (IntervalAD.const 2)
          (certificate.tangent.base.kernel.coordinate.vAD box)).value = true ∧
      (0 : ℚ) <
        (certificate.tangent.base.kernel.coordinate.vAD box).value.lower ∧
      (0 : ℚ) < (onePlusVAD box certificate).value.lower ∧
      (0 : ℚ) <
        (IntervalAD.add (IntervalAD.const 2)
          (certificate.tangent.base.kernel.coordinate.vAD box)).value.lower ∧
      (0 : ℚ) <
        (IntervalAD.mul
          (certificate.tangent.base.kernel.coordinate.vAD box)
          (certificate.tangent.base.kernel.coordinate.vAD box)).value.lower := by
    simpa [LRHighShapeTangentCertificate.check, onePlusVAD] using hparts.1
  have hbaseParts :
      certificate.tangent.base.kernel.check box = true ∧
      certificate.tangent.base.gShape.check box
        certificate.tangent.base.kernel.coordinate = true ∧
      certificate.tangent.base.ab.check box
        certificate.tangent.base.kernel.coordinate = true ∧
      (0 : ℚ) < (onePlusVAD box certificate).value.lower ∧
      (0 : ℚ) <
        (LRHighShapeMidpointCertificate.denominatorAD box).value.lower := by
    simpa [LRHighShapeMidpointCertificate.check, onePlusVAD]
      using htangentParts.1
  have hkernelParts :
      certificate.tangent.base.kernel.coordinate.check box = true ∧
      certificate.tangent.base.kernel.omegaZero.check
        (lrCertificateSAD box) = true ∧
      certificate.tangent.base.kernel.omegaY0.check
        (lrCertificateSAD box) (lrCertificateY0AD box) = true ∧
      certificate.tangent.base.kernel.omegaE.check
        (lrCertificateSAD box) (lrCertificateEAD box) = true ∧
      (0 : ℚ) <
        (certificate.tangent.base.kernel.coordinate.vAD box).value.lower := by
    simpa [LRHighShapeKernelCertificate.check] using hbaseParts.1

  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have hR := lrCertificateRAD_sound hpoint
  have hx := lrCertificateXAD_sound hpoint
  have hv := certificate.tangent.base.kernel.coordinate.vAD_sound
    hpoint hkernelParts.1
  have hab := certificate.tangent.base.ab.sound terms hpoint
    hbaseParts.2.2.1
  have hg := certificate.tangent.base.gShape.sound terms hpoint
    hbaseParts.2.1
  have hw := certificate.tangent.base.kernel.wAD_sound terms hpoint
    hbaseParts.1
  have hpw := certificate.tangent.base.kernel.pwAD_sound terms hpoint
    hbaseParts.1
  have htangent := certificate.tangent.evaluateAll_sound terms hpoint hparts.1
  have hd1 := certificate.d1AD_value_sound terms hpoint
    hparts.2.1 hparts.2.2.1 hparts.2.2.2.2.1
    hparts.2.2.2.2.2.1

  have honePlusV := IntervalAD.contains_add
    (IntervalAD.contains_const 1) hv
  have hpsi := IntervalAD.contains_sub
    (IntervalAD.contains_add hg hpw)
    (IntervalAD.contains_divPositive hparts.2.2.2.2.2.2
      (IntervalAD.contains_mul (IntervalAD.contains_const 4) hw)
      honePlusV)
  have hdelta := IntervalAD.contains_divPositive hparts.2.2.2.2.2.2
    (IntervalAD.contains_sub (IntervalAD.contains_const 1)
      (IntervalAD.contains_mul hv hx)) honePlusV
  have hfourDeltaW := IntervalAD.contains_mul
    (IntervalAD.contains_mul (IntervalAD.contains_const 4) hdelta) hw
  have hbase := IntervalAD.contains_add
    (IntervalAD.contains_sub hpsi hg) hfourDeltaW
  have hfirstValue := RationalEnclosure.contains_add
    (RationalEnclosure.contains_mul hab.2.1.1 hbase.1)
    (RationalEnclosure.contains_mul hd1 hpsi.1)

  have hfactorValue := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_mul hab.2.1.1 hx.1) hd1
  have hleadingValue := RationalEnclosure.contains_mul
    (RationalEnclosure.contains_mul
      (RationalEnclosure.contains_point 3) htangent.halfSlope.1)
    hfirstValue
  have hcorrectionValue := RationalEnclosure.contains_mul
    (RationalEnclosure.contains_mul
      (RationalEnclosure.contains_mul
        (RationalEnclosure.contains_point 4) hw.1) htangent.gap.1)
    hfactorValue
  have htargetValue := RationalEnclosure.contains_add
    hleadingValue hcorrectionValue

  have hsLowerReal : (0 : ℝ) < ((lrCertificateSAD box).value.lower : ℝ) := by
    exact_mod_cast hparts.2.1
  have hRLowerReal : (0 : ℝ) < ((lrCertificateRAD box).value.lower : ℝ) := by
    exact_mod_cast hparts.2.2.2.1
  have hsPos : 0 < point.s := hsLowerReal.trans_le hs.1.1
  have hRPos : 0 < lrCertificateR point := hRLowerReal.trans_le hR.1.1
  have htargetEq :
      lrFiniteDeterminantD9ReplayTarget point =
        3 * lrCertificateHalfSlope point *
            lrDeterminantFirstBracket
              (lrCertificateBFlow point) (lrDeterminantD1 point)
              (lrCertificateGShape point) (lrDeterminantPsi point)
              (lrDeterminantDelta point) (lrCertificateW point) +
          4 * lrCertificateW point * lrCertificateGap point *
            (lrCertificateBFlow point * lrCertificateX point -
              lrDeterminantD1 point) := by
    unfold lrFiniteDeterminantD9ReplayTarget lrDeterminantHd lrDeterminantT
    field_simp [hsPos.ne', hRPos.ne']

  unfold enclose evaluateAD firstBracketAD psiAD deltaAD onePlusVAD
  dsimp only
  rw [htargetEq]
  simpa [onePlusVAD, IntervalAD.const, IntervalAD.add, IntervalAD.sub,
    IntervalAD.mul, lrDeterminantFirstBracket, lrDeterminantPsi,
    lrDeterminantDelta] using htargetValue

/-- Kernel-checked accepted-leaf soundness for the actual D9 evaluator. -/
noncomputable def checkedEvaluatorSound (terms : ℕ) :
    CheckedEnclosureLeafEvaluatorSound
      lrFiniteDeterminantD9ReplayTarget payloadCheck (enclose terms) := by
  constructor
  intro box certificate hcheck point hpoint
  exact certificate.evaluate_value_sound terms hpoint hcheck

/-- Deterministically propose the full payload for one raw-coordinate leaf.
Proposal generation is untrusted; `payloadCheck` validates every field. -/
def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRFiniteDeterminantD9Certificate :=
  let tangent := LRHighShapeTangentCertificate.auto sqrtFuel logFuel box
  { tangent := tangent
    logD1Mean := RationalEnclosure.autoLogIntervalCertificate logFuel
      (d1MeanAD box).value }

def autoAccepts (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (_unit : Unit) : Bool :=
  checkedEnclosureLeafAccepts
    (fun b _unit ↦ payloadCheck b (auto sqrtFuel logFuel b))
    (fun b _unit ↦ enclose terms b (auto sqrtFuel logFuel b))
    box ()

/-- Package any checked raw subdivision using this concrete evaluator and
the already verified physical/`J` discard checker. -/
def toRawCheckedTree
    (terms : ℕ) {root : CertificateBox}
    (tree : SubdivisionCertificate LRFiniteDeterminantD9Certificate
      LRHighShapeVDiscardData)
    (hcheck : tree.check
      (checkedEnclosureLeafAccepts payloadCheck (enclose terms))
      (lrHighShapeVDiscardCheck terms) root = true) :
    LRFiniteDeterminantRawD9CheckedTree root where
  AcceptData := LRFiniteDeterminantD9Certificate
  DiscardData := LRHighShapeVDiscardData
  payloadCheck := payloadCheck
  enclose := enclose terms
  discardCheck := lrHighShapeVDiscardCheck terms
  encloseSound := checkedEvaluatorSound terms
  discardCompatible := lrHighShapeVDiscardCheck_sound terms
  certificate := tree
  checked := hcheck

/-- Fixed-16 specialization: a checked concrete tree immediately supplies
the corresponding finite determinant ledger row. -/
theorem fixed16Region_certificate_of_checkedTree
    (terms : ℕ)
    (tree : SubdivisionCertificate LRFiniteDeterminantD9Certificate
      LRHighShapeVDiscardData)
    (hcheck : tree.check
      (checkedEnclosureLeafAccepts payloadCheck (enclose terms))
      (lrHighShapeVDiscardCheck terms) lrDeterminantFixed16Root = true) :
    LRDeterminantRegionCertificateTheorem LRDeterminantFixed16Region := by
  exact lrDeterminantFixed16Region_certificate_of_D9Tree
    (toRawCheckedTree terms tree hcheck)

end LRFiniteDeterminantD9Certificate
end CourtadeKumar

/-!
# A value-only zero-face path for the finite D9 determinant evaluator

The ordinary D9 evaluator reuses a full interval-AD tangent payload.  That
payload asks for a bounded derivative of `Q (chi * e)`, so it necessarily
rejects a closed leaf with `chiLo = 0`.  The D9 target itself only uses
values.  This file rebuilds its value enclosure with the endpoint-safe
`Q(chi*e)` and `omega_s(chi*e)` certificates from
`LRHighShapeVZeroFaceEvaluator`.

The gap and half-slope pieces do not contain either singular node.  They are
therefore evaluated from the usual `Q(B_s(chi e))`, `Q(B_s(e))`, `Q(s)`, and
logarithm payloads.  The two exact cancellations used by the regular D9
evaluator are retained:

`s * Hd = halfSlope`,  `R * T = gap`.

Thus this is a second accepted-leaf rule for exactly the same D9 replay
target, not a surrogate direct-`V` theorem.
-/

namespace CourtadeKumar

structure LRFiniteDeterminantD9ZeroFaceCertificate where
  zero : LRHighShapeVZeroFaceCertificate
  qBY0 : LRQADCertificate
  qBE : LRQADCertificate
  qS : LRQADCertificate
  logTwoPlusV : RationalEnclosure.LogIntervalCertificate
  logD1Mean : RationalEnclosure.LogIntervalCertificate

namespace LRFiniteDeterminantD9ZeroFaceCertificate

/-- A regular-shell payload used only to share the already proved D1 node.
No theorem in this file assumes that this shell passes the regular tangent
checker. -/
def regularShell (certificate : LRFiniteDeterminantD9ZeroFaceCertificate) :
    LRFiniteDeterminantD9Certificate where
  tangent :=
    { base := certificate.zero.base
      qBY0 := certificate.qBY0
      qBE := certificate.qBE
      qS := certificate.qS
      logTwoPlusV := certificate.logTwoPlusV }
  logD1Mean := certificate.logD1Mean

structure Evaluation where
  g : RationalEnclosure
  pw : RationalEnclosure
  w : RationalEnclosure
  gap : RationalEnclosure
  halfSlope : RationalEnclosure
  d1 : RationalEnclosure
  firstBracket : RationalEnclosure
  target : RationalEnclosure

/-- Endpoint-safe value evaluation of every component used by D9. -/
def evaluateAll (terms : ℕ) (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9ZeroFaceCertificate) : Evaluation :=
  let regular := certificate.zero.base
  let coordinate := regular.kernel.coordinate
  let s := lrCertificateSAD box
  let e := lrCertificateEAD box
  let x := (lrCertificateXAD box).value
  let y0 := lrCertificateY0NonnegativeAD box
  let by0 := lrCertificateBAD s y0
  let be := lrCertificateBAD s e
  let v := (coordinate.vAD box).value
  let onePlusV := RationalEnclosure.add (RationalEnclosure.point 1) v
  let vSq := RationalEnclosure.mul v v
  let g0 := (regular.gShape.g0.evaluate terms (coordinate.vAD box)).value
  let qY0 := certificate.zero.qY0.enclosure terms y0.value
  let qE := regular.gShape.qE.value.enclosure terms
  let g := RationalEnclosure.add (RationalEnclosure.add g0 qY0)
    (RationalEnclosure.div qE v)
  let w := (regular.kernel.omegaZero.evaluate terms s).value
  let omegaY0 := certificate.zero.omegaY0.evaluate terms s y0
  let omegaE := (regular.kernel.omegaE.evaluate terms s e).value
  let pw := RationalEnclosure.add omegaY0
    (RationalEnclosure.div omegaE v)
  let qBY0 := (certificate.qBY0.evaluate terms by0).value
  let qBE := (certificate.qBE.evaluate terms be).value
  let qS := (certificate.qS.evaluate terms s).value
  let logTwo := (IntervalAD.log terms regular.gShape.g0.logTwo
    (IntervalAD.const 2)).value
  let logOnePlusV := (IntervalAD.log terms regular.ab.logOnePlusV
    (IntervalAD.add (IntervalAD.const 1) (coordinate.vAD box))).value
  let logTwoPlusV := (IntervalAD.log terms certificate.logTwoPlusV
    (IntervalAD.add (IntervalAD.const 2) (coordinate.vAD box))).value
  let squareTarget := RationalEnclosure.add
    (RationalEnclosure.add g0 qBY0) (RationalEnclosure.div qBE v)
  let core := RationalEnclosure.add g0
    (RationalEnclosure.mul
      (RationalEnclosure.add (RationalEnclosure.point 1)
        (RationalEnclosure.div (RationalEnclosure.point 1) v)) logTwo)
  let logDelta := RationalEnclosure.sub qS
    (RationalEnclosure.mul s.value logTwo)
  let prefixAtM := RationalEnclosure.add
    (RationalEnclosure.mul s.value core)
    (RationalEnclosure.div
      (RationalEnclosure.mul (RationalEnclosure.point 4) logDelta)
      onePlusV)
  let gap := RationalEnclosure.sub squareTarget prefixAtM
  let logFactor := RationalEnclosure.sub
    (RationalEnclosure.add logTwo logOnePlusV) logTwoPlusV
  let ratio := RationalEnclosure.div
    (RationalEnclosure.mul
      (RationalEnclosure.mul (RationalEnclosure.point 4) s.value)
      (RationalEnclosure.mul onePlusV onePlusV)) vSq
  let halfSlope := RationalEnclosure.add
    (RationalEnclosure.mul ratio logFactor)
    (RationalEnclosure.mul (RationalEnclosure.point 4) logDelta)
  let ab := regular.ab.evaluate terms box coordinate
  let d1 := ((certificate.regularShell).d1AD terms box).value
  let psi := RationalEnclosure.sub (RationalEnclosure.add g pw)
    (RationalEnclosure.div
      (RationalEnclosure.mul (RationalEnclosure.point 4) w) onePlusV)
  let delta := RationalEnclosure.div
    (RationalEnclosure.sub (RationalEnclosure.point 1)
      (RationalEnclosure.mul v x)) onePlusV
  let firstBracket := RationalEnclosure.add
    (RationalEnclosure.mul ab.b.value
      (RationalEnclosure.add (RationalEnclosure.sub psi g)
        (RationalEnclosure.mul
          (RationalEnclosure.mul (RationalEnclosure.point 4) delta) w)))
    (RationalEnclosure.mul d1 psi)
  let factor := RationalEnclosure.sub
    (RationalEnclosure.mul ab.b.value x) d1
  let target := RationalEnclosure.add
    (RationalEnclosure.mul
      (RationalEnclosure.mul (RationalEnclosure.point 3) halfSlope)
      firstBracket)
    (RationalEnclosure.mul
      (RationalEnclosure.mul
        (RationalEnclosure.mul (RationalEnclosure.point 4) w) gap)
      factor)
  { g := g
    pw := pw
    w := w
    gap := gap
    halfSlope := halfSlope
    d1 := d1
    firstBracket := firstBracket
    target := target }

def enclose (terms : ℕ) (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9ZeroFaceCertificate) :
    RationalEnclosure :=
  (certificate.evaluateAll terms box).target

/-- Every transcendental proposal and every positive denominator used by the
value-only evaluator is checked.  In particular, this asks only for the
zero-aware value payloads at `chi*e`; no derivative of `Q` at zero occurs. -/
def payloadCheck (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9ZeroFaceCertificate) : Bool :=
  let regular := certificate.zero.base
  let coordinate := regular.kernel.coordinate
  let s := lrCertificateSAD box
  let e := lrCertificateEAD box
  let y0 := lrCertificateY0NonnegativeAD box
  let v := coordinate.vAD box
  decide (
    certificate.zero.check box = true ∧
    certificate.qBY0.check (lrCertificateBAD s y0).value = true ∧
    certificate.qBE.check (lrCertificateBAD s e).value = true ∧
    certificate.qS.check s.value = true ∧
    certificate.logTwoPlusV.check
      (IntervalAD.add (IntervalAD.const 2) v).value = true ∧
    certificate.logD1Mean.check
      (LRFiniteDeterminantD9Certificate.d1MeanAD box).value = true ∧
    (0 : ℚ) < (lrCertificateSAD box).value.lower ∧
    (0 : ℚ) < (lrCertificateKAD box).value.lower ∧
    (0 : ℚ) < (lrCertificateRAD box).value.lower ∧
    (0 : ℚ) <
      (LRFiniteDeterminantD9Certificate.d1DenominatorAD box).value.lower ∧
    (0 : ℚ) <
      (RationalEnclosure.add (RationalEnclosure.point 1) v.value).lower ∧
    (0 : ℚ) <
      (RationalEnclosure.add (RationalEnclosure.point 2) v.value).lower ∧
    (0 : ℚ) < (RationalEnclosure.mul v.value v.value).lower)

set_option maxHeartbeats 800000 in
theorem evaluate_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint}
    {certificate : LRFiniteDeterminantD9ZeroFaceCertificate}
    (hpoint : box.Contains point)
    (hcheck : certificate.payloadCheck box = true) :
    (certificate.enclose terms box).Contains
      (lrFiniteDeterminantD9ReplayTarget point) := by
  let regular := certificate.zero.base
  let coordinate := regular.kernel.coordinate
  let s := lrCertificateSAD box
  let e := lrCertificateEAD box
  let x := (lrCertificateXAD box).value
  let y0 := lrCertificateY0NonnegativeAD box
  let by0 := lrCertificateBAD s y0
  let be := lrCertificateBAD s e
  let vAD := coordinate.vAD box
  let v := vAD.value
  let onePlusV := RationalEnclosure.add (RationalEnclosure.point 1) v
  let twoPlusV := RationalEnclosure.add (RationalEnclosure.point 2) v
  let vSq := RationalEnclosure.mul v v
  have hparts :
      certificate.zero.check box = true ∧
      certificate.qBY0.check by0.value = true ∧
      certificate.qBE.check be.value = true ∧
      certificate.qS.check s.value = true ∧
      certificate.logTwoPlusV.check
        (IntervalAD.add (IntervalAD.const 2) vAD).value = true ∧
      certificate.logD1Mean.check
        (LRFiniteDeterminantD9Certificate.d1MeanAD box).value = true ∧
      (0 : ℚ) < (lrCertificateSAD box).value.lower ∧
      (0 : ℚ) < (lrCertificateKAD box).value.lower ∧
      (0 : ℚ) < (lrCertificateRAD box).value.lower ∧
      (0 : ℚ) <
        (LRFiniteDeterminantD9Certificate.d1DenominatorAD box).value.lower ∧
      (0 : ℚ) < onePlusV.lower ∧
      (0 : ℚ) < twoPlusV.lower ∧
      (0 : ℚ) < vSq.lower := by
    simpa [payloadCheck, regular, coordinate, s, e, y0, by0, be,
      vAD, v, onePlusV, twoPlusV, vSq] using hcheck
  rcases hparts with ⟨hzero, hqBY0Check, hqBECheck, hqSCheck,
    hlogTwoPlusVCheck, hlogD1Check, hsLower, hkLower, hRLower,
    hd1Den, honePlusVLower, htwoPlusVLower, hvSqLower⟩

  have hzeroChecked :
      decide ((0 : ℚ) ≤ box.chiLo ∧
        (0 : ℚ) ≤ (lrCertificateEAD box).value.lower) = true ∧
      decide (
        coordinate.check box = true ∧
        regular.kernel.omegaZero.check s = true ∧
        certificate.zero.omegaY0.check s y0 = true ∧
        regular.kernel.omegaE.check s e = true ∧
        regular.gShape.g0.check vAD = true ∧
        certificate.zero.qY0.check y0.value = true ∧
        regular.gShape.qE.value.check e.value = true ∧
        regular.ab.check box coordinate = true ∧
        (0 : ℚ) < v.lower) = true := by
    simpa [LRHighShapeVZeroFaceCertificate.check, regular, coordinate,
      s, e, y0, vAD, v] using hzero
  have hdomain : (0 : ℚ) ≤ box.chiLo ∧
      (0 : ℚ) ≤ (lrCertificateEAD box).value.lower := by
    simpa using hzeroChecked.1
  have hzeroParts :
      coordinate.check box = true ∧
      regular.kernel.omegaZero.check s = true ∧
      certificate.zero.omegaY0.check s y0 = true ∧
      regular.kernel.omegaE.check s e = true ∧
      regular.gShape.g0.check vAD = true ∧
      certificate.zero.qY0.check y0.value = true ∧
      regular.gShape.qE.value.check e.value = true ∧
      regular.ab.check box coordinate = true ∧
      (0 : ℚ) < v.lower := by
    simpa using hzeroChecked.2
  rcases hzeroParts with ⟨hcoordinate, homegaZeroCheck,
    homegaY0Check, homegaECheck, hg0Check, hqY0Check, hqECheck,
    habCheck, hvLower⟩

  have hg0Parts :
      regular.gShape.g0.logV.check v = true ∧
      regular.gShape.g0.logOnePlusV.check
        (LRG0ADCertificate.onePlusV vAD).value = true ∧
      regular.gShape.g0.logTwo.check (IntervalAD.const 2).value = true ∧
      (0 : ℚ) < v.lower := by
    simpa [LRG0ADCertificate.check] using hg0Check
  have habParts :
      coordinate.check box = true ∧
      regular.ab.logOnePlusV.check
        (IntervalAD.add (IntervalAD.const 1) vAD).value = true ∧
      regular.ab.logE.check e.value = true ∧
      regular.ab.logBE.check (lrCertificateBAD s e).value = true := by
    simpa [LRHighShapeABCertificate.check, regular, coordinate, vAD, s, e]
      using habCheck

  have hsAD := IntervalAD.contains_variableS
    (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have heAD := lrCertificateEAD_sound hpoint
  have hxAD := lrCertificateXAD_sound hpoint
  have hy0AD := lrCertificateY0NonnegativeAD_sound hpoint
    hdomain.1 hdomain.2
  have hvADSound := coordinate.vAD_sound hpoint hcoordinate
  have hvValue : v.Contains (lrCertificateV point) := by
    simpa [v, vAD] using hvADSound.1
  have hvLowerReal : (0 : ℝ) < (v.lower : ℝ) := by
    exact_mod_cast hvLower
  have hvPos : 0 < lrCertificateV point :=
    hvLowerReal.trans_le hvValue.1
  have hvPlus : 1 + lrCertificateV point ≠ 0 := by linarith
  have htwoPlus : 2 + lrCertificateV point ≠ 0 := by linarith
  have hby0AD := lrCertificateBAD_sound hsAD hy0AD
  have hbeAD := lrCertificateBAD_sound hsAD heAD
  have hqBY0AD := certificate.qBY0.sound terms hqBY0Check hby0AD
  have hqBEAD := certificate.qBE.sound terms hqBECheck hbeAD
  have hqSAD := certificate.qS.sound terms hqSCheck hsAD
  have hg0AD := regular.gShape.g0.sound terms hg0Check hvADSound
  have hqY0 := certificate.zero.qY0.sound terms hqY0Check hy0AD.1
  have hqE := regular.gShape.qE.value.sound terms hqECheck heAD.1
  have hab := regular.ab.sound terms hpoint habCheck
  have hwAD := regular.kernel.omegaZero.sound terms homegaZeroCheck hsAD
  have homegaY0 := certificate.zero.omegaY0.sound terms
    homegaY0Check hsAD hy0AD
  have homegaEAD := regular.kernel.omegaE.sound terms
    homegaECheck hsAD heAD

  have hg0 := hg0AD.1
  have hqBY0 := hqBY0AD.1
  have hqBE := hqBEAD.1
  have hqS := hqSAD.1
  have hw := hwAD.1
  have homegaE := homegaEAD.1
  have hqEdiv := RationalEnclosure.contains_div hvLower hqE hvValue
  have hg := RationalEnclosure.contains_add
    (RationalEnclosure.contains_add hg0 hqY0) hqEdiv
  have homegaEdiv := RationalEnclosure.contains_div hvLower
    homegaE hvValue
  have hpw := RationalEnclosure.contains_add homegaY0 homegaEdiv

  have hlogTwoAD := IntervalAD.contains_log terms hg0Parts.2.2.1
    (IntervalAD.contains_const 2)
  have honePlusVAD := IntervalAD.contains_add
    (IntervalAD.contains_const 1) hvADSound
  have htwoPlusVAD := IntervalAD.contains_add
    (IntervalAD.contains_const 2) hvADSound
  have hlogOnePlusVAD := IntervalAD.contains_log terms habParts.2.1
    honePlusVAD
  have hlogTwoPlusVAD := IntervalAD.contains_log terms
    hlogTwoPlusVCheck htwoPlusVAD
  have hlogTwo := hlogTwoAD.1
  have hlogOnePlusV := hlogOnePlusVAD.1
  have hlogTwoPlusV := hlogTwoPlusVAD.1
  have honePlusV := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 1) hvValue
  have htwoPlusV := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 2) hvValue
  have hvSq := RationalEnclosure.contains_mul hvValue hvValue

  have hsquare := RationalEnclosure.contains_add
    (RationalEnclosure.contains_add hg0 hqBY0)
    (RationalEnclosure.contains_div hvLower hqBE hvValue)
  have hsquareNamed :
      (RationalEnclosure.add
        (RationalEnclosure.add
          (regular.gShape.g0.evaluate terms vAD).value
          (certificate.qBY0.evaluate terms by0).value)
        (RationalEnclosure.div
          (certificate.qBE.evaluate terms be).value v)).Contains
        (lrCertificateSquareTarget point) := by
    exact hsquare

  have hinvV := RationalEnclosure.contains_div hvLower
    (RationalEnclosure.contains_point 1) hvValue
  have hfactor := RationalEnclosure.contains_add
    (RationalEnclosure.contains_point 1) hinvV
  have hcore := RationalEnclosure.contains_add hg0
    (RationalEnclosure.contains_mul hfactor hlogTwo)
  have hlogDelta := RationalEnclosure.contains_sub hqS
    (RationalEnclosure.contains_mul hsAD.1 hlogTwo)
  have hprefix := RationalEnclosure.contains_add
    (RationalEnclosure.contains_mul hsAD.1 hcore)
    (RationalEnclosure.contains_div honePlusVLower
      (RationalEnclosure.contains_mul
        (RationalEnclosure.contains_point 4) hlogDelta)
      honePlusV)
  have hprefixNamed :
      (RationalEnclosure.add
        (RationalEnclosure.mul s.value
          (RationalEnclosure.add
            (regular.gShape.g0.evaluate terms vAD).value
            (RationalEnclosure.mul
              (RationalEnclosure.add (RationalEnclosure.point 1)
                (RationalEnclosure.div (RationalEnclosure.point 1) v))
              (IntervalAD.log terms regular.gShape.g0.logTwo
                (IntervalAD.const 2)).value)))
        (RationalEnclosure.div
          (RationalEnclosure.mul (RationalEnclosure.point 4)
            (RationalEnclosure.sub (certificate.qS.evaluate terms s).value
              (RationalEnclosure.mul s.value
                (IntervalAD.log terms regular.gShape.g0.logTwo
                  (IntervalAD.const 2)).value))) onePlusV)).Contains
        (lrCertificatePrefixAtM point) := by
    convert hprefix using 1
    simp only [lrCertificatePrefixAtM]
    field_simp [hvPos.ne', hvPlus]
    ring
  have hgap := RationalEnclosure.contains_sub hsquareNamed hprefixNamed

  have hlogFactor := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add hlogTwo hlogOnePlusV)
    hlogTwoPlusV
  have honePlusVSq := RationalEnclosure.contains_mul honePlusV honePlusV
  have hratio := RationalEnclosure.contains_div hvSqLower
    (RationalEnclosure.contains_mul
      (RationalEnclosure.contains_mul
        (RationalEnclosure.contains_point 4) hsAD.1) honePlusVSq) hvSq
  have hhalfSlope := RationalEnclosure.contains_add
    (RationalEnclosure.contains_mul hratio hlogFactor)
    (RationalEnclosure.contains_mul
      (RationalEnclosure.contains_point 4) hlogDelta)
  have hhalfSlopeNamed :
      (RationalEnclosure.add
        (RationalEnclosure.mul
          (RationalEnclosure.div
            (RationalEnclosure.mul
              (RationalEnclosure.mul (RationalEnclosure.point 4) s.value)
              (RationalEnclosure.mul onePlusV onePlusV)) vSq)
          (RationalEnclosure.sub
            (RationalEnclosure.add
              (IntervalAD.log terms regular.gShape.g0.logTwo
                (IntervalAD.const 2)).value
              (IntervalAD.log terms regular.ab.logOnePlusV
                (IntervalAD.add (IntervalAD.const 1) vAD)).value)
            (IntervalAD.log terms certificate.logTwoPlusV
              (IntervalAD.add (IntervalAD.const 2) vAD)).value))
        (RationalEnclosure.mul (RationalEnclosure.point 4)
          (RationalEnclosure.sub (certificate.qS.evaluate terms s).value
            (RationalEnclosure.mul s.value
              (IntervalAD.log terms regular.gShape.g0.logTwo
                (IntervalAD.const 2)).value)))).Contains
        (lrCertificateHalfSlope point) := by
    convert hhalfSlope using 1
    simp only [lrCertificateHalfSlope, pow_two]
    field_simp [hvPos.ne', hvPlus, htwoPlus]
    ring

  have hd1 := (certificate.regularShell).d1AD_value_sound terms hpoint
    hsLower hkLower hlogD1Check hd1Den
  have hpsi := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_add hg hpw)
    (RationalEnclosure.contains_div honePlusVLower
      (RationalEnclosure.contains_mul
        (RationalEnclosure.contains_point 4) hw) honePlusV)
  have hdelta := RationalEnclosure.contains_div honePlusVLower
    (RationalEnclosure.contains_sub (RationalEnclosure.contains_point 1)
      (RationalEnclosure.contains_mul hvValue hxAD.1)) honePlusV
  have hfourDeltaW := RationalEnclosure.contains_mul
    (RationalEnclosure.contains_mul
      (RationalEnclosure.contains_point 4) hdelta) hw
  have hfirst := RationalEnclosure.contains_add
    (RationalEnclosure.contains_mul hab.2.1.1
      (RationalEnclosure.contains_add
        (RationalEnclosure.contains_sub hpsi hg) hfourDeltaW))
    (RationalEnclosure.contains_mul hd1 hpsi)
  have hfactorD1 := RationalEnclosure.contains_sub
    (RationalEnclosure.contains_mul hab.2.1.1 hxAD.1) hd1
  have htarget := RationalEnclosure.contains_add
    (RationalEnclosure.contains_mul
      (RationalEnclosure.contains_mul
        (RationalEnclosure.contains_point 3) hhalfSlopeNamed) hfirst)
    (RationalEnclosure.contains_mul
      (RationalEnclosure.contains_mul
        (RationalEnclosure.contains_mul
          (RationalEnclosure.contains_point 4) hw) hgap) hfactorD1)

  have hsLowerReal : (0 : ℝ) <
      (((lrCertificateSAD box).value.lower : ℚ) : ℝ) := by
    exact_mod_cast hsLower
  have hRLowerReal : (0 : ℝ) <
      (((lrCertificateRAD box).value.lower : ℚ) : ℝ) := by
    exact_mod_cast hRLower
  have hR := lrCertificateRAD_sound hpoint
  have hsPos : 0 < point.s := hsLowerReal.trans_le hsAD.1.1
  have hRPos : 0 < lrCertificateR point :=
    hRLowerReal.trans_le hR.1.1
  have htargetEq :
      lrFiniteDeterminantD9ReplayTarget point =
        3 * lrCertificateHalfSlope point *
            lrDeterminantFirstBracket
              (lrCertificateBFlow point) (lrDeterminantD1 point)
              (lrCertificateGShape point) (lrDeterminantPsi point)
              (lrDeterminantDelta point) (lrCertificateW point) +
          4 * lrCertificateW point * lrCertificateGap point *
            (lrCertificateBFlow point * lrCertificateX point -
              lrDeterminantD1 point) := by
    unfold lrFiniteDeterminantD9ReplayTarget lrDeterminantHd lrDeterminantT
    field_simp [hsPos.ne', hRPos.ne']

  unfold enclose evaluateAll
  dsimp only
  rw [htargetEq]
  simpa [regular, coordinate, s, e, x, y0, by0, be, vAD, v,
    onePlusV, twoPlusV, vSq, lrCertificateGShape,
    lrCertificateGShapeValue, lrCertificatePW, lrCertificatePWValue,
    lrDeterminantPsi, lrDeterminantDelta, lrDeterminantFirstBracket]
    using htarget

noncomputable def checkedEvaluatorSound (terms : ℕ) :
    CheckedEnclosureLeafEvaluatorSound lrFiniteDeterminantD9ReplayTarget
      payloadCheck (enclose terms) := by
  constructor
  intro box certificate hpayload point hpoint
  exact certificate.evaluate_sound terms hpoint hpayload

def accepts (terms : ℕ) (box : CertificateBox)
    (certificate : LRFiniteDeterminantD9ZeroFaceCertificate) : Bool :=
  checkedEnclosureLeafAccepts payloadCheck (enclose terms) box certificate

/-- Deterministic untrusted proposal for one zero-face leaf. -/
def auto (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    LRFiniteDeterminantD9ZeroFaceCertificate :=
  let zero := LRHighShapeVZeroFaceCertificate.auto sqrtFuel logFuel box
  let regular := zero.base
  let s := lrCertificateSAD box
  let e := lrCertificateEAD box
  let y0 := lrCertificateY0NonnegativeAD box
  let v := regular.kernel.coordinate.vAD box
  { zero := zero
    qBY0 := LRQADCertificate.auto sqrtFuel logFuel
      (lrCertificateBAD s y0).value
    qBE := LRQADCertificate.auto sqrtFuel logFuel
      (lrCertificateBAD s e).value
    qS := LRQADCertificate.auto sqrtFuel logFuel s.value
    logTwoPlusV := RationalEnclosure.autoLogIntervalCertificate logFuel
      (IntervalAD.add (IntervalAD.const 2) v).value
    logD1Mean := RationalEnclosure.autoLogIntervalCertificate logFuel
      (LRFiniteDeterminantD9Certificate.d1MeanAD box).value }

end LRFiniteDeterminantD9ZeroFaceCertificate

/-! ## Hybrid accepted-leaf rule -/

inductive LRFiniteDeterminantD9HybridAcceptData where
  | regular (certificate : LRFiniteDeterminantD9Certificate)
  | zeroFace (certificate : LRFiniteDeterminantD9ZeroFaceCertificate)

namespace LRFiniteDeterminantD9HybridAcceptData

def payloadCheck (box : CertificateBox) :
    LRFiniteDeterminantD9HybridAcceptData → Bool
  | .regular certificate =>
      LRFiniteDeterminantD9Certificate.payloadCheck box certificate
  | .zeroFace certificate =>
      LRFiniteDeterminantD9ZeroFaceCertificate.payloadCheck box certificate

def enclose (terms : ℕ) (box : CertificateBox) :
    LRFiniteDeterminantD9HybridAcceptData → RationalEnclosure
  | .regular certificate =>
      LRFiniteDeterminantD9Certificate.enclose terms box certificate
  | .zeroFace certificate =>
      LRFiniteDeterminantD9ZeroFaceCertificate.enclose terms box certificate

noncomputable def checkedEvaluatorSound (terms : ℕ) :
    CheckedEnclosureLeafEvaluatorSound lrFiniteDeterminantD9ReplayTarget
      payloadCheck (enclose terms) := by
  constructor
  intro box data hpayload point hpoint
  cases data with
  | regular certificate =>
      exact certificate.evaluate_value_sound terms hpoint hpayload
  | zeroFace certificate =>
      exact certificate.evaluate_sound terms hpoint hpayload

def accepts (terms : ℕ) (box : CertificateBox)
    (data : LRFiniteDeterminantD9HybridAcceptData) : Bool :=
  checkedEnclosureLeafAccepts payloadCheck (enclose terms) box data

/-- A hybrid checked tree has exactly the historical D9 semantics, while
allowing closed leaves at `chi = 0` to use endpoint-safe values. -/
def toRawCheckedTree
    (terms : ℕ) {root : CertificateBox}
    (tree : SubdivisionCertificate LRFiniteDeterminantD9HybridAcceptData
      LRHighShapeVDiscardData)
    (hcheck : tree.check (accepts terms)
      (lrHighShapeVDiscardCheck terms) root = true) :
    LRFiniteDeterminantRawD9CheckedTree root where
  AcceptData := LRFiniteDeterminantD9HybridAcceptData
  DiscardData := LRHighShapeVDiscardData
  payloadCheck := payloadCheck
  enclose := enclose terms
  discardCheck := lrHighShapeVDiscardCheck terms
  encloseSound := checkedEvaluatorSound terms
  discardCompatible := lrHighShapeVDiscardCheck_sound terms
  certificate := tree
  checked := hcheck

end LRFiniteDeterminantD9HybridAcceptData
end CourtadeKumar
