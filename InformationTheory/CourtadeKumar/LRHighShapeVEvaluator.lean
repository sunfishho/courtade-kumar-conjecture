import InformationTheory.CourtadeKumar.LRHighShapeTangentEvaluator
import InformationTheory.CourtadeKumar.LRLowShapeTAlgebra
import InformationTheory.CourtadeKumar.LRPhysicalDiscardCertificate
import InformationTheory.CourtadeKumar.LRFullFlowAssembly

/-!
# Direct evaluator for the high-shape cancellation reserve `V`

The final audited high-shape ledger proves the outer-midpoint numerator,
called `s² V` in the manuscript.  It is obtained from the already verified
half-midpoint numerator by the exact affine correction

`N(M) = N(M / 2) - 2 W M J`.

This file packages that identity as a payload-checked whole-box interval
extension.  Unlike the tangent evaluator it needs no square-target, gap, or
half-slope payload.
-/

open Set

namespace CourtadeKumar

/-- The unnormalized manuscript target `s² V`, expressed in cancellation
coordinates. -/
noncomputable def lrCertificateVTarget (point : CertificatePoint) : ℝ :=
  lrCertificateMidpointNumerator point

theorem lrCertificateVTarget_eq_halfMidpoint_sub
    (point : CertificatePoint) :
    lrCertificateVTarget point =
      lrCertificateHalfMidpointNumerator point -
        2 * lrCertificateW point * lrCertificateM point *
          lrCertificateJ point := by
  unfold lrCertificateVTarget lrCertificateMidpointNumerator
    lrCertificateHalfMidpointNumerator lrCertificateMidpointBracket
    lrCertificateHalfMidpointBracket lrCertificateJ
  ring

/-- Identification of the finite target with the analytic outer-midpoint
reserve used by the direct flow closure. -/
theorem lrCertificateVTarget_eq_lrLowVReserve
    {point : CertificatePoint}
    (hs : point.s ∈ Ioo (0 : ℝ) 1)
    (he : lrCertificateE point ∈ Ioo (0 : ℝ) 1)
    (hchi : point.chi ∈ Icc (0 : ℝ) 1) :
    lrCertificateVTarget point =
      lrLowVReserve (lrCertificateR point) (lrCertificateV point)
        (lrCertificateT point) := by
  have hxPos : 0 < lrCertificateX point := by
    unfold lrCertificateX
    have hprod : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point ≤ 1 * lrCertificateE point :=
          mul_le_mul_of_nonneg_right hchi.2 he.1.le
        _ = lrCertificateE point := one_mul _
        _ < 1 := he.2
    linarith
  have hradPos : 0 <
      (1 - lrCertificateE point) / lrCertificateX point :=
    div_pos (sub_pos.mpr he.2) hxPos
  have hvPos : 0 < lrCertificateV point := Real.sqrt_pos.2 hradPos
  unfold lrCertificateVTarget
  rw [lrCertificateMidpointNumerator_eq_flow hs he hchi,
    lrFlowNumeratorP_midpoint_eq_lrLowVReserve (by linarith)]

theorem lrCertificateVTarget_flow
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrCertificateVTarget (lrFlowCertificatePoint R v t) =
      lrLowVReserve R v t := by
  have hRNe : R ≠ 1 := hR.2.ne
  have hvtPos : 0 < v * t := mul_pos hv.1 ht.1
  have hvtLt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hePos : 0 < 1 - v ^ 2 * t ^ 2 := by
    nlinarith [sq_pos_of_pos hvtPos]
  have heLt : 1 - v ^ 2 * t ^ 2 < 1 := by
    nlinarith [sq_pos_of_pos hvtPos]
  have he : lrCertificateE (lrFlowCertificatePoint R v t) ∈
      Ioo (0 : ℝ) 1 := by
    rw [lrCertificateE_flow hRNe]
    exact ⟨hePos, heLt⟩
  have htSqLe : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hvSqLe : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
  have hchi : (lrFlowCertificatePoint R v t).chi ∈ Icc (0 : ℝ) 1 := by
    change (1 - t ^ 2) / (1 - v ^ 2 * t ^ 2) ∈ Icc (0 : ℝ) 1
    constructor
    · exact div_nonneg (sub_nonneg.mpr htSqLe) hePos.le
    · rw [div_le_one hePos]
      nlinarith [mul_nonneg (sub_nonneg.mpr hvSqLe) (sq_nonneg t)]
  have hs : (lrFlowCertificatePoint R v t).s ∈ Ioo (0 : ℝ) 1 := by
    change 1 - R ∈ Ioo (0 : ℝ) 1
    constructor <;> linarith [hR.1, hR.2]
  rw [lrCertificateVTarget_eq_lrLowVReserve hs he hchi,
    lrCertificateR_flow,
    lrCertificateV_flow hRNe hePos.ne' hv.1 ht.1,
    lrCertificateT_flow hRNe hePos.ne' ht.1]

/-- No new untrusted data are needed beyond the half-midpoint payload. -/
abbrev LRHighShapeVCertificate := LRHighShapeMidpointCertificate

namespace LRHighShapeVCertificate

def jAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeVCertificate) : IntervalAD :=
  let coordinate := certificate.kernel.coordinate
  let ab := certificate.ab.evaluate terms box coordinate
  IntervalAD.sub
    (IntervalAD.mul ab.b (lrCertificateXAD box)) ab.d

/-- Whole-box interval extension of `N(M) = s² V`. -/
def evaluateAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeVCertificate) : IntervalAD :=
  let half := certificate.numeratorAD terms box
  let correction := IntervalAD.mul
    (IntervalAD.mul
      (IntervalAD.mul (IntervalAD.const 2)
        (certificate.kernel.wAD terms box))
      (certificate.mAD box))
    (certificate.jAD terms box)
  IntervalAD.sub half correction

def enclose (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeVCertificate) : RationalEnclosure :=
  (certificate.evaluateAD terms box).value

def payloadCheck (box : CertificateBox)
    (certificate : LRHighShapeVCertificate) : Bool :=
  lrHighShapeInteriorBoxCheck box && certificate.check box

def accepts (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeVCertificate) : Bool :=
  checkedEnclosureLeafAccepts payloadCheck (enclose terms) box certificate

/-- The whole-box `V` extension only uses the arithmetic payload.  In
particular, unlike the derivative-based midpoint evaluators, its soundness
does not require every point of the box to lie in the open `χ` chart.  This
variant can therefore certify boxes whose closed faces touch `χ = 0` or
`χ = 1`. -/
def rawPayloadCheck (box : CertificateBox)
    (certificate : LRHighShapeVCertificate) : Bool :=
  certificate.check box

def rawAccepts (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeVCertificate) : Bool :=
  checkedEnclosureLeafAccepts rawPayloadCheck (enclose terms) box certificate

theorem jAD_value_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint} {certificate : LRHighShapeVCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true) :
    (certificate.jAD terms box).value.Contains (lrCertificateJ point) := by
  have hparts :
      certificate.kernel.check box = true ∧
      certificate.gShape.check box certificate.kernel.coordinate = true ∧
      certificate.ab.check box certificate.kernel.coordinate = true ∧
      (0 : ℚ) < (IntervalAD.add (IntervalAD.const 1)
        (certificate.kernel.coordinate.vAD box)).value.lower ∧
      (0 : ℚ) <
        (LRHighShapeMidpointCertificate.denominatorAD box).value.lower := by
    simpa [LRHighShapeMidpointCertificate.check] using hcheck
  have hab := certificate.ab.sound terms hpoint hparts.2.2.1
  have hx := lrCertificateXAD_sound hpoint
  have hj := IntervalAD.contains_sub
    (IntervalAD.contains_mul hab.2.1 hx) hab.2.2
  simpa [jAD, lrCertificateJ] using hj.1

theorem evaluate_value_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint} {certificate : LRHighShapeVCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true) :
    (certificate.enclose terms box).Contains (lrCertificateVTarget point) := by
  have hparts :
      certificate.kernel.check box = true ∧
      certificate.gShape.check box certificate.kernel.coordinate = true ∧
      certificate.ab.check box certificate.kernel.coordinate = true ∧
      (0 : ℚ) < (IntervalAD.add (IntervalAD.const 1)
        (certificate.kernel.coordinate.vAD box)).value.lower ∧
      (0 : ℚ) <
        (LRHighShapeMidpointCertificate.denominatorAD box).value.lower := by
    simpa [LRHighShapeMidpointCertificate.check] using hcheck
  have hhalf := certificate.numeratorAD_sound terms hpoint hcheck
  have hw := certificate.kernel.wAD_sound terms hpoint hparts.1
  have hm := certificate.mAD_sound hpoint hcheck
  have hab := certificate.ab.sound terms hpoint hparts.2.2.1
  have hx := lrCertificateXAD_sound hpoint
  have hj := IntervalAD.contains_sub
    (IntervalAD.contains_mul hab.2.1 hx) hab.2.2
  have hcorrection := IntervalAD.contains_mul
    (IntervalAD.contains_mul
      (IntervalAD.contains_mul (IntervalAD.contains_const 2) hw) hm) hj
  have h := IntervalAD.contains_sub hhalf hcorrection
  unfold enclose evaluateAD jAD
  dsimp only
  rw [lrCertificateVTarget_eq_halfMidpoint_sub]
  exact h.1

noncomputable def checkedEvaluatorSound (terms : ℕ) :
    CheckedEnclosureLeafEvaluatorSound lrCertificateVTarget payloadCheck
      (enclose terms) := by
  constructor
  intro box certificate hpayload point hpoint
  have hparts : lrHighShapeInteriorBoxCheck box = true ∧
      certificate.check box = true := by
    simpa [payloadCheck] using hpayload
  exact certificate.evaluate_value_sound terms hpoint hparts.2

noncomputable def rawCheckedEvaluatorSound (terms : ℕ) :
    CheckedEnclosureLeafEvaluatorSound lrCertificateVTarget rawPayloadCheck
      (enclose terms) := by
  constructor
  intro box certificate hpayload point hpoint
  exact certificate.evaluate_value_sound terms hpoint (by
    simpa [rawPayloadCheck] using hpayload)

end LRHighShapeVCertificate

/-- The actual finite domain: the algebraic high-shape constraints together
with the positive-`J` branch. -/
def LRHighShapeVRelevant (point : CertificatePoint) : Prop :=
  LRHighShapePhysical point ∧ 0 < lrCertificateJ point

/-- A leaf can either violate an algebraic physical constraint or lie wholly
in the nonpositive-`J` chart. -/
inductive LRHighShapeVDiscardData where
  | physical (reason : LRPhysicalDiscardData)
  | jNonpositive (certificate : LRHighShapeVCertificate)

def lrHighShapeVDiscardCheck (terms : ℕ) (box : CertificateBox)
    (data : LRHighShapeVDiscardData) : Bool :=
  match data with
  | .physical reason => lrPhysicalDiscardCheck box reason
  | .jNonpositive certificate =>
      LRHighShapeVCertificate.payloadCheck box certificate &&
        decide ((certificate.jAD terms box).value.upper ≤ 0)

theorem lrHighShapeVDiscardCheck_sound (terms : ℕ)
    (box : CertificateBox) (data : LRHighShapeVDiscardData)
    (hcheck : lrHighShapeVDiscardCheck terms box data = true) :
    ∀ point, box.Contains point → ¬ LRHighShapeVRelevant point := by
  intro point hpoint hRelevant
  rcases hRelevant with ⟨hphysical, hJ⟩
  cases data with
  | physical reason =>
      exact lrPhysicalDiscardCheck_sound box reason
        (by simpa [lrHighShapeVDiscardCheck] using hcheck)
        point hpoint hphysical
  | jNonpositive certificate =>
      have hparts :
          LRHighShapeVCertificate.payloadCheck box certificate = true ∧
          (certificate.jAD terms box).value.upper ≤ 0 := by
        simpa [lrHighShapeVDiscardCheck] using hcheck
      have hpayload : lrHighShapeInteriorBoxCheck box = true ∧
          certificate.check box = true := by
        simpa [LRHighShapeVCertificate.payloadCheck] using hparts.1
      have henclose := certificate.jAD_value_sound terms hpoint hpayload.2
      have hupper :
          (((certificate.jAD terms box).value.upper : ℚ) : ℝ) ≤ 0 := by
        exact_mod_cast hparts.2
      linarith [henclose.2]

/-- End-to-end checker theorem for a concrete high-shape `V` subdivision. -/
theorem lrHighShapeVSubdivisionCertificate_nonnegative
    (terms : ℕ) {box : CertificateBox}
    {certificate : SubdivisionCertificate LRHighShapeVCertificate
      LRHighShapeVDiscardData}
    (hcheck : certificate.check
      (LRHighShapeVCertificate.accepts terms)
      (lrHighShapeVDiscardCheck terms) box = true) :
    ∀ point, box.Contains point → LRHighShapeVRelevant point →
      0 ≤ lrCertificateVTarget point := by
  exact subdivisionCertificate_nonnegative_checkedEnclosure
    (LRHighShapeVCertificate.checkedEvaluatorSound terms)
    (lrHighShapeVDiscardCheck_sound terms) hcheck

/-- Direct-`V` subdivisions may use the closed-chart raw checker at accepted
leaves.  Discard leaves retain their existing, independently sound checker. -/
theorem lrHighShapeVRawSubdivisionCertificate_nonnegative
    (terms : ℕ) {box : CertificateBox}
    {certificate : SubdivisionCertificate LRHighShapeVCertificate
      LRHighShapeVDiscardData}
    (hcheck : certificate.check
      (LRHighShapeVCertificate.rawAccepts terms)
      (lrHighShapeVDiscardCheck terms) box = true) :
    ∀ point, box.Contains point → LRHighShapeVRelevant point →
      0 ≤ lrCertificateVTarget point := by
  exact subdivisionCertificate_nonnegative_checkedEnclosure
    (LRHighShapeVCertificate.rawCheckedEvaluatorSound terms)
    (lrHighShapeVDiscardCheck_sound terms) hcheck

/-- Every analytic high-shape positive-`J` point maps into the exact
relevance predicate used by the finite cancellation-coordinate checker. -/
theorem lrFlowCertificatePoint_highShapeVRelevant
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htHigh : 17 / 20 ≤ t ^ 2) (hvHigh : 1 / 3 ≤ v)
    (hJ : 0 < lrFlowJ R v t) :
    LRHighShapeVRelevant (lrFlowCertificatePoint R v t) := by
  let point := lrFlowCertificatePoint R v t
  have hRNe : R ≠ 1 := hR.2.ne
  have hvtPos : 0 < v * t := mul_pos hv.1 ht.1
  have hvtLt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hePos : 0 < 1 - v ^ 2 * t ^ 2 := by
    nlinarith [sq_pos_of_pos hvtPos]
  have heLt : 1 - v ^ 2 * t ^ 2 < 1 := by
    nlinarith [sq_pos_of_pos hvtPos]
  have he : lrCertificateE point ∈ Ioo (0 : ℝ) 1 := by
    rw [show lrCertificateE point = 1 - v ^ 2 * t ^ 2 by
      exact lrCertificateE_flow hRNe]
    exact ⟨hePos, heLt⟩
  have htSqLe : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hvSqLe : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 := by
    change (1 - t ^ 2) / (1 - v ^ 2 * t ^ 2) ∈ Icc (0 : ℝ) 1
    constructor
    · exact div_nonneg (sub_nonneg.mpr htSqLe) hePos.le
    · rw [div_le_one hePos]
      nlinarith [mul_nonneg (sub_nonneg.mpr hvSqLe) (sq_nonneg t)]
  have hs : point.s ∈ Ioo (0 : ℝ) 1 := by
    change 1 - R ∈ Ioo (0 : ℝ) 1
    constructor <;> linarith [hR.1, hR.2]
  have hphysical : LRHighShapePhysical point := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [point] using he.2
    · rw [show point.s * point.k = lrCertificateE point by rfl,
        show lrCertificateE point = 1 - v ^ 2 * t ^ 2 by
          exact lrCertificateE_flow hRNe]
      change (1 - t ^ 2) / (1 - v ^ 2 * t ^ 2) *
          (1 - v ^ 2 * t ^ 2) ≤ 3 / 20
      rw [div_mul_cancel₀ _ hePos.ne']
      linarith
    · rw [show point.s * point.k = lrCertificateE point by rfl,
        show lrCertificateE point = 1 - v ^ 2 * t ^ 2 by
          exact lrCertificateE_flow hRNe]
      change 0 ≤ 8 - (1 - v ^ 2 * t ^ 2) *
        (9 - (1 - t ^ 2) / (1 - v ^ 2 * t ^ 2))
      have hid : 8 - (1 - v ^ 2 * t ^ 2) *
          (9 - (1 - t ^ 2) / (1 - v ^ 2 * t ^ 2)) =
          t ^ 2 * (9 * v ^ 2 - 1) := by
        field_simp [hePos.ne']
        ring
      rw [hid]
      have hvFactor : 0 ≤ (v - 1 / 3) * (v + 1 / 3) :=
        mul_nonneg (sub_nonneg.mpr hvHigh) (by linarith [hv.1])
      have : 0 ≤ 9 * v ^ 2 - 1 := by nlinarith
      exact mul_nonneg (sq_nonneg t) this
  refine ⟨hphysical, ?_⟩
  change 0 < lrCertificateJ (lrFlowCertificatePoint R v t)
  rw [lrCertificateJ_eq_flow hs he hchi, lrCertificateR_flow,
    lrCertificateV_flow hRNe hePos.ne' hv.1 ht.1,
    lrCertificateT_flow hRNe hePos.ne' ht.1]
  exact hJ

/-- Coordinate-level statement supplied by the complete collection of
finite roots and analytic tails. -/
def LRHighShapeVCoordinateTheorem : Prop :=
  ∀ point : CertificatePoint,
    LRHighShapeVRelevant point → 0 ≤ lrCertificateVTarget point

/-- Once all cancellation-coordinate roots are covered, the exact change of
variables turns their result into the sole high-shape assumption required by
the reduced flow assembly. -/
theorem lrHighShapeVTheorem_of_coordinateTheorem
    (hcoordinate : LRHighShapeVCoordinateTheorem) :
    LRHighShapeVTheorem := by
  intro R v t hR hv ht htHigh hvHigh hJ
  have htarget := hcoordinate (lrFlowCertificatePoint R v t)
    (lrFlowCertificatePoint_highShapeVRelevant
      hR hv ht htHigh hvHigh hJ)
  rw [lrCertificateVTarget_flow hR hv ht] at htarget
  exact htarget

end CourtadeKumar
