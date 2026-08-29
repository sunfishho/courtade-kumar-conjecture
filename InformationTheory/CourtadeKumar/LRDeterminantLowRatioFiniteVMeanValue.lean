import InformationTheory.CourtadeKumar.IntervalMidpointSKCertificate
import InformationTheory.CourtadeKumar.LRDeterminantFiniteRegions
import InformationTheory.CourtadeKumar.LRDeterminantFiniteReplayTargets
import InformationTheory.CourtadeKumar.LRDeterminantLowRatio
import InformationTheory.CourtadeKumar.LRDeterminantPositiveFactors
import InformationTheory.CourtadeKumar.LRHighShapeVMidpointEvaluator

/-!
# Correlated mean-value boundary for the last two low-ratio `V` roots

The first twenty finite low-ratio roots use exactly the same historical
target as the sharp upper-`K` evaluator:

`FirstBracket / e` in the chart `k = s*K`, `chi = h^2`.

Consequently those roots should reuse `LRUpperKReplayCertificate` rather
than acquire a second copy of its substantial cancellation arithmetic.
Only the last two roots, on

`1/16 <= s <= 1/10`, `1/4 <= K <= 1`, `0 <= h <= 1`,

switch to the stronger direct-`V` target.  This file gives the complete
analytic and structural boundary for that genuinely new evaluator:

* the sign-equivalent normalized target used by the historical replay;
* its cancellation-preserving exact identity;
* exact `(s,K)` chart derivatives and their calculus proofs;
* a two-coordinate mean-value leaf checker which encloses the full closed
  `h` interval directly (so no derivative at `h = 0` is requested);
* checked-tree and two-root adapters proving the upper finite-`V` band.

The only remaining implementation work behind the abstract `Oracle` below
is exact interval arithmetic.  A concrete oracle should reuse the sharp
upper-`K` payload, add the `log Y` enclosure needed for `D = log Y / 2`, and
evaluate the cancellation target `cancellationTarget` below.  There are no
proof fields in generated tree data and no use of `native_decide`.
-/

open Set

namespace CourtadeKumar
namespace LRLowRatioFiniteVMeanValue

/-! ## Sign-equivalent cancellation target -/

/-- The exact historical direct-`V` replay target.  Its denominator is
strictly positive on the high-shape interior, so its sign is exactly the
sign of the unnormalized `lrCertificateVTarget`. -/
noncomputable def normalizedTarget (point : CertificatePoint) : ℝ :=
  lrCertificateVTarget point /
    (lrCertificateBFlow point * lrCertificateE point)

/-- Cancellation-preserving form evaluated by the historical low-`K`
checker.  Writing `C = Psi - G`, the numerator is

`(D/B) G + (1 + D/B) C + 4 delta W`.

It avoids forming the badly correlated sum `D*Psi + B*(Psi-G+4*delta*W)`
before division by the positive factors `B*e`. -/
noncomputable def cancellationTarget (point : CertificatePoint) : ℝ :=
  ((lrCertificateD point / lrCertificateBFlow point) *
        lrCertificateGShape point +
      (1 + lrCertificateD point / lrCertificateBFlow point) *
        (lrDeterminantPsi point - lrCertificateGShape point) +
      4 * lrDeterminantDelta point * lrCertificateW point) /
    lrCertificateE point

/-- The cancellation expression is exactly the normalized physical target,
not merely a lower bound. -/
theorem normalizedTarget_eq_cancellationTarget
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    normalizedTarget point = cancellationTarget point := by
  have hB : lrCertificateBFlow point ≠ 0 :=
    (lrCertificateBFlow_pos hinterior).ne'
  have he : lrCertificateE point ≠ 0 := hinterior.2.1.1.ne'
  have hvPlus : 1 + lrCertificateV point ≠ 0 := by
    linarith [(lrCertificateV_mem_Ioo hinterior).1]
  have hbrackets :=
    lrCertificateMidpointNumerator_eq_determinant_brackets
      (point := point) hvPlus
  unfold normalizedTarget cancellationTarget lrCertificateVTarget
  rw [hbrackets]
  field_simp [hB, he]
  ring

/-- A nonnegative normalized target implies the physical direct-`V` target.
This is the sole sign adapter needed after a successful replay. -/
theorem vTarget_nonnegative_of_normalizedTarget
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hnormalized : 0 ≤ normalizedTarget point) :
    0 ≤ lrCertificateVTarget point := by
  have hden : 0 <
      lrCertificateBFlow point * lrCertificateE point :=
    mul_pos (lrCertificateBFlow_pos hinterior) hinterior.2.1.1
  have hmul : 0 ≤ normalizedTarget point *
      (lrCertificateBFlow point * lrCertificateE point) :=
    mul_nonneg hnormalized hden.le
  rw [normalizedTarget, div_mul_cancel₀ _ hden.ne'] at hmul
  exact hmul

/-- The first twenty roots can be transported directly from the already
implemented upper-`K` replay target. -/
theorem vTarget_nonnegative_of_upperKReplayTarget
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hquotient : 0 ≤ lrFiniteDeterminantUpperKReplayTarget point) :
    0 ≤ lrCertificateVTarget point := by
  let first := lrDeterminantFirstBracket
    (lrCertificateBFlow point) (lrDeterminantD1 point)
    (lrCertificateGShape point) (lrDeterminantPsi point)
    (lrDeterminantDelta point) (lrCertificateW point)
  have hePos : 0 < lrCertificateE point := hinterior.2.1.1
  have hproduct : 0 ≤ lrCertificateE point *
      (first / lrCertificateE point) :=
    mul_nonneg hePos.le (by
      simpa [lrFiniteDeterminantUpperKReplayTarget, first] using hquotient)
  have hcancel : lrCertificateE point *
      (first / lrCertificateE point) = first := by
    field_simp [hePos.ne']
  rw [hcancel] at hproduct
  exact lrCertificateVTarget_nonnegative_of_firstBracket hinterior (by
    simpa [LRDeterminantFirstBracketAt, first] using hproduct)

/-! ## Exact derivatives in the correlated chart -/

/-- Quotient-rule derivative of `normalizedTarget` along an arbitrary raw
`(s,k,chi)` curve. -/
noncomputable def normalizedTargetCurveDeriv
    (point : CertificatePoint) (s' k' chi' : ℝ) : ℝ :=
  let e' := s' * point.k + point.s * k'
  let x' := -(chi' * lrCertificateE point + point.chi * e')
  let v' := lrCertificateVDeriv point e' x'
  let B' := lrCertificateBFlowDeriv point s' e' v'
  let V' := lrCertificateVTargetCurveDeriv point s' k' chi'
  let denominator := lrCertificateBFlow point * lrCertificateE point
  let denominator' :=
    B' * lrCertificateE point + lrCertificateBFlow point * e'
  (V' * denominator - lrCertificateVTarget point * denominator') /
    denominator ^ 2

/-- The first chart direction simultaneously changes raw `s` and raw
`k = s*K`; this is the correlation lost by an axis-aligned raw hull. -/
noncomputable def chartDerivS (coordinate : CertificatePoint) : ℝ :=
  normalizedTargetCurveDeriv (lrDeterminantKChartDecode coordinate)
    1 coordinate.k 0

/-- The second chart direction changes raw `k` at speed `s`. -/
noncomputable def chartDerivK (coordinate : CertificatePoint) : ℝ :=
  normalizedTargetCurveDeriv (lrDeterminantKChartDecode coordinate)
    0 coordinate.s 0

noncomputable def chartTarget (coordinate : CertificatePoint) : ℝ :=
  normalizedTarget (lrDeterminantKChartDecode coordinate)

/-- Calculus proof for the raw normalized target.  It deliberately derives
the quotient rule from the already verified direct-`V`, `B`, `e`, and `v`
curve derivatives rather than trusting an interval-AD formula. -/
theorem hasDerivAt_normalizedTarget_curve
    {z s' k' chi' : ℝ} {sfun kfun chifun : ℝ → ℝ}
    (hs : HasDerivAt sfun s' z) (hk : HasDerivAt kfun k' z)
    (hchi : HasDerivAt chifun chi' z)
    (hinterior : LRHighShapeInterior
      (lrCertificateCurve sfun kfun chifun z)) :
    HasDerivAt
      (fun q ↦ normalizedTarget
        (lrCertificateCurve sfun kfun chifun q))
      (normalizedTargetCurveDeriv
        (lrCertificateCurve sfun kfun chifun z) s' k' chi') z := by
  let point := lrCertificateCurve sfun kfun chifun z
  let e' := s' * point.k + point.s * k'
  let x' := -(chi' * lrCertificateE point + point.chi * e')
  let v' := lrCertificateVDeriv point e' x'
  let B' := lrCertificateBFlowDeriv point s' e' v'
  let V' := lrCertificateVTargetCurveDeriv point s' k' chi'
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
  have hBRaw := hasDerivAt_lrCertificateBFlowValue_along
    hs he hv hinterior.1 hinterior.2.1
      (lrCertificateV_mem_Ioo hinterior).1
  have hB : HasDerivAt
      (fun q ↦ lrCertificateBFlow
        (lrCertificateCurve sfun kfun chifun q)) B' z := by
    simpa [lrCertificateBFlow, lrCertificateBFlowDeriv,
      point, e', v', B'] using hBRaw
  have hV : HasDerivAt
      (fun q ↦ lrCertificateVTarget
        (lrCertificateCurve sfun kfun chifun q)) V' z := by
    simpa [point, V'] using
      (hasDerivAt_lrCertificateVTarget_curve hs hk hchi
        hinterior.1 hinterior.2.1 hinterior.2.2)
  have hden := hB.mul he
  have hdenNe :
      lrCertificateBFlow point * lrCertificateE point ≠ 0 :=
    (mul_pos (lrCertificateBFlow_pos hinterior)
      hinterior.2.1.1).ne'
  have hquot := hV.div hden hdenNe
  unfold normalizedTarget normalizedTargetCurveDeriv
  dsimp only
  simpa [point, e', x', v', B', V'] using hquot

theorem hasDerivAt_chartTarget_s
    {coordinate : CertificatePoint}
    (hinterior : LRHighShapeInterior
      (lrDeterminantKChartDecode coordinate)) :
    HasDerivAt
      (fun s ↦ chartTarget { coordinate with s := s })
      (chartDerivS coordinate) coordinate.s := by
  have h := hasDerivAt_normalizedTarget_curve
    (sfun := fun s ↦ s)
    (kfun := fun s ↦ s * coordinate.k)
    (chifun := fun _ ↦ coordinate.chi ^ 2)
    (hasDerivAt_id coordinate.s)
    ((hasDerivAt_id coordinate.s).mul_const coordinate.k)
    (hasDerivAt_const coordinate.s (coordinate.chi ^ 2)) hinterior
  simpa [chartTarget, chartDerivS, lrCertificateCurve,
    lrDeterminantKChartDecode] using h

theorem hasDerivAt_chartTarget_k
    {coordinate : CertificatePoint}
    (hinterior : LRHighShapeInterior
      (lrDeterminantKChartDecode coordinate)) :
    HasDerivAt
      (fun K ↦ chartTarget { coordinate with k := K })
      (chartDerivK coordinate) coordinate.k := by
  have h := hasDerivAt_normalizedTarget_curve
    (sfun := fun _ ↦ coordinate.s)
    (kfun := fun K ↦ coordinate.s * K)
    (chifun := fun _ ↦ coordinate.chi ^ 2)
    (hasDerivAt_const coordinate.k coordinate.s)
    ((hasDerivAt_const coordinate.k coordinate.s).mul
      (hasDerivAt_id coordinate.k))
    (hasDerivAt_const coordinate.k (coordinate.chi ^ 2)) hinterior
  simpa [chartTarget, chartDerivK, lrCertificateCurve,
    lrDeterminantKChartDecode] using h

/-! ## Closed chart geometry -/

/-- Freeze only `(s,K)`.  The full `h` interval remains in the value
enclosure, which is the decisive endpoint-safe feature of the leaf rule. -/
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

/-- Rational box conditions sufficient for each point with `0 < h < 1`
to decode to the raw high-shape interior. -/
def chartBoxCheck (box : CertificateBox) : Bool :=
  decide (
    (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
    (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
      box.sHi * box.sHi * box.kHi < 1 ∧
    (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
      box.chiHi ≤ 1)

theorem chartBoxCheck_sound
    {box : CertificateBox} (hcheck : chartBoxCheck box = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hh : 0 < coordinate.chi) (hhOne : coordinate.chi < 1) :
    LRHighShapeInterior (lrDeterminantKChartDecode coordinate) := by
  have hparts :
      (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
      (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
        box.sHi * box.sHi * box.kHi < 1 ∧
      (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
        box.chiHi ≤ 1 := by
    simpa [chartBoxCheck] using hcheck
  rcases hparts with
    ⟨hsLoQ, hsOrderQ, hsHiQ, hKLoQ, hKOrderQ, heHiQ,
      _hhLoQ, _hhOrderQ, _hhHiQ⟩
  have hsLo : (0 : ℝ) < box.sLo := by exact_mod_cast hsLoQ
  have hsHi : (box.sHi : ℝ) < 1 := by exact_mod_cast hsHiQ
  have hKLo : (0 : ℝ) < box.kLo := by exact_mod_cast hKLoQ
  have heHi : (((box.sHi * box.sHi * box.kHi : ℚ) : ℝ)) < 1 := by
    exact_mod_cast heHiQ
  have hs : coordinate.s ∈ Ioo (0 : ℝ) 1 :=
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
      Ioo (0 : ℝ) 1 := by
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
  have hhSqPos : 0 < coordinate.chi ^ 2 := pow_pos hh 2
  have hhSqLt : coordinate.chi ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hhOne)
      (show 0 < 1 + coordinate.chi by linarith)]
  exact ⟨hs, he, by
    simpa [lrDeterminantKChartDecode] using
      (show coordinate.chi ^ 2 ∈ Ioo (0 : ℝ) 1 from
        ⟨hhSqPos, hhSqLt⟩)⟩

/-! ## Abstract exact interval oracle and executable leaf checker -/

/-- Minimal soundness interface for a concrete exact interval evaluator.
The intended implementation evaluates `cancellationTarget`; the semantic
contract is stated using the equal `chartTarget`. -/
structure Oracle where
  Payload : Type
  DerivativePayload : Type
  check : CertificateBox → Payload → Bool
  derivativeCheck : CertificateBox → DerivativePayload → Bool
  value : CertificateBox → Payload → RationalEnclosure
  derivS : CertificateBox → DerivativePayload → RationalEnclosure
  derivK : CertificateBox → DerivativePayload → RationalEnclosure
  value_sound : ∀ box payload, check box payload = true →
    ∀ coordinate, box.Contains coordinate →
      (value box payload).Contains (chartTarget coordinate)
  derivS_sound : ∀ box payload, derivativeCheck box payload = true →
    ∀ coordinate, box.Contains coordinate →
      (derivS box payload).Contains (chartDerivS coordinate)
  derivK_sound : ∀ box payload, derivativeCheck box payload = true →
    ∀ coordinate, box.Contains coordinate →
      (derivK box payload).Contains (chartDerivK coordinate)

structure CenteredPayload (oracle : Oracle) where
  center : oracle.Payload
  derivative : oracle.DerivativePayload

def payloadCheck (oracle : Oracle) (box : CertificateBox)
    (payload : CenteredPayload oracle) : Bool :=
  chartBoxCheck box &&
    oracle.check (centerSKBox box) payload.center &&
    oracle.derivativeCheck box payload.derivative

def evaluate (oracle : Oracle) (box : CertificateBox)
    (payload : CenteredPayload oracle) : MidpointSKCertificate :=
  { value := oracle.value (centerSKBox box) payload.center
    derivS := oracle.derivS box payload.derivative
    derivK := oracle.derivK box payload.derivative }

def accepts (oracle : Oracle) (box : CertificateBox)
    (payload : CenteredPayload oracle) : Bool :=
  payloadCheck oracle box payload && (evaluate oracle box payload).check box

noncomputable def derivativeEnclosures (oracle : Oracle)
    {box : CertificateBox} {payload : CenteredPayload oracle}
    (hderivative : oracle.derivativeCheck box payload.derivative = true)
    (hdomain : chartBoxCheck box = true) :
    BoxSKDerivativeEnclosuresOn chartTarget box
      (evaluate oracle box payload) (fun h ↦ 0 < h ∧ h < 1) := by
  refine
    { partialS := chartDerivS
      partialK := chartDerivK
      derivS := ?_
      derivK := ?_
      boundS := ?_
      boundK := ?_ }
  · intro coordinate hcoordinate hh
    exact hasDerivAt_chartTarget_s
      (chartBoxCheck_sound hdomain hcoordinate hh.1 hh.2)
  · intro coordinate hcoordinate hh
    exact hasDerivAt_chartTarget_k
      (chartBoxCheck_sound hdomain hcoordinate hh.1 hh.2)
  · intro coordinate hcoordinate
    simpa [evaluate] using
      oracle.derivS_sound box payload.derivative hderivative
        coordinate hcoordinate
  · intro coordinate hcoordinate
    simpa [evaluate] using
      oracle.derivK_sound box payload.derivative hderivative
        coordinate hcoordinate

/-- Soundness of one accepted correlated mean-value leaf. -/
theorem positive_of_accepts (oracle : Oracle)
    {box : CertificateBox} {payload : CenteredPayload oracle}
    (haccept : accepts oracle box payload = true)
    {coordinate : CertificatePoint} (hcoordinate : box.Contains coordinate)
    (hh : 0 < coordinate.chi) (hhOne : coordinate.chi < 1) :
    0 < chartTarget coordinate := by
  have hacceptParts : payloadCheck oracle box payload = true ∧
      (evaluate oracle box payload).check box = true := by
    simpa [accepts] using haccept
  have hpayloadParts :
      (chartBoxCheck box = true ∧
        oracle.check (centerSKBox box) payload.center = true) ∧
      oracle.derivativeCheck box payload.derivative = true := by
    simpa [payloadCheck] using hacceptParts.1
  have hvalue : ∀ anchor, box.Contains anchor →
      (evaluate oracle box payload).value.Contains
        (chartTarget (box.anchorSK anchor)) := by
    intro anchor hanchor
    have hcenter := oracle.value_sound
      (centerSKBox box) payload.center hpayloadParts.1.2
      (box.anchorSK anchor) (centerSKBox_contains_anchorSK hanchor)
    simpa [evaluate] using hcenter
  exact (evaluate oracle box payload).soundOn_of_derivativeEnclosures
    hvalue
    (derivativeEnclosures oracle hpayloadParts.2 hpayloadParts.1.1)
    hacceptParts.2 hcoordinate ⟨hh, hhOne⟩

/-! ## Hybrid natural/mean-value leaves and checked trees -/

/-- The historical generator first tries a direct whole-box enclosure and
uses the correlated mean-value rule only when interval dependency defeats
that cheaper test. -/
inductive LeafPayload (oracle : Oracle) where
  | natural (payload : oracle.Payload)
  | meanValue (payload : CenteredPayload oracle)

def leafAccepts (oracle : Oracle) (box : CertificateBox) :
    LeafPayload oracle → Bool
  | .natural payload =>
      oracle.check box payload &&
        (oracle.value box payload).provesNonnegative
  | .meanValue payload => accepts oracle box payload

/-! ## Checked-tree and final two-root adapters -/

structure CheckedTree (oracle : Oracle) (root : CertificateBox) where
  DiscardData : Type
  discardCheck : CertificateBox → DiscardData → Bool
  discardSound : ∀ box data, discardCheck box data = true →
    ∀ coordinate, box.Contains coordinate →
      ¬ LRHighShapeVRelevant (lrDeterminantKChartDecode coordinate)
  certificate : SubdivisionCertificate (LeafPayload oracle) DiscardData
  checked : certificate.check (leafAccepts oracle) discardCheck root = true

namespace CheckedTree

/-- A checked tree proves the normalized target at every relevant decoded
interior point in its root. -/
theorem normalized_nonnegative
    {oracle : Oracle} {root : CertificateBox}
    (tree : CheckedTree oracle root)
    {coordinate : CertificatePoint} (hcoordinate : root.Contains coordinate)
    (hinterior : LRHighShapeInterior
      (lrDeterminantKChartDecode coordinate))
    (hrelevant : LRHighShapeVRelevant
      (lrDeterminantKChartDecode coordinate)) :
    0 ≤ chartTarget coordinate := by
  have hconditional := subdivisionCertificate_sound
      (Relevant := fun coordinate ↦
        LRHighShapeVRelevant (lrDeterminantKChartDecode coordinate))
      (Property := fun coordinate ↦
        LRHighShapeInterior (lrDeterminantKChartDecode coordinate) →
          0 ≤ chartTarget coordinate)
      (acceptBox := leafAccepts oracle)
      (discardBox := tree.discardCheck)
      (box := root) (certificate := tree.certificate) (by
    intro box payload haccept point hpoint
    cases payload with
    | natural payload =>
        have hparts : oracle.check box payload = true ∧
            (oracle.value box payload).provesNonnegative = true := by
          simpa [leafAccepts] using haccept
        intro _hpointInterior
        exact RationalEnclosure.nonnegative_of_provesNonnegative hparts.2
          (oracle.value_sound box payload hparts.1 point hpoint)
    | meanValue payload =>
        have hacceptMean : accepts oracle box payload = true := by
          simpa [leafAccepts] using haccept
        have hacceptParts : payloadCheck oracle box payload = true ∧
            (evaluate oracle box payload).check box = true := by
          simpa [accepts] using hacceptMean
        have hpayloadParts :
            (chartBoxCheck box = true ∧
              oracle.check (centerSKBox box) payload.center = true) ∧
            oracle.derivativeCheck box payload.derivative = true := by
          simpa [payloadCheck] using hacceptParts.1
        have hopenParts :
            (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
            (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
              box.sHi * box.sHi * box.kHi < 1 ∧
            (0 : ℚ) ≤ box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
              box.chiHi ≤ 1 := by
          simpa [chartBoxCheck] using hpayloadParts.1.1
        intro hpointInterior
        have hhNonnegative : 0 ≤ point.chi := by
          have hlo : (0 : ℝ) ≤ box.chiLo := by
            exact_mod_cast hopenParts.2.2.2.2.2.2.1
          exact hlo.trans hpoint.2.2.2.2.1
        have hhSqPos : 0 < point.chi ^ 2 := by
          simpa [lrDeterminantKChartDecode] using hpointInterior.2.2.1
        have hhSqLt : point.chi ^ 2 < 1 := by
          simpa [lrDeterminantKChartDecode] using hpointInterior.2.2.2
        have hhPositive : 0 < point.chi := by nlinarith
        have hhOne : point.chi < 1 := by nlinarith
        exact (positive_of_accepts oracle hacceptMean hpoint
          hhPositive hhOne).le)
      tree.discardSound tree.checked coordinate hcoordinate hrelevant
  exact hconditional hinterior

/-- Convert the normalized replay result back to the exact direct-`V`
target consumed by `LRDeterminantLowRatioFiniteVTargetTheorem`. -/
theorem vTarget_nonnegative
    {oracle : Oracle} {root : CertificateBox}
    (tree : CheckedTree oracle root)
    {coordinate : CertificatePoint} (hcoordinate : root.Contains coordinate)
    (hinterior : LRHighShapeInterior
      (lrDeterminantKChartDecode coordinate))
    (hrelevant : LRHighShapeVRelevant
      (lrDeterminantKChartDecode coordinate)) :
    0 ≤ lrCertificateVTarget (lrDeterminantKChartDecode coordinate) := by
  exact vTarget_nonnegative_of_normalizedTarget hinterior
    (tree.normalized_nonnegative hcoordinate hinterior hrelevant)

end CheckedTree

def firstQuarterHalfRoot : CertificateBox where
  sLo := 1 / 16384
  sHi := 1 / 16
  kLo := 1 / 4
  kHi := 1 / 2
  chiLo := 0
  chiHi := 1

def firstHalfOneRoot : CertificateBox where
  sLo := 1 / 16384
  sHi := 1 / 16
  kLo := 1 / 2
  kHi := 1
  chiLo := 0
  chiHi := 1

def quarterHalfRoot : CertificateBox where
  sLo := 1 / 16
  sHi := 1 / 10
  kLo := 1 / 4
  kHi := 1 / 2
  chiLo := 0
  chiHi := 1

def halfOneRoot : CertificateBox where
  sLo := 1 / 16
  sHi := 1 / 10
  kLo := 1 / 2
  kHi := 1
  chiLo := 0
  chiHi := 1

private theorem root_contains_encode
    {point : CertificatePoint} {sLo sHi KLo KHi : ℚ}
    (hinterior : LRHighShapeInterior point)
    (hsLower : (sLo : ℝ) ≤ point.s)
    (hsUpper : point.s ≤ (sHi : ℝ))
    (hKLo : (KLo : ℝ) ≤ point.k / point.s)
    (hKHi : point.k / point.s ≤ (KHi : ℝ)) :
    ({ sLo := sLo, sHi := sHi,
       kLo := KLo, kHi := KHi, chiLo := 0, chiHi := 1 } :
      CertificateBox).Contains (lrDeterminantKChartEncode point) := by
  have hchiLo : 0 ≤ point.chi := hinterior.2.2.1.le
  have hchiHi : point.chi ≤ 1 := hinterior.2.2.2.le
  have hsqrtLo : 0 ≤ Real.sqrt point.chi := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt point.chi) ^ 2 = point.chi :=
    Real.sq_sqrt hchiLo
  have hsqrtHi : Real.sqrt point.chi ≤ 1 := by nlinarith
  simpa [lrDeterminantKChartEncode, CertificateBox.Contains] using
    And.intro hsLower (And.intro hsUpper (And.intro hKLo
      (And.intro hKHi (And.intro hsqrtLo hsqrtHi))))

/-- Abstract view of a sharp upper-`K` checked tree.  The existing
`LRUpperKReplayCertificate.CenteredCheckedTree` supplies this field verbatim;
the wrapper keeps this source-only file independent of that scratch module. -/
structure FirstBracketTree (root : CertificateBox) : Type where
  target_nonnegative : ∀ {coordinate : CertificatePoint},
    root.Contains coordinate →
    LRHighShapeInterior (lrDeterminantKChartDecode coordinate) →
    LRHighShapeVRelevant (lrDeterminantKChartDecode coordinate) →
    0 ≤ lrFiniteDeterminantUpperKReplayTarget
      (lrDeterminantKChartDecode coordinate)

namespace FirstBracketTree

/-- Any standard checked `FirstBracket/e` chart tree has the required
interface immediately. -/
def ofCheckedKChartTree {root : CertificateBox}
    (tree : LRFiniteDeterminantKChartCheckedTree root
      lrFiniteDeterminantUpperKReplayTarget) :
    FirstBracketTree root where
  target_nonnegative := by
    intro coordinate hcoordinate _hinterior hrelevant
    exact tree.target_nonnegative hcoordinate hrelevant

end FirstBracketTree

/-- Reusing two sharp first-bracket trees closes the lower twenty historical
roots, aggregated into their two `K` bands. -/
theorem lowerFiniteVBand_of_firstBracketTrees
    (quarterHalf : FirstBracketTree firstQuarterHalfRoot)
    (halfOne : FirstBracketTree firstHalfOneRoot) :
    ∀ point : CertificatePoint,
      LRHighShapeInterior point →
      LRHighShapeVRelevant point →
      LRDeterminantLowRatioRegion point →
      (1 / 16384 : ℝ) ≤ point.s →
      point.s ≤ (1 / 16 : ℝ) →
      0 ≤ lrCertificateVTarget point := by
  intro point hinterior hrelevant hregion hsLo hsHi
  have hsPos : 0 < point.s := hinterior.1.1
  have hKLower : (1 / 4 : ℝ) ≤ point.k / point.s := by
    rw [le_div_iff₀ hsPos]
    simpa [div_eq_mul_inv, mul_comm] using hregion.1.le
  have hKUpper : point.k / point.s ≤ (1 : ℝ) := by
    rw [div_le_one hsPos]
    exact hregion.2
  have hsLoCast : (((1 / 16384 : ℚ) : ℝ)) ≤ point.s := by
    convert hsLo using 1 <;> norm_num
  have hsHiCast : point.s ≤ (((1 / 16 : ℚ) : ℝ)) := by
    convert hsHi using 1 <;> norm_num
  have hKLowerCast : (((1 / 4 : ℚ) : ℝ)) ≤ point.k / point.s := by
    convert hKLower using 1 <;> norm_num
  have hKUpperCast : point.k / point.s ≤ (((1 : ℚ) : ℝ)) := by
    convert hKUpper using 1 <;> norm_num
  have hdecoded := lrDeterminantKChartDecode_encode hinterior
  have hinteriorEncoded : LRHighShapeInterior
      (lrDeterminantKChartDecode (lrDeterminantKChartEncode point)) := by
    rw [hdecoded]
    exact hinterior
  have hrelevantEncoded : LRHighShapeVRelevant
      (lrDeterminantKChartDecode (lrDeterminantKChartEncode point)) := by
    rw [hdecoded]
    exact hrelevant
  by_cases hKMid : point.k / point.s ≤ (1 / 2 : ℝ)
  · have hcontains : firstQuarterHalfRoot.Contains
        (lrDeterminantKChartEncode point) := by
      have hKMidCast : point.k / point.s ≤ (((1 / 2 : ℚ) : ℝ)) := by
        convert hKMid using 1 <;> norm_num
      simpa [firstQuarterHalfRoot] using
        (root_contains_encode
          (sLo := 1 / 16384) (sHi := 1 / 16)
          (KLo := 1 / 4) (KHi := 1 / 2)
          hinterior hsLoCast hsHiCast hKLowerCast hKMidCast)
    have htarget := quarterHalf.target_nonnegative hcontains
      hinteriorEncoded hrelevantEncoded
    rw [hdecoded] at htarget
    exact vTarget_nonnegative_of_upperKReplayTarget hinterior htarget
  · have hKMid' : (1 / 2 : ℝ) ≤ point.k / point.s :=
      le_of_lt (lt_of_not_ge hKMid)
    have hcontains : firstHalfOneRoot.Contains
        (lrDeterminantKChartEncode point) := by
      have hKMidCast : (((1 / 2 : ℚ) : ℝ)) ≤ point.k / point.s := by
        convert hKMid' using 1 <;> norm_num
      simpa [firstHalfOneRoot] using
        (root_contains_encode
          (sLo := 1 / 16384) (sHi := 1 / 16)
          (KLo := 1 / 2) (KHi := 1)
          hinterior hsLoCast hsHiCast hKMidCast hKUpperCast)
    have htarget := halfOne.target_nonnegative hcontains
      hinteriorEncoded hrelevantEncoded
    rw [hdecoded] at htarget
    exact vTarget_nonnegative_of_upperKReplayTarget hinterior htarget

/-- The two correlated checked trees give exactly the direct-`V` part of
the finite low-ratio replay, i.e. the final two historical roots. -/
theorem upperFiniteVBand_of_checkedTrees
    {oracle : Oracle}
    (quarterHalf : CheckedTree oracle quarterHalfRoot)
    (halfOne : CheckedTree oracle halfOneRoot) :
    ∀ point : CertificatePoint,
      LRHighShapeInterior point →
      LRHighShapeVRelevant point →
      LRDeterminantLowRatioRegion point →
      (1 / 16 : ℝ) ≤ point.s →
      point.s ≤ (1 / 10 : ℝ) →
      0 ≤ lrCertificateVTarget point := by
  intro point hinterior hrelevant hregion hsLo hsHi
  have hsPos : 0 < point.s := hinterior.1.1
  have hKLower : (1 / 4 : ℝ) ≤ point.k / point.s := by
    rw [le_div_iff₀ hsPos]
    simpa [div_eq_mul_inv, mul_comm] using hregion.1.le
  have hKUpper : point.k / point.s ≤ (1 : ℝ) := by
    rw [div_le_one hsPos]
    exact hregion.2
  have hsLoCast : (((1 / 16 : ℚ) : ℝ)) ≤ point.s := by
    convert hsLo using 1 <;> norm_num
  have hsHiCast : point.s ≤ (((1 / 10 : ℚ) : ℝ)) := by
    convert hsHi using 1 <;> norm_num
  have hKLowerCast : (((1 / 4 : ℚ) : ℝ)) ≤ point.k / point.s := by
    convert hKLower using 1 <;> norm_num
  have hKUpperCast : point.k / point.s ≤ (((1 : ℚ) : ℝ)) := by
    convert hKUpper using 1 <;> norm_num
  have hdecoded := lrDeterminantKChartDecode_encode hinterior
  have hinteriorEncoded : LRHighShapeInterior
      (lrDeterminantKChartDecode (lrDeterminantKChartEncode point)) := by
    rw [hdecoded]
    exact hinterior
  have hrelevantEncoded : LRHighShapeVRelevant
      (lrDeterminantKChartDecode (lrDeterminantKChartEncode point)) := by
    rw [hdecoded]
    exact hrelevant
  by_cases hKMid : point.k / point.s ≤ (1 / 2 : ℝ)
  · have hcontains : quarterHalfRoot.Contains
        (lrDeterminantKChartEncode point) := by
      have hKMidCast : point.k / point.s ≤ (((1 / 2 : ℚ) : ℝ)) := by
        convert hKMid using 1 <;> norm_num
      simpa [quarterHalfRoot] using
        (root_contains_encode
          (sLo := 1 / 16) (sHi := 1 / 10)
          (KLo := 1 / 4) (KHi := 1 / 2)
          hinterior hsLoCast hsHiCast hKLowerCast hKMidCast)
    have htarget := quarterHalf.vTarget_nonnegative hcontains
      hinteriorEncoded hrelevantEncoded
    rwa [hdecoded] at htarget
  · have hKMid' : (1 / 2 : ℝ) ≤ point.k / point.s :=
      le_of_lt (lt_of_not_ge hKMid)
    have hcontains : halfOneRoot.Contains
        (lrDeterminantKChartEncode point) := by
      have hKMidCast : (((1 / 2 : ℚ) : ℝ)) ≤ point.k / point.s := by
        convert hKMid' using 1 <;> norm_num
      simpa [halfOneRoot] using
        (root_contains_encode
          (sLo := 1 / 16) (sHi := 1 / 10)
          (KLo := 1 / 2) (KHi := 1)
          hinterior hsLoCast hsHiCast hKMidCast hKUpperCast)
    have htarget := halfOne.vTarget_nonnegative hcontains
      hinteriorEncoded hrelevantEncoded
    rwa [hdecoded] at htarget

/-- Complete four-tree boundary for
`LRDeterminantLowRatioFiniteVTargetTheorem`: two reused sharp
`FirstBracket/e` trees below `s = 1/16`, and two new normalized direct-`V`
trees above it. -/
theorem finiteVTargetTheorem_of_fourTrees
    {oracle : Oracle}
    (firstQuarterHalf : FirstBracketTree firstQuarterHalfRoot)
    (firstHalfOne : FirstBracketTree firstHalfOneRoot)
    (vQuarterHalf : CheckedTree oracle quarterHalfRoot)
    (vHalfOne : CheckedTree oracle halfOneRoot) :
    LRDeterminantLowRatioFiniteVTargetTheorem := by
  intro point hinterior hrelevant hregion hsLower hsUpper
  by_cases hsMid : point.s ≤ (1 / 16 : ℝ)
  · exact lowerFiniteVBand_of_firstBracketTrees
      firstQuarterHalf firstHalfOne point hinterior hrelevant hregion
      hsLower hsMid
  · exact upperFiniteVBand_of_checkedTrees
      vQuarterHalf vHalfOne point hinterior hrelevant hregion
      (le_of_lt (lt_of_not_ge hsMid)) hsUpper

/-!
## Concrete-oracle implementation plan

The exact interval oracle should be a thin extension of the sharp
`LRUpperKReplayCertificate` graph:

1. Reuse `sAD`, `ratioAD`, `hAD`, `physicalKAD`, `physicalChiAD`, `eAD`,
   `xAD`, `vAD`, `gSKAD`, `wAD`, `deltaAD`, and the sharp cancellation
   enclosure for `Psi-G`.
2. Add one checked logarithm payload for `Y = (1+k-e)/k`, form
   `D = log Y / 2`, and reuse the existing positive enclosure for `B`.
3. Evaluate
   `((D/B)*G + (1+D/B)*(Psi-G) + 4*delta*W)/e`.
4. For a natural leaf, return its value interval directly.  For a
   mean-value leaf, evaluate the value on `centerSKBox box`, evaluate exact
   `s` and `K` derivatives on the whole box, and instantiate `Oracle`.
5. Use the existing upper-`K` sharp centered tree for the first twenty
   `FirstBracket/e` roots; use `upperFiniteVBand_of_checkedTrees` only for
   the final two direct-`V` roots.

This isolates all new arithmetic to one logarithm and one collected final
expression.  The calculus, closed-face handling, subdivision soundness, and
physical sign transport are already supplied above.
-/

end LRLowRatioFiniteVMeanValue
end CourtadeKumar
