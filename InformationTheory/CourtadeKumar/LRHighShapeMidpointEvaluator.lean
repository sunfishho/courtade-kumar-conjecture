import InformationTheory.CourtadeKumar.LRHighShapeABAssembly
import InformationTheory.CourtadeKumar.IntervalCertificateAssembly

/-!
# Verified evaluator for the high-shape half-midpoint target

This module assembles the checked interval-AD nodes for the exact numerator
`N(M/2)` and divides by the manuscript normalization `s * e`.  The assembly
uses the cancellation-safe coordinates `e`, `x`, `A`, `B`, `D`, `G`, `W`, and
`P_W`; it is subsequently identified with `lrHighShapeUCertificateTarget`.
-/

open Set

namespace CourtadeKumar

noncomputable def lrCertificateM (point : CertificatePoint) : ℝ :=
  lrCertificateV point / (1 + lrCertificateV point)

noncomputable def lrCertificateMDeriv
    (point : CertificatePoint) (v' : ℝ) : ℝ :=
  v' / (1 + lrCertificateV point) ^ 2

noncomputable def lrCertificateHalfMidpointBracket
    (point : CertificatePoint) : ℝ :=
  let p := lrCertificateM point / 2
  (1 - p) * lrCertificateD point +
    p * lrCertificateX point * lrCertificateBFlow point

noncomputable def lrCertificateHalfMidpointBracketDeriv
    (point : CertificatePoint) (b' d' m' x' : ℝ) : ℝ :=
  let p := lrCertificateM point / 2
  let p' := m' / 2
  (-p') * lrCertificateD point + (1 - p) * d' +
    (p' * lrCertificateX point + p * x') * lrCertificateBFlow point +
    (p * lrCertificateX point) * b'

noncomputable def lrCertificateHalfMidpointNumerator
    (point : CertificatePoint) : ℝ :=
  lrCertificateD point * lrCertificateGShape point +
    lrCertificateA point * lrCertificatePW point -
    4 * lrCertificateW point * lrCertificateHalfMidpointBracket point

noncomputable def lrCertificateHalfMidpointNumeratorDeriv
    (point : CertificatePoint)
    (a' d' g' w' pw' b' m' x' : ℝ) : ℝ :=
  d' * lrCertificateGShape point + lrCertificateD point * g' +
    (a' * lrCertificatePW point + lrCertificateA point * pw') -
    4 * (w' * lrCertificateHalfMidpointBracket point +
      lrCertificateW point *
        lrCertificateHalfMidpointBracketDeriv point b' d' m' x')

def lrCertificateUDenominator (point : CertificatePoint) : ℝ :=
  point.s * lrCertificateE point

def lrCertificateUDenominatorDeriv
    (point : CertificatePoint) (s' e' : ℝ) : ℝ :=
  s' * lrCertificateE point + point.s * e'

noncomputable def lrCertificateUTarget (point : CertificatePoint) : ℝ :=
  lrCertificateHalfMidpointNumerator point /
    lrCertificateUDenominator point

noncomputable def lrCertificateUTargetDeriv
    (point : CertificatePoint) (numerator' denominator' : ℝ) : ℝ :=
  (numerator' * lrCertificateUDenominator point -
      lrCertificateHalfMidpointNumerator point * denominator') /
    lrCertificateUDenominator point ^ 2

noncomputable def lrCertificateUTargetCurveDeriv
    (point : CertificatePoint) (s' k' chi' : ℝ) : ℝ :=
  let e' := s' * point.k + point.s * k'
  let x' := -(chi' * lrCertificateE point + point.chi * e')
  let v' := lrCertificateVDeriv point e' x'
  let y0' := chi' * lrCertificateE point + point.chi * e'
  let a' := lrCertificateADeriv point e' v'
  let b' := lrCertificateBFlowDeriv point s' e' v'
  let d' := lrCertificateDDeriv point s' e' v'
  let g' := lrCertificateGShapeDeriv point y0' e' v'
  let w' := lrCertificateOmegaDeriv point.s 0 s' 0
  let pw' := lrCertificatePWDeriv point s' y0' e' v'
  let m' := lrCertificateMDeriv point v'
  let numerator' := lrCertificateHalfMidpointNumeratorDeriv point
    a' d' g' w' pw' b' m' x'
  let denominator' := lrCertificateUDenominatorDeriv point s' e'
  lrCertificateUTargetDeriv point numerator' denominator'

theorem hasDerivAt_lrCertificateUTarget_curve
    {z s' k' chi' : ℝ} {sfun kfun chifun : ℝ → ℝ}
    (hs : HasDerivAt sfun s' z) (hk : HasDerivAt kfun k' z)
    (hchi : HasDerivAt chifun chi' z)
    (hsMem : sfun z ∈ Ioo (0 : ℝ) 1)
    (heMem : lrCertificateE (lrCertificateCurve sfun kfun chifun z) ∈
      Ioo (0 : ℝ) 1)
    (hchiMem : chifun z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun q ↦ lrCertificateUTarget
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificateUTargetCurveDeriv
        (lrCertificateCurve sfun kfun chifun z) s' k' chi') z := by
  let point := lrCertificateCurve sfun kfun chifun z
  let e' := s' * point.k + point.s * k'
  let x' := -(chi' * lrCertificateE point + point.chi * e')
  let v' := lrCertificateVDeriv point e' x'
  let y0' := chi' * lrCertificateE point + point.chi * e'
  let a' := lrCertificateADeriv point e' v'
  let b' := lrCertificateBFlowDeriv point s' e' v'
  let d' := lrCertificateDDeriv point s' e' v'
  let g' := lrCertificateGShapeDeriv point y0' e' v'
  let w' := lrCertificateOmegaDeriv point.s 0 s' 0
  let pw' := lrCertificatePWDeriv point s' y0' e' v'
  let m' := lrCertificateMDeriv point v'
  have he := hasDerivAt_lrCertificateE_curve (chi := chifun) hs hk
  have hxRaw := hasDerivAt_lrCertificateX_curve hs hk hchi
  have hx : HasDerivAt
      (fun q ↦ lrCertificateX (lrCertificateCurve sfun kfun chifun q))
      x' z := by
    simpa [point, e', x', lrCertificateCurve] using hxRaw
  have hvRaw := hasDerivAt_lrCertificateV_curve hs hk hchi heMem hchiMem
  have hv : HasDerivAt
      (fun q ↦ lrCertificateV (lrCertificateCurve sfun kfun chifun q))
      v' z := by
    simpa [point, e', x', v', lrCertificateCurve] using hvRaw
  have hxPos : 0 < lrCertificateX point := by
    change 0 < 1 - chifun z * lrCertificateE point
    have hprod : chifun z * lrCertificateE point < 1 := by
      calc
        chifun z * lrCertificateE point < 1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hchiMem.2 heMem.1
        _ = lrCertificateE point := one_mul _
        _ < 1 := heMem.2
    exact sub_pos.mpr hprod
  have hradPos : 0 < lrCertificateVRadicand point :=
    div_pos (sub_pos.mpr heMem.2) hxPos
  have hvPos : 0 < lrCertificateV point := Real.sqrt_pos.2 hradPos
  have hy0 : HasDerivAt
      (fun q ↦ lrCertificateY0 (lrCertificateCurve sfun kfun chifun q))
      y0' z := by
    have h := hchi.mul he
    simpa [lrCertificateY0, point, e', y0', lrCertificateCurve] using h
  have hy0Mem : lrCertificateY0 point ∈ Ioo (0 : ℝ) 1 := by
    unfold lrCertificateY0
    constructor
    · exact mul_pos hchiMem.1 heMem.1
    · calc
        point.chi * lrCertificateE point < 1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hchiMem.2 heMem.1
        _ = lrCertificateE point := one_mul _
        _ < 1 := heMem.2
  have hAraw := hasDerivAt_lrCertificateAValue_along he hv heMem.1 hvPos
  have hA : HasDerivAt
      (fun q ↦ lrCertificateA (lrCertificateCurve sfun kfun chifun q))
      a' z := by
    simpa [lrCertificateA, lrCertificateADeriv, point, e', v', a'] using hAraw
  have hBraw := hasDerivAt_lrCertificateBFlowValue_along
    hs he hv hsMem heMem hvPos
  have hB : HasDerivAt
      (fun q ↦ lrCertificateBFlow (lrCertificateCurve sfun kfun chifun q))
      b' z := by
    simpa [lrCertificateBFlow, lrCertificateBFlowDeriv,
      point, e', v', b', lrCertificateCurve] using hBraw
  have hD : HasDerivAt
      (fun q ↦ lrCertificateD (lrCertificateCurve sfun kfun chifun q))
      d' z := by
    have h := hA.sub hB
    simpa [lrCertificateD, lrCertificateDDeriv, point, e', v', a', b', d']
      using h
  have hGraw := hasDerivAt_lrCertificateGShapeValue_along
    hy0 he hv hy0Mem heMem hvPos
  have hG : HasDerivAt
      (fun q ↦ lrCertificateGShape (lrCertificateCurve sfun kfun chifun q))
      g' z := by
    simpa [lrCertificateGShape, lrCertificateGShapeDeriv,
      point, e', v', y0', g'] using hGraw
  have hWraw := hasDerivAt_lrCertificateOmega_zero_along hs rfl hsMem
  have hW : HasDerivAt
      (fun q ↦ lrCertificateW (lrCertificateCurve sfun kfun chifun q))
      w' z := by
    simpa [lrCertificateW, point, w', lrCertificateCurve] using hWraw
  have hPWraw := hasDerivAt_lrCertificatePWValue_along
    hs hy0 he hv hsMem hy0Mem heMem hvPos
  have hPW : HasDerivAt
      (fun q ↦ lrCertificatePW (lrCertificateCurve sfun kfun chifun q))
      pw' z := by
    simpa [lrCertificatePW, lrCertificatePWDeriv,
      point, e', v', y0', pw', lrCertificateCurve] using hPWraw
  have honePlusV := (hasDerivAt_const z 1).add hv
  have hMraw := hv.div honePlusV (by
    change 1 + lrCertificateV point ≠ 0
    linarith)
  have hM : HasDerivAt
      (fun q ↦ lrCertificateM (lrCertificateCurve sfun kfun chifun q))
      m' z := by
    unfold lrCertificateM
    convert hMraw using 1 <;>
      dsimp [point, v', m', lrCertificateMDeriv] <;>
      field_simp [(by linarith : 1 + lrCertificateV point ≠ 0)] <;> ring
  have hp := hM.mul (hasDerivAt_const z (1 / 2 : ℝ))
  have honeMinusP := (hasDerivAt_const z 1).sub hp
  have hleft := honeMinusP.mul hD
  have hpx := hp.mul hx
  have hright := hpx.mul hB
  have hbracketRaw := hleft.add hright
  have hbracket : HasDerivAt
      (fun q ↦ lrCertificateHalfMidpointBracket
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificateHalfMidpointBracketDeriv point b' d' m' x') z := by
    unfold lrCertificateHalfMidpointBracket
      lrCertificateHalfMidpointBracketDeriv
    dsimp only
    convert hbracketRaw using 1 <;>
      first
      | (funext q; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; ring)
      | (dsimp [point]; ring)
  have hdg := hD.mul hG
  have hapw := hA.mul hPW
  have hpositive := hdg.add hapw
  have hcorrection := ((hasDerivAt_const z 4).mul hW).mul hbracket
  have hnumRaw := hpositive.sub hcorrection
  have hnum : HasDerivAt
      (fun q ↦ lrCertificateHalfMidpointNumerator
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificateHalfMidpointNumeratorDeriv point
        a' d' g' w' pw' b' m' x') z := by
    unfold lrCertificateHalfMidpointNumerator
      lrCertificateHalfMidpointNumeratorDeriv
    convert hnumRaw using 1 <;> dsimp [point] <;> ring
  have hdenRaw := hs.mul he
  have hden : HasDerivAt
      (fun q ↦ lrCertificateUDenominator
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificateUDenominatorDeriv point s' e') z := by
    unfold lrCertificateUDenominator lrCertificateUDenominatorDeriv
    convert hdenRaw using 1 <;> dsimp [point, e', lrCertificateCurve] <;> ring
  have hdenPos : 0 < lrCertificateUDenominator point :=
    mul_pos hsMem.1 heMem.1
  have htargetRaw := hnum.div hden hdenPos.ne'
  unfold lrCertificateUTarget lrCertificateUTargetCurveDeriv
    lrCertificateUTargetDeriv
  dsimp only
  convert htargetRaw using 1 <;>
    dsimp [point, e', x', v', y0', a', b', d', g', w', pw', m'] <;>
    field_simp [hdenPos.ne'] <;> ring

private noncomputable def lrCertificateADerivS (point : CertificatePoint) : ℝ :=
  lrCertificateADeriv point (lrCertificateEDerivS point)
    (lrCertificateVDerivS point)

private noncomputable def lrCertificateADerivK (point : CertificatePoint) : ℝ :=
  lrCertificateADeriv point (lrCertificateEDerivK point)
    (lrCertificateVDerivK point)

private noncomputable def lrCertificateADerivChi (point : CertificatePoint) : ℝ :=
  lrCertificateADeriv point (lrCertificateEDerivChi point)
    (lrCertificateVDerivChi point)

private noncomputable def lrCertificateBFlowDerivS
    (point : CertificatePoint) : ℝ :=
  lrCertificateBFlowDeriv point 1 (lrCertificateEDerivS point)
    (lrCertificateVDerivS point)

private noncomputable def lrCertificateBFlowDerivK
    (point : CertificatePoint) : ℝ :=
  lrCertificateBFlowDeriv point 0 (lrCertificateEDerivK point)
    (lrCertificateVDerivK point)

private noncomputable def lrCertificateBFlowDerivChi
    (point : CertificatePoint) : ℝ :=
  lrCertificateBFlowDeriv point 0 (lrCertificateEDerivChi point)
    (lrCertificateVDerivChi point)

private noncomputable def lrCertificateDDerivS (point : CertificatePoint) : ℝ :=
  lrCertificateDDeriv point 1 (lrCertificateEDerivS point)
    (lrCertificateVDerivS point)

private noncomputable def lrCertificateDDerivK (point : CertificatePoint) : ℝ :=
  lrCertificateDDeriv point 0 (lrCertificateEDerivK point)
    (lrCertificateVDerivK point)

private noncomputable def lrCertificateDDerivChi (point : CertificatePoint) : ℝ :=
  lrCertificateDDeriv point 0 (lrCertificateEDerivChi point)
    (lrCertificateVDerivChi point)

noncomputable def lrCertificateHalfMidpointNumeratorDerivS
    (point : CertificatePoint) : ℝ :=
  lrCertificateHalfMidpointNumeratorDeriv point
    (lrCertificateADerivS point) (lrCertificateDDerivS point)
    (lrCertificateGShapeDerivS point) (lrCertificateWDerivS point)
    (lrCertificatePWDerivS point) (lrCertificateBFlowDerivS point)
    (lrCertificateMDeriv point (lrCertificateVDerivS point))
    (lrCertificateXDerivS point)

noncomputable def lrCertificateHalfMidpointNumeratorDerivK
    (point : CertificatePoint) : ℝ :=
  lrCertificateHalfMidpointNumeratorDeriv point
    (lrCertificateADerivK point) (lrCertificateDDerivK point)
    (lrCertificateGShapeDerivK point) (lrCertificateWDerivK point)
    (lrCertificatePWDerivK point) (lrCertificateBFlowDerivK point)
    (lrCertificateMDeriv point (lrCertificateVDerivK point))
    (lrCertificateXDerivK point)

noncomputable def lrCertificateHalfMidpointNumeratorDerivChi
    (point : CertificatePoint) : ℝ :=
  lrCertificateHalfMidpointNumeratorDeriv point
    (lrCertificateADerivChi point) (lrCertificateDDerivChi point)
    (lrCertificateGShapeDerivChi point) (lrCertificateWDerivChi point)
    (lrCertificatePWDerivChi point) (lrCertificateBFlowDerivChi point)
    (lrCertificateMDeriv point (lrCertificateVDerivChi point))
    (lrCertificateXDerivChi point)

/-- Directional derivative of the half-midpoint numerator in cancellation
coordinates.  This public form lets other checked evaluators reuse the
already-established coordinate derivative identities. -/
noncomputable def lrCertificateHalfMidpointNumeratorCurveDeriv
    (point : CertificatePoint) (s' k' chi' : ℝ) : ℝ :=
  let e' := s' * point.k + point.s * k'
  let x' := -(chi' * lrCertificateE point + point.chi * e')
  let y0' := chi' * lrCertificateE point + point.chi * e'
  let v' := lrCertificateVDeriv point e' x'
  lrCertificateHalfMidpointNumeratorDeriv point
    (lrCertificateADeriv point e' v')
    (lrCertificateDDeriv point s' e' v')
    (lrCertificateGShapeDeriv point y0' e' v')
    (lrCertificateOmegaDeriv point.s 0 s' 0)
    (lrCertificatePWDeriv point s' y0' e' v')
    (lrCertificateBFlowDeriv point s' e' v')
    (lrCertificateMDeriv point v') x'

theorem lrCertificateHalfMidpointNumeratorCurveDeriv_s
    (point : CertificatePoint) :
    lrCertificateHalfMidpointNumeratorCurveDeriv point 1 0 0 =
      lrCertificateHalfMidpointNumeratorDerivS point := by
  unfold lrCertificateHalfMidpointNumeratorCurveDeriv
    lrCertificateHalfMidpointNumeratorDerivS lrCertificateADerivS
    lrCertificateBFlowDerivS lrCertificateDDerivS
    lrCertificateGShapeDerivS lrCertificateWDerivS
    lrCertificatePWDerivS lrCertificateY0DerivS lrCertificateVDerivS
    lrCertificateEDerivS lrCertificateXDerivS
  dsimp only
  ring

theorem lrCertificateHalfMidpointNumeratorCurveDeriv_k
    (point : CertificatePoint) :
    lrCertificateHalfMidpointNumeratorCurveDeriv point 0 1 0 =
      lrCertificateHalfMidpointNumeratorDerivK point := by
  unfold lrCertificateHalfMidpointNumeratorCurveDeriv
    lrCertificateHalfMidpointNumeratorDerivK lrCertificateADerivK
    lrCertificateBFlowDerivK lrCertificateDDerivK
    lrCertificateGShapeDerivK lrCertificateWDerivK
    lrCertificatePWDerivK lrCertificateY0DerivK lrCertificateVDerivK
    lrCertificateEDerivK lrCertificateXDerivK
  dsimp only
  ring

theorem lrCertificateHalfMidpointNumeratorCurveDeriv_chi
    (point : CertificatePoint) :
    lrCertificateHalfMidpointNumeratorCurveDeriv point 0 0 1 =
      lrCertificateHalfMidpointNumeratorDerivChi point := by
  unfold lrCertificateHalfMidpointNumeratorCurveDeriv
    lrCertificateHalfMidpointNumeratorDerivChi lrCertificateADerivChi
    lrCertificateBFlowDerivChi lrCertificateDDerivChi
    lrCertificateGShapeDerivChi lrCertificateWDerivChi
    lrCertificatePWDerivChi lrCertificateY0DerivChi lrCertificateVDerivChi
    lrCertificateEDerivChi lrCertificateXDerivChi
  dsimp only
  ring

noncomputable def lrCertificateUTargetDerivS (point : CertificatePoint) : ℝ :=
  lrCertificateUTargetDeriv point
    (lrCertificateHalfMidpointNumeratorDerivS point)
    (lrCertificateUDenominatorDeriv point 1 (lrCertificateEDerivS point))

noncomputable def lrCertificateUTargetDerivK (point : CertificatePoint) : ℝ :=
  lrCertificateUTargetDeriv point
    (lrCertificateHalfMidpointNumeratorDerivK point)
    (lrCertificateUDenominatorDeriv point 0 (lrCertificateEDerivK point))

noncomputable def lrCertificateUTargetDerivChi
    (point : CertificatePoint) : ℝ :=
  lrCertificateUTargetDeriv point
    (lrCertificateHalfMidpointNumeratorDerivChi point)
    (lrCertificateUDenominatorDeriv point 0 (lrCertificateEDerivChi point))

def LRHighShapeInterior (point : CertificatePoint) : Prop :=
  point.s ∈ Ioo (0 : ℝ) 1 ∧
    lrCertificateE point ∈ Ioo (0 : ℝ) 1 ∧
    point.chi ∈ Ioo (0 : ℝ) 1

def lrHighShapeInteriorBoxCheck (box : CertificateBox) : Bool :=
  decide (
    (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
    (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
      box.sHi * box.kHi < 1 ∧
    (0 : ℚ) < box.chiLo ∧ box.chiLo ≤ box.chiHi ∧ box.chiHi < 1)

theorem lrHighShapeInteriorBoxCheck_sound {box : CertificateBox}
    (hcheck : lrHighShapeInteriorBoxCheck box = true)
    {point : CertificatePoint} (hpoint : box.Contains point) :
    LRHighShapeInterior point := by
  have hparts :
      (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
      (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
        box.sHi * box.kHi < 1 ∧
      (0 : ℚ) < box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
        box.chiHi < 1 := by
    simpa [lrHighShapeInteriorBoxCheck] using hcheck
  have hsLo : (0 : ℝ) < box.sLo := by exact_mod_cast hparts.1
  have hsOrder : (box.sLo : ℝ) ≤ box.sHi := by
    exact_mod_cast hparts.2.1
  have hsHi : (box.sHi : ℝ) < 1 := by exact_mod_cast hparts.2.2.1
  have hkLo : (0 : ℝ) < box.kLo := by exact_mod_cast hparts.2.2.2.1
  have hkOrder : (box.kLo : ℝ) ≤ box.kHi := by
    exact_mod_cast hparts.2.2.2.2.1
  have hprodHi : ((box.sHi * box.kHi : ℚ) : ℝ) < 1 := by
    exact_mod_cast hparts.2.2.2.2.2.1
  have hchiLo : (0 : ℝ) < box.chiLo := by
    exact_mod_cast hparts.2.2.2.2.2.2.1
  have hchiHi : (box.chiHi : ℝ) < 1 := by
    exact_mod_cast hparts.2.2.2.2.2.2.2.2
  have hs : point.s ∈ Ioo (0 : ℝ) 1 :=
    ⟨hsLo.trans_le hpoint.1, hpoint.2.1.trans_lt hsHi⟩
  have hkPos : 0 < point.k := hkLo.trans_le hpoint.2.2.1
  have hkHiNonneg : (0 : ℝ) ≤ box.kHi :=
    hkLo.le.trans hkOrder
  have heUpper : lrCertificateE point ≤
      (box.sHi : ℝ) * box.kHi := by
    unfold lrCertificateE
    exact mul_le_mul hpoint.2.1 hpoint.2.2.2.1 hkPos.le
      (hsLo.le.trans hsOrder)
  have he : lrCertificateE point ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · unfold lrCertificateE
      exact mul_pos hs.1 hkPos
    · exact heUpper.trans_lt (by simpa using hprodHi)
  have hchi : point.chi ∈ Ioo (0 : ℝ) 1 :=
    ⟨hchiLo.trans_le hpoint.2.2.2.2.1,
      hpoint.2.2.2.2.2.trans_lt hchiHi⟩
  exact ⟨hs, he, hchi⟩

theorem lrHighShapeInteriorBoxCheck_midpoint {box : CertificateBox}
    (hcheck : lrHighShapeInteriorBoxCheck box = true) :
    box.Contains box.midpoint := by
  have hparts :
      (0 : ℚ) < box.sLo ∧ box.sLo ≤ box.sHi ∧ box.sHi < 1 ∧
      (0 : ℚ) < box.kLo ∧ box.kLo ≤ box.kHi ∧
        box.sHi * box.kHi < 1 ∧
      (0 : ℚ) < box.chiLo ∧ box.chiLo ≤ box.chiHi ∧
        box.chiHi < 1 := by
    simpa [lrHighShapeInteriorBoxCheck] using hcheck
  let witness : CertificatePoint :=
    { s := box.sLo, k := box.kLo, chi := box.chiLo }
  have hwitness : box.Contains witness := by
    dsimp [witness]
    constructor
    · rfl
    constructor
    · change ((box.sLo : ℚ) : ℝ) ≤ box.sHi
      exact_mod_cast hparts.2.1
    constructor
    · rfl
    constructor
    · change ((box.kLo : ℚ) : ℝ) ≤ box.kHi
      exact_mod_cast hparts.2.2.2.2.1
    constructor
    · rfl
    · change ((box.chiLo : ℚ) : ℝ) ≤ box.chiHi
      exact_mod_cast hparts.2.2.2.2.2.2.2.1
  exact box.midpoint_mem hwitness

private lemma lrCertificateUTargetCurveDeriv_s (point : CertificatePoint) :
    lrCertificateUTargetCurveDeriv point 1 0 0 =
      lrCertificateUTargetDerivS point := by
  unfold lrCertificateUTargetCurveDeriv lrCertificateUTargetDerivS
    lrCertificateHalfMidpointNumeratorDerivS lrCertificateADerivS
    lrCertificateBFlowDerivS lrCertificateDDerivS
    lrCertificateGShapeDerivS lrCertificateWDerivS
    lrCertificatePWDerivS lrCertificateY0DerivS
    lrCertificateVDerivS
  unfold lrCertificateEDerivS lrCertificateXDerivS
  dsimp only
  ring

private lemma lrCertificateUTargetCurveDeriv_k (point : CertificatePoint) :
    lrCertificateUTargetCurveDeriv point 0 1 0 =
      lrCertificateUTargetDerivK point := by
  unfold lrCertificateUTargetCurveDeriv lrCertificateUTargetDerivK
    lrCertificateHalfMidpointNumeratorDerivK lrCertificateADerivK
    lrCertificateBFlowDerivK lrCertificateDDerivK
    lrCertificateGShapeDerivK lrCertificateWDerivK
    lrCertificatePWDerivK lrCertificateY0DerivK
    lrCertificateVDerivK
  unfold lrCertificateEDerivK lrCertificateXDerivK
  dsimp only
  ring

private lemma lrCertificateUTargetCurveDeriv_chi (point : CertificatePoint) :
    lrCertificateUTargetCurveDeriv point 0 0 1 =
      lrCertificateUTargetDerivChi point := by
  unfold lrCertificateUTargetCurveDeriv lrCertificateUTargetDerivChi
    lrCertificateHalfMidpointNumeratorDerivChi lrCertificateADerivChi
    lrCertificateBFlowDerivChi lrCertificateDDerivChi
    lrCertificateGShapeDerivChi lrCertificateWDerivChi
    lrCertificatePWDerivChi lrCertificateY0DerivChi
    lrCertificateVDerivChi
  unfold lrCertificateEDerivChi lrCertificateXDerivChi
  dsimp only
  ring

theorem hasDerivAt_lrCertificateUTarget_s {point : CertificatePoint}
    (hpoint : LRHighShapeInterior point) :
    HasDerivAt (fun s ↦ lrCertificateUTarget { point with s := s })
      (lrCertificateUTargetDerivS point) point.s := by
  have h := hasDerivAt_lrCertificateUTarget_curve
    (sfun := fun q ↦ q) (kfun := fun _q ↦ point.k)
    (chifun := fun _q ↦ point.chi)
    (hasDerivAt_id point.s) (hasDerivAt_const point.s point.k)
    (hasDerivAt_const point.s point.chi) hpoint.1 hpoint.2.1 hpoint.2.2
  convert h using 1
  simpa [lrCertificateCurve] using
    (lrCertificateUTargetCurveDeriv_s point).symm

theorem hasDerivAt_lrCertificateUTarget_k {point : CertificatePoint}
    (hpoint : LRHighShapeInterior point) :
    HasDerivAt (fun k ↦ lrCertificateUTarget { point with k := k })
      (lrCertificateUTargetDerivK point) point.k := by
  have h := hasDerivAt_lrCertificateUTarget_curve
    (sfun := fun _q ↦ point.s) (kfun := fun q ↦ q)
    (chifun := fun _q ↦ point.chi)
    (hasDerivAt_const point.k point.s) (hasDerivAt_id point.k)
    (hasDerivAt_const point.k point.chi) hpoint.1 hpoint.2.1 hpoint.2.2
  convert h using 1
  simpa [lrCertificateCurve] using
    (lrCertificateUTargetCurveDeriv_k point).symm

theorem hasDerivAt_lrCertificateUTarget_chi {point : CertificatePoint}
    (hpoint : LRHighShapeInterior point) :
    HasDerivAt (fun chi ↦ lrCertificateUTarget { point with chi := chi })
      (lrCertificateUTargetDerivChi point) point.chi := by
  have h := hasDerivAt_lrCertificateUTarget_curve
    (sfun := fun _q ↦ point.s) (kfun := fun _q ↦ point.k)
    (chifun := fun q ↦ q)
    (hasDerivAt_const point.chi point.s)
    (hasDerivAt_const point.chi point.k) (hasDerivAt_id point.chi)
    hpoint.1 hpoint.2.1 hpoint.2.2
  convert h using 1
  simpa [lrCertificateCurve] using
    (lrCertificateUTargetCurveDeriv_chi point).symm

/-- All untrusted scalar payloads needed at one accepted midpoint leaf. -/
structure LRHighShapeMidpointCertificate where
  kernel : LRHighShapeKernelCertificate
  gShape : LRHighShapeGCertificate
  ab : LRHighShapeABCertificate

namespace LRHighShapeMidpointCertificate

def mAD (box : CertificateBox)
    (certificate : LRHighShapeMidpointCertificate) : IntervalAD :=
  let v := certificate.kernel.coordinate.vAD box
  IntervalAD.divPositive v (IntervalAD.add (IntervalAD.const 1) v)

def numeratorAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeMidpointCertificate) : IntervalAD :=
  let coordinate := certificate.kernel.coordinate
  let ab := certificate.ab.evaluate terms box coordinate
  let g := certificate.gShape.evaluate terms box coordinate
  let w := certificate.kernel.wAD terms box
  let pw := certificate.kernel.pwAD terms box
  let p := IntervalAD.mul (certificate.mAD box) (IntervalAD.const (1 / 2))
  let bracket := IntervalAD.add
    (IntervalAD.mul (IntervalAD.sub (IntervalAD.const 1) p) ab.d)
    (IntervalAD.mul (IntervalAD.mul p (lrCertificateXAD box)) ab.b)
  IntervalAD.sub
    (IntervalAD.add (IntervalAD.mul ab.d g) (IntervalAD.mul ab.a pw))
    (IntervalAD.mul (IntervalAD.mul (IntervalAD.const 4) w) bracket)

def denominatorAD (box : CertificateBox) : IntervalAD :=
  IntervalAD.mul (lrCertificateSAD box) (lrCertificateEAD box)

def evaluateAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeMidpointCertificate) : IntervalAD :=
  IntervalAD.divPositive (certificate.numeratorAD terms box)
    (denominatorAD box)

def evaluate (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeMidpointCertificate) : MidpointCertificate :=
  let result := certificate.evaluateAD terms box
  { value := result.value
    derivS := result.derivS
    derivK := result.derivK
    derivChi := result.derivChi }

def check (box : CertificateBox)
    (certificate : LRHighShapeMidpointCertificate) : Bool :=
  let coordinate := certificate.kernel.coordinate
  let v := coordinate.vAD box
  decide (
    certificate.kernel.check box = true ∧
    certificate.gShape.check box coordinate = true ∧
    certificate.ab.check box coordinate = true ∧
    (0 : ℚ) < (IntervalAD.add (IntervalAD.const 1) v).value.lower ∧
    (0 : ℚ) < (denominatorAD box).value.lower)

def payloadCheck (box : CertificateBox)
    (certificate : LRHighShapeMidpointCertificate) : Bool :=
  lrHighShapeInteriorBoxCheck box && certificate.check box

def accepts (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeMidpointCertificate) : Bool :=
  checkedMidpointLeafAccepts payloadCheck (evaluate terms) box certificate

theorem mAD_sound {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRHighShapeMidpointCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true) :
    (certificate.mAD box).Contains (lrCertificateM point)
      (lrCertificateMDeriv point (lrCertificateVDerivS point))
      (lrCertificateMDeriv point (lrCertificateVDerivK point))
      (lrCertificateMDeriv point (lrCertificateVDerivChi point)) := by
  have hparts :
      certificate.kernel.check box = true ∧
      certificate.gShape.check box certificate.kernel.coordinate = true ∧
      certificate.ab.check box certificate.kernel.coordinate = true ∧
      (0 : ℚ) < (IntervalAD.add (IntervalAD.const 1)
        (certificate.kernel.coordinate.vAD box)).value.lower ∧
      (0 : ℚ) < (denominatorAD box).value.lower := by
    simpa [check] using hcheck
  have hkernelParts :
      certificate.kernel.coordinate.check box = true ∧
      certificate.kernel.omegaZero.check (lrCertificateSAD box) = true ∧
      certificate.kernel.omegaY0.check (lrCertificateSAD box)
        (lrCertificateY0AD box) = true ∧
      certificate.kernel.omegaE.check (lrCertificateSAD box)
        (lrCertificateEAD box) = true ∧
      (0 : ℚ) < (certificate.kernel.coordinate.vAD box).value.lower := by
    simpa [LRHighShapeKernelCertificate.check] using hparts.1
  have hv := certificate.kernel.coordinate.vAD_sound hpoint hkernelParts.1
  have honePlus := IntervalAD.contains_add (IntervalAD.contains_const 1) hv
  have h := IntervalAD.contains_divPositive hparts.2.2.2.1 hv honePlus
  unfold mAD lrCertificateM lrCertificateMDeriv
  dsimp only
  convert h using 1 <;> field_simp <;> ring

theorem numeratorAD_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint} {certificate : LRHighShapeMidpointCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true) :
    (certificate.numeratorAD terms box).Contains
      (lrCertificateHalfMidpointNumerator point)
      (lrCertificateHalfMidpointNumeratorDerivS point)
      (lrCertificateHalfMidpointNumeratorDerivK point)
      (lrCertificateHalfMidpointNumeratorDerivChi point) := by
  have hparts :
      certificate.kernel.check box = true ∧
      certificate.gShape.check box certificate.kernel.coordinate = true ∧
      certificate.ab.check box certificate.kernel.coordinate = true ∧
      (0 : ℚ) < (IntervalAD.add (IntervalAD.const 1)
        (certificate.kernel.coordinate.vAD box)).value.lower ∧
      (0 : ℚ) < (denominatorAD box).value.lower := by
    simpa [check] using hcheck
  have hab := certificate.ab.sound terms hpoint hparts.2.2.1
  have hg := certificate.gShape.sound terms hpoint hparts.2.1
  have hw := certificate.kernel.wAD_sound terms hpoint hparts.1
  have hpw := certificate.kernel.pwAD_sound terms hpoint hparts.1
  have hm := certificate.mAD_sound hpoint hcheck
  have hx := lrCertificateXAD_sound hpoint
  have hp := IntervalAD.contains_mul hm (IntervalAD.contains_const (1 / 2))
  have honeMinusP := IntervalAD.contains_sub (IntervalAD.contains_const 1) hp
  have hleft := IntervalAD.contains_mul honeMinusP hab.2.2
  have hpx := IntervalAD.contains_mul hp hx
  have hright := IntervalAD.contains_mul hpx hab.2.1
  have hbracket := IntervalAD.contains_add hleft hright
  have hdg := IntervalAD.contains_mul hab.2.2 hg
  have hapw := IntervalAD.contains_mul hab.1 hpw
  have hpositive := IntervalAD.contains_add hdg hapw
  have h4w := IntervalAD.contains_mul
    (IntervalAD.contains_mul (IntervalAD.contains_const 4) hw) hbracket
  have h := IntervalAD.contains_sub hpositive h4w
  unfold numeratorAD lrCertificateHalfMidpointNumerator
    lrCertificateHalfMidpointNumeratorDerivS
    lrCertificateHalfMidpointNumeratorDerivK
    lrCertificateHalfMidpointNumeratorDerivChi
    lrCertificateHalfMidpointNumeratorDeriv
    lrCertificateHalfMidpointBracket
    lrCertificateHalfMidpointBracketDeriv
    lrCertificateADerivS lrCertificateADerivK lrCertificateADerivChi
    lrCertificateBFlowDerivS lrCertificateBFlowDerivK
    lrCertificateBFlowDerivChi lrCertificateDDerivS
    lrCertificateDDerivK lrCertificateDDerivChi
  dsimp only
  convert h using 1 <;> ring

theorem denominatorAD_sound {box : CertificateBox} {point : CertificatePoint}
    (hpoint : box.Contains point) :
    (denominatorAD box).Contains (lrCertificateUDenominator point)
      (lrCertificateUDenominatorDeriv point 1 (lrCertificateEDerivS point))
      (lrCertificateUDenominatorDeriv point 0 (lrCertificateEDerivK point))
      (lrCertificateUDenominatorDeriv point 0
        (lrCertificateEDerivChi point)) := by
  have hs := IntervalAD.contains_variableS
    (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have h := IntervalAD.contains_mul hs (lrCertificateEAD_sound hpoint)
  simpa [denominatorAD, lrCertificateSAD, lrCertificateUDenominator,
    lrCertificateUDenominatorDeriv] using h

theorem evaluateAD_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint} {certificate : LRHighShapeMidpointCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true) :
    (certificate.evaluateAD terms box).Contains (lrCertificateUTarget point)
      (lrCertificateUTargetDerivS point)
      (lrCertificateUTargetDerivK point)
      (lrCertificateUTargetDerivChi point) := by
  have hparts :
      certificate.kernel.check box = true ∧
      certificate.gShape.check box certificate.kernel.coordinate = true ∧
      certificate.ab.check box certificate.kernel.coordinate = true ∧
      (0 : ℚ) < (IntervalAD.add (IntervalAD.const 1)
        (certificate.kernel.coordinate.vAD box)).value.lower ∧
      (0 : ℚ) < (denominatorAD box).value.lower := by
    simpa [check] using hcheck
  have h := IntervalAD.contains_divPositive hparts.2.2.2.2
    (certificate.numeratorAD_sound terms hpoint hcheck)
    (denominatorAD_sound hpoint)
  unfold evaluateAD lrCertificateUTarget lrCertificateUTargetDerivS
    lrCertificateUTargetDerivK lrCertificateUTargetDerivChi
    lrCertificateUTargetDeriv
  convert h using 1

theorem evaluate_value_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint} {certificate : LRHighShapeMidpointCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true) :
    (certificate.evaluate terms box).value.Contains
      (lrCertificateUTarget point) := by
  exact (certificate.evaluateAD_sound terms hpoint hcheck).1

noncomputable def evaluate_derivativeEnclosures (terms : ℕ)
    {box : CertificateBox}
    {certificate : LRHighShapeMidpointCertificate}
    (hcheck : certificate.check box = true)
    (hinterior : ∀ point, box.Contains point → LRHighShapeInterior point) :
    BoxDerivativeEnclosures lrCertificateUTarget box
      (certificate.evaluate terms box) := by
  refine
    { partialS := lrCertificateUTargetDerivS
      partialK := lrCertificateUTargetDerivK
      partialChi := lrCertificateUTargetDerivChi
      derivS := ?_
      derivK := ?_
      derivChi := ?_
      boundS := ?_
      boundK := ?_
      boundChi := ?_ }
  · intro point hpoint
    exact hasDerivAt_lrCertificateUTarget_s (hinterior point hpoint)
  · intro point hpoint
    exact hasDerivAt_lrCertificateUTarget_k (hinterior point hpoint)
  · intro point hpoint
    exact hasDerivAt_lrCertificateUTarget_chi (hinterior point hpoint)
  · intro point hpoint
    have h := certificate.evaluateAD_sound terms hpoint hcheck
    simpa [evaluate] using h.2.1
  · intro point hpoint
    have h := certificate.evaluateAD_sound terms hpoint hcheck
    simpa [evaluate] using h.2.2.1
  · intro point hpoint
    have h := certificate.evaluateAD_sound terms hpoint hcheck
    simpa [evaluate] using h.2.2.2

noncomputable def checkedEvaluatorSound (terms : ℕ) :
    CheckedMidpointLeafEvaluatorSound lrCertificateUTarget payloadCheck
      (evaluate terms) := by
  constructor
  · intro box certificate hpayload
    have hparts : lrHighShapeInteriorBoxCheck box = true ∧
        certificate.check box = true := by
      simpa [payloadCheck] using hpayload
    exact certificate.evaluate_value_sound terms
      (lrHighShapeInteriorBoxCheck_midpoint hparts.1) hparts.2
  · intro box certificate hpayload
    have hparts : lrHighShapeInteriorBoxCheck box = true ∧
        certificate.check box = true := by
      simpa [payloadCheck] using hpayload
    exact certificate.evaluate_derivativeEnclosures terms hparts.2
      (fun _point hpoint ↦ lrHighShapeInteriorBoxCheck_sound hparts.1 hpoint)

end LRHighShapeMidpointCertificate

theorem lrCertificateHalfMidpointNumerator_eq_flow
    {point : CertificatePoint}
    (hs : point.s ∈ Ioo (0 : ℝ) 1)
    (he : lrCertificateE point ∈ Ioo (0 : ℝ) 1)
    (hchi : point.chi ∈ Icc (0 : ℝ) 1) :
    lrCertificateHalfMidpointNumerator point =
      lrFlowNumeratorP (lrCertificateR point)
        (lrFlowM (lrCertificateV point) / 2)
        (lrCertificateV point) (lrCertificateT point) := by
  have hab := lrCertificateA_B_D_eq_flow hs he hchi
  have hg := lrCertificateGShape_eq_lrGShape he hchi
  have hw := lrCertificateW_eq_lrWKernel hs
  have hpw := lrCertificatePW_eq_lrFlowPW hs he hchi
  have hxPos : 0 < lrCertificateX point := by
    unfold lrCertificateX
    have hprod : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point ≤ 1 * lrCertificateE point :=
          mul_le_mul_of_nonneg_right hchi.2 he.1.le
        _ = lrCertificateE point := one_mul _
        _ < 1 := he.2
    linarith
  have htSq : lrCertificateT point ^ 2 = lrCertificateX point :=
    Real.sq_sqrt hxPos.le
  unfold lrCertificateHalfMidpointNumerator
    lrCertificateHalfMidpointBracket lrCertificateM lrFlowNumeratorP lrFlowM
  rw [hab.1, hab.2.1, hab.2.2, hg, hw, hpw, ← htSq]

theorem lrCertificateUTarget_eq_highShapeTarget
    {point : CertificatePoint}
    (hs : point.s ∈ Ioo (0 : ℝ) 1)
    (he : lrCertificateE point ∈ Ioo (0 : ℝ) 1)
    (hchi : point.chi ∈ Icc (0 : ℝ) 1) :
    lrCertificateUTarget point = lrHighShapeUCertificateTarget point := by
  unfold lrCertificateUTarget lrCertificateUDenominator
    lrHighShapeUCertificateTarget
  rw [lrCertificateHalfMidpointNumerator_eq_flow hs he hchi]

end CourtadeKumar
