import InformationTheory.CourtadeKumar.LRHighShapeVEvaluator

/-!
# Midpoint-form evaluator for the corrected direct reserve

The original direct-`V` leaf uses only the raw whole-box value interval.
This module retains the same payload and interval-AD expression, but also
uses its three derivative enclosures in the generic midpoint theorem.
-/

open Set

namespace CourtadeKumar

noncomputable def lrCertificateVTargetDeriv
    (point : CertificatePoint) (half' w' m' j' : ℝ) : ℝ :=
  half' - 2 *
    (w' * lrCertificateM point * lrCertificateJ point +
      lrCertificateW point * m' * lrCertificateJ point +
      lrCertificateW point * lrCertificateM point * j')

noncomputable def lrCertificateVTargetCurveDeriv
    (point : CertificatePoint) (s' k' chi' : ℝ) : ℝ :=
  let e' := s' * point.k + point.s * k'
  let x' := -(chi' * lrCertificateE point + point.chi * e')
  let v' := lrCertificateVDeriv point e' x'
  let m' := lrCertificateMDeriv point v'
  let b' := lrCertificateBFlowDeriv point s' e' v'
  let d' := lrCertificateDDeriv point s' e' v'
  let w' := lrCertificateOmegaDeriv point.s 0 s' 0
  let half' := lrCertificateHalfMidpointNumeratorCurveDeriv
    point s' k' chi'
  let j' := lrCertificateJDeriv point b' x' d'
  lrCertificateVTargetDeriv point half' w' m' j'

theorem hasDerivAt_lrCertificateVTarget_curve
    {z s' k' chi' : ℝ} {sfun kfun chifun : ℝ → ℝ}
    (hs : HasDerivAt sfun s' z) (hk : HasDerivAt kfun k' z)
    (hchi : HasDerivAt chifun chi' z)
    (hsMem : sfun z ∈ Ioo (0 : ℝ) 1)
    (heMem : lrCertificateE (lrCertificateCurve sfun kfun chifun z) ∈
      Ioo (0 : ℝ) 1)
    (hchiMem : chifun z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun q ↦ lrCertificateVTarget
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificateVTargetCurveDeriv
        (lrCertificateCurve sfun kfun chifun z) s' k' chi') z := by
  let point := lrCertificateCurve sfun kfun chifun z
  let e' := s' * point.k + point.s * k'
  let x' := -(chi' * lrCertificateE point + point.chi * e')
  let y0' := chi' * lrCertificateE point + point.chi * e'
  let v' := lrCertificateVDeriv point e' x'
  let m' := lrCertificateMDeriv point v'
  let a' := lrCertificateADeriv point e' v'
  let b' := lrCertificateBFlowDeriv point s' e' v'
  let d' := lrCertificateDDeriv point s' e' v'
  let g' := lrCertificateGShapeDeriv point y0' e' v'
  let w' := lrCertificateOmegaDeriv point.s 0 s' 0
  let pw' := lrCertificatePWDeriv point s' y0' e' v'
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
  have hJRaw := (hB.mul hx).sub hD
  have hJ : HasDerivAt
      (fun q ↦ lrCertificateJ (lrCertificateCurve sfun kfun chifun q))
      (lrCertificateJDeriv point b' x' d') z := by
    unfold lrCertificateJ lrCertificateJDeriv
    convert hJRaw using 1 <;> dsimp [point] <;> ring
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
  have hpositive := (hD.mul hG).add (hA.mul hPW)
  have hhalfCorrection := ((hasDerivAt_const z 4).mul hW).mul hbracket
  have hhalfRaw := hpositive.sub hhalfCorrection
  have hhalf : HasDerivAt
      (fun q ↦ lrCertificateHalfMidpointNumerator
        (lrCertificateCurve sfun kfun chifun q))
      (lrCertificateHalfMidpointNumeratorDeriv point
        a' d' g' w' pw' b' m' x') z := by
    unfold lrCertificateHalfMidpointNumerator
      lrCertificateHalfMidpointNumeratorDeriv
    convert hhalfRaw using 1 <;> dsimp [point] <;> ring
  have hcorrection :=
    (((hasDerivAt_const z 2).mul hW).mul hM).mul hJ
  have htargetRaw := hhalf.sub hcorrection
  rw [show (fun q ↦ lrCertificateVTarget
      (lrCertificateCurve sfun kfun chifun q)) =
      (fun q ↦ lrCertificateHalfMidpointNumerator
          (lrCertificateCurve sfun kfun chifun q) -
        2 * lrCertificateW (lrCertificateCurve sfun kfun chifun q) *
          lrCertificateM (lrCertificateCurve sfun kfun chifun q) *
          lrCertificateJ (lrCertificateCurve sfun kfun chifun q)) by
    funext q
    exact lrCertificateVTarget_eq_halfMidpoint_sub _]
  unfold lrCertificateVTargetCurveDeriv lrCertificateVTargetDeriv
  dsimp only
  convert htargetRaw using 1 <;>
    dsimp [point, e', x', y0', v', m', a', b', d', g', w', pw',
      lrCertificateHalfMidpointNumeratorCurveDeriv] <;> ring

noncomputable def lrCertificateVTargetDerivS (point : CertificatePoint) : ℝ :=
  lrCertificateVTargetCurveDeriv point 1 0 0

noncomputable def lrCertificateVTargetDerivK (point : CertificatePoint) : ℝ :=
  lrCertificateVTargetCurveDeriv point 0 1 0

noncomputable def lrCertificateVTargetDerivChi (point : CertificatePoint) : ℝ :=
  lrCertificateVTargetCurveDeriv point 0 0 1

theorem hasDerivAt_lrCertificateVTarget_s {point : CertificatePoint}
    (hpoint : LRHighShapeInterior point) :
    HasDerivAt (fun s ↦ lrCertificateVTarget { point with s := s })
      (lrCertificateVTargetDerivS point) point.s := by
  have h := hasDerivAt_lrCertificateVTarget_curve
    (sfun := fun q ↦ q) (kfun := fun _q ↦ point.k)
    (chifun := fun _q ↦ point.chi)
    (hasDerivAt_id point.s) (hasDerivAt_const point.s point.k)
    (hasDerivAt_const point.s point.chi) hpoint.1 hpoint.2.1 hpoint.2.2
  simpa [lrCertificateCurve, lrCertificateVTargetDerivS] using h

theorem hasDerivAt_lrCertificateVTarget_k {point : CertificatePoint}
    (hpoint : LRHighShapeInterior point) :
    HasDerivAt (fun k ↦ lrCertificateVTarget { point with k := k })
      (lrCertificateVTargetDerivK point) point.k := by
  have h := hasDerivAt_lrCertificateVTarget_curve
    (sfun := fun _q ↦ point.s) (kfun := fun q ↦ q)
    (chifun := fun _q ↦ point.chi)
    (hasDerivAt_const point.k point.s) (hasDerivAt_id point.k)
    (hasDerivAt_const point.k point.chi) hpoint.1 hpoint.2.1 hpoint.2.2
  simpa [lrCertificateCurve, lrCertificateVTargetDerivK] using h

theorem hasDerivAt_lrCertificateVTarget_chi {point : CertificatePoint}
    (hpoint : LRHighShapeInterior point) :
    HasDerivAt (fun chi ↦ lrCertificateVTarget { point with chi := chi })
      (lrCertificateVTargetDerivChi point) point.chi := by
  have h := hasDerivAt_lrCertificateVTarget_curve
    (sfun := fun _q ↦ point.s) (kfun := fun _q ↦ point.k)
    (chifun := fun q ↦ q)
    (hasDerivAt_const point.chi point.s)
    (hasDerivAt_const point.chi point.k) (hasDerivAt_id point.chi)
    hpoint.1 hpoint.2.1 hpoint.2.2
  simpa [lrCertificateCurve, lrCertificateVTargetDerivChi] using h

namespace LRHighShapeVCertificate

def midpointEvaluate (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeVCertificate) : MidpointCertificate :=
  let result := certificate.evaluateAD terms box
  { value := result.value
    derivS := result.derivS
    derivK := result.derivK
    derivChi := result.derivChi }

def midpointAccepts (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeVCertificate) : Bool :=
  checkedMidpointLeafAccepts payloadCheck (midpointEvaluate terms) box certificate

theorem evaluateAD_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint} {certificate : LRHighShapeVCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true) :
    (certificate.evaluateAD terms box).Contains
      (lrCertificateVTarget point)
      (lrCertificateVTargetDerivS point)
      (lrCertificateVTargetDerivK point)
      (lrCertificateVTargetDerivChi point) := by
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
  unfold evaluateAD jAD
  dsimp only
  rw [lrCertificateVTarget_eq_halfMidpoint_sub]
  convert h using 1 <;>
    simp only [lrCertificateVTargetDerivS, lrCertificateVTargetDerivK,
      lrCertificateVTargetDerivChi, lrCertificateVTargetCurveDeriv,
      lrCertificateVTargetDeriv, lrCertificateJ, lrCertificateJDeriv,
      lrCertificateHalfMidpointNumeratorCurveDeriv_s,
      lrCertificateHalfMidpointNumeratorCurveDeriv_k,
      lrCertificateHalfMidpointNumeratorCurveDeriv_chi,
      lrCertificateWDerivS, lrCertificateWDerivK,
      lrCertificateWDerivChi,
      lrCertificateVDerivS, lrCertificateVDerivK,
      lrCertificateVDerivChi,
      lrCertificateEDerivS, lrCertificateEDerivK,
      lrCertificateEDerivChi,
      lrCertificateXDerivS, lrCertificateXDerivK,
      lrCertificateXDerivChi] <;>
    ring

noncomputable def midpointDerivativeEnclosures (terms : ℕ)
    {box : CertificateBox} {certificate : LRHighShapeVCertificate}
    (hcheck : certificate.check box = true)
    (hinterior : ∀ point, box.Contains point → LRHighShapeInterior point) :
    BoxDerivativeEnclosures lrCertificateVTarget box
      (certificate.midpointEvaluate terms box) := by
  refine
    { partialS := lrCertificateVTargetDerivS
      partialK := lrCertificateVTargetDerivK
      partialChi := lrCertificateVTargetDerivChi
      derivS := ?_
      derivK := ?_
      derivChi := ?_
      boundS := ?_
      boundK := ?_
      boundChi := ?_ }
  · intro point hpoint
    exact hasDerivAt_lrCertificateVTarget_s (hinterior point hpoint)
  · intro point hpoint
    exact hasDerivAt_lrCertificateVTarget_k (hinterior point hpoint)
  · intro point hpoint
    exact hasDerivAt_lrCertificateVTarget_chi (hinterior point hpoint)
  · intro point hpoint
    have h := certificate.evaluateAD_sound terms hpoint hcheck
    simpa [midpointEvaluate] using h.2.1
  · intro point hpoint
    have h := certificate.evaluateAD_sound terms hpoint hcheck
    simpa [midpointEvaluate] using h.2.2.1
  · intro point hpoint
    have h := certificate.evaluateAD_sound terms hpoint hcheck
    simpa [midpointEvaluate] using h.2.2.2

noncomputable def checkedMidpointEvaluatorSound (terms : ℕ) :
    CheckedMidpointLeafEvaluatorSound lrCertificateVTarget payloadCheck
      (midpointEvaluate terms) := by
  constructor
  · intro box certificate hpayload
    have hparts : lrHighShapeInteriorBoxCheck box = true ∧
        certificate.check box = true := by
      simpa [payloadCheck] using hpayload
    have h := certificate.evaluateAD_sound terms
      (lrHighShapeInteriorBoxCheck_midpoint hparts.1) hparts.2
    simpa [midpointEvaluate] using h.1
  · intro box certificate hpayload
    have hparts : lrHighShapeInteriorBoxCheck box = true ∧
        certificate.check box = true := by
      simpa [payloadCheck] using hpayload
    exact certificate.midpointDerivativeEnclosures terms hparts.2
      (fun _point hpoint ↦ lrHighShapeInteriorBoxCheck_sound hparts.1 hpoint)

end LRHighShapeVCertificate

/-- Sound subdivision theorem using the stronger midpoint-form direct-`V`
leaf checker. -/
theorem lrHighShapeVMidpointSubdivisionCertificate_nonnegative
    (terms : ℕ) {box : CertificateBox}
    {certificate : SubdivisionCertificate LRHighShapeVCertificate
      LRHighShapeVDiscardData}
    (hcheck : certificate.check
      (LRHighShapeVCertificate.midpointAccepts terms)
      (lrHighShapeVDiscardCheck terms) box = true) :
    ∀ point, box.Contains point → LRHighShapeVRelevant point →
      0 ≤ lrCertificateVTarget point := by
  exact subdivisionCertificate_nonnegative_checked
    (LRHighShapeVCertificate.checkedMidpointEvaluatorSound terms)
    (lrHighShapeVDiscardCheck_sound terms) hcheck

end CourtadeKumar
