import InformationTheory.CourtadeKumar.LRHighShapeMidpointEvaluator

/-!
# Cancellation-safe evaluator for the high-shape tangent target

The tangent reserve contains the midpoint gap, the full-midpoint flow
numerator, and the slope `-ell'(M/2)`.  This file rewrites all three in the
high-shape coordinates `(s,k,chi)`.  In particular, the slope is evaluated
through

`log 2 + log (1 + v) - log (2 + v) = -log (1 - M/2)`,

which is the exact half-midpoint factor.
-/

open Set

namespace CourtadeKumar

noncomputable def lrCertificateSquareTarget (point : CertificatePoint) : ℝ :=
  lrCertificateG0 (lrCertificateV point) +
    lrCertificateQ
      (lrCertificateB point.s (lrCertificateY0 point)) +
    lrCertificateQ
      (lrCertificateB point.s (lrCertificateE point)) /
        lrCertificateV point

noncomputable def lrCertificatePrefixAtM (point : CertificatePoint) : ℝ :=
  point.s *
      (lrCertificateG0 (lrCertificateV point) +
        (1 + 1 / lrCertificateV point) * Real.log 2) +
    4 * (lrCertificateQ point.s - point.s * Real.log 2) /
      (1 + lrCertificateV point)

noncomputable def lrCertificateGap (point : CertificatePoint) : ℝ :=
  lrCertificateSquareTarget point - lrCertificatePrefixAtM point

noncomputable def lrCertificateHalfSlope (point : CertificatePoint) : ℝ :=
  4 * point.s * (1 + lrCertificateV point) ^ 2 /
        lrCertificateV point ^ 2 *
      (Real.log 2 + Real.log (1 + lrCertificateV point) -
        Real.log (2 + lrCertificateV point)) +
    4 * (lrCertificateQ point.s - point.s * Real.log 2)

noncomputable def lrCertificateJ (point : CertificatePoint) : ℝ :=
  lrCertificateBFlow point * lrCertificateX point - lrCertificateD point

noncomputable def lrCertificateMidpointBracket
    (point : CertificatePoint) : ℝ :=
  (1 - lrCertificateM point) * lrCertificateD point +
    lrCertificateM point * lrCertificateX point * lrCertificateBFlow point

noncomputable def lrCertificateMidpointNumerator
    (point : CertificatePoint) : ℝ :=
  lrCertificateD point * lrCertificateGShape point +
    lrCertificateA point * lrCertificatePW point -
    4 * lrCertificateW point * lrCertificateMidpointBracket point

noncomputable def lrCertificateTTarget (point : CertificatePoint) : ℝ :=
  4 * lrCertificateW point * lrCertificateJ point * lrCertificateGap point +
    lrCertificateHalfSlope point * lrCertificateMidpointNumerator point

theorem lrCertificateSquareTarget_eq_flow
    {point : CertificatePoint}
    (hs : point.s ∈ Ioo (0 : ℝ) 1)
    (he : lrCertificateE point ∈ Ioo (0 : ℝ) 1)
    (hchi : point.chi ∈ Icc (0 : ℝ) 1) :
    lrCertificateSquareTarget point =
      lrSquareTarget (lrCertificateR point) (lrCertificateV point)
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
  have htPos : 0 < lrCertificateT point := Real.sqrt_pos.2 hxPos
  have htSq : lrCertificateT point ^ 2 = lrCertificateX point :=
    Real.sq_sqrt hxPos.le
  have hradPos : 0 <
      (1 - lrCertificateE point) / lrCertificateX point :=
    div_pos (sub_pos.mpr he.2) hxPos
  have hvPos : 0 < lrCertificateV point := Real.sqrt_pos.2 hradPos
  have hvSq : lrCertificateV point ^ 2 =
      (1 - lrCertificateE point) / lrCertificateX point :=
    Real.sq_sqrt hradPos.le
  have hvtSq : (lrCertificateV point * lrCertificateT point) ^ 2 =
      1 - lrCertificateE point := by
    rw [mul_pow, hvSq, htSq]
    field_simp [hxPos.ne']
  have hRnonneg : 0 ≤ lrCertificateR point := by
    unfold lrCertificateR
    linarith [hs.2]
  have hsqrtRSq : Real.sqrt (lrCertificateR point) ^ 2 =
      lrCertificateR point := Real.sq_sqrt hRnonneg
  have hby0 : lrCertificateB point.s (lrCertificateY0 point) =
      1 - (Real.sqrt (lrCertificateR point) *
        lrCertificateT point) ^ 2 := by
    unfold lrCertificateB lrCertificateY0 lrCertificateR
      lrCertificateX at *
    rw [show (Real.sqrt (1 - point.s) * lrCertificateT point) ^ 2 =
      Real.sqrt (1 - point.s) ^ 2 * lrCertificateT point ^ 2 by ring,
      hsqrtRSq, htSq]
    ring
  have hbe : lrCertificateB point.s (lrCertificateE point) =
      1 - (lrCertificateV point *
        (Real.sqrt (lrCertificateR point) * lrCertificateT point)) ^ 2 := by
    rw [show (lrCertificateV point *
        (Real.sqrt (lrCertificateR point) * lrCertificateT point)) ^ 2 =
      Real.sqrt (lrCertificateR point) ^ 2 *
        (lrCertificateV point * lrCertificateT point) ^ 2 by ring,
      hsqrtRSq, hvtSq]
    unfold lrCertificateB lrCertificateR
    ring
  have hz1Pos : 0 < Real.sqrt (lrCertificateR point) *
      lrCertificateT point :=
    mul_pos (Real.sqrt_pos.2 (by unfold lrCertificateR; linarith [hs.2])) htPos
  have hz2Pos : 0 < lrCertificateV point *
      (Real.sqrt (lrCertificateR point) * lrCertificateT point) :=
    mul_pos hvPos hz1Pos
  have hsqrtBY0 : Real.sqrt
      (1 - lrCertificateB point.s (lrCertificateY0 point)) =
        Real.sqrt (lrCertificateR point) * lrCertificateT point := by
    rw [hby0, show 1 - (1 - (Real.sqrt (lrCertificateR point) *
      lrCertificateT point) ^ 2) =
        (Real.sqrt (lrCertificateR point) * lrCertificateT point) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos hz1Pos]
  have hsqrtBE : Real.sqrt
      (1 - lrCertificateB point.s (lrCertificateE point)) =
        lrCertificateV point *
          (Real.sqrt (lrCertificateR point) * lrCertificateT point) := by
    rw [hbe, show 1 - (1 - (lrCertificateV point *
      (Real.sqrt (lrCertificateR point) * lrCertificateT point)) ^ 2) =
        (lrCertificateV point *
          (Real.sqrt (lrCertificateR point) * lrCertificateT point)) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos hz2Pos]
  unfold lrCertificateSquareTarget lrSquareTarget lrGShape
  rw [lrCertificateG0_eq_lrG, lrCertificateQ_eq, lrCertificateQ_eq,
    hsqrtBY0, hsqrtBE]
  field_simp [hvPos.ne']
  ring

theorem lrCertificatePrefixAtM_eq_flow
    {point : CertificatePoint}
    (hs : point.s ∈ Ioo (0 : ℝ) 1)
    (he : lrCertificateE point ∈ Ioo (0 : ℝ) 1)
    (hchi : point.chi ∈ Icc (0 : ℝ) 1) :
    lrCertificatePrefixAtM point =
      lrPrefixEll (lrCertificateR point)
        (lrFlowM (lrCertificateV point)) := by
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
  have hvPlus : 0 < 1 + lrCertificateV point := by linarith
  have hG := lrG_eq_binEntropy_div hvPos
  have hprob : lrOddsToProbability (lrCertificateV point) =
      lrFlowM (lrCertificateV point) := rfl
  rw [hprob] at hG
  have hMne : lrFlowM (lrCertificateV point) ≠ 0 := by
    unfold lrFlowM
    exact div_ne_zero hvPos.ne' hvPlus.ne'
  have hOneMinusM : 1 - lrFlowM (lrCertificateV point) =
      1 / (1 + lrCertificateV point) := by
    unfold lrFlowM
    field_simp [hvPlus.ne']
    ring
  have hdelta : lrCertificateQ point.s - point.s * Real.log 2 =
      lrCertificateR point * Real.log 2 -
        topPhi (Real.sqrt (lrCertificateR point)) := by
    rw [lrCertificateQ_eq]
    unfold lrCertificateR
    ring
  unfold lrCertificatePrefixAtM lrPrefixEll
  rw [lrCertificateG0_eq_lrG, hG, hOneMinusM, hdelta]
  unfold lrCertificateR
  field_simp [hMne, hvPos.ne', hvPlus.ne']
  ring

theorem lrCertificateGap_eq_flow
    {point : CertificatePoint}
    (hs : point.s ∈ Ioo (0 : ℝ) 1)
    (he : lrCertificateE point ∈ Ioo (0 : ℝ) 1)
    (hchi : point.chi ∈ Icc (0 : ℝ) 1) :
    lrCertificateGap point =
      lrFlowGap (lrCertificateR point) (lrCertificateV point)
        (lrCertificateT point) := by
  unfold lrCertificateGap lrFlowGap
  rw [lrCertificateSquareTarget_eq_flow hs he hchi,
    lrCertificatePrefixAtM_eq_flow hs he hchi]

theorem lrCertificateHalfSlope_eq_flow
    {point : CertificatePoint}
    (hs : point.s ∈ Ioo (0 : ℝ) 1)
    (he : lrCertificateE point ∈ Ioo (0 : ℝ) 1)
    (hchi : point.chi ∈ Icc (0 : ℝ) 1) :
    lrCertificateHalfSlope point =
      lrFlowHalfSlope (lrCertificateR point) (lrCertificateV point) := by
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
  have hvPlus : 0 < 1 + lrCertificateV point := by linarith
  have htwoPlus : 0 < 2 + lrCertificateV point := by linarith
  have hMne : lrFlowM (lrCertificateV point) ≠ 0 := by
    unfold lrFlowM
    exact div_ne_zero hvPos.ne' hvPlus.ne'
  have hOneMinusHalf :
      1 - lrFlowM (lrCertificateV point) / 2 =
        (2 + lrCertificateV point) /
          (2 * (1 + lrCertificateV point)) := by
    unfold lrFlowM
    field_simp [hvPlus.ne']
    ring
  have hlog : Real.log
      (1 - lrFlowM (lrCertificateV point) / 2) =
        Real.log (2 + lrCertificateV point) - Real.log 2 -
          Real.log (1 + lrCertificateV point) := by
    rw [hOneMinusHalf,
      Real.log_div htwoPlus.ne' (mul_ne_zero (by norm_num) hvPlus.ne'),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hvPlus.ne']
    ring
  have hdelta : lrCertificateQ point.s - point.s * Real.log 2 =
      lrCertificateR point * Real.log 2 -
        topPhi (Real.sqrt (lrCertificateR point)) := by
    rw [lrCertificateQ_eq]
    unfold lrCertificateR
    ring
  unfold lrCertificateHalfSlope lrFlowHalfSlope lrFlowEllDeriv
  rw [hlog, hdelta]
  unfold lrCertificateR lrFlowM
  field_simp [hvPos.ne', hvPlus.ne', hMne]
  ring

theorem lrCertificateJ_eq_flow
    {point : CertificatePoint}
    (hs : point.s ∈ Ioo (0 : ℝ) 1)
    (he : lrCertificateE point ∈ Ioo (0 : ℝ) 1)
    (hchi : point.chi ∈ Icc (0 : ℝ) 1) :
    lrCertificateJ point =
      lrFlowJ (lrCertificateR point) (lrCertificateV point)
        (lrCertificateT point) := by
  have hab := lrCertificateA_B_D_eq_flow hs he hchi
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
  unfold lrCertificateJ lrFlowJ
  rw [hab.2.1, hab.2.2, htSq]

theorem lrCertificateMidpointNumerator_eq_flow
    {point : CertificatePoint}
    (hs : point.s ∈ Ioo (0 : ℝ) 1)
    (he : lrCertificateE point ∈ Ioo (0 : ℝ) 1)
    (hchi : point.chi ∈ Icc (0 : ℝ) 1) :
    lrCertificateMidpointNumerator point =
      lrFlowNumeratorP (lrCertificateR point)
        (lrFlowM (lrCertificateV point))
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
  unfold lrCertificateMidpointNumerator lrCertificateMidpointBracket
    lrCertificateM lrFlowNumeratorP lrFlowM
  rw [hab.1, hab.2.1, hab.2.2, hg, hw, hpw, htSq]

theorem lrCertificateTTarget_eq_highShapeTarget
    {point : CertificatePoint}
    (hs : point.s ∈ Ioo (0 : ℝ) 1)
    (he : lrCertificateE point ∈ Ioo (0 : ℝ) 1)
    (hchi : point.chi ∈ Icc (0 : ℝ) 1) :
    lrCertificateTTarget point = lrHighShapeTCertificateTarget point := by
  unfold lrCertificateTTarget lrHighShapeTCertificateTarget lrFlowTReserve
  rw [lrCertificateW_eq_lrWKernel hs,
    lrCertificateJ_eq_flow hs he hchi,
    lrCertificateGap_eq_flow hs he hchi,
    lrCertificateHalfSlope_eq_flow hs he hchi,
    lrCertificateMidpointNumerator_eq_flow hs he hchi]

/-! ## Exact first-derivative formulas -/

noncomputable def lrCertificateSquareTargetDeriv
    (point : CertificatePoint) (s' y0' e' v' : ℝ) : ℝ :=
  let by0 := lrCertificateB point.s (lrCertificateY0 point)
  let be := lrCertificateB point.s (lrCertificateE point)
  let by0' := lrCertificateBDeriv point.s (lrCertificateY0 point) s' y0'
  let be' := lrCertificateBDeriv point.s (lrCertificateE point) s' e'
  lrCertificateG0Prime (lrCertificateV point) * v' +
    lrCertificateQPrime by0 * by0' +
    (lrCertificateQPrime be * be' * lrCertificateV point -
      lrCertificateQ be * v') / lrCertificateV point ^ 2

noncomputable def lrCertificatePrefixAtMDeriv
    (point : CertificatePoint) (s' v' : ℝ) : ℝ :=
  let v := lrCertificateV point
  let core := lrCertificateG0 v + (1 + 1 / v) * Real.log 2
  let core' := lrCertificateG0Prime v * v' -
    v' / v ^ 2 * Real.log 2
  let delta := lrCertificateQ point.s - point.s * Real.log 2
  let delta' := lrCertificateQPrime point.s * s' - s' * Real.log 2
  s' * core + point.s * core' +
    4 * (delta' * (1 + v) - delta * v') / (1 + v) ^ 2

noncomputable def lrCertificateGapDeriv
    (point : CertificatePoint) (s' y0' e' v' : ℝ) : ℝ :=
  lrCertificateSquareTargetDeriv point s' y0' e' v' -
    lrCertificatePrefixAtMDeriv point s' v'

noncomputable def lrCertificateHalfSlopeDeriv
    (point : CertificatePoint) (s' v' : ℝ) : ℝ :=
  let v := lrCertificateV point
  let ratio := 4 * point.s * (1 + v) ^ 2 / v ^ 2
  let ratio' :=
    4 * s' * (1 + v) ^ 2 / v ^ 2 +
      8 * point.s * (1 + v) * v' / v ^ 2 -
      8 * point.s * (1 + v) ^ 2 * v' / v ^ 3
  let logFactor := Real.log 2 + Real.log (1 + v) - Real.log (2 + v)
  let logFactor' := v' / (1 + v) - v' / (2 + v)
  let delta' := lrCertificateQPrime point.s * s' - s' * Real.log 2
  ratio' * logFactor + ratio * logFactor' + 4 * delta'

noncomputable def lrCertificateJDeriv
    (point : CertificatePoint) (b' x' d' : ℝ) : ℝ :=
  b' * lrCertificateX point + lrCertificateBFlow point * x' - d'

noncomputable def lrCertificateMidpointBracketDeriv
    (point : CertificatePoint) (m' d' x' b' : ℝ) : ℝ :=
  (-m') * lrCertificateD point + (1 - lrCertificateM point) * d' +
    (m' * lrCertificateX point + lrCertificateM point * x') *
      lrCertificateBFlow point +
    (lrCertificateM point * lrCertificateX point) * b'

noncomputable def lrCertificateMidpointNumeratorDeriv
    (point : CertificatePoint)
    (d' g' a' pw' w' m' x' b' : ℝ) : ℝ :=
  d' * lrCertificateGShape point + lrCertificateD point * g' +
    (a' * lrCertificatePW point + lrCertificateA point * pw') -
    4 * (w' * lrCertificateMidpointBracket point +
      lrCertificateW point *
        lrCertificateMidpointBracketDeriv point m' d' x' b')

noncomputable def lrCertificateTTargetDeriv
    (point : CertificatePoint)
    (w' j' gap' halfSlope' numerator' : ℝ) : ℝ :=
  4 * (w' * lrCertificateJ point * lrCertificateGap point +
      lrCertificateW point * j' * lrCertificateGap point +
      lrCertificateW point * lrCertificateJ point * gap') +
    halfSlope' * lrCertificateMidpointNumerator point +
      lrCertificateHalfSlope point * numerator'

noncomputable def lrCertificateTTargetCoordinateDeriv
    (point : CertificatePoint)
    (s' e' x' y0' v' w' : ℝ) : ℝ :=
  let m' := lrCertificateMDeriv point v'
  let a' := lrCertificateADeriv point e' v'
  let b' := lrCertificateBFlowDeriv point s' e' v'
  let d' := lrCertificateDDeriv point s' e' v'
  let g' := lrCertificateGShapeDeriv point y0' e' v'
  let pw' := lrCertificatePWDeriv point s' y0' e' v'
  let square' := lrCertificateSquareTargetDeriv point s' y0' e' v'
  let prefix' := lrCertificatePrefixAtMDeriv point s' v'
  let gap' := square' - prefix'
  let halfSlope' := lrCertificateHalfSlopeDeriv point s' v'
  let j' := lrCertificateJDeriv point b' x' d'
  let numerator' := lrCertificateMidpointNumeratorDeriv point
    d' g' a' pw' w' m' x' b'
  lrCertificateTTargetDeriv point w' j' gap' halfSlope' numerator'

noncomputable def lrCertificateTTargetCurveDeriv
    (point : CertificatePoint) (s' k' chi' : ℝ) : ℝ :=
  let e' := s' * point.k + point.s * k'
  let x' := -(chi' * lrCertificateE point + point.chi * e')
  let y0' := chi' * lrCertificateE point + point.chi * e'
  let v' := lrCertificateVDeriv point e' x'
  lrCertificateTTargetCoordinateDeriv point s' e' x' y0' v'
    (lrCertificateOmegaDeriv point.s 0 s' 0)

noncomputable def lrCertificateTTargetDerivS
    (point : CertificatePoint) : ℝ :=
  lrCertificateTTargetCoordinateDeriv point 1
    (lrCertificateEDerivS point) (lrCertificateXDerivS point)
    (lrCertificateY0DerivS point) (lrCertificateVDerivS point)
    (lrCertificateWDerivS point)

noncomputable def lrCertificateTTargetDerivK
    (point : CertificatePoint) : ℝ :=
  lrCertificateTTargetCoordinateDeriv point 0
    (lrCertificateEDerivK point) (lrCertificateXDerivK point)
    (lrCertificateY0DerivK point) (lrCertificateVDerivK point)
    (lrCertificateWDerivK point)

noncomputable def lrCertificateTTargetDerivChi
    (point : CertificatePoint) : ℝ :=
  lrCertificateTTargetCoordinateDeriv point 0
    (lrCertificateEDerivChi point) (lrCertificateXDerivChi point)
    (lrCertificateY0DerivChi point) (lrCertificateVDerivChi point)
    (lrCertificateWDerivChi point)

/-! ## Checked interval-AD assembly -/

structure LRHighShapeTangentCertificate where
  base : LRHighShapeMidpointCertificate
  qBY0 : LRQADCertificate
  qBE : LRQADCertificate
  qS : LRQADCertificate
  logTwoPlusV : RationalEnclosure.LogIntervalCertificate

namespace LRHighShapeTangentCertificate

structure Evaluation where
  target : IntervalAD
  squareTarget : IntervalAD
  prefixAtM : IntervalAD
  gap : IntervalAD
  halfSlope : IntervalAD
  j : IntervalAD
  midpointNumerator : IntervalAD

def evaluateAll (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeTangentCertificate) : Evaluation :=
  let coordinate := certificate.base.kernel.coordinate
  let v := coordinate.vAD box
  let s := lrCertificateSAD box
  let e := lrCertificateEAD box
  let x := lrCertificateXAD box
  let y0 := lrCertificateY0AD box
  let by0 := lrCertificateBAD s y0
  let be := lrCertificateBAD s e
  let qBY0 := certificate.qBY0.evaluate terms by0
  let qBE := certificate.qBE.evaluate terms be
  let qS := certificate.qS.evaluate terms s
  let g0 := certificate.base.gShape.g0.evaluate terms v
  let logTwo := IntervalAD.log terms certificate.base.gShape.g0.logTwo
    (IntervalAD.const 2)
  let logOnePlusV := IntervalAD.log terms certificate.base.ab.logOnePlusV
    (IntervalAD.add (IntervalAD.const 1) v)
  let logTwoPlusV := IntervalAD.log terms certificate.logTwoPlusV
    (IntervalAD.add (IntervalAD.const 2) v)
  let squareTarget := IntervalAD.add (IntervalAD.add g0 qBY0)
    (IntervalAD.divPositive qBE v)
  let core := IntervalAD.add g0
    (IntervalAD.mul
      (IntervalAD.add (IntervalAD.const 1) (IntervalAD.invPositive v))
      logTwo)
  let delta := IntervalAD.sub qS (IntervalAD.mul s logTwo)
  let prefixAtM := IntervalAD.add (IntervalAD.mul s core)
    (IntervalAD.divPositive (IntervalAD.mul (IntervalAD.const 4) delta)
      (IntervalAD.add (IntervalAD.const 1) v))
  let gap := IntervalAD.sub squareTarget prefixAtM
  let logFactor := IntervalAD.sub (IntervalAD.add logTwo logOnePlusV)
    logTwoPlusV
  let onePlusVSq := IntervalAD.mul
    (IntervalAD.add (IntervalAD.const 1) v)
    (IntervalAD.add (IntervalAD.const 1) v)
  let vSq := IntervalAD.mul v v
  let ratio := IntervalAD.divPositive
    (IntervalAD.mul (IntervalAD.mul (IntervalAD.const 4) s)
      onePlusVSq)
    vSq
  let halfSlope := IntervalAD.add (IntervalAD.mul ratio logFactor)
    (IntervalAD.mul (IntervalAD.const 4) delta)
  let ab := certificate.base.ab.evaluate terms box coordinate
  let g := certificate.base.gShape.evaluate terms box coordinate
  let w := certificate.base.kernel.wAD terms box
  let pw := certificate.base.kernel.pwAD terms box
  let m := certificate.base.mAD box
  let j := IntervalAD.sub (IntervalAD.mul ab.b x) ab.d
  let bracket := IntervalAD.add
    (IntervalAD.mul (IntervalAD.sub (IntervalAD.const 1) m) ab.d)
    (IntervalAD.mul (IntervalAD.mul m x) ab.b)
  let midpointNumerator := IntervalAD.sub
    (IntervalAD.add (IntervalAD.mul ab.d g) (IntervalAD.mul ab.a pw))
    (IntervalAD.mul (IntervalAD.mul (IntervalAD.const 4) w) bracket)
  let target := IntervalAD.add
    (IntervalAD.mul
      (IntervalAD.mul (IntervalAD.mul (IntervalAD.const 4) w) j) gap)
    (IntervalAD.mul halfSlope midpointNumerator)
  { target := target
    squareTarget := squareTarget
    prefixAtM := prefixAtM
    gap := gap
    halfSlope := halfSlope
    j := j
    midpointNumerator := midpointNumerator }

def evaluateAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeTangentCertificate) : IntervalAD :=
  (certificate.evaluateAll terms box).target

def check (box : CertificateBox)
    (certificate : LRHighShapeTangentCertificate) : Bool :=
  let coordinate := certificate.base.kernel.coordinate
  let v := coordinate.vAD box
  let s := lrCertificateSAD box
  let e := lrCertificateEAD box
  let y0 := lrCertificateY0AD box
  let by0 := lrCertificateBAD s y0
  let be := lrCertificateBAD s e
  decide (
    certificate.base.check box = true ∧
    certificate.qBY0.check by0.value = true ∧
    certificate.qBE.check be.value = true ∧
    certificate.qS.check s.value = true ∧
    certificate.logTwoPlusV.check
      (IntervalAD.add (IntervalAD.const 2) v).value = true ∧
    (0 : ℚ) < v.value.lower ∧
    (0 : ℚ) < (IntervalAD.add (IntervalAD.const 1) v).value.lower ∧
    (0 : ℚ) < (IntervalAD.add (IntervalAD.const 2) v).value.lower ∧
    (0 : ℚ) < (IntervalAD.mul v v).value.lower)

set_option maxHeartbeats 800000 in
theorem evaluateAD_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint}
    {certificate : LRHighShapeTangentCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true) :
    (certificate.evaluateAD terms box).Contains
      (lrCertificateTTarget point)
      (lrCertificateTTargetDerivS point)
      (lrCertificateTTargetDerivK point)
      (lrCertificateTTargetDerivChi point) := by
  let coordinate := certificate.base.kernel.coordinate
  let v := coordinate.vAD box
  let s := lrCertificateSAD box
  let e := lrCertificateEAD box
  let x := lrCertificateXAD box
  let y0 := lrCertificateY0AD box
  let by0 := lrCertificateBAD s y0
  let be := lrCertificateBAD s e
  have hparts :
      certificate.base.check box = true ∧
      certificate.qBY0.check by0.value = true ∧
      certificate.qBE.check be.value = true ∧
      certificate.qS.check s.value = true ∧
      certificate.logTwoPlusV.check
        (IntervalAD.add (IntervalAD.const 2) v).value = true ∧
      (0 : ℚ) < v.value.lower ∧
      (0 : ℚ) < (IntervalAD.add (IntervalAD.const 1) v).value.lower ∧
      (0 : ℚ) < (IntervalAD.add (IntervalAD.const 2) v).value.lower ∧
      (0 : ℚ) < (IntervalAD.mul v v).value.lower := by
    simpa [check, coordinate, v, s, e, y0, by0, be] using hcheck
  have hbaseParts :
      certificate.base.kernel.check box = true ∧
      certificate.base.gShape.check box coordinate = true ∧
      certificate.base.ab.check box coordinate = true ∧
      (0 : ℚ) <
        (IntervalAD.add (IntervalAD.const 1) v).value.lower ∧
      (0 : ℚ) <
        (LRHighShapeMidpointCertificate.denominatorAD box).value.lower := by
    simpa [LRHighShapeMidpointCertificate.check, coordinate, v]
      using hparts.1
  have hgParts :
      coordinate.check box = true ∧
      certificate.base.gShape.g0.check v = true ∧
      certificate.base.gShape.qY0.check y0.value = true ∧
      certificate.base.gShape.qE.check e.value = true ∧
      (0 : ℚ) < v.value.lower := by
    simpa [LRHighShapeGCertificate.check, coordinate, v, e, y0]
      using hbaseParts.2.1
  have hg0Parts :
      certificate.base.gShape.g0.logV.check v.value = true ∧
      certificate.base.gShape.g0.logOnePlusV.check
        (LRG0ADCertificate.onePlusV v).value = true ∧
      certificate.base.gShape.g0.logTwo.check
        (IntervalAD.const 2).value = true ∧
      (0 : ℚ) < v.value.lower := by
    simpa [LRG0ADCertificate.check] using hgParts.2.1
  have habParts :
      coordinate.check box = true ∧
      certificate.base.ab.logOnePlusV.check
        (IntervalAD.add (IntervalAD.const 1) v).value = true ∧
      certificate.base.ab.logE.check e.value = true ∧
      certificate.base.ab.logBE.check
        (lrCertificateBAD s e).value = true := by
    simpa [LRHighShapeABCertificate.check, coordinate, v, s, e]
      using hbaseParts.2.2.1
  have hsAD := IntervalAD.contains_variableS
    (show box.sInterval.Contains point.s from ⟨hpoint.1, hpoint.2.1⟩)
  have heAD := lrCertificateEAD_sound hpoint
  have hxAD := lrCertificateXAD_sound hpoint
  have hy0AD := lrCertificateY0AD_sound hpoint
  have hvAD := coordinate.vAD_sound hpoint hgParts.1
  have hvLowerReal : (0 : ℝ) < v.value.lower := by
    exact_mod_cast hparts.2.2.2.2.2.1
  have hvPos : 0 < lrCertificateV point :=
    hvLowerReal.trans_le hvAD.1.1
  have hvPlus : 1 + lrCertificateV point ≠ 0 := by linarith
  have htwoPlus : 2 + lrCertificateV point ≠ 0 := by linarith
  have hby0AD := lrCertificateBAD_sound hsAD hy0AD
  have hbeAD := lrCertificateBAD_sound hsAD heAD
  have hqBY0 := certificate.qBY0.sound terms hparts.2.1 hby0AD
  have hqBE := certificate.qBE.sound terms hparts.2.2.1 hbeAD
  have hqS := certificate.qS.sound terms hparts.2.2.2.1 hsAD
  have hg0 := certificate.base.gShape.g0.sound terms hgParts.2.1 hvAD
  have hlogTwo := IntervalAD.contains_log terms hg0Parts.2.2.1
    (IntervalAD.contains_const 2)
  have honePlusV := IntervalAD.contains_add
    (IntervalAD.contains_const 1) hvAD
  have htwoPlusV := IntervalAD.contains_add
    (IntervalAD.contains_const 2) hvAD
  have hlogOnePlusV := IntervalAD.contains_log terms habParts.2.1 honePlusV
  have hlogTwoPlusV := IntervalAD.contains_log terms hparts.2.2.2.2.1
    htwoPlusV
  have hqBEdiv := IntervalAD.contains_divPositive hparts.2.2.2.2.2.1
    hqBE hvAD
  have hsquare := IntervalAD.contains_add (IntervalAD.contains_add hg0 hqBY0)
    hqBEdiv
  have hsquareNamed :
      ((IntervalAD.add (IntervalAD.add
        (certificate.base.gShape.g0.evaluate terms v)
        (certificate.qBY0.evaluate terms by0))
        (IntervalAD.divPositive (certificate.qBE.evaluate terms be) v))).Contains
          (lrCertificateSquareTarget point)
          (lrCertificateSquareTargetDeriv point 1
            (lrCertificateY0DerivS point) (lrCertificateEDerivS point)
            (lrCertificateVDerivS point))
          (lrCertificateSquareTargetDeriv point 0
            (lrCertificateY0DerivK point) (lrCertificateEDerivK point)
            (lrCertificateVDerivK point))
          (lrCertificateSquareTargetDeriv point 0
            (lrCertificateY0DerivChi point) (lrCertificateEDerivChi point)
            (lrCertificateVDerivChi point)) := by
    convert hsquare using 1 <;>
      simp only [lrCertificateSquareTarget,
        lrCertificateSquareTargetDeriv] <;>
      field_simp [hvPos.ne'] <;> ring
  have hinvV := IntervalAD.contains_invPositive hparts.2.2.2.2.2.1 hvAD
  have hfactor := IntervalAD.contains_add (IntervalAD.contains_const 1) hinvV
  have hcore := IntervalAD.contains_add hg0
    (IntervalAD.contains_mul hfactor hlogTwo)
  have hdelta := IntervalAD.contains_sub hqS
    (IntervalAD.contains_mul hsAD hlogTwo)
  have hprefix := IntervalAD.contains_add
    (IntervalAD.contains_mul hsAD hcore)
    (IntervalAD.contains_divPositive hparts.2.2.2.2.2.2.1
      (IntervalAD.contains_mul (IntervalAD.contains_const 4) hdelta)
      honePlusV)
  have hprefixNamed :
      ((IntervalAD.add
        (IntervalAD.mul s
          (IntervalAD.add (certificate.base.gShape.g0.evaluate terms v)
            (IntervalAD.mul
              (IntervalAD.add (IntervalAD.const 1)
                (IntervalAD.invPositive v))
              (IntervalAD.log terms certificate.base.gShape.g0.logTwo
                (IntervalAD.const 2)))))
        (IntervalAD.divPositive
          (IntervalAD.mul (IntervalAD.const 4)
            (IntervalAD.sub (certificate.qS.evaluate terms s)
              (IntervalAD.mul s
                (IntervalAD.log terms certificate.base.gShape.g0.logTwo
                  (IntervalAD.const 2)))))
          (IntervalAD.add (IntervalAD.const 1) v)))).Contains
        (lrCertificatePrefixAtM point)
        (lrCertificatePrefixAtMDeriv point 1
          (lrCertificateVDerivS point))
        (lrCertificatePrefixAtMDeriv point 0
          (lrCertificateVDerivK point))
        (lrCertificatePrefixAtMDeriv point 0
          (lrCertificateVDerivChi point)) := by
    convert hprefix using 1 <;>
      simp only [lrCertificatePrefixAtM,
        lrCertificatePrefixAtMDeriv, pow_two] <;>
      field_simp [hvPos.ne', hvPlus] <;> ring
  have hgapNamed := IntervalAD.contains_sub hsquareNamed hprefixNamed
  have hlogFactor := IntervalAD.contains_sub
    (IntervalAD.contains_add hlogTwo hlogOnePlusV) hlogTwoPlusV
  have honePlusVSq := IntervalAD.contains_mul honePlusV honePlusV
  have hvSq := IntervalAD.contains_mul hvAD hvAD
  have hratio := IntervalAD.contains_divPositive hparts.2.2.2.2.2.2.2.2
    (IntervalAD.contains_mul
      (IntervalAD.contains_mul (IntervalAD.contains_const 4) hsAD)
      honePlusVSq)
    hvSq
  have hhalfSlope := IntervalAD.contains_add
    (IntervalAD.contains_mul hratio hlogFactor)
    (IntervalAD.contains_mul (IntervalAD.contains_const 4) hdelta)
  have hhalfSlopeNamed :
      ((IntervalAD.add
        (IntervalAD.mul
          (IntervalAD.divPositive
            (IntervalAD.mul (IntervalAD.mul (IntervalAD.const 4) s)
              (IntervalAD.mul
                (IntervalAD.add (IntervalAD.const 1) v)
                (IntervalAD.add (IntervalAD.const 1) v)))
            (IntervalAD.mul v v))
          (IntervalAD.sub
            (IntervalAD.add
              (IntervalAD.log terms certificate.base.gShape.g0.logTwo
                (IntervalAD.const 2))
              (IntervalAD.log terms certificate.base.ab.logOnePlusV
                (IntervalAD.add (IntervalAD.const 1) v)))
            (IntervalAD.log terms certificate.logTwoPlusV
              (IntervalAD.add (IntervalAD.const 2) v))))
        (IntervalAD.mul (IntervalAD.const 4)
          (IntervalAD.sub (certificate.qS.evaluate terms s)
            (IntervalAD.mul s
              (IntervalAD.log terms certificate.base.gShape.g0.logTwo
                (IntervalAD.const 2))))))).Contains
        (lrCertificateHalfSlope point)
        (lrCertificateHalfSlopeDeriv point 1
          (lrCertificateVDerivS point))
        (lrCertificateHalfSlopeDeriv point 0
          (lrCertificateVDerivK point))
        (lrCertificateHalfSlopeDeriv point 0
          (lrCertificateVDerivChi point)) := by
    convert hhalfSlope using 1 <;>
      simp only [lrCertificateHalfSlope,
        lrCertificateHalfSlopeDeriv, pow_two] <;>
      field_simp [hvPos.ne', hvPlus, htwoPlus] <;> ring
  have hab := certificate.base.ab.sound terms hpoint hbaseParts.2.2.1
  have hg := certificate.base.gShape.sound terms hpoint hbaseParts.2.1
  have hw := certificate.base.kernel.wAD_sound terms hpoint hbaseParts.1
  have hpw := certificate.base.kernel.pwAD_sound terms hpoint hbaseParts.1
  have hm := certificate.base.mAD_sound hpoint hparts.1
  have hj := IntervalAD.contains_sub (IntervalAD.contains_mul hab.2.1 hxAD)
    hab.2.2
  have hjNamed :
      (IntervalAD.sub
        (IntervalAD.mul
          (certificate.base.ab.evaluate terms box coordinate).b x)
        (certificate.base.ab.evaluate terms box coordinate).d).Contains
        (lrCertificateJ point)
        (lrCertificateJDeriv point
          (lrCertificateBFlowDeriv point 1 (lrCertificateEDerivS point)
            (lrCertificateVDerivS point))
          (lrCertificateXDerivS point)
          (lrCertificateDDeriv point 1 (lrCertificateEDerivS point)
            (lrCertificateVDerivS point)))
        (lrCertificateJDeriv point
          (lrCertificateBFlowDeriv point 0 (lrCertificateEDerivK point)
            (lrCertificateVDerivK point))
          (lrCertificateXDerivK point)
          (lrCertificateDDeriv point 0 (lrCertificateEDerivK point)
            (lrCertificateVDerivK point)))
        (lrCertificateJDeriv point
          (lrCertificateBFlowDeriv point 0 (lrCertificateEDerivChi point)
            (lrCertificateVDerivChi point))
          (lrCertificateXDerivChi point)
          (lrCertificateDDeriv point 0 (lrCertificateEDerivChi point)
            (lrCertificateVDerivChi point))) := by
    simpa [lrCertificateJ, lrCertificateJDeriv] using hj
  have hbracket := IntervalAD.contains_add
    (IntervalAD.contains_mul
      (IntervalAD.contains_sub (IntervalAD.contains_const 1) hm) hab.2.2)
    (IntervalAD.contains_mul (IntervalAD.contains_mul hm hxAD) hab.2.1)
  have hmidpointNumerator := IntervalAD.contains_sub
    (IntervalAD.contains_add (IntervalAD.contains_mul hab.2.2 hg)
      (IntervalAD.contains_mul hab.1 hpw))
    (IntervalAD.contains_mul
      (IntervalAD.contains_mul (IntervalAD.contains_const 4) hw) hbracket)
  have hmidpointNumeratorNamed :
      (IntervalAD.sub
        (IntervalAD.add
          (IntervalAD.mul
            (certificate.base.ab.evaluate terms box coordinate).d
            (certificate.base.gShape.evaluate terms box coordinate))
          (IntervalAD.mul
            (certificate.base.ab.evaluate terms box coordinate).a
            (certificate.base.kernel.pwAD terms box)))
        (IntervalAD.mul
          (IntervalAD.mul (IntervalAD.const 4)
            (certificate.base.kernel.wAD terms box))
          (IntervalAD.add
            (IntervalAD.mul
              (IntervalAD.sub (IntervalAD.const 1)
                (certificate.base.mAD box))
              (certificate.base.ab.evaluate terms box coordinate).d)
            (IntervalAD.mul
              (IntervalAD.mul (certificate.base.mAD box) x)
              (certificate.base.ab.evaluate terms box coordinate).b)))).Contains
        (lrCertificateMidpointNumerator point)
        (lrCertificateMidpointNumeratorDeriv point
          (lrCertificateDDeriv point 1 (lrCertificateEDerivS point)
            (lrCertificateVDerivS point))
          (lrCertificateGShapeDerivS point)
          (lrCertificateADeriv point (lrCertificateEDerivS point)
            (lrCertificateVDerivS point))
          (lrCertificatePWDerivS point) (lrCertificateWDerivS point)
          (lrCertificateMDeriv point (lrCertificateVDerivS point))
          (lrCertificateXDerivS point)
          (lrCertificateBFlowDeriv point 1 (lrCertificateEDerivS point)
            (lrCertificateVDerivS point)))
        (lrCertificateMidpointNumeratorDeriv point
          (lrCertificateDDeriv point 0 (lrCertificateEDerivK point)
            (lrCertificateVDerivK point))
          (lrCertificateGShapeDerivK point)
          (lrCertificateADeriv point (lrCertificateEDerivK point)
            (lrCertificateVDerivK point))
          (lrCertificatePWDerivK point) (lrCertificateWDerivK point)
          (lrCertificateMDeriv point (lrCertificateVDerivK point))
          (lrCertificateXDerivK point)
          (lrCertificateBFlowDeriv point 0 (lrCertificateEDerivK point)
            (lrCertificateVDerivK point)))
        (lrCertificateMidpointNumeratorDeriv point
          (lrCertificateDDeriv point 0 (lrCertificateEDerivChi point)
            (lrCertificateVDerivChi point))
          (lrCertificateGShapeDerivChi point)
          (lrCertificateADeriv point (lrCertificateEDerivChi point)
            (lrCertificateVDerivChi point))
          (lrCertificatePWDerivChi point) (lrCertificateWDerivChi point)
          (lrCertificateMDeriv point (lrCertificateVDerivChi point))
          (lrCertificateXDerivChi point)
          (lrCertificateBFlowDeriv point 0 (lrCertificateEDerivChi point)
            (lrCertificateVDerivChi point))) := by
    convert hmidpointNumerator using 1 <;>
      simp only [lrCertificateMidpointNumerator,
        lrCertificateMidpointNumeratorDeriv,
        lrCertificateMidpointBracket,
        lrCertificateMidpointBracketDeriv] <;> ring
  have htarget := IntervalAD.contains_add
    (IntervalAD.contains_mul
      (IntervalAD.contains_mul
        (IntervalAD.contains_mul (IntervalAD.contains_const 4) hw) hjNamed)
      hgapNamed)
    (IntervalAD.contains_mul hhalfSlopeNamed hmidpointNumeratorNamed)
  unfold evaluateAD evaluateAll
  dsimp only
  convert htarget using 1 <;>
    simp only [lrCertificateTTargetDerivS, lrCertificateTTargetDerivK,
      lrCertificateTTargetDerivChi,
      lrCertificateTTargetCoordinateDeriv,
      lrCertificateTTarget, lrCertificateTTargetDeriv,
      lrCertificateGap, lrCertificateGapDeriv,
      lrCertificateGShapeDerivS, lrCertificateGShapeDerivK,
      lrCertificateGShapeDerivChi,
      lrCertificatePWDerivS, lrCertificatePWDerivK,
      lrCertificatePWDerivChi] <;>
    ring

theorem evaluate_value_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint}
    {certificate : LRHighShapeTangentCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true) :
    (certificate.evaluateAD terms box).value.Contains
      (lrCertificateTTarget point) :=
  (certificate.evaluateAD_sound terms hpoint hcheck).1

theorem evaluate_highShapeTarget_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint}
    {certificate : LRHighShapeTangentCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true)
    (hinterior : LRHighShapeInterior point) :
    (certificate.evaluateAD terms box).value.Contains
      (lrHighShapeTCertificateTarget point) := by
  rw [← lrCertificateTTarget_eq_highShapeTarget hinterior.1
    hinterior.2.1 ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩]
  exact certificate.evaluate_value_sound terms hpoint hcheck

end LRHighShapeTangentCertificate

end CourtadeKumar
