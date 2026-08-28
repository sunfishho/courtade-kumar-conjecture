import InformationTheory.CourtadeKumar.LRHighShapeTangentEvaluator
import InformationTheory.CourtadeKumar.LRPositiveGapBudgetAssembly

/-!
# The positive-chart gap budget in high-shape coordinates

This file transports `lrFlowGapBudget` to the cancellation coordinates
`(s,k,chi)`.  It also records the exact `k`-derivative needed to turn a
lower bound at `k = 4` into a proof on the noncompact `k >= 4` tail.
-/

open Set

namespace CourtadeKumar

/-- The target gap left after paying the half-midpoint tangent expenditure,
written in the cancellation coordinates used by the checked evaluators. -/
noncomputable def lrCertificateGapBudget (point : CertificatePoint) : ℝ :=
  lrCertificateGap point -
    lrCertificateHalfSlope point * (lrCertificateM point / 2)

/-- Exact identification of the coordinate gap budget with the flow budget. -/
theorem lrCertificateGapBudget_eq_flow
    {point : CertificatePoint}
    (hs : point.s ∈ Ioo (0 : ℝ) 1)
    (he : lrCertificateE point ∈ Ioo (0 : ℝ) 1)
    (hchi : point.chi ∈ Icc (0 : ℝ) 1) :
    lrCertificateGapBudget point =
      lrFlowGapBudget (lrCertificateR point) (lrCertificateV point)
        (lrCertificateT point) := by
  unfold lrCertificateGapBudget lrFlowGapBudget lrCertificateM lrFlowM
  rw [lrCertificateGap_eq_flow hs he hchi,
    lrCertificateHalfSlope_eq_flow hs he hchi]

/-- The coordinate budget evaluated at a physical flow point is exactly the
analytic flow budget. -/
theorem lrCertificateGapBudget_flow
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (he : 0 < 1 - v ^ 2 * t ^ 2) :
    lrCertificateGapBudget (lrFlowCertificatePoint R v t) =
      lrFlowGapBudget R v t := by
  have heLt : 1 - v ^ 2 * t ^ 2 < 1 := by
    nlinarith [mul_pos (sq_pos_of_pos hv.1) (sq_pos_of_pos ht.1)]
  have heNe : 1 - v ^ 2 * t ^ 2 ≠ 0 := he.ne'
  have hpointE :
      lrCertificateE (lrFlowCertificatePoint R v t) ∈ Ioo (0 : ℝ) 1 := by
    rw [lrCertificateE_flow hR.2.ne]
    exact ⟨he, heLt⟩
  have hpointChi :
      (lrFlowCertificatePoint R v t).chi ∈ Icc (0 : ℝ) 1 := by
    unfold lrFlowCertificatePoint
    have htSqLe : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have hnum : 0 ≤ 1 - t ^ 2 := sub_nonneg.mpr htSqLe
    constructor
    · exact div_nonneg hnum he.le
    · rw [div_le_one he]
      have hvSqLe : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
      have hscaled : v ^ 2 * t ^ 2 ≤ 1 * t ^ 2 :=
        mul_le_mul_of_nonneg_right hvSqLe (sq_nonneg t)
      nlinarith
  rw [lrCertificateGapBudget_eq_flow
      (by simpa [lrFlowCertificatePoint] using
        (show 1 - R ∈ Ioo (0 : ℝ) 1 by constructor <;> linarith [hR.1, hR.2]))
      hpointE hpointChi,
    lrCertificateR_flow,
    lrCertificateV_flow hR.2.ne heNe hv.1 ht.1,
    lrCertificateT_flow hR.2.ne heNe ht.1]

/-- Coordinate-chain derivative of the gap budget. -/
noncomputable def lrCertificateGapBudgetCurveDeriv
    (point : CertificatePoint) (s' k' chi' : ℝ) : ℝ :=
  let e' := s' * point.k + point.s * k'
  let x' := -(chi' * lrCertificateE point + point.chi * e')
  let y0' := chi' * lrCertificateE point + point.chi * e'
  let v' := lrCertificateVDeriv point e' x'
  lrCertificateGapDeriv point s' y0' e' v' -
    (lrCertificateHalfSlopeDeriv point s' v' *
        (lrCertificateM point / 2) +
      lrCertificateHalfSlope point *
        (lrCertificateMDeriv point v' / 2))

/-- Partial derivative of the gap budget in the unbounded `k` direction. -/
noncomputable def lrCertificateGapBudgetDerivK
    (point : CertificatePoint) : ℝ :=
  lrCertificateGapBudgetCurveDeriv point 0 1 0

noncomputable def lrCertificateGapBudgetDerivS
    (point : CertificatePoint) : ℝ :=
  lrCertificateGapBudgetCurveDeriv point 1 0 0

noncomputable def lrCertificateGapBudgetDerivChi
    (point : CertificatePoint) : ℝ :=
  lrCertificateGapBudgetCurveDeriv point 0 0 1

theorem hasDerivAt_lrCertificateGapBudget_k
    {point : CertificatePoint} (hpoint : LRHighShapeInterior point) :
    HasDerivAt (fun k ↦ lrCertificateGapBudget { point with k := k })
      (lrCertificateGapBudgetDerivK point) point.k := by
  let sfun : ℝ → ℝ := fun _q ↦ point.s
  let kfun : ℝ → ℝ := fun q ↦ q
  let chifun : ℝ → ℝ := fun _q ↦ point.chi
  let curve : ℝ → CertificatePoint := lrCertificateCurve sfun kfun chifun
  have hs : HasDerivAt sfun 0 point.k := hasDerivAt_const point.k point.s
  have hk : HasDerivAt kfun 1 point.k := hasDerivAt_id point.k
  have hchi : HasDerivAt chifun 0 point.k :=
    hasDerivAt_const point.k point.chi
  have he : HasDerivAt (fun q ↦ lrCertificateE (curve q)) point.s point.k := by
    simpa [curve, sfun, kfun, chifun] using
      (hasDerivAt_lrCertificateE_curve (chi := chifun) hs hk)
  have hx : HasDerivAt (fun q ↦ lrCertificateX (curve q))
      (-point.chi * point.s) point.k := by
    simpa [curve, sfun, kfun, chifun, lrCertificateCurve] using
      (hasDerivAt_lrCertificateX_curve hs hk hchi)
  have hvRaw := hasDerivAt_lrCertificateV_curve hs hk hchi
    hpoint.2.1 hpoint.2.2
  have hv : HasDerivAt (fun q ↦ lrCertificateV (curve q))
      (lrCertificateVDerivK point) point.k := by
    simpa [curve, sfun, kfun, chifun, lrCertificateCurve,
      lrCertificateVDerivK, lrCertificateEDerivK,
      lrCertificateXDerivK] using hvRaw
  have hy0 : HasDerivAt (fun q ↦ lrCertificateY0 (curve q))
      (point.chi * point.s) point.k := by
    have h := hchi.mul he
    simpa [curve, sfun, kfun, chifun, lrCertificateY0,
      lrCertificateCurve] using h
  have hxPos : 0 < lrCertificateX point := by
    change 0 < 1 - point.chi * lrCertificateE point
    have hprod : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point <
            1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hpoint.2.2.2 hpoint.2.1.1
        _ = lrCertificateE point := one_mul _
        _ < 1 := hpoint.2.1.2
    exact sub_pos.mpr hprod
  have hvPos : 0 < lrCertificateV point := by
    unfold lrCertificateV
    exact Real.sqrt_pos.2 (div_pos (sub_pos.mpr hpoint.2.1.2) hxPos)
  have hy0Mem : lrCertificateY0 point ∈ Ioo (0 : ℝ) 1 := by
    unfold lrCertificateY0
    constructor
    · exact mul_pos hpoint.2.2.1 hpoint.2.1.1
    · calc
        point.chi * lrCertificateE point <
            1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hpoint.2.2.2 hpoint.2.1.1
        _ = lrCertificateE point := one_mul _
        _ < 1 := hpoint.2.1.2
  have hSquareRaw := hasDerivAt_lrCertificateSquareTarget_along
    hs hy0 he hv hpoint.1 hy0Mem hpoint.2.1 hvPos
  have hSquare : HasDerivAt
      (fun q ↦ lrCertificateSquareTarget (curve q))
      (lrCertificateSquareTargetDeriv point 0 (point.chi * point.s)
        point.s (lrCertificateVDerivK point)) point.k := by
    simpa [curve, sfun, kfun, chifun, lrCertificateCurve,
      lrCertificateSquareTarget] using hSquareRaw
  have hPrefixRaw := hasDerivAt_lrCertificatePrefixAtM_along
    hs hv hpoint.1 hvPos
  have hPrefix : HasDerivAt
      (fun q ↦ lrCertificatePrefixAtM (curve q))
      (lrCertificatePrefixAtMDeriv point 0
        (lrCertificateVDerivK point)) point.k := by
    simpa [curve, sfun, kfun, chifun, lrCertificateCurve,
      lrCertificatePrefixAtM, lrCertificatePrefixAtMDeriv] using hPrefixRaw
  have hGapRaw := hSquare.sub hPrefix
  have hGap : HasDerivAt (fun q ↦ lrCertificateGap (curve q))
      (lrCertificateGapDeriv point 0 (point.chi * point.s)
        point.s (lrCertificateVDerivK point)) point.k := by
    simpa [lrCertificateGap, lrCertificateGapDeriv] using hGapRaw
  have hHalfRaw := hasDerivAt_lrCertificateHalfSlope_along
    hs hv hpoint.1 hvPos
  have hHalf : HasDerivAt
      (fun q ↦ lrCertificateHalfSlope (curve q))
      (lrCertificateHalfSlopeDeriv point 0
        (lrCertificateVDerivK point)) point.k := by
    simpa [curve, sfun, kfun, chifun, lrCertificateCurve,
      lrCertificateHalfSlope, lrCertificateHalfSlopeDeriv] using hHalfRaw
  have honePlusV := (hasDerivAt_const point.k 1).add hv
  have hMRaw := hv.div honePlusV (by
    change 1 + lrCertificateV point ≠ 0
    linarith)
  have hM : HasDerivAt (fun q ↦ lrCertificateM (curve q))
      (lrCertificateMDeriv point (lrCertificateVDerivK point)) point.k := by
    unfold lrCertificateM lrCertificateMDeriv
    convert hMRaw using 1 <;>
      simp only [curve, sfun, kfun, chifun, lrCertificateCurve,
        Pi.add_apply] <;>
      field_simp [(by linarith : 1 + lrCertificateV point ≠ 0)] <;> ring
  have hBudgetRaw := hGap.sub (hHalf.mul (hM.mul_const (1 / 2)))
  unfold lrCertificateGapBudget lrCertificateGapBudgetDerivK
    lrCertificateGapBudgetCurveDeriv
  convert hBudgetRaw using 1
  · funext q
    change lrCertificateGap { point with k := q } -
        lrCertificateHalfSlope { point with k := q } *
          (lrCertificateM { point with k := q } / 2) =
      lrCertificateGap { point with k := q } -
        lrCertificateHalfSlope { point with k := q } *
          (lrCertificateM { point with k := q } * (1 / 2))
    ring
  · simp [curve, sfun, kfun, chifun, lrCertificateCurve,
      lrCertificateVDerivK, lrCertificateEDerivK,
      lrCertificateXDerivK]
    ring

/-- Monotonicity closes the noncompact `k >= 4` direction once the boundary
budget and the `k` derivative have been certified.  This is the abstract
tail step; subsequent files need only discharge its two scalar hypotheses. -/
theorem lrCertificateGapBudget_nonneg_of_four_of_derivK_nonneg
    {point : CertificatePoint} (hk : 4 ≤ point.k)
    (hinterior : ∀ q ∈ Icc (4 : ℝ) point.k,
      LRHighShapeInterior { point with k := q })
    (hfour : 0 ≤ lrCertificateGapBudget { point with k := 4 })
    (hderiv : ∀ q ∈ Ioo (4 : ℝ) point.k,
      0 ≤ lrCertificateGapBudgetDerivK { point with k := q }) :
    0 ≤ lrCertificateGapBudget point := by
  let f : ℝ → ℝ := fun q ↦ lrCertificateGapBudget { point with k := q }
  have hmono : MonotoneOn f (Icc (4 : ℝ) point.k) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (4 : ℝ) point.k)
    · intro q hq
      exact (hasDerivAt_lrCertificateGapBudget_k (hinterior q hq)).continuousAt
        |>.continuousWithinAt
    · intro q hq
      rw [interior_Icc] at hq
      exact (hasDerivAt_lrCertificateGapBudget_k
        (hinterior q ⟨hq.1.le, hq.2.le⟩)).differentiableAt
        |>.differentiableWithinAt
    · intro q hq
      rw [interior_Icc] at hq
      rw [(hasDerivAt_lrCertificateGapBudget_k
        (hinterior q ⟨hq.1.le, hq.2.le⟩)).deriv]
      exact hderiv q hq
  have hle := hmono (show (4 : ℝ) ∈ Icc 4 point.k from ⟨le_rfl, hk⟩)
    (show point.k ∈ Icc (4 : ℝ) point.k from ⟨hk, le_rfl⟩) hk
  change 0 ≤ f point.k
  exact hfour.trans hle

namespace LRHighShapeTangentCertificate

/-- Interval-AD evaluation of the exact gap budget.  All nonlinear pieces
come from the checked tangent payload; this definition only forms the exact
product and difference in the budget identity. -/
def gapBudgetAD (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeTangentCertificate) : IntervalAD :=
  let all := certificate.evaluateAll terms box
  let mHalf := IntervalAD.mul (certificate.base.mAD box)
    (IntervalAD.const (1 / 2))
  IntervalAD.sub all.gap (IntervalAD.mul all.halfSlope mHalf)

theorem gapBudgetAD_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint}
    {certificate : LRHighShapeTangentCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true) :
    (certificate.gapBudgetAD terms box).Contains
      (lrCertificateGapBudget point)
      (lrCertificateGapBudgetDerivS point)
      (lrCertificateGapBudgetDerivK point)
      (lrCertificateGapBudgetDerivChi point) := by
  have hall := certificate.evaluateAll_sound terms hpoint hcheck
  have hmHalf := IntervalAD.contains_mul hall.midpoint
    (IntervalAD.contains_const (1 / 2))
  have hcost := IntervalAD.contains_mul hall.halfSlope hmHalf
  have hbudget := IntervalAD.contains_sub hall.gap hcost
  unfold gapBudgetAD lrCertificateGapBudget
    lrCertificateGapBudgetDerivS lrCertificateGapBudgetDerivK
    lrCertificateGapBudgetDerivChi lrCertificateGapBudgetCurveDeriv
  dsimp only
  convert hbudget using 1
  · ring
  all_goals
    simp only [lrCertificateEDerivS, lrCertificateEDerivK,
      lrCertificateEDerivChi, lrCertificateXDerivS,
      lrCertificateXDerivK, lrCertificateXDerivChi,
      lrCertificateY0DerivS, lrCertificateY0DerivK,
      lrCertificateY0DerivChi, lrCertificateVDerivS,
      lrCertificateVDerivK, lrCertificateVDerivChi]
    ring

/-- A kernel-checked box assertion that the gap budget is nonnegative. -/
def gapBudgetNonnegative (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeTangentCertificate) : Bool :=
  decide ((0 : ℚ) ≤ (certificate.gapBudgetAD terms box).value.lower)

/-- A kernel-checked box assertion that the `k` derivative of the gap budget
is nonnegative. -/
def gapBudgetDerivKNonnegative (terms : ℕ) (box : CertificateBox)
    (certificate : LRHighShapeTangentCertificate) : Bool :=
  decide ((0 : ℚ) ≤ (certificate.gapBudgetAD terms box).derivK.lower)

theorem gapBudgetNonnegative_sound (terms : ℕ) {box : CertificateBox}
    {point : CertificatePoint}
    {certificate : LRHighShapeTangentCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true)
    (hnonneg : certificate.gapBudgetNonnegative terms box = true) :
    0 ≤ lrCertificateGapBudget point := by
  have hsound := certificate.gapBudgetAD_sound terms hpoint hcheck
  have hlower : (0 : ℝ) ≤
      (certificate.gapBudgetAD terms box).value.lower := by
    exact_mod_cast (show (0 : ℚ) ≤
      (certificate.gapBudgetAD terms box).value.lower by
        simpa [gapBudgetNonnegative] using hnonneg)
  exact hlower.trans hsound.1.1

theorem gapBudgetDerivKNonnegative_sound (terms : ℕ)
    {box : CertificateBox} {point : CertificatePoint}
    {certificate : LRHighShapeTangentCertificate}
    (hpoint : box.Contains point) (hcheck : certificate.check box = true)
    (hnonneg : certificate.gapBudgetDerivKNonnegative terms box = true) :
    0 ≤ lrCertificateGapBudgetDerivK point := by
  have hsound := certificate.gapBudgetAD_sound terms hpoint hcheck
  have hlower : (0 : ℝ) ≤
      (certificate.gapBudgetAD terms box).derivK.lower := by
    exact_mod_cast (show (0 : ℚ) ≤
      (certificate.gapBudgetAD terms box).derivK.lower by
        simpa [gapBudgetDerivKNonnegative] using hnonneg)
  exact hlower.trans hsound.2.2.1.1

end LRHighShapeTangentCertificate

end CourtadeKumar
