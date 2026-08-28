import InformationTheory.CourtadeKumar.LRDeterminantFlowCoordinates
import InformationTheory.CourtadeKumar.LRLowShapeUTail

/-!
# Positive factors in the determinant chart

This file proves the regular-interior positivity assertions used by the
sign chain (D2)--(D7), directly for the cancellation-coordinate point.
-/

open Set

namespace CourtadeKumar

theorem lrCertificateT_mem_Ioo {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrCertificateT point ∈ Ioo (0 : ℝ) 1 := by
  have he := hinterior.2.1
  have hchi := hinterior.2.2
  have hprodPos : 0 < point.chi * lrCertificateE point :=
    mul_pos hchi.1 he.1
  have hprodLt : point.chi * lrCertificateE point < 1 := by
    calc
      point.chi * lrCertificateE point < 1 * lrCertificateE point :=
        mul_lt_mul_of_pos_right hchi.2 he.1
      _ < 1 := by simpa using he.2
  have hx : lrCertificateX point ∈ Ioo (0 : ℝ) 1 := by
    unfold lrCertificateX
    constructor <;> linarith
  have htPos : 0 < lrCertificateT point := by
    unfold lrCertificateT
    exact Real.sqrt_pos.2 hx.1
  have htSq : lrCertificateT point ^ 2 = lrCertificateX point := by
    exact Real.sq_sqrt hx.1.le
  exact ⟨htPos, by nlinarith [htSq, hx.2]⟩

theorem lrCertificateV_mem_Ioo {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrCertificateV point ∈ Ioo (0 : ℝ) 1 := by
  have he := hinterior.2.1
  have hchi := hinterior.2.2
  have hxPos : 0 < lrCertificateX point := by
    unfold lrCertificateX
    have hprodLt : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point < 1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hchi.2 he.1
        _ < 1 := by simpa using he.2
    linarith
  have hnumLt : 1 - lrCertificateE point < lrCertificateX point := by
    unfold lrCertificateX
    have hscaled := mul_lt_mul_of_pos_right hchi.2 he.1
    nlinarith
  have hrad : (1 - lrCertificateE point) / lrCertificateX point ∈
      Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (sub_pos.mpr he.2) hxPos
    · rw [div_lt_one hxPos]
      exact hnumLt
  have hvPos : 0 < lrCertificateV point := by
    unfold lrCertificateV
    exact Real.sqrt_pos.2 hrad.1
  have hvSq : lrCertificateV point ^ 2 =
      (1 - lrCertificateE point) / lrCertificateX point := by
    exact Real.sq_sqrt hrad.1.le
  exact ⟨hvPos, by nlinarith [hvSq, hrad.2]⟩

theorem lrGShape_pos
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < lrGShape t v := by
  have hbound := lrGShape_ge_tail_envelope hv ht
  have htop : 0 < Real.log 2 - topPhi t := by
    simpa [topJ] using topJ_pos
      (show t ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [ht.1], ht.2⟩)
  have hbeta : 0 ≤ lrFlowBeta v := by
    unfold lrFlowBeta
    exact (Real.log_pos (by linarith [hv.1])).le
  have hvt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hL : 0 ≤ lrL (v * t) :=
    lrL_nonneg (mul_nonneg hv.1.le ht.1.le) hvt
  have hratio : 0 ≤ (1 - v) / v :=
    div_nonneg (sub_nonneg.mpr hv.2.le) hv.1.le
  have hlower : 0 <
      2 * (Real.log 2 - topPhi t) +
        (1 - v) / v * (lrFlowBeta v + lrL (v * t)) :=
    add_pos_of_pos_of_nonneg (mul_pos (by norm_num) htop)
      (mul_nonneg hratio (add_nonneg hbeta hL))
  exact hlower.trans_le hbound

theorem lrCertificateBFlow_pos {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 < lrCertificateBFlow point := by
  have he := hinterior.2.1
  have hv := lrCertificateV_mem_Ioo hinterior
  have hb := lrCertificateB_mem_Ioo hinterior.1 he
  have hlogV : 0 < Real.log (1 + lrCertificateV point) :=
    Real.log_pos (by linarith [hv.1])
  have hlogB : Real.log (lrCertificateB point.s (lrCertificateE point)) ≤ 0 :=
    Real.log_nonpos hb.1.le hb.2.le
  unfold lrCertificateBFlow lrCertificateBFlowValue
  nlinarith

theorem lrCertificateGShape_pos {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 < lrCertificateGShape point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have ht := lrCertificateT_mem_Ioo hinterior
  rw [lrCertificateGShape_eq_lrGShape hinterior.2.1
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩]
  exact lrGShape_pos hv ht

theorem lrCertificateW_pos {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 < lrCertificateW point := by
  have hR : lrCertificateR point ∈ Ioo (0 : ℝ) 1 := by
    unfold lrCertificateR
    constructor <;> linarith [hinterior.1.1, hinterior.1.2]
  rw [lrCertificateW_eq_lrWKernel hinterior.1]
  exact lrWKernel_one_pos hR

/-- The compensation coefficient `delta = (1-vx)/(1+v)` is nonnegative
throughout the regular physical chart. -/
theorem lrDeterminantDelta_nonnegative {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 ≤ lrDeterminantDelta point := by
  have hv := lrCertificateV_mem_Ioo hinterior
  have hx : lrCertificateX point ∈ Ioo (0 : ℝ) 1 := by
    have hprodPos : 0 < point.chi * lrCertificateE point :=
      mul_pos hinterior.2.2.1 hinterior.2.1.1
    have hprodLt : point.chi * lrCertificateE point < 1 := by
      calc
        point.chi * lrCertificateE point < 1 * lrCertificateE point :=
          mul_lt_mul_of_pos_right hinterior.2.2.2 hinterior.2.1.1
        _ < 1 := by simpa using hinterior.2.1.2
    unfold lrCertificateX
    constructor <;> linarith
  have hproduct : lrCertificateV point * lrCertificateX point ≤ 1 :=
    calc
      lrCertificateV point * lrCertificateX point ≤
          1 * lrCertificateX point :=
        mul_le_mul_of_nonneg_right hv.2.le hx.1.le
      _ ≤ 1 := by simpa using hx.2.le
  unfold lrDeterminantDelta
  exact div_nonneg (sub_nonneg.mpr hproduct) (by linarith [hv.1])

theorem lrCertificateHalfSlope_pos {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 < lrCertificateHalfSlope point := by
  have hR : lrCertificateR point ∈ Ioo (0 : ℝ) 1 := by
    unfold lrCertificateR
    constructor <;> linarith [hinterior.1.1, hinterior.1.2]
  have hv := lrCertificateV_mem_Ioo hinterior
  rw [lrCertificateHalfSlope_eq_flow hinterior.1 hinterior.2.1
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩]
  exact lrFlowHalfSlope_pos hR hv

theorem lrDeterminantHd_pos {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 < lrDeterminantHd point := by
  unfold lrDeterminantHd
  exact div_pos (lrCertificateHalfSlope_pos hinterior) hinterior.1.1

theorem lrCertificateGap_nonnegative {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 ≤ lrCertificateGap point := by
  have hR : lrCertificateR point ∈ Ioo (0 : ℝ) 1 := by
    unfold lrCertificateR
    constructor <;> linarith [hinterior.1.1, hinterior.1.2]
  have hv := lrCertificateV_mem_Ioo hinterior
  have ht := lrCertificateT_mem_Ioo hinterior
  rw [lrCertificateGap_eq_flow hinterior.1 hinterior.2.1
    ⟨hinterior.2.2.1.le, hinterior.2.2.2.le⟩]
  exact lrFlowGap_nonneg hR hv ht

/-- The coefficient conclusion in (D3), in unnormalized certificate
coordinates.  This is the elementary final step of the coefficient
Wronskian lemma. -/
theorem lrDeterminantCoefficient_nonnegative_of_wronskian
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hwronskian :
      12 * Real.log 2 * lrDeterminantC0 point * lrDeterminantT point ≤
        lrDeterminantPsi point) :
    0 ≤ lrDeterminantPsi point / lrCertificateGShape point -
      lrDeterminantC0 point *
        (lrDeterminantT point / lrCertificateGShape point) := by
  have hs : 0 < point.s := hinterior.1.1
  have hR : 0 < lrCertificateR point := by
    unfold lrCertificateR
    linarith [hinterior.1.2]
  have hG := lrCertificateGShape_pos hinterior
  have hW := (lrCertificateW_pos hinterior).le
  have hgap := lrCertificateGap_nonnegative hinterior
  have hHd := lrDeterminantHd_pos hinterior
  have hc0 := lrDeterminantC0_nonnegative hs hHd hR.le hW
  have hT := lrDeterminantT_nonnegative hR hgap
  have hconstant : (1 : ℝ) ≤ 12 * Real.log 2 := by
    have hlog := Real.log_two_gt_d9
    norm_num at hlog ⊢
    linarith
  have hscale : lrDeterminantC0 point * lrDeterminantT point ≤
      (12 * Real.log 2) *
        (lrDeterminantC0 point * lrDeterminantT point) :=
    by simpa using
      mul_le_mul_of_nonneg_right hconstant (mul_nonneg hc0 hT)
  have hbase : lrDeterminantC0 point * lrDeterminantT point ≤
      lrDeterminantPsi point := by
    calc
      lrDeterminantC0 point * lrDeterminantT point ≤
          (12 * Real.log 2) *
            (lrDeterminantC0 point * lrDeterminantT point) := hscale
      _ = 12 * Real.log 2 * lrDeterminantC0 point *
          lrDeterminantT point := by ring
      _ ≤ lrDeterminantPsi point := hwronskian
  have hdiv := div_le_div_of_nonneg_right hbase hG.le
  rw [sub_nonneg]
  calc
    lrDeterminantC0 point *
        (lrDeterminantT point / lrCertificateGShape point) =
      (lrDeterminantC0 point * lrDeterminantT point) /
        lrCertificateGShape point := by ring
    _ ≤ lrDeterminantPsi point / lrCertificateGShape point := hdiv

/-- All routine regular-interior factors required by the determinant sign
chain. -/
theorem lrCertificateTTarget_nonnegative_of_clearedSingular_core
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hcoeff : 0 ≤
      lrDeterminantPsi point / lrCertificateGShape point -
        lrDeterminantC0 point *
          (lrDeterminantT point / lrCertificateGShape point))
    (hcleared : 0 ≤ lrDeterminantClearedSingular
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrCertificateGShape point) (lrDeterminantPsi point)
      (lrDeterminantDelta point) (lrCertificateW point)
      (lrDeterminantC0 point) (lrCertificateX point)
      (lrDeterminantT point)) :
    0 ≤ lrCertificateTTarget point := by
  exact lrCertificateTTarget_nonnegative_of_clearedSingular
    hinterior hrelevant
    (lrCertificateBFlow_pos hinterior)
    (lrCertificateGShape_pos hinterior)
    (lrDeterminantHd_pos hinterior)
    (lrCertificateW_pos hinterior).le
    (lrCertificateGap_nonnegative hinterior)
    hcoeff hcleared

/-- First-bracket counterpart of the routine-factor-free interface. -/
theorem lrCertificateTTarget_nonnegative_of_firstBracket_core
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hcoeff : 0 ≤
      lrDeterminantPsi point / lrCertificateGShape point -
        lrDeterminantC0 point *
          (lrDeterminantT point / lrCertificateGShape point))
    (hfirst : 0 ≤ lrDeterminantFirstBracket
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrCertificateGShape point) (lrDeterminantPsi point)
      (lrDeterminantDelta point) (lrCertificateW point)) :
    0 ≤ lrCertificateTTarget point := by
  exact lrCertificateTTarget_nonnegative_of_firstBracket
    hinterior hrelevant
    (lrCertificateBFlow_pos hinterior)
    (lrCertificateGShape_pos hinterior)
    (lrDeterminantHd_pos hinterior)
    (lrCertificateW_pos hinterior).le
    (lrCertificateGap_nonnegative hinterior)
    hcoeff hfirst

/-- Exact first-bracket ledger interface after discharging the coefficient
sign from the manuscript Wronskian bound. -/
theorem lrCertificateTTarget_nonnegative_of_firstBracket_wronskian
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hwronskian :
      12 * Real.log 2 * lrDeterminantC0 point * lrDeterminantT point ≤
        lrDeterminantPsi point)
    (hfirst : 0 ≤ lrDeterminantFirstBracket
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrCertificateGShape point) (lrDeterminantPsi point)
      (lrDeterminantDelta point) (lrCertificateW point)) :
    0 ≤ lrCertificateTTarget point := by
  exact lrCertificateTTarget_nonnegative_of_firstBracket_core
    hinterior hrelevant
    (lrDeterminantCoefficient_nonnegative_of_wronskian
      hinterior hwronskian)
    hfirst

end CourtadeKumar
