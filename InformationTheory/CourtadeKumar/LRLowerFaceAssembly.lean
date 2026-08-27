import InformationTheory.CourtadeKumar.LRLowerFaceR0Payment
import InformationTheory.CourtadeKumar.LRHighShapeKernelAssembly
import InformationTheory.CourtadeKumar.LRPositiveChartAssembly

/-!
# Lower-face assembly

This transports the analytic `(s,k,chi)` lower-face estimate to the exact LR
flow and proves (M26), hence the exact half-midpoint inequality on
`s ≤ 1/128`, `k ≤ 1/4`.
-/

open Set

namespace CourtadeKumar

/-- Strict version of the positive-chart `U` assembly when `Y₀>0`. -/
theorem lrFlowUReserve_pos_of_Y₀_pos
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hJ : 0 < lrFlowJ R v t)
    (hY : 0 < lrFlowY₀ R v t) :
    0 < lrFlowUReserve R v t := by
  have hsqrt := lrB_sqrt_mem_Ioo hR
  have hvt : v * t < 1 := by
    calc
      v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
      _ < 1 := by simpa using ht.2
  have hshape : Real.sqrt R * v * t < 1 := by
    rw [mul_assoc]
    calc
      Real.sqrt R * (v * t) < 1 * (v * t) :=
        mul_lt_mul_of_pos_right hsqrt.2 (mul_pos hv.1 ht.1)
      _ < 1 := by simpa using hvt
  have hB : 0 < lrFlowB R v t := lrFlowB_pos hv.1 ht.1.le hshape
  have hCcal : 0 ≤ lrFlowCcal R v t := by
    unfold lrFlowCcal
    have hden : 0 < 1 - R * v ^ 2 * t ^ 2 := by
      have hRvt : R * (v ^ 2 * t ^ 2) < 1 := by
        have hvtSq : v ^ 2 * t ^ 2 < 1 := by
          have hsq : (v * t) ^ 2 < 1 := by
            nlinarith [mul_pos hv.1 ht.1]
          nlinarith [hsq]
        have hvtSqPos : 0 < v ^ 2 * t ^ 2 :=
          mul_pos (sq_pos_of_pos hv.1) (sq_pos_of_pos ht.1)
        calc
          R * (v ^ 2 * t ^ 2) < 1 * (v ^ 2 * t ^ 2) :=
            mul_lt_mul_of_pos_right hR.2 hvtSqPos
          _ < 1 := by simpa using hvtSq
      linarith
    exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr hR.2.le)
        (mul_nonneg (sq_nonneg v) (sq_nonneg t)))
      (mul_nonneg (by norm_num) hden.le)
  have hAbel := lrFlow_noise_lift_nonneg hR hv ht
  have hq := lrFlowQWeight_nonneg
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
    (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩)
  have hZ : 0 ≤ lrFlowZ R v t := by
    have hH : lrFlowH R v t = -lrFlowJ R v t := lrFlowH_eq_negJ R v t
    rw [hH] at hAbel
    nlinarith [mul_nonneg hq hJ.le]
  by_cases hX : 0 ≤ lrFlowX₀ R v t
  · unfold lrFlowUReserve
    exact add_pos_of_pos_of_nonneg (mul_pos hB hY) (mul_nonneg hCcal hX)
  · have hXneg : lrFlowX₀ R v t < 0 := lt_of_not_ge hX
    have hratio : lrFlowD R v t / lrFlowB R v t < t ^ 2 := by
      rw [div_lt_iff₀ hB]
      unfold lrFlowJ at hJ
      nlinarith
    have hratioX : t ^ 2 * lrFlowX₀ R v t <
        (lrFlowD R v t / lrFlowB R v t) * lrFlowX₀ R v t :=
      mul_lt_mul_of_neg_right hratio hXneg
    have hYX : 0 < lrFlowY₀ R v t +
        (lrFlowD R v t / lrFlowB R v t) * lrFlowX₀ R v t := by
      have hidentity := lrFlowY₀_add_t_sq_mul_X₀
        (R := R) (v := v) (t := t) (by linarith [hv.1])
      linarith
    have hscaled := mul_pos hB hYX
    unfold lrFlowUReserve
    have hDterm : lrFlowB R v t *
        ((lrFlowD R v t / lrFlowB R v t) * lrFlowX₀ R v t) =
        lrFlowD R v t * lrFlowX₀ R v t := by
      field_simp [hB.ne']
    rw [mul_add, hDterm] at hscaled
    have hCge := lrFlowCcal_le_lrFlowD hR hv ht
    have hCX : lrFlowD R v t * lrFlowX₀ R v t ≤
        lrFlowCcal R v t * lrFlowX₀ R v t :=
      mul_le_mul_of_nonpos_right hCge hXneg.le
    nlinarith

/-- The coordinate `Y` is exactly the flow reserve `Y₀`. -/
theorem lrLowerFaceY_flow
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    let point := lrFlowCertificatePoint R v t
    lrLowerFaceY point.s point.k point.chi v = lrFlowY₀ R v t := by
  let point := lrFlowCertificatePoint R v t
  have hRNe : R ≠ 1 := hR.2.ne
  have hvtPos : 0 < v * t := mul_pos hv.1 ht.1
  have hvtLt : v * t < 1 := by
    calc
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
  have hvPoint : lrCertificateV point = v :=
    lrCertificateV_flow hRNe hePos.ne' hv.1 ht.1
  have htPoint : lrCertificateT point = t :=
    lrCertificateT_flow hRNe hePos.ne' ht.1
  have hpw := lrCertificatePW_eq_lrFlowPW hs he hchi
  have hw := lrCertificateW_eq_lrWKernel hs
  have hePoint := lrCertificateE_flow (R := R) (v := v) (t := t) hRNe
  have hxPoint := lrCertificateX_flow (R := R) (v := v) (t := t)
    hRNe hePos.ne'
  have hpwValue :
      lrCertificatePWValue point.s (point.chi * (point.s * point.k))
          (point.s * point.k) v = lrFlowPW R v t := by
    have hpw' := hpw
    unfold lrCertificatePW lrCertificateY0 lrCertificateE at hpw'
    rw [lrCertificateR_flow, hvPoint, htPoint] at hpw'
    exact hpw'
  have hwValue : lrCertificateOmega point.s 0 = lrWKernel R 1 := by
    have hw' := hw
    rw [lrCertificateR_flow] at hw'
    simpa [lrCertificateW] using hw'
  have hxValue : 1 - point.chi * (point.s * point.k) = t ^ 2 := by
    simpa [lrCertificateX, lrCertificateE] using hxPoint
  change lrLowerFaceY point.s point.k point.chi v = lrFlowY₀ R v t
  unfold lrLowerFaceY lrFlowY₀
  rw [hpwValue, hwValue, hxValue]
  unfold lrFlowM
  ring

/-- Manuscript (M26): the analytic lower face closes the exact
half-midpoint target. -/
theorem lrLowerFace_halfMidpoint_nonneg
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hJ : 0 < lrFlowJ R v t)
    (hsSmall : 1 - R ≤ 1 / 128)
    (hkSmall : (1 - v ^ 2 * t ^ 2) / (1 - R) ≤ 1 / 4) :
    0 ≤ lrFlowNumeratorP R (lrFlowM v / 2) v t := by
  let point := lrFlowCertificatePoint R v t
  have hRNe : R ≠ 1 := hR.2.ne
  have hsPos : 0 < 1 - R := sub_pos.mpr hR.2
  have hvtPos : 0 < v * t := mul_pos hv.1 ht.1
  have hvtLt : v * t < 1 := by
    calc
      v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
      _ < 1 := by simpa using ht.2
  have hePos : 0 < 1 - v ^ 2 * t ^ 2 := by
    nlinarith [sq_pos_of_pos hvtPos]
  have hs : point.s ∈ Ioc (0 : ℝ) (1 / 128) := by
    change 1 - R ∈ Ioc (0 : ℝ) (1 / 128)
    exact ⟨hsPos, hsSmall⟩
  have hk : point.k ∈ Ioc (0 : ℝ) (1 / 4) := by
    change (1 - v ^ 2 * t ^ 2) / (1 - R) ∈ Ioc (0 : ℝ) (1 / 4)
    exact ⟨div_pos hePos hsPos, hkSmall⟩
  have htSqLe : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hvSqLe : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
  have hchi : point.chi ∈ Icc (0 : ℝ) 1 := by
    change (1 - t ^ 2) / (1 - v ^ 2 * t ^ 2) ∈ Icc (0 : ℝ) 1
    constructor
    · exact div_nonneg (sub_nonneg.mpr htSqLe) hePos.le
    · rw [div_le_one hePos]
      nlinarith [mul_nonneg (sub_nonneg.mpr hvSqLe) (sq_nonneg t)]
  have heUpper : 1 - v ^ 2 * t ^ 2 ≤ 1 / 512 := by
    have hprod := mul_le_mul hs.2 hk.2 hk.1.le (by norm_num)
    change point.s * point.k ≤ (1 / 128 : ℝ) * (1 / 4) at hprod
    rw [show 1 - v ^ 2 * t ^ 2 = lrCertificateE point by
      symm; exact lrCertificateE_flow hRNe]
    change point.s * point.k ≤ 1 / 512
    exact hprod.trans_eq (by norm_num)
  have hvSqLower : (511 / 512 : ℝ) ≤ v ^ 2 := by
    have htSqUpper : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have hvScale : v ^ 2 * t ^ 2 ≤ v ^ 2 :=
      mul_le_of_le_one_right (sq_nonneg v) htSqUpper
    nlinarith
  have hYCoord := lrLowerFaceY_pos hs hk hchi
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩) hvSqLower
  have hY : 0 < lrFlowY₀ R v t := by
    rw [← lrLowerFaceY_flow hR hv ht]
    exact hYCoord
  have hU := lrFlowUReserve_pos_of_Y₀_pos hR hv ht hJ hY
  exact lrFlowNumeratorP_halfMidpoint_nonneg_of_U hR hv ht hJ hU.le

end CourtadeKumar
