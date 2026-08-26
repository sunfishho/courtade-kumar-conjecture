import InformationTheory.CourtadeKumar.LRAbelLiftAssembly
import InformationTheory.CourtadeKumar.LRBVComparison

/-! Closure of the audited LR sign charts using the analytic inequalities. -/

open Set

namespace CourtadeKumar

/-- On the regular physical interior, the corrected Abel lift closes the
`J = 0` chart: there the numerator is `B * Z`, with both factors nonnegative. -/
theorem lrFlowNumeratorP_nonneg_of_J_eq_zero_physical
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hJ : lrFlowJ R v t = 0) :
    0 ≤ lrFlowNumeratorP R p v t := by
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hvt : v * t < 1 := by
    nlinarith [mul_lt_mul_of_pos_right hv.2 ht.1,
      mul_lt_mul_of_pos_left ht.2 hv.1]
  have hshape : Real.sqrt R * v * t < 1 := by
    rw [mul_assoc]
    calc
      Real.sqrt R * (v * t) < 1 * (v * t) :=
        mul_lt_mul_of_pos_right hsqrtLt (mul_pos hv.1 ht.1)
      _ < 1 := by simpa using hvt
  exact lrFlowNumeratorP_nonneg_of_J_eq_zero
    (by linarith [hv.1])
    (lrFlowB_pos hv.1 ht.1.le hshape).le hJ
    (lrFlow_noise_lift_nonneg hR hv ht)

/-- Algebraic closure of the negative-`J` chart once the two elementary
tangent estimates `g ≤ C` and `4 D_R ≤ q₀` are supplied.  All analytic
inputs in the final comparison are the proved `B` comparison and Abel lift. -/
theorem lrFlowNumeratorP_nonneg_of_J_neg_physical
    {R p v t g q₀ : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hJ : lrFlowJ R v t < 0)
    (hg : 0 ≤ g) (hCge : g ≤ lrFlowC R v t)
    (hq₀ : 0 < q₀) (hq₀Delta : 4 * lrBDelta R ≤ q₀)
    (hpT : lrFlowM v - g / q₀ ≤ p) :
    0 ≤ lrFlowNumeratorP R p v t := by
  have hH : 0 < lrFlowH R v t := by
    rw [lrFlowH_eq_negJ]
    linarith
  have hW : 0 ≤ lrWKernel R 1 := lrWKernel_one_nonneg hR
  have hC : 0 ≤ lrFlowC R v t := hg.trans hCge
  have hgammaNonneg : 0 ≤ lrBGamma R := (lrBGamma_pos hR).le
  have honeGamma : 0 ≤ 1 - lrBGamma R := sub_nonneg.mpr (lrBGamma_le_one hR)
  have hratio : 4 * lrWKernel R 1 / q₀ ≤ 1 - lrBGamma R := by
    rw [div_le_iff₀ hq₀]
    rw [lrWKernel_one_eq_delta_mul_one_sub_gamma hR]
    have hscaled := mul_le_mul_of_nonneg_right hq₀Delta honeGamma
    nlinarith
  have hadjust :
      lrBGamma R * lrFlowC R v t ≤
        lrFlowC R v t - 4 * lrWKernel R 1 * g / q₀ := by
    have hgScaled := mul_le_mul hratio hCge hg honeGamma
    have hrewrite :
        (4 * lrWKernel R 1 / q₀) * g =
          4 * lrWKernel R 1 * g / q₀ := by
      field_simp [hq₀.ne']
    rw [hrewrite] at hgScaled
    nlinarith
  have hBComp := lrBComparisonReserve_nonneg hR hv ht
  unfold lrBComparisonReserve at hBComp
  have hAbel := lrFlow_noise_lift_nonneg hR hv ht
  have hBpos : 0 < lrFlowB R v t := by
    have hsqrt := lrB_sqrt_mem_Ioo hR
    have hshape : Real.sqrt R * v * t < 1 := by
      have hvt : v * t < 1 := by
        nlinarith [mul_lt_mul_of_pos_right hv.2 ht.1,
          mul_lt_mul_of_pos_left ht.2 hv.1]
      calc
        Real.sqrt R * v * t = Real.sqrt R * (v * t) := by ring
        _ < 1 * (v * t) := mul_lt_mul_of_pos_right hsqrt.2 (mul_pos hv.1 ht.1)
        _ < 1 := by simpa using hvt
    exact lrFlowB_pos hv.1 ht.1.le hshape
  have hmid := lrFlowNumeratorP_midpoint
    (R := R) (v := v) (t := t) (by linarith [hv.1])
  have htoT := lrFlowNumeratorP_sub R (lrFlowM v)
    (lrFlowM v - g / q₀) v t
  have hNT : 0 ≤ lrFlowNumeratorP R (lrFlowM v - g / q₀) v t := by
    rw [hmid] at htoT
    have hcompScaled := mul_le_mul_of_nonneg_left hBComp hH.le
    have hAbelScaled := mul_nonneg hBpos.le hAbel
    have hcore : 0 ≤
        lrFlowB R v t * lrFlowZ R v t +
          lrFlowH R v t *
            (lrFlowC R v t - 4 * lrWKernel R 1 * g / q₀) := by
      nlinarith [mul_le_mul_of_nonneg_left hadjust hH.le]
    have hdelta :
        lrFlowNumeratorP R (lrFlowM v - g / q₀) v t =
          lrFlowB R v t * lrFlowZ R v t +
            lrFlowH R v t *
              (lrFlowC R v t - 4 * lrWKernel R 1 * g / q₀) := by
      field_simp [hq₀.ne'] at htoT ⊢
      nlinarith [htoT]
    rw [hdelta]
    exact hcore
  have hmove := lrFlowNumeratorP_sub R
    (lrFlowM v - g / q₀) p v t
  have hmoveNonneg : 0 ≤
      4 * lrWKernel R 1 * lrFlowH R v t *
        (p - (lrFlowM v - g / q₀)) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hW) hH.le)
      (sub_nonneg.mpr hpT)
  nlinarith

end CourtadeKumar
