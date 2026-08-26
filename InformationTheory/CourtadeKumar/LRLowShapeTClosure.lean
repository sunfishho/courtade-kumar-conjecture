import InformationTheory.CourtadeKumar.LRLowShapeVSeries

/-!
# Closure of the low-shape tangent chart from its `V` coefficients

Coefficientwise nonnegativity is transferred to the analytic reserve and
then through the existing positive-chart assembly.
-/

open Set

namespace CourtadeKumar

theorem lrLowVReserve_nonneg_of_coeff_nonneg
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hcoeff : ∀ n : ℕ, 0 ≤ lrLowVConvolutionCoeff v t n) :
    0 ≤ lrLowVReserve R v t := by
  have hsum := lrLowVConvolutionCoeff_hasSum hR hv ht
  have hseries : 0 ≤ lrLowVReserve R v t / (1 - R) ^ 2 :=
    hsum.nonneg (fun n ↦ mul_nonneg (hcoeff n) (pow_nonneg hR.1.le n))
  have hden : 0 < (1 - R) ^ 2 := sq_pos_of_pos (sub_pos.mpr hR.2)
  have hmul := mul_nonneg hseries hden.le
  rw [div_mul_cancel₀ _ hden.ne'] at hmul
  exact hmul

theorem lrFlowTReserve_nonneg_of_lrLowVReserve_nonneg
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hJ : 0 ≤ lrFlowJ R v t) (hV : 0 ≤ lrLowVReserve R v t) :
    0 ≤ lrFlowTReserve R v t := by
  have hW : 0 ≤ lrWKernel R 1 := (lrWKernel_one_pos hR).le
  have hgap : 0 ≤ lrFlowGap R v t := lrFlowGap_nonneg hR hv ht
  have hslope : 0 ≤ lrFlowHalfSlope R v :=
    (lrFlowHalfSlope_pos hR hv).le
  unfold lrFlowTReserve
  rw [lrFlowNumeratorP_midpoint_eq_lrLowVReserve (by linarith [hv.1])]
  exact add_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hW) hJ) hgap)
    (mul_nonneg hslope hV)

theorem lrFlowTReserve_nonneg_lowShape_of_coeff_nonneg
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hJ : 0 ≤ lrFlowJ R v t)
    (hcoeff : ∀ n : ℕ, 0 ≤ lrLowVConvolutionCoeff v t n) :
    0 ≤ lrFlowTReserve R v t := by
  exact lrFlowTReserve_nonneg_of_lrLowVReserve_nonneg hR hv ht hJ
    (lrLowVReserve_nonneg_of_coeff_nonneg hR hv ht hcoeff)

theorem lrFlowNumeratorP_nonneg_target_lowShape_of_coeff_nonneg
    {R p v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioc (0 : ℝ) (1 / 2 : ℝ))
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (htSq : t ^ 2 ≤ (17 / 20 : ℝ))
    (htarget : lrPrefixEll R p = lrSquareTarget R v t)
    (hcoeff : ∀ n : ℕ, 0 ≤ lrLowVConvolutionCoeff v t n) :
    0 ≤ lrFlowNumeratorP R p v t := by
  rcases lt_trichotomy (lrFlowJ R v t) 0 with hJneg | hJzero | hJpos
  · exact lrFlowNumeratorP_nonneg_of_J_neg_target hR hp hv ht htarget hJneg
  · exact lrFlowNumeratorP_nonneg_of_J_eq_zero_physical hR hv ht hJzero
  · have hU := lrFlowUReserve_nonneg_lowShape hR hv ht htSq
    have hT := lrFlowTReserve_nonneg_lowShape_of_coeff_nonneg
      hR hv ht hJpos.le hcoeff
    exact lrFlowNumeratorP_nonneg_of_J_pos_target_of_U_T
      hR hp hv ht htarget hJpos hU hT

end CourtadeKumar
