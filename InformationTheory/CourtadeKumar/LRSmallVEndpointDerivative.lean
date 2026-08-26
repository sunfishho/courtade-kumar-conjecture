import InformationTheory.CourtadeKumar.LRSmallVEndpointA
import InformationTheory.CourtadeKumar.LRLowShapeVStarBridge

/-!
# Angular monotonicity of the small-odds endpoint envelope

This formalizes equation (94): the endpoint envelope decreases in `t`
because `A < 1/2` throughout the `v ≤ 1/3` chart.
-/

open Set

namespace CourtadeKumar

theorem hasDerivAt_lrLowVStarEnvelopeActual_t
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (lrLowVStarEnvelopeActual v)
      (-Real.artanh t - Real.artanh (v * t) +
        2 * v * t / (1 + v) * (2 * lrFlowA v t - 1)) t := by
  have hvt : v * t ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_pos hv.1 ht.1]
    · have hprod : v * t < 1 := calc
        v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
        _ < 1 := by simpa using ht.2
      exact hprod
  have htFull : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  have harg : HasDerivAt (fun y : ℝ ↦ v * y) v t := by
    simpa using (hasDerivAt_id t).const_mul v
  have hshape : HasDerivAt (fun y : ℝ ↦ lrGShape y v)
      (-Real.artanh t - Real.artanh (v * t)) t := by
    have htPhi := hasDerivAt_topPhi htFull
    have hvtPhi := (hasDerivAt_topPhi hvt).comp t harg
    have h := ((hasDerivAt_const t (lrG v)).sub htPhi).sub
      (hvtPhi.div_const v)
    unfold lrGShape
    convert h using 1
    field_simp [hv.1.ne']
    ring
  have hdenL : 1 - (v * t) ^ 2 ≠ 0 := by
    nlinarith [hvt.1, hvt.2]
  have hA : HasDerivAt (fun y : ℝ ↦ lrFlowA v y)
      (v ^ 2 * t / (1 - v ^ 2 * t ^ 2)) t := by
    have hL := (hasDerivAt_lrL hdenL).comp t harg
    unfold lrFlowA
    convert (hasDerivAt_const t (lrFlowBeta v)).add hL using 1
    simp only [zero_add]
    field_simp [hdenL]
  have hfactor : HasDerivAt
      (fun y : ℝ ↦ 2 * (1 - v ^ 2 * y ^ 2)) (-4 * v ^ 2 * t) t := by
    convert ((hasDerivAt_const t 1).sub
      ((hasDerivAt_id t).pow 2 |>.const_mul (v ^ 2))).const_mul 2 using 1 <;>
      simp only [id_eq] <;> ring
  have hprod := hfactor.mul hA
  have hquot := hprod.div_const (v * (1 + v))
  unfold lrLowVStarEnvelopeActual
  convert hshape.sub hquot using 1
  have hvden : v * (1 + v) ≠ 0 :=
    mul_ne_zero hv.1.ne' (by linarith [hv.1])
  have hqden : 1 - v ^ 2 * t ^ 2 ≠ 0 := by
    rw [show v ^ 2 * t ^ 2 = (v * t) ^ 2 by ring]
    exact hdenL
  field_simp [hvden, hqden]
  ring

theorem lrLowVStarEnvelopeActual_deriv_neg_smallV
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (hvSmall : v ≤ 1 / 3) (ht : t ∈ Ioo (0 : ℝ) 1) :
    deriv (lrLowVStarEnvelopeActual v) t < 0 := by
  rw [(hasDerivAt_lrLowVStarEnvelopeActual_t hv ht).deriv]
  have hA := lrFlowA_lt_half_smallV hv hvSmall
    (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩)
  have hcoef : 0 < 2 * v * t / (1 + v) :=
    div_pos (mul_pos (mul_pos (by norm_num) hv.1) ht.1) (by linarith [hv.1])
  have hlast : 2 * v * t / (1 + v) * (2 * lrFlowA v t - 1) < 0 :=
    mul_neg_of_pos_of_neg hcoef (by linarith)
  have hart : 0 < Real.artanh t := Real.artanh_pos ht
  have hvert : 0 ≤ Real.artanh (v * t) :=
    Real.artanh_nonneg (mul_nonneg hv.1.le ht.1.le)
  linarith

end CourtadeKumar
