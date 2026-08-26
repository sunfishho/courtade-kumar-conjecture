import InformationTheory.CourtadeKumar.LRSmallVEndpointOne

/-!
# Closure of the small-odds endpoint comparison

The analytic endpoint envelope is decreasing in the angular variable.  Its
terminal value is nonnegative, so the endpoint comparison `V_*` is
nonnegative throughout the complete chart `0 < v ≤ 1/3`, `0 < t < 1`.
-/

open Set

namespace CourtadeKumar

lemma continuousOn_lrLowVStarEnvelopeActual_Icc
    {v a : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ha : a ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (lrLowVStarEnvelopeActual v) (Icc a 1) := by
  intro x hx
  have hxPos : 0 < x := ha.1.trans_le hx.1
  have hxOne : x ≤ 1 := hx.2
  have harg : HasDerivAt (fun y : ℝ ↦ v * y) v x := by
    simpa using (hasDerivAt_id x).const_mul v
  have hvxLt : v * x < 1 := calc
    v * x ≤ v * 1 := mul_le_mul_of_nonneg_left hxOne hv.1.le
    _ < 1 := by simpa using hv.2
  have hvxPos : 0 < v * x := mul_pos hv.1 hxPos
  have hdenL : 1 - (v * x) ^ 2 ≠ 0 := by
    nlinarith [hvxPos, hvxLt]
  have hL : ContinuousAt (fun y : ℝ ↦ lrL (v * y)) x :=
    ((hasDerivAt_lrL hdenL).comp x harg).continuousAt
  have hA : ContinuousAt (fun y : ℝ ↦ lrFlowA v y) x := by
    unfold lrFlowA
    exact continuousAt_const.add hL
  have hshape : ContinuousAt (fun y : ℝ ↦ lrGShape y v) x := by
    unfold lrGShape
    exact (continuousAt_const.sub continuous_topPhi.continuousAt).sub
      ((continuous_topPhi.continuousAt.comp harg.continuousAt).div_const v)
  have hfactor : ContinuousAt (fun y : ℝ ↦ 2 * (1 - v ^ 2 * y ^ 2)) x := by
    fun_prop
  unfold lrLowVStarEnvelopeActual
  exact (hshape.sub ((hfactor.mul hA).div_const (v * (1 + v)))).continuousWithinAt

theorem lrLowVStarEnvelopeActual_nonneg_smallV
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (hvSmall : v ≤ 1 / 3) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrLowVStarEnvelopeActual v t := by
  have hanti : AntitoneOn (lrLowVStarEnvelopeActual v) (Icc t 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc t 1)
    · exact continuousOn_lrLowVStarEnvelopeActual_Icc hv ht
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_lrLowVStarEnvelopeActual_t hv
        ⟨ht.1.trans hx.1, hx.2⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (lrLowVStarEnvelopeActual_deriv_neg_smallV hv hvSmall
        ⟨ht.1.trans hx.1, hx.2⟩).le
  have hterminal : 0 ≤ lrLowVStarEnvelopeActual v 1 := by
    rw [lrLowVStarEnvelopeActual_one hv]
    exact lrSmallVEndpointOne_nonneg hv hvSmall
  exact hterminal.trans (hanti
    (show t ∈ Icc t (1 : ℝ) from ⟨le_rfl, ht.2.le⟩)
    (show (1 : ℝ) ∈ Icc t 1 from ⟨ht.2.le, le_rfl⟩) ht.2.le)

theorem lrLowVStar_nonneg_smallV
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (hvSmall : v ≤ 1 / 3) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrLowVStar v (t ^ 2) (lrGShape t v) := by
  have henv := lrLowVStarEnvelopeActual_nonneg_smallV hv hvSmall ht
  have hvt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hpref : 0 ≤ v ^ 2 * t ^ 2 / (2 * (1 - v ^ 2 * t ^ 2)) := by
    have hq : v ^ 2 * t ^ 2 < 1 := by
      rw [show v ^ 2 * t ^ 2 = (v * t) ^ 2 by ring]
      nlinarith [mul_pos (mul_pos hv.1 ht.1) (sub_pos.mpr hvt)]
    exact div_nonneg (mul_nonneg (sq_nonneg v) (sq_nonneg t))
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hq.le))
  rw [lrLowVStar_eq_envelope hv ht]
  exact mul_nonneg hpref henv

end CourtadeKumar
