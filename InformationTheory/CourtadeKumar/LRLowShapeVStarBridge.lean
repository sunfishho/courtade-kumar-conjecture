import InformationTheory.CourtadeKumar.LRLowShapeVStarCertificate
import InformationTheory.CourtadeKumar.LRLowShapeComparisonDecomposition

/-!
# Analytic bridge for the low-shape `V_*` certificate

This identifies the rational upper envelope certified by the Bernstein table
with a lower bound for the actual analytic envelope, then converts its sign
to the nonnegativity of `lrLowVStar`.
-/

open Set

namespace CourtadeKumar

noncomputable def lrLowVStarEnvelopeActual (v t : ℝ) : ℝ :=
  lrGShape t v -
    2 * (1 - v ^ 2 * t ^ 2) * lrFlowA v t / (v * (1 + v))

lemma lrLowVBetaEndpointUpper_eq_atanhUpper
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrLowVBetaEndpointUpper v = lrAtanh5Upper (v / (2 + v)) := by
  have h1 : 1 + v ≠ 0 := by linarith [hv.1]
  have h2 : 2 + v ≠ 0 := by linarith [hv.1]
  unfold lrLowVBetaEndpointUpper lrAtanh5Upper
  congr 1
  rw [show 1 - (v / (2 + v)) ^ 2 =
      4 * (1 + v) / (2 + v) ^ 2 by
    field_simp [h2]
    ring]
  field_simp [h1, h2]
  ring

lemma lrLowVStar_actualA_le_upper
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrFlowA v t ≤
      lrLowVBetaEndpointUpper v + lrLowL12Upper (v ^ 2 * t ^ 2) := by
  have hA := (lrLowA_bounds hv
    (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩)).2
  unfold lrLowAUpper at hA
  rw [lrLowVBetaEndpointUpper_eq_atanhUpper
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)]
  simpa [lrFlowA] using hA

lemma lrLowVStarEnvelopeLower_le_actual
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrLowVStarEnvelopeLower v (t ^ 2) ≤ lrLowVStarEnvelopeActual v t := by
  have hG := lrLowGShapeLower_le hv ht
  have hA := lrLowVStar_actualA_le_upper hv ht
  have hq : v ^ 2 * t ^ 2 ≤ 1 := by
    have hvt : v * t < 1 := calc
      v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
      _ < 1 := by simpa using ht.2
    rw [show v ^ 2 * t ^ 2 = (v * t) ^ 2 by ring]
    nlinarith [mul_pos (mul_pos hv.1 ht.1) (sub_pos.mpr hvt)]
  have hden : 0 < v * (1 + v) := mul_pos hv.1 (by linarith [hv.1])
  have hfactor : 0 ≤ 2 * (1 - v ^ 2 * t ^ 2) / (v * (1 + v)) :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hq)) hden.le
  have hprod := mul_le_mul_of_nonneg_left hA hfactor
  have hprod' :
      2 * (1 - v ^ 2 * t ^ 2) * lrFlowA v t / (v * (1 + v)) ≤
        2 * (1 - v ^ 2 * t ^ 2) *
          (lrLowVBetaEndpointUpper v + lrLowL12Upper (v ^ 2 * t ^ 2)) /
            (v * (1 + v)) := by
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hprod
  unfold lrLowVStarEnvelopeLower lrLowVStarEnvelopeActual
  exact sub_le_sub hG hprod'

theorem lrLowVStarEnvelopeActual_nonneg
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (htShape : t ^ 2 ≤ 17 / 20) :
    0 ≤ lrLowVStarEnvelopeActual v t := by
  have hcert := lrLowVStarEnvelopeLower_nonneg
    (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
    (show t ^ 2 ∈ Icc (0 : ℝ) (17 / 20) from
      ⟨sq_nonneg t, htShape⟩)
  exact hcert.trans (lrLowVStarEnvelopeLower_le_actual hv ht)

lemma lrLowVStar_eq_envelope
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrLowVStar v (t ^ 2) (lrGShape t v) =
      v ^ 2 * t ^ 2 / (2 * (1 - v ^ 2 * t ^ 2)) *
        lrLowVStarEnvelopeActual v t := by
  have hvt : v * t < 1 := by
    calc
      v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
      _ < 1 := by simpa using ht.2
  have hq : 1 - v ^ 2 * t ^ 2 ≠ 0 := by
    rw [show v ^ 2 * t ^ 2 = (v * t) ^ 2 by ring]
    nlinarith [mul_pos (mul_pos hv.1 ht.1) (sub_pos.mpr hvt)]
  have h1 : 1 + v ≠ 0 := ne_of_gt (by nlinarith [hv.1])
  unfold lrLowVStar lrLowVStarEnvelopeActual lrFlowM
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ht.1]
  field_simp [hv.1.ne', hq, h1]

theorem lrLowVStar_nonneg_lowShape
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (htShape : t ^ 2 ≤ 17 / 20) :
    0 ≤ lrLowVStar v (t ^ 2) (lrGShape t v) := by
  have henv := lrLowVStarEnvelopeActual_nonneg hv ht htShape
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
