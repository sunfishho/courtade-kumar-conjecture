import InformationTheory.CourtadeKumar.LRUniformTailPW
import InformationTheory.CourtadeKumar.LRHighShapeMidpointEvaluator

/-!
# Exact collection in the uniform cancellation tail

These are the cancellation-safe coordinates and the exact identity (M20)
used by the analytic `k ≥ 4` chart.
-/

open Set

namespace CourtadeKumar

noncomputable def lrUniformTailZ (R v t : ℝ) : ℝ :=
  (1 - R) * (v ^ 2 * t ^ 2) / lrUniformTailE v t

noncomputable def lrUniformTailRatio (R v t : ℝ) : ℝ :=
  Real.log (1 + lrUniformTailZ R v t) / lrUniformTailZ R v t

noncomputable def lrUniformTailWScaled (R : ℝ) : ℝ :=
  4 * lrWKernel R 1 / (1 - R)

noncomputable def lrUniformTailL0 (R v t : ℝ) : ℝ :=
  v * t ^ 2 / 2 *
    (v * lrGShape t v / lrUniformTailE v t -
      lrUniformTailAStar v t / (1 + v))

lemma lrUniformTailZ_pos
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < lrUniformTailZ R v t := by
  unfold lrUniformTailZ
  exact div_pos
    (mul_pos (sub_pos.mpr hR.2) (mul_pos (sq_pos_of_pos hv.1) (sq_pos_of_pos ht.1)))
    (lrUniformTailE_pos hv ht)

lemma lrUniformTailZ_le_one_fourth
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hk : 4 * (1 - R) ≤ lrUniformTailE v t) :
    lrUniformTailZ R v t ≤ 1 / 4 := by
  have hePos := lrUniformTailE_pos hv ht
  have hvtSqLe : v ^ 2 * t ^ 2 ≤ 1 := by
    have hvSqLe : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
    have htSqLe : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    nlinarith [mul_le_mul hvSqLe htSqLe (sq_nonneg t) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [show lrUniformTailZ R v t =
      ((1 - R) / lrUniformTailE v t) * (v ^ 2 * t ^ 2) by
    unfold lrUniformTailZ
    ring]
  have hratio : (1 - R) / lrUniformTailE v t ≤ 1 / 4 := by
    rw [div_le_iff₀ hePos]
    nlinarith
  nlinarith [mul_le_mul hratio hvtSqLe
    (mul_nonneg (sq_nonneg v) (sq_nonneg t)) (by norm_num : (0 : ℝ) ≤ 1 / 4)]

lemma lrUniformTailRatio_lower
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - lrUniformTailZ R v t / 2 ≤ lrUniformTailRatio R v t := by
  have hzPos := lrUniformTailZ_pos hR hv ht
  have hlog := lr_log_one_add_lower hzPos.le
  unfold lrUniformTailRatio
  rw [le_div_iff₀ hzPos]
  have hden : 0 < 2 + lrUniformTailZ R v t := by linarith
  have hrational :
      lrUniformTailZ R v t * (1 - lrUniformTailZ R v t / 2) ≤
        2 * lrUniformTailZ R v t / (2 + lrUniformTailZ R v t) := by
    rw [le_div_iff₀ hden]
    nlinarith [sq_nonneg (lrUniformTailZ R v t)]
  simpa [mul_comm] using hrational.trans hlog

lemma lrUniformTailD_eq_ratio
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrFlowD R v t =
      lrUniformTailZ R v t * lrUniformTailRatio R v t / 2 := by
  have hePos := lrUniformTailE_pos hv ht
  have hsqrtSq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.1.le
  have hbePos : 0 < 1 - R * v ^ 2 * t ^ 2 := by
    have hprod : R * (v ^ 2 * t ^ 2) < 1 := by
      have hvt : v * t < 1 := calc
        v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
        _ < 1 := by simpa using ht.2
      have hsq : v ^ 2 * t ^ 2 < 1 := by nlinarith [mul_pos hv.1 ht.1]
      calc
        R * (v ^ 2 * t ^ 2) < 1 * (v ^ 2 * t ^ 2) :=
          mul_lt_mul_of_pos_right hR.2
            (mul_pos (sq_pos_of_pos hv.1) (sq_pos_of_pos ht.1))
        _ < 1 := by simpa using hsq
    linarith
  have hratio :
      (1 - R * v ^ 2 * t ^ 2) / lrUniformTailE v t =
        1 + lrUniformTailZ R v t := by
    have heRawNe : 1 - v ^ 2 * t ^ 2 ≠ 0 := by
      simpa [lrUniformTailE] using hePos.ne'
    unfold lrUniformTailE lrUniformTailZ
    field_simp [heRawNe]
    simp only [lrUniformTailE]
    ring
  have hlog :
      Real.log (1 - R * v ^ 2 * t ^ 2) -
          Real.log (lrUniformTailE v t) =
        Real.log (1 + lrUniformTailZ R v t) := by
    rw [← Real.log_div hbePos.ne' hePos.ne', hratio]
  have hlogRaw :
      Real.log (1 - R * v ^ 2 * t ^ 2) -
          Real.log (1 - v ^ 2 * t ^ 2) =
        Real.log (1 + lrUniformTailZ R v t) := by
    simpa [lrUniformTailE] using hlog
  unfold lrFlowD lrFlowA lrFlowB lrFlowBeta lrL
  rw [show (Real.sqrt R * v * t) ^ 2 = R * v ^ 2 * t ^ 2 by
    rw [show (Real.sqrt R * v * t) ^ 2 =
      Real.sqrt R ^ 2 * v ^ 2 * t ^ 2 by ring, hsqrtSq]]
  rw [show (v * t) ^ 2 = v ^ 2 * t ^ 2 by ring]
  unfold lrUniformTailRatio
  have hzNe := (lrUniformTailZ_pos hR hv ht).ne'
  rw [← hlogRaw]
  field_simp [hzNe]
  ring

/-- Exact collection identity (M20). -/
theorem lrUniformTail_exact_collection
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrFlowNumeratorP R (lrFlowM v / 2) v t / (1 - R) =
      lrUniformTailRatio R v t * lrUniformTailL0 R v t +
        lrUniformTailAStar v t *
          (lrFlowPW R v t / (1 - R) +
            (lrUniformTailRatio R v t - lrUniformTailWScaled R) *
              v * t ^ 2 / (2 * (1 + v))) -
        lrUniformTailWScaled R * lrFlowD R v t *
          (2 + v - v * t ^ 2) / (2 * (1 + v)) := by
  have hsPos : 0 < 1 - R := sub_pos.mpr hR.2
  have hePos := lrUniformTailE_pos hv ht
  have hvPlus : 1 + v ≠ 0 := by linarith [hv.1]
  have hD := lrUniformTailD_eq_ratio hR hv ht
  have hA := lrUniformTailAStar_eq_lrFlowA (v := v) (t := t)
  have hB : lrFlowB R v t = lrFlowA v t - lrFlowD R v t := by
    unfold lrFlowD
    ring
  have hmid := lrFlowNumeratorP_halfMidpoint
    (R := R) (v := v) (t := t) (by linarith [hv.1])
  rw [hmid]
  unfold lrUniformTailL0 lrUniformTailWScaled
    lrFlowX₀ lrFlowY₀ lrFlowC lrFlowM
  rw [hA, hB, hD]
  unfold lrUniformTailZ
  field_simp [hsPos.ne', hePos.ne', hvPlus]
  ring

end CourtadeKumar
