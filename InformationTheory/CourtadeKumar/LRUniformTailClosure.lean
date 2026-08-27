import InformationTheory.CourtadeKumar.LRUniformTailCollection

/-!
# Closure of the uniform `k ≥ 4` cancellation tail

This proves manuscript (M21), with the explicit positive margin used there.
No positivity assumption on the physical reserve `J` is needed.
-/

open Set

namespace CourtadeKumar

lemma lrUniformTailRatio_le_one
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrUniformTailRatio R v t ≤ 1 := by
  have hzPos := lrUniformTailZ_pos hR hv ht
  have hlog := Real.log_le_sub_one_of_pos
    (show 0 < 1 + lrUniformTailZ R v t by linarith)
  have hlog' : Real.log (1 + lrUniformTailZ R v t) ≤
      lrUniformTailZ R v t := by linarith
  unfold lrUniformTailRatio
  rw [div_le_iff₀ hzPos]
  simpa using hlog'

lemma lrUniformTailRatio_pos
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < lrUniformTailRatio R v t := by
  have hzPos := lrUniformTailZ_pos hR hv ht
  unfold lrUniformTailRatio
  exact div_pos (Real.log_pos (by linarith)) hzPos

lemma lrUniformTailWScaled_mem
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    lrUniformTailWScaled R ∈ Ioc (0 : ℝ) 1 := by
  have hs : 1 - R ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hR.1, hR.2]
  have hW := lrCertificateOmega_zero_mem hs
  have heq := lrCertificateOmega_one_sub_sq hs
    (show (1 : ℝ) ∈ Ioc 0 1 by norm_num)
  simp only [one_pow, sub_self] at heq
  rw [heq] at hW
  have hW' : lrWKernel R 1 ∈ Ioc (0 : ℝ) ((1 - R) / 4) := by
    simpa only [sub_sub_cancel] using hW
  unfold lrUniformTailWScaled
  constructor
  · exact div_pos (mul_pos (by norm_num) hW'.1) hs.1
  · rw [div_le_iff₀ hs.1]
    nlinarith [hW'.2]

lemma lrUniformTailAStar_pos
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < lrUniformTailAStar v t := by
  have he := lrUniformTailE_pos hv ht
  have heLt : lrUniformTailE v t < 1 := by
    unfold lrUniformTailE
    nlinarith [mul_pos (sq_pos_of_pos hv.1) (sq_pos_of_pos ht.1)]
  have hlogV : 0 < Real.log (1 + v) := Real.log_pos (by linarith [hv.1])
  have hlogE : Real.log (lrUniformTailE v t) < 0 := Real.log_neg he heLt
  unfold lrUniformTailAStar
  linarith

lemma lrUniformTailL0_ge_channel
    {R v t : ℝ} (hv : v ∈ Set.Ico (1 / 3 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    Real.log 2 * (v * t ^ 2 / (4 * (1 + v))) ≤
      lrUniformTailL0 R v t := by
  have hvIoo : v ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hv.1], hv.2⟩
  have hePos := lrUniformTailE_pos hvIoo ht
  have hK := lrUniformTailKChannel_ge hv ht
  have hcoef : 0 ≤ v * t ^ 2 /
      (2 * lrUniformTailE v t * (1 + v)) :=
    div_nonneg (mul_nonneg hvIoo.1.le (sq_nonneg t))
      (mul_nonneg (mul_nonneg (by norm_num) hePos.le) (by linarith [hvIoo.1]))
  have hscaled := mul_le_mul_of_nonneg_left hK hcoef
  have hidentity :
      (v * t ^ 2 / (2 * lrUniformTailE v t * (1 + v))) *
          lrUniformTailKChannel v t = lrUniformTailL0 R v t := by
    unfold lrUniformTailKChannel lrUniformTailL0
    field_simp [hePos.ne', (by linarith [hvIoo.1] : 1 + v ≠ 0)]
  have hleft :
      (v * t ^ 2 / (2 * lrUniformTailE v t * (1 + v))) *
          (Real.log 2 / 2 * lrUniformTailE v t) =
        Real.log 2 * (v * t ^ 2 / (4 * (1 + v))) := by
    field_simp [hePos.ne', (by linarith [hvIoo.1] : 1 + v ≠ 0)]
    ring
  rwa [hidentity, hleft] at hscaled

lemma lrUniformTailZ_le_vsq_four
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hk : 4 * (1 - R) ≤ lrUniformTailE v t) :
    lrUniformTailZ R v t ≤ v ^ 2 * t ^ 2 / 4 := by
  have hePos := lrUniformTailE_pos hv ht
  unfold lrUniformTailZ
  rw [div_le_iff₀ hePos]
  have hnonneg : 0 ≤ v ^ 2 * t ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hk hnonneg]

/-- The coefficient of `A_*` in (M20) is nonnegative. -/
lemma lrUniformTailAStar_coefficient_nonneg
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hk : 4 * (1 - R) ≤ lrUniformTailE v t) :
    0 ≤ lrFlowPW R v t / (1 - R) +
      (lrUniformTailRatio R v t - lrUniformTailWScaled R) *
        v * t ^ 2 / (2 * (1 + v)) := by
  have hratio := lrUniformTailRatio_lower hR hv ht
  have hw := lrUniformTailWScaled_mem hR
  have hrw : -lrUniformTailZ R v t / 2 ≤
      lrUniformTailRatio R v t - lrUniformTailWScaled R := by
    linarith [hratio, hw.2]
  have hfactor : 0 ≤ v * t ^ 2 / (2 * (1 + v)) :=
    div_nonneg (mul_nonneg hv.1.le (sq_nonneg t))
      (mul_nonneg (by norm_num) (by linarith [hv.1]))
  have hscaled := mul_le_mul_of_nonneg_right hrw hfactor
  have hscaled' :
      (-lrUniformTailZ R v t / 2) * v * t ^ 2 / (2 * (1 + v)) ≤
        (lrUniformTailRatio R v t - lrUniformTailWScaled R) *
          v * t ^ 2 / (2 * (1 + v)) := by
    convert hscaled using 1 <;> ring
  have hsPos : 0 < 1 - R := sub_pos.mpr hR.2
  have hk3 : 3 * (1 - R) ≤ lrUniformTailE v t := by linarith [hk]
  have hpwRaw := lrUniformTailPW_div_lower hR hv ht hk3
  have hpw :
      (1 - R) * (v ^ 2 * t ^ 2) ^ 2 /
          (4 * lrUniformTailE v t * v * (1 + v)) ≤
        lrFlowPW R v t / (1 - R) := by
    simpa [lrUniformTailE] using hpwRaw
  have hcancel :
      (1 - R) * (v ^ 2 * t ^ 2) ^ 2 /
          (4 * lrUniformTailE v t * v * (1 + v)) +
        (-lrUniformTailZ R v t / 2) * v * t ^ 2 /
          (2 * (1 + v)) = 0 := by
    have hePos := lrUniformTailE_pos hv ht
    unfold lrUniformTailZ
    field_simp [hePos.ne', hv.1.ne', (by linarith [hv.1] : 1 + v ≠ 0)]
    ring
  linarith only [add_le_add hpw hscaled', hcancel]

/-- Manuscript (M21), including its explicit rational margin. -/
theorem lrUniformTail_halfMidpoint_margin
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Set.Ico (1 / 3 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hx : 17 / 20 ≤ t ^ 2)
    (hk : 4 * (1 - R) ≤ lrUniformTailE v t) :
    187 / 76800 <
      lrFlowNumeratorP R (lrFlowM v / 2) v t / (1 - R) := by
  have hvIoo : v ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hv.1], hv.2⟩
  have hzQuarter := lrUniformTailZ_le_one_fourth hR hvIoo ht hk
  have hrLower := lrUniformTailRatio_lower hR hvIoo ht
  have hrUpper := lrUniformTailRatio_le_one hR hvIoo ht
  have hrPos := lrUniformTailRatio_pos hR hvIoo ht
  have hw := lrUniformTailWScaled_mem hR
  have hD := lrUniformTailD_eq_ratio hR hvIoo ht
  have hL0 := lrUniformTailL0_ge_channel (R := R) hv ht
  have hcoef := lrUniformTailAStar_coefficient_nonneg hR hvIoo ht hk
  have hA := lrUniformTailAStar_pos hvIoo ht
  let base : ℝ := v * t ^ 2 / (4 * (1 + v))
  have hbasePos : 0 < base := by
    unfold base
    exact div_pos (mul_pos hvIoo.1 (sq_pos_of_pos ht.1))
      (mul_pos (by norm_num) (by linarith [hvIoo.1]))
  have hvRatio : 1 / 4 ≤ v / (1 + v) := by
    rw [le_div_iff₀ (by linarith [hvIoo.1] : 0 < 1 + v)]
    nlinarith [hv.1]
  have hbaseLower : 17 / 320 ≤ base := by
    have hprod := mul_le_mul hvRatio hx (by norm_num : (0 : ℝ) ≤ 17 / 20)
      (div_nonneg hvIoo.1.le (by linarith [hvIoo.1] : 0 ≤ 1 + v))
    have hdiv := div_le_div_of_nonneg_right hprod (by norm_num : (0 : ℝ) ≤ 4)
    calc
      17 / 320 = ((1 / 4 : ℝ) * (17 / 20)) / 4 := by norm_num
      _ ≤ ((v / (1 + v)) * t ^ 2) / 4 := hdiv
      _ = base := by
        unfold base
        field_simp [(by linarith [hvIoo.1] : 1 + v ≠ 0)]
  have hrSeven : 7 / 8 ≤ lrUniformTailRatio R v t := by
    nlinarith [hrLower, hzQuarter]
  have hlog : 2 / 3 < Real.log 2 := by
    exact (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hrlog : 7 / 12 < lrUniformTailRatio R v t * Real.log 2 := by
    have hmul := mul_lt_mul_of_pos_left hlog hrPos
    nlinarith [mul_le_mul_of_nonneg_right hrSeven (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  have hpositive : base * (7 / 12) <
      lrUniformTailRatio R v t * lrUniformTailL0 R v t := by
    have hL0' : Real.log 2 * base ≤ lrUniformTailL0 R v t := by
      simpa [base] using hL0
    have hscaled := mul_le_mul_of_nonneg_left hL0' hrPos.le
    have hstrict := mul_lt_mul_of_pos_left hrlog hbasePos
    nlinarith
  have hzStrong := lrUniformTailZ_le_vsq_four hR hvIoo ht hk
  have hshapeFactor :
      v * (2 + v - v * t ^ 2) ≤ 43 / 20 := by
    have hvOne : v ≤ 1 := hv.2.le
    have hxUpper : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have htail : 0 ≤ 1 - t ^ 2 := sub_nonneg.mpr hxUpper
    have htailUpper : 1 - t ^ 2 ≤ 3 / 20 := by linarith [hx]
    have hprod := mul_le_mul hvOne htailUpper htail
      (by norm_num : (0 : ℝ) ≤ 1)
    have hprod2 := mul_le_mul hvOne hprod
      (mul_nonneg hvIoo.1.le htail) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hcorrection :
      lrUniformTailWScaled R * lrFlowD R v t *
          (2 + v - v * t ^ 2) / (2 * (1 + v)) ≤
        base * (43 / 80) := by
    have hshapeNonneg : 0 ≤ 2 + v - v * t ^ 2 := by
      have htSqLe : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      nlinarith [mul_le_mul_of_nonneg_left htSqLe hvIoo.1.le]
    rw [hD]
    have hwr : lrUniformTailWScaled R * lrUniformTailRatio R v t ≤ 1 := by
      nlinarith [mul_le_mul hw.2 hrUpper hrPos.le (by norm_num : (0 : ℝ) ≤ 1)]
    have hwz : lrUniformTailWScaled R * lrUniformTailRatio R v t *
        lrUniformTailZ R v t ≤ v ^ 2 * t ^ 2 / 4 := by
      calc
        lrUniformTailWScaled R * lrUniformTailRatio R v t *
            lrUniformTailZ R v t ≤ 1 * lrUniformTailZ R v t :=
          mul_le_mul_of_nonneg_right hwr (lrUniformTailZ_pos hR hvIoo ht).le
        _ ≤ v ^ 2 * t ^ 2 / 4 := by simpa using hzStrong
    have hdenPos : 0 < 4 * (1 + v) :=
      mul_pos (by norm_num) (by linarith [hvIoo.1])
    rw [show lrUniformTailWScaled R *
          (lrUniformTailZ R v t * lrUniformTailRatio R v t / 2) *
          (2 + v - v * t ^ 2) / (2 * (1 + v)) =
        (lrUniformTailWScaled R * lrUniformTailRatio R v t *
          lrUniformTailZ R v t) * (2 + v - v * t ^ 2) /
            (4 * (1 + v)) by
      field_simp [(by linarith [hvIoo.1] : 1 + v ≠ 0)]
      ring]
    have hnum := mul_le_mul hwz hshapeFactor
      (mul_nonneg hvIoo.1.le hshapeNonneg)
      (by positivity : 0 ≤ v ^ 2 * t ^ 2 / 4)
    have hnumCancel :
        (lrUniformTailWScaled R * lrUniformTailRatio R v t *
            lrUniformTailZ R v t) * (2 + v - v * t ^ 2) ≤
          v * t ^ 2 * (43 / 80) := by
      rw [← (mul_le_mul_iff_right₀ hvIoo.1)]
      convert hnum using 1 <;> ring
    unfold base
    rw [div_le_iff₀ hdenPos]
    convert hnumCancel using 1 <;>
      field_simp [(by linarith [hvIoo.1] : 1 + v ≠ 0)] <;> ring
  have hexact := lrUniformTail_exact_collection hR hvIoo ht
  have hdrop :
      lrUniformTailRatio R v t * lrUniformTailL0 R v t -
          lrUniformTailWScaled R * lrFlowD R v t *
            (2 + v - v * t ^ 2) / (2 * (1 + v)) ≤
        lrFlowNumeratorP R (lrFlowM v / 2) v t / (1 - R) := by
    rw [hexact]
    linarith only [mul_nonneg hA.le hcoef]
  have hmargin :
      base * (7 / 12 - 43 / 80) <
        lrFlowNumeratorP R (lrFlowM v / 2) v t / (1 - R) := by
    linarith only [hpositive, hcorrection, hdrop]
  have hrat : (187 / 76800 : ℝ) =
      (17 / 320) * (7 / 12 - 43 / 80) := by norm_num
  rw [hrat]
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hbaseLower (by norm_num)) hmargin

theorem lrUniformTail_halfMidpoint_pos
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Set.Ico (1 / 3 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hx : 17 / 20 ≤ t ^ 2)
    (hk : 4 * (1 - R) ≤ lrUniformTailE v t) :
    0 < lrFlowNumeratorP R (lrFlowM v / 2) v t := by
  have hmargin := lrUniformTail_halfMidpoint_margin hR hv ht hx hk
  have hsPos : 0 < 1 - R := sub_pos.mpr hR.2
  have hconst : (0 : ℝ) < 187 / 76800 := by norm_num
  have hratio : 0 <
      lrFlowNumeratorP R (lrFlowM v / 2) v t / (1 - R) :=
    hconst.trans hmargin
  rcases div_pos_iff.mp hratio with hpos | hneg
  · exact hpos.1
  · linarith [hsPos, hneg.2]

end CourtadeKumar
