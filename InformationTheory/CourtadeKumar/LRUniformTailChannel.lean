import InformationTheory.CourtadeKumar.LRCompactVCorrelatedReplayLedger
import InformationTheory.CourtadeKumar.LRAbelElementaryBounds
import InformationTheory.CourtadeKumar.LRSmallVEndpointA

/-!
# Analytic channel inequalities for the uniform cancellation tail

This begins the kernel proof of manuscript (M15)--(M16).  The auxiliary
channel derivative bracket is bounded below using only `atanh z >= z` and
`log u <= u-1`; no numerical certificate is involved.
-/

open Set

namespace CourtadeKumar

noncomputable def lrUniformTailE (v t : ℝ) : ℝ :=
  1 - v ^ 2 * t ^ 2

noncomputable def lrUniformTailAStar (v t : ℝ) : ℝ :=
  Real.log (1 + v) - (1 / 2 : ℝ) * Real.log (lrUniformTailE v t)

noncomputable def lrUniformTailKChannel (v t : ℝ) : ℝ :=
  v * (1 + v) * lrGShape t v -
    lrUniformTailE v t * lrUniformTailAStar v t

noncomputable def lrUniformTailDChannel (v t : ℝ) : ℝ :=
  (1 + v) * Real.artanh t +
    (1 + v - 2 * v * t) * Real.artanh (v * t) -
    2 * v * t * Real.log ((1 + v) / (1 + v * t)) + v * t

lemma lrUniformTailE_pos
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < lrUniformTailE v t := by
  unfold lrUniformTailE
  have hvt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  nlinarith [mul_pos hv.1 ht.1]

lemma lrUniformTailAStar_eq_lrFlowA
    {v t : ℝ} :
    lrUniformTailAStar v t = lrFlowA v t := by
  unfold lrUniformTailAStar lrUniformTailE lrFlowA lrFlowBeta lrL
  rw [show v ^ 2 * t ^ 2 = (v * t) ^ 2 by ring]
  ring

lemma lrUniformTail_log_ratio_le
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    Real.log ((1 + v) / (1 + v * t)) ≤
      v * (1 - t) / (1 + v * t) := by
  have hden : 0 < 1 + v * t := by
    linarith [mul_pos hv.1 ht.1]
  have hnum : 0 < 1 + v := by linarith [hv.1]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hnum hden)
  have hid : (1 + v) / (1 + v * t) - 1 =
      v * (1 - t) / (1 + v * t) := by
    field_simp [hden.ne']
    ring
  simpa [hid] using hlog

theorem lrUniformTailDChannel_ge_t
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    t ≤ lrUniformTailDChannel v t := by
  have hvtPos : 0 < v * t := mul_pos hv.1 ht.1
  have hvtLt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hartT : t ≤ Real.artanh t :=
    (self_lt_artanh ht).le
  have hartVT : v * t ≤ Real.artanh (v * t) :=
    (self_lt_artanh ⟨hvtPos, hvtLt⟩).le
  have hcoef : 0 ≤ 1 + v - 2 * v * t := by
    have hvtLeV : v * t ≤ v :=
      mul_le_of_le_one_right hv.1.le ht.2.le
    linarith [hv.2]
  have hlog := lrUniformTail_log_ratio_le hv ht
  have hfirst := mul_le_mul_of_nonneg_left hartT
    (show 0 ≤ 1 + v by linarith [hv.1])
  have hsecond := mul_le_mul_of_nonneg_left hartVT hcoef
  have hlogCoef : 0 ≤ 2 * v * t := by nlinarith [hvtPos]
  have hthird := mul_le_mul_of_nonneg_left hlog hlogCoef
  have hlower :
      (1 + v) * t + (1 + v - 2 * v * t) * (v * t) -
          2 * v * t * (v * (1 - t) / (1 + v * t)) + v * t ≤
        lrUniformTailDChannel v t := by
    unfold lrUniformTailDChannel
    linarith
  have hden : 0 < 1 + v * t := by linarith [hvtPos]
  have hsqLe : (v * t) ^ 2 ≤ v * t := by
    nlinarith
  have hbracket : 0 ≤
      3 - v + t * v ^ 2 + 3 * t * v - 2 * t ^ 2 * v ^ 2 := by
    have htwice : 2 * t ^ 2 * v ^ 2 ≤ 2 * v * t := by
      nlinarith [hsqLe]
    have hpos1 : 0 ≤ t * v ^ 2 :=
      mul_nonneg ht.1.le (sq_nonneg v)
    have hpos2 : 0 ≤ t * v := mul_nonneg ht.1.le hv.1.le
    nlinarith [hv.2]
  have hid :
      ((1 + v) * t + (1 + v - 2 * v * t) * (v * t) -
          2 * v * t * (v * (1 - t) / (1 + v * t)) + v * t) - t =
        v * t *
          (3 - v + t * v ^ 2 + 3 * t * v - 2 * t ^ 2 * v ^ 2) /
            (1 + v * t) := by
    field_simp [hden.ne']
    ring
  have hlowerT : t ≤
      (1 + v) * t + (1 + v - 2 * v * t) * (v * t) -
        2 * v * t * (v * (1 - t) / (1 + v * t)) + v * t := by
    rw [← sub_nonneg, hid]
    positivity
  exact hlowerT.trans hlower

theorem lrUniformTailDChannel_ge_vt_log_two
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    v * t * Real.log 2 ≤ lrUniformTailDChannel v t := by
  have hlog : Real.log 2 ≤ 1 := lr_log_two_lt_three_quarters.le.trans
    (by norm_num)
  have hvt : v * t ≤ t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hv.2.le) ht.1.le]
  have : v * t * Real.log 2 ≤ t := by
    have hvt0 : 0 ≤ v * t := mul_nonneg hv.1.le ht.1.le
    nlinarith [mul_le_mul_of_nonneg_left hlog hvt0]
  exact this.trans (lrUniformTailDChannel_ge_t hv ht)

lemma lrUniformTailAStar_eq_artanh_add_log_ratio
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrUniformTailAStar v t =
      Real.artanh (v * t) + Real.log ((1 + v) / (1 + v * t)) := by
  have hvtPos : 0 < v * t := mul_pos hv.1 ht.1
  have hvtLt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have hplus : 0 < 1 + v * t := by linarith
  have hminus : 0 < 1 - v * t := by linarith
  have hvplus : 0 < 1 + v := by linarith [hv.1]
  rw [Real.artanh_eq_half_log
    (show v * t ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, hvtLt.le⟩)]
  unfold lrUniformTailAStar lrUniformTailE
  rw [show 1 - v ^ 2 * t ^ 2 =
      (1 - v * t) * (1 + v * t) by ring,
    Real.log_mul hminus.ne' hplus.ne',
    Real.log_div hvplus.ne' hplus.ne',
    Real.log_div hplus.ne' hminus.ne']
  ring

theorem hasDerivAt_lrUniformTailKChannel_sub
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun x : ℝ => lrUniformTailKChannel v x -
        (Real.log 2 / 2) * lrUniformTailE v x)
      (-v * (lrUniformTailDChannel v t - v * t * Real.log 2)) t := by
  have hvtPos : 0 < v * t := mul_pos hv.1 ht.1
  have hvtLt : v * t < 1 := calc
    v * t < 1 * t := mul_lt_mul_of_pos_right hv.2 ht.1
    _ < 1 := by simpa using ht.2
  have htMem : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  have hvtMem : v * t ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [hvtPos], hvtLt⟩
  have harg : HasDerivAt (fun x : ℝ => v * x) v t := by
    simpa using (hasDerivAt_id t).const_mul v
  have hG : HasDerivAt (fun x : ℝ => lrGShape x v)
      (-Real.artanh t - Real.artanh (v * t)) t := by
    have htPhi := hasDerivAt_topPhi htMem
    have hvtPhi := (hasDerivAt_topPhi hvtMem).comp t harg
    have h := ((hasDerivAt_const t (lrG v)).sub htPhi).sub
      (hvtPhi.div_const v)
    unfold lrGShape
    convert h using 1
    field_simp [hv.1.ne']
    ring
  have hE : HasDerivAt (lrUniformTailE v) (-2 * v ^ 2 * t) t := by
    unfold lrUniformTailE
    convert (hasDerivAt_const t 1).sub
      ((hasDerivAt_id t).pow 2 |>.const_mul (v ^ 2)) using 1 <;>
      simp only [id_eq] <;> ring
  have hden : 1 - (v * t) ^ 2 ≠ 0 := by
    nlinarith [hvtPos, hvtLt]
  have hA : HasDerivAt (lrUniformTailAStar v)
      (v ^ 2 * t / lrUniformTailE v t) t := by
    rw [show lrUniformTailAStar v = lrFlowA v by
      funext x
      exact lrUniformTailAStar_eq_lrFlowA]
    have hL := (hasDerivAt_lrL hden).comp t harg
    unfold lrFlowA lrUniformTailE
    convert (hasDerivAt_const t (lrFlowBeta v)).add hL using 1
    simp only [zero_add]
    rw [show v ^ 2 * t ^ 2 = (v * t) ^ 2 by ring]
    field_simp [hden]
  have hK : HasDerivAt (lrUniformTailKChannel v)
      (v * (1 + v) *
          (-Real.artanh t - Real.artanh (v * t)) -
        ((-2 * v ^ 2 * t) * lrUniformTailAStar v t +
          lrUniformTailE v t *
            (v ^ 2 * t / lrUniformTailE v t))) t := by
    unfold lrUniformTailKChannel
    convert (hG.const_mul (v * (1 + v))).sub (hE.mul hA) using 1
  have hscaledE := hE.const_mul (Real.log 2 / 2)
  have htotal := hK.sub hscaledE
  convert htotal using 1
  have hePos := lrUniformTailE_pos hv ht
  have hAidentity := lrUniformTailAStar_eq_artanh_add_log_ratio hv ht
  rw [hAidentity]
  unfold lrUniformTailDChannel
  field_simp [hePos.ne']
  ring

lemma continuousAt_lrUniformTailKChannel_sub
    {v t : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt
      (fun x : ℝ => lrUniformTailKChannel v x -
        (Real.log 2 / 2) * lrUniformTailE v x) t := by
  have hvt0 : 0 ≤ v * t := mul_nonneg hv.1.le ht.1
  have hvtLt : v * t < 1 := calc
    v * t ≤ v * 1 := mul_le_mul_of_nonneg_left ht.2 hv.1.le
    _ < 1 := by simpa using hv.2
  have he : lrUniformTailE v t ≠ 0 := by
    unfold lrUniformTailE
    nlinarith
  have hE : ContinuousAt (lrUniformTailE v) t := by
    unfold lrUniformTailE
    fun_prop
  have hlogE : ContinuousAt
      (fun x : ℝ => Real.log (lrUniformTailE v x)) t :=
    hE.log he
  have hA : ContinuousAt (lrUniformTailAStar v) t := by
    unfold lrUniformTailAStar
    fun_prop
  have hG : ContinuousAt (fun x : ℝ => lrGShape x v) t := by
    have harg : ContinuousAt (fun x : ℝ => v * x) t := by fun_prop
    have hphiT : ContinuousAt topPhi t := continuous_topPhi.continuousAt
    have hphiVT : ContinuousAt (fun x : ℝ => topPhi (v * x)) t :=
      continuous_topPhi.continuousAt.comp harg
    unfold lrGShape
    exact ((continuousAt_const.sub hphiT).sub (hphiVT.div_const v))
  unfold lrUniformTailKChannel
  fun_prop

theorem lrUniformTailKChannel_sub_antitoneOn
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    AntitoneOn
      (fun t : ℝ => lrUniformTailKChannel v t -
        (Real.log 2 / 2) * lrUniformTailE v t)
      (Set.Icc (0 : ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) 1)
  · intro t ht
    exact (continuousAt_lrUniformTailKChannel_sub hv ht).continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (hasDerivAt_lrUniformTailKChannel_sub hv ht).differentiableAt
      |>.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hasDerivAt_lrUniformTailKChannel_sub hv ht).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv.1.le) <|
      sub_nonneg.mpr (lrUniformTailDChannel_ge_vt_log_two hv ht)

noncomputable def lrUniformTailEndpointRatio (v : ℝ) : ℝ :=
  v / (1 - v) * Real.log ((1 + v) / (2 * v))

theorem hasDerivAt_lrUniformTailEndpointRatio
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt lrUniformTailEndpointRatio
      ((Real.log ((1 + v) / (2 * v)) - (1 - v) / (1 + v)) /
        (1 - v) ^ 2) v := by
  have hvNe : v ≠ 0 := hv.1.ne'
  have honeSub : 1 - v ≠ 0 := by linarith [hv.2]
  have honePlus : 1 + v ≠ 0 := by linarith [hv.1]
  have htwoV : 2 * v ≠ 0 := mul_ne_zero (by norm_num) hvNe
  have hcoef : HasDerivAt (fun x : ℝ => x / (1 - x))
      (1 / (1 - v) ^ 2) v := by
    have hden := (hasDerivAt_const v 1).sub (hasDerivAt_id v)
    convert (hasDerivAt_id v).div hden honeSub using 1
    dsimp only [id_eq, Pi.sub_apply]
    field_simp [honeSub]
    ring
  have hnum : HasDerivAt (fun x : ℝ => 1 + x) 1 v := by
    simpa using (hasDerivAt_id v).const_add 1
  have hden : HasDerivAt (fun x : ℝ => 2 * x) 2 v := by
    simpa using (hasDerivAt_id v).const_mul 2
  have hratio : HasDerivAt (fun x : ℝ => (1 + x) / (2 * x))
      ((1 * (2 * v) - (1 + v) * 2) / (2 * v) ^ 2) v := by
    simpa only [Pi.div_apply] using hnum.div hden htwoV
  have hratioPos : 0 < (1 + v) / (2 * v) :=
    div_pos (by linarith [hv.1]) (by nlinarith [hv.1])
  have hlog := hratio.log hratioPos.ne'
  unfold lrUniformTailEndpointRatio
  convert hcoef.mul hlog using 1
  field_simp [hvNe, honeSub, honePlus]
  ring

lemma lrUniformTailEndpointRatio_deriv_nonneg
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    0 ≤ deriv lrUniformTailEndpointRatio v := by
  rw [(hasDerivAt_lrUniformTailEndpointRatio hv).deriv]
  have hratioPos : 0 < (1 + v) / (2 * v) :=
    div_pos (by linarith [hv.1]) (by nlinarith [hv.1])
  have hlog := Real.one_sub_inv_le_log_of_pos hratioPos
  have hid : 1 - ((1 + v) / (2 * v))⁻¹ =
      (1 - v) / (1 + v) := by
    field_simp [hv.1.ne', (by linarith [hv.1] : 1 + v ≠ 0)]
    ring
  rw [hid] at hlog
  exact div_nonneg (sub_nonneg.mpr hlog) (sq_nonneg (1 - v))

theorem lrUniformTailEndpointRatio_monotoneOn :
    MonotoneOn lrUniformTailEndpointRatio (Set.Ico (1 / 3 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ico (1 / 3 : ℝ) 1)
  · intro v hv
    have hvIoo : v ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hv.1], hv.2⟩
    exact (hasDerivAt_lrUniformTailEndpointRatio hvIoo).continuousAt
      |>.continuousWithinAt
  · intro v hv
    rw [interior_Ico] at hv
    have hvIoo : v ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hv.1], hv.2⟩
    exact (hasDerivAt_lrUniformTailEndpointRatio hvIoo).differentiableAt
      |>.differentiableWithinAt
  · intro v hv
    rw [interior_Ico] at hv
    exact lrUniformTailEndpointRatio_deriv_nonneg
      ⟨by linarith [hv.1], hv.2⟩

theorem lrUniformTailEndpointRatio_ge_log_two_half
    {v : ℝ} (hv : v ∈ Set.Ico (1 / 3 : ℝ) 1) :
    Real.log 2 / 2 ≤ lrUniformTailEndpointRatio v := by
  have hmono := lrUniformTailEndpointRatio_monotoneOn
    (show (1 / 3 : ℝ) ∈ Ico (1 / 3 : ℝ) 1 by norm_num)
    hv
    hv.1
  have hendpoint : lrUniformTailEndpointRatio (1 / 3 : ℝ) =
      Real.log 2 / 2 := by
    unfold lrUniformTailEndpointRatio
    norm_num
    ring
  rwa [hendpoint] at hmono

lemma lrUniformTailKChannel_one
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    lrUniformTailKChannel v 1 =
      (1 - v ^ 2) * lrUniformTailEndpointRatio v := by
  have hvMem : v ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hv.1], hv.2⟩
  have hvIcc : v ∈ Icc (-1 : ℝ) 1 := ⟨hvMem.1.le, hvMem.2.le⟩
  have hvNe : v ≠ 0 := hv.1.ne'
  have honeSub : 1 - v ≠ 0 := by linarith [hv.2]
  have honePlus : 1 + v ≠ 0 := by linarith [hv.1]
  have htwoV : 2 * v ≠ 0 := mul_ne_zero (by norm_num) hvNe
  unfold lrUniformTailKChannel
  rw [lrUniformTailAStar_eq_lrFlowA,
    lrFlowA_at_one_eq_artanh hv]
  unfold lrUniformTailE lrUniformTailEndpointRatio lrGShape lrG
  norm_num only [mul_one, one_pow]
  rw [topPhi_one, topPhi_eq_mul_artanh_add_log hvMem,
    Real.artanh_eq_half_log hvIcc,
    Real.log_div honePlus honeSub,
    Real.log_div honePlus htwoV,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hvNe]
  rw [show 1 - v ^ 2 = (1 - v) * (1 + v) by ring,
    Real.log_mul honeSub honePlus]
  field_simp [hvNe, honeSub, honePlus]
  ring

/-- Manuscript (M16): the channel energy controls the cancellation
parameter uniformly on the retained `v ≥ 1/3` chart. -/
theorem lrUniformTailKChannel_ge
    {v t : ℝ} (hv : v ∈ Set.Ico (1 / 3 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    Real.log 2 / 2 * lrUniformTailE v t ≤
      lrUniformTailKChannel v t := by
  have hvIoo : v ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hv.1], hv.2⟩
  have hanti := lrUniformTailKChannel_sub_antitoneOn hvIoo
    (show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1.le, ht.2.le⟩)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) ht.2.le
  have hratio := lrUniformTailEndpointRatio_ge_log_two_half hv
  have heOne : 0 ≤ 1 - v ^ 2 := by
    nlinarith [hvIoo.1, hvIoo.2]
  have hend : 0 ≤ lrUniformTailKChannel v 1 -
      Real.log 2 / 2 * lrUniformTailE v 1 := by
    rw [lrUniformTailKChannel_one hvIoo]
    unfold lrUniformTailE
    norm_num only [mul_one, one_pow]
    nlinarith [mul_nonneg heOne
      (sub_nonneg.mpr hratio)]
  linarith

end CourtadeKumar
