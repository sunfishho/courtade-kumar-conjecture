import InformationTheory.CourtadeKumar.LRBVEndpoint

/-! Integration in `v` at the `t = 1` endpoint of the LR `B` comparison. -/

open Set

namespace CourtadeKumar

noncomputable def lrBVDerivativeBracket (R v : ℝ) : ℝ :=
  lrBScalarReserve R v +
    (Real.log 2 - Real.log (1 + v)) + (1 - v) / (1 + v) +
    R * v * (1 - v) / (1 - R * v ^ 2) *
      (1 - v * (1 + v) / 2) +
    lrBGamma R * lrBH R v

theorem lrBVDerivativeBracket_nonneg
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioc (0 : ℝ) 1) :
    0 ≤ lrBVDerivativeBracket R v := by
  have hScalar := lrBScalarReserve_nonneg hR hv
  have hLog : 0 ≤ Real.log 2 - Real.log (1 + v) := by
    rw [sub_nonneg]
    exact Real.log_le_log (by linarith [hv.1]) (by linarith [hv.2])
  have hfrac : 0 ≤ (1 - v) / (1 + v) :=
    div_nonneg (sub_nonneg.mpr hv.2) (by linarith [hv.1])
  have hRden : 0 < 1 - R * v ^ 2 := by
    have hvSq : v ^ 2 ≤ 1 := pow_le_one₀ hv.1.le hv.2
    have hmul : R * v ^ 2 ≤ R := by
      simpa using mul_le_mul_of_nonneg_left hvSq hR.1.le
    exact sub_pos.mpr (hmul.trans_lt hR.2)
  have hcurly : 0 ≤ 1 - v * (1 + v) / 2 := by
    have hmul : v * (1 + v) ≤ 2 := by nlinarith [hv.1, hv.2]
    linarith
  have hrational : 0 ≤
      R * v * (1 - v) / (1 - R * v ^ 2) *
        (1 - v * (1 + v) / 2) := by
    exact mul_nonneg
      (div_nonneg
        (mul_nonneg (mul_nonneg hR.1.le hv.1.le) (sub_nonneg.mpr hv.2))
        hRden.le)
      hcurly
  have hH := lrBH_nonneg hR hv
  have hgammaH := mul_nonneg (lrBGamma_pos hR).le hH
  unfold lrBVDerivativeBracket
  positivity

noncomputable def lrBVCDerivRaw (R v : ℝ) : ℝ :=
  -(Real.log (1 + v) + lrL v) / v ^ 2 +
    ((Real.artanh v - v * lrBKernelK R v) * v - lrWKernel R v) / v ^ 2 +
    4 * lrWKernel R 1 / (1 + v) ^ 2

noncomputable def lrBVBDerivRaw (R v : ℝ) : ℝ :=
  1 / (1 + v) + R * v / (1 - R * v ^ 2)

theorem hasDerivAt_lrFlowC_v_one
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ ↦ lrFlowC R x 1)
      (lrBVCDerivRaw R v) v := by
  have hG := hasDerivAt_lrGShape hv.1 (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa using hv.2)
  have hW := hasDerivAt_lrWKernel_z hR hv
  have hquot := hW.div (hasDerivAt_id v) hv.1.ne'
  have hplus : HasDerivAt (fun x : ℝ ↦ 1 + x) 1 v := by
    simpa using (hasDerivAt_id v).const_add 1
  have hcorr := (hasDerivAt_const v (4 * lrWKernel R 1)).div hplus
    (by linarith [hv.1] : 1 + v ≠ 0)
  have hconst := hasDerivAt_const v (lrWKernel R 1)
  unfold lrFlowC lrFlowPW lrBVCDerivRaw
  simp only [mul_one]
  convert (hG.add (hconst.add hquot)).sub hcorr using 1
  simp only [id_eq, one_mul]
  field_simp [hv.1.ne', (by linarith [hv.1] : 1 + v ≠ 0)]
  ring

theorem hasDerivAt_lrFlowB_v_one
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ ↦ lrFlowB R x 1)
      (lrBVBDerivRaw R v) v := by
  have hsqrt := lrB_sqrt_mem_Ioo hR
  have hargVal : Real.sqrt R * v ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_pos hsqrt.1 hv.1]
    · nlinarith [mul_lt_mul_of_pos_right hsqrt.2 hv.1,
        mul_lt_mul_of_pos_left hv.2 hsqrt.1]
  have hplus : HasDerivAt (fun x : ℝ ↦ 1 + x) 1 v := by
    simpa using (hasDerivAt_id v).const_add 1
  have hlog := hplus.log (by linarith [hv.1] : 1 + v ≠ 0)
  have harg : HasDerivAt (fun x : ℝ ↦ Real.sqrt R * x)
      (Real.sqrt R) v := by
    simpa using (hasDerivAt_id v).const_mul (Real.sqrt R)
  have hL := (hasDerivAt_lrL (by
    nlinarith [hargVal.1, hargVal.2] : 1 - (Real.sqrt R * v) ^ 2 ≠ 0)).comp v harg
  unfold lrFlowB lrFlowBeta lrBVBDerivRaw
  simp only [mul_one]
  convert hlog.add hL using 1
  rw [show (Real.sqrt R * v) ^ 2 = R * v ^ 2 by
    rw [mul_pow, Real.sq_sqrt hR.1.le]]
  ring_nf
  rw [Real.sq_sqrt hR.1.le]
  ring

lemma lrBV_raw_deriv_eq_neg_bracket
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    lrBGamma R * lrBVCDerivRaw R v -
        (lrBVBDerivRaw R v * (1 - v) - lrFlowB R v 1) =
      -lrBVDerivativeBracket R v := by
  have hsqrt := lrB_sqrt_mem_Ioo hR
  have hvMem : v ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hv.1], hv.2⟩
  have hrvMem : Real.sqrt R * v ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_pos hsqrt.1 hv.1]
    · nlinarith [mul_lt_mul_of_pos_right hsqrt.2 hv.1,
        mul_lt_mul_of_pos_left hv.2 hsqrt.1]
  have hLv := mul_artanh_sub_topPhi_eq_lrL hvMem
  have hLRv := mul_artanh_sub_topPhi_eq_lrL hrvMem
  have hdenR : 1 - R * v ^ 2 ≠ 0 := by
    nlinarith [hrvMem.1, hrvMem.2, Real.sq_sqrt hR.1.le]
  unfold lrBVCDerivRaw lrBVBDerivRaw lrBVDerivativeBracket
    lrBScalarReserve lrBH lrFlowB lrFlowBeta lrBKernelK lrWKernel
  simp only [mul_one]
  rw [← hLv, ← hLRv]
  field_simp [hv.1.ne', hsqrt.1.ne', (by linarith [hv.1] : 1 + v ≠ 0), hdenR]
  ring_nf
  rw [Real.sq_sqrt hR.1.le]

theorem hasDerivAt_lrBComparisonReserve_v_one
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ ↦ lrBComparisonReserve R x 1)
      (-lrBVDerivativeBracket R v) v := by
  have hC := hasDerivAt_lrFlowC_v_one hR hv
  have hB := hasDerivAt_lrFlowB_v_one hR hv
  have hq : HasDerivAt (fun x : ℝ ↦ lrFlowQWeight x 1) (-1) v := by
    unfold lrFlowQWeight
    convert (hasDerivAt_const v 1).sub (hasDerivAt_id v) using 1
    · funext x
      simp [id_eq]
    · norm_num
  unfold lrBComparisonReserve
  convert (hC.const_mul (lrBGamma R)).sub (hB.mul hq) using 1
  rw [show lrFlowQWeight v 1 = 1 - v by simp [lrFlowQWeight]]
  rw [← lrBV_raw_deriv_eq_neg_bracket hR hv]
  ring

lemma lrBComparisonReserve_one_one (R : ℝ) :
    lrBComparisonReserve R 1 1 = 0 := by
  unfold lrBComparisonReserve lrFlowC lrFlowPW lrFlowQWeight
  simp only [lrGShape_one, topPhi_one]
  ring

theorem lrBComparisonReserve_at_one_nonneg
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrBComparisonReserve R v 1 := by
  have hanti : AntitoneOn (fun x : ℝ ↦ lrBComparisonReserve R x 1)
      (Icc v 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc v 1)
    · intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hv.1 hx.1
      have hxne : x ≠ 0 := hxpos.ne'
      have hplus : HasDerivAt (fun y : ℝ ↦ 1 + y) 1 x := by
        simpa using (hasDerivAt_id x).const_add 1
      have hlogPlus := hplus.log (by linarith [hxpos] : 1 + x ≠ 0)
      have hlogX := (hasDerivAt_id x).log hxne
      have hinv : ContinuousAt (fun y : ℝ ↦ 1 / y) x :=
        continuousAt_const.div continuousAt_id hxne
      have hlrG : ContinuousAt (fun y : ℝ ↦ lrG y) x := by
        unfold lrG
        exact ((continuousAt_const.add hinv).mul hlogPlus.continuousAt).sub
          hlogX.continuousAt
      have hphiDiv : ContinuousAt (fun y : ℝ ↦ topPhi y / y) x :=
        continuous_topPhi.continuousAt.div continuousAt_id hxne
      have hphiDiv' : ContinuousAt
          (fun y : ℝ ↦ topPhi (y * 1) / y) x := by
        simpa using hphiDiv
      have hG : ContinuousAt (fun y : ℝ ↦ lrGShape 1 y) x := by
        unfold lrGShape
        exact (hlrG.sub continuousAt_const).sub hphiDiv'
      have hsqrt := lrB_sqrt_mem_Ioo hR
      have hrx : Real.sqrt R * x ∈ Ioo (-1 : ℝ) 1 := by
        constructor
        · nlinarith [mul_pos hsqrt.1 hxpos]
        · exact lt_of_le_of_lt
            (mul_le_mul_of_nonneg_left hx.2 hsqrt.1.le) (by simpa using hsqrt.2)
      have hW := continuousAt_lrWKernel_z hrx
      have hWdiv : ContinuousAt (fun y : ℝ ↦ lrWKernel R y / y) x :=
        hW.div continuousAt_id hxne
      have hcorr : ContinuousAt
          (fun y : ℝ ↦ 4 * lrWKernel R 1 / (1 + y)) x := by
        exact continuousAt_const.div hplus.continuousAt (by linarith [hxpos])
      have hC : ContinuousAt (fun y : ℝ ↦ lrFlowC R y 1) x := by
        unfold lrFlowC lrFlowPW
        simp only [mul_one]
        exact (hG.add (continuousAt_const.add hWdiv)).sub hcorr
      have harg : HasDerivAt (fun y : ℝ ↦ Real.sqrt R * y)
          (Real.sqrt R) x := by
        simpa using (hasDerivAt_id x).const_mul (Real.sqrt R)
      have hL : ContinuousAt (fun y : ℝ ↦ lrL (Real.sqrt R * y)) x :=
        ((hasDerivAt_lrL (by
          nlinarith [hrx.1, hrx.2] : 1 - (Real.sqrt R * x) ^ 2 ≠ 0)).comp
          x harg).continuousAt
      have hB : ContinuousAt (fun y : ℝ ↦ lrFlowB R y 1) x := by
        unfold lrFlowB lrFlowBeta
        simp only [mul_one]
        exact hlogPlus.continuousAt.add hL
      have hq : ContinuousAt (fun y : ℝ ↦ lrFlowQWeight y 1) x := by
        unfold lrFlowQWeight
        fun_prop
      unfold lrBComparisonReserve
      have hreserve : ContinuousAt
          (fun y : ℝ ↦ lrBGamma R * lrFlowC R y 1 -
            lrFlowB R y 1 * lrFlowQWeight y 1) x :=
        (hC.const_mul (lrBGamma R)).sub (hB.mul hq)
      exact hreserve.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxPhysical : x ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_trans hv.1 hx.1, hx.2⟩
      exact (hasDerivAt_lrBComparisonReserve_v_one hR hxPhysical).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxPhysical : x ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_trans hv.1 hx.1, hx.2⟩
      rw [(hasDerivAt_lrBComparisonReserve_v_one hR hxPhysical).deriv]
      exact neg_nonpos.mpr (lrBVDerivativeBracket_nonneg hR
        (show x ∈ Ioc (0 : ℝ) 1 from ⟨hxPhysical.1, hxPhysical.2.le⟩))
  have h := hanti ⟨le_rfl, hv.2.le⟩ ⟨hv.2.le, le_rfl⟩ hv.2.le
  change lrBComparisonReserve R 1 1 ≤ lrBComparisonReserve R v 1 at h
  rw [lrBComparisonReserve_one_one] at h
  exact h

/-- The complete audited `B` comparison on the regular physical interior. -/
theorem lrBComparisonReserve_nonneg
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrBComparisonReserve R v t := by
  exact (lrBComparisonReserve_at_one_nonneg hR hv).trans
    (lrBComparisonReserve_ge_at_one hR hv ht)

end CourtadeKumar
