import InformationTheory.CourtadeKumar.LRNegativeChartBounds

/-! The quantitative midpoint-gap comparison `C >= g` in the negative LR chart. -/

open Set

namespace CourtadeKumar

noncomputable def lrFlowGapReserve (R v t : ℝ) : ℝ :=
  lrFlowC R v t - lrFlowGap R v t

lemma hasDerivAt_lrSquareTarget_t
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ ↦ lrSquareTarget R v x)
      (-Real.sqrt R * Real.artanh (Real.sqrt R * t) -
        Real.sqrt R * Real.artanh (Real.sqrt R * v * t)) t := by
  have hsqrt := lrB_sqrt_mem_Ioo hR
  have htArg : Real.sqrt R * t ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_pos hsqrt.1 ht.1]
    · nlinarith [mul_lt_mul_of_pos_right hsqrt.2 ht.1,
        mul_lt_mul_of_pos_left ht.2 hsqrt.1]
  have hvtArg : Real.sqrt R * v * t ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_pos (mul_pos hsqrt.1 hv.1) ht.1]
    · have hrv : Real.sqrt R * v < 1 := by
        nlinarith [mul_lt_mul_of_pos_right hsqrt.2 hv.1,
          mul_lt_mul_of_pos_left hv.2 hsqrt.1]
      calc
        Real.sqrt R * v * t < 1 * t := mul_lt_mul_of_pos_right hrv ht.1
        _ < 1 := by simpa using ht.2
  have htDeriv : HasDerivAt (fun x : ℝ ↦ Real.sqrt R * x)
      (Real.sqrt R) t := by
    simpa using (hasDerivAt_id t).const_mul (Real.sqrt R)
  have hvtDeriv : HasDerivAt (fun x : ℝ ↦ Real.sqrt R * v * x)
      (Real.sqrt R * v) t := by
    simpa using (hasDerivAt_id t).const_mul (Real.sqrt R * v)
  have hphiT := (hasDerivAt_topPhi htArg).comp t htDeriv
  have hphiVT := (hasDerivAt_topPhi hvtArg).comp t hvtDeriv
  have hconst := hasDerivAt_const t (lrG v)
  unfold lrSquareTarget lrGShape
  convert (hconst.sub hphiT).sub (hphiVT.const_mul (1 / v)) using 1
  · funext x
    simp only [Pi.sub_apply, Function.comp_apply]
    field_simp [hv.1.ne']
  · field_simp [hv.1.ne']
    ring

lemma hasDerivAt_lrFlowGap_t
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ ↦ lrFlowGap R v x)
      (-Real.sqrt R * Real.artanh (Real.sqrt R * t) -
        Real.sqrt R * Real.artanh (Real.sqrt R * v * t)) t := by
  unfold lrFlowGap
  simpa using (hasDerivAt_lrSquareTarget_t hR hv ht).sub_const
    (lrPrefixEll R (lrFlowM v))

lemma sqrt_mul_artanh_le_mul_lrBKernelK
    {R z : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    Real.sqrt R * Real.artanh (Real.sqrt R * z) ≤
      z * lrBKernelK R z := by
  have hsqrt := lrB_sqrt_mem_Ioo hR
  have hsqrtSq : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR.1.le
  have hden : 0 < 1 - R * z ^ 2 := by
    have hzSqPos : 0 < z ^ 2 := sq_pos_of_pos hz.1
    have hzSqLt : z ^ 2 < 1 := by nlinarith [hz.1, hz.2]
    have hmul : R * z ^ 2 < 1 := calc
      R * z ^ 2 < 1 * z ^ 2 := mul_lt_mul_of_pos_right hR.2 hzSqPos
      _ < 1 := by simpa using hzSqLt
    linarith
  have harg : Real.sqrt R * z ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hsqrt.1 hz.1
    · nlinarith [mul_lt_mul_of_pos_right hsqrt.2 hz.1,
        mul_lt_mul_of_pos_left hz.2 hsqrt.1]
  have hatanh : 0 ≤ Real.artanh (Real.sqrt R * z) :=
    (Real.artanh_pos harg).le
  have hfirst : 0 ≤
      (1 - R) / (2 * Real.sqrt R) * Real.artanh (Real.sqrt R * z) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hR.2.le)
      (mul_nonneg (by norm_num) hsqrt.1.le)) hatanh
  have hsecond : 0 ≤ (1 - R) * z / (2 * (1 - R * z ^ 2)) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hR.2.le) hz.1.le)
      (mul_nonneg (by norm_num) hden.le)
  have hid :
      z * lrBKernelK R z -
          Real.sqrt R * Real.artanh (Real.sqrt R * z) =
        (1 - R) / (2 * Real.sqrt R) *
            Real.artanh (Real.sqrt R * z) +
          (1 - R) * z / (2 * (1 - R * z ^ 2)) := by
    unfold lrBKernelK
    field_simp [hsqrt.1.ne', hz.1.ne', hden.ne']
    ring_nf
    rw [hsqrtSq]
    ring
  rw [← sub_nonneg, hid]
  positivity

theorem hasDerivAt_lrFlowGapReserve_t
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ ↦ lrFlowGapReserve R v x)
      (-t * (lrBKernelK R t + v * lrBKernelK R (v * t)) +
        Real.sqrt R * Real.artanh (Real.sqrt R * t) +
        Real.sqrt R * Real.artanh (Real.sqrt R * v * t)) t := by
  unfold lrFlowGapReserve
  convert (hasDerivAt_lrFlowC_t hR hv ht).sub
    (hasDerivAt_lrFlowGap_t hR hv ht) using 1 <;> ring

lemma lrFlowGapReserve_t_deriv_nonpos
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    -t * (lrBKernelK R t + v * lrBKernelK R (v * t)) +
        Real.sqrt R * Real.artanh (Real.sqrt R * t) +
        Real.sqrt R * Real.artanh (Real.sqrt R * v * t) ≤ 0 := by
  have hvt : v * t ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hv.1 ht.1
    · nlinarith [mul_lt_mul_of_pos_right hv.2 ht.1,
        mul_lt_mul_of_pos_left ht.2 hv.1]
  have htBound := sqrt_mul_artanh_le_mul_lrBKernelK hR ht
  have hvtBound := sqrt_mul_artanh_le_mul_lrBKernelK hR hvt
  rw [show Real.sqrt R * v * t = Real.sqrt R * (v * t) by ring]
  nlinarith

lemma lrWKernel_deriv_balance
    {R z : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    (Real.artanh z - z * lrBKernelK R z) * z - lrWKernel R z =
      lrL z - lrL (Real.sqrt R * z) -
        (1 - R) * z ^ 2 / (2 * (1 - R * z ^ 2)) := by
  have hsqrt := lrB_sqrt_mem_Ioo hR
  have hsqrtSq : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR.1.le
  have hzMem : z ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hz.1], hz.2⟩
  have hrhoz : Real.sqrt R * z ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_pos hsqrt.1 hz.1]
    · nlinarith [mul_lt_mul_of_pos_right hsqrt.2 hz.1,
        mul_lt_mul_of_pos_left hz.2 hsqrt.1]
  have hden : 1 - R * z ^ 2 ≠ 0 := by
    rw [show R * z ^ 2 = (Real.sqrt R * z) ^ 2 by
      rw [mul_pow, hsqrtSq]]
    nlinarith [hrhoz.1, hrhoz.2]
  have hLz := mul_artanh_sub_topPhi_eq_lrL hzMem
  have hLrho := mul_artanh_sub_topPhi_eq_lrL hrhoz
  rw [← hLz, ← hLrho]
  unfold lrBKernelK lrWKernel
  field_simp [hsqrt.1.ne', hz.1.ne', hden]
  ring_nf
  rw [hsqrtSq]

lemma hasDerivAt_lrFlowM {v : ℝ} (hv : v ≠ -1) :
    HasDerivAt lrFlowM (1 / (1 + v) ^ 2) v := by
  have hden : 1 + v ≠ 0 := by
    intro h
    apply hv
    linarith
  unfold lrFlowM
  convert (hasDerivAt_id v).div
      ((hasDerivAt_id v).const_add 1) hden using 1
  simp only [id_eq]
  field_simp [hden]
  ring

noncomputable def lrFlowGapVDerivRaw (R v : ℝ) : ℝ :=
  -(Real.log (1 + v) + lrL (Real.sqrt R * v)) / v ^ 2 -
    lrFlowEllDeriv R (lrFlowM v) / (1 + v) ^ 2

lemma hasDerivAt_lrFlowGap_v_one
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ ↦ lrFlowGap R x 1)
      (lrFlowGapVDerivRaw R v) v := by
  have hsqrt := lrB_sqrt_mem_Ioo hR
  have hshape : Real.sqrt R * v < 1 := by
    nlinarith [mul_lt_mul_of_pos_right hsqrt.2 hv.1,
      mul_lt_mul_of_pos_left hv.2 hsqrt.1]
  have hG := hasDerivAt_lrGShape hv.1 hsqrt.1.le hshape
  have hMmem : lrFlowM v ∈ Ioo (0 : ℝ) 1 := by
    have hM := lrFlowM_mem_Ioc (show v ∈ Ioc (0 : ℝ) 1 from
      ⟨hv.1, hv.2.le⟩)
    exact ⟨hM.1, hM.2.trans_lt (by norm_num)⟩
  have hM := hasDerivAt_lrFlowM (by linarith [hv.1])
  have hEll := (hasDerivAt_lrPrefixEll (R := R) hMmem).comp v hM
  unfold lrFlowGap lrSquareTarget lrFlowGapVDerivRaw
  simp only [mul_one]
  convert hG.sub hEll using 1
  ring

noncomputable def lrFlowGapReserveVDeriv (R v : ℝ) : ℝ :=
  -(1 - R) * Real.log (1 + v) / v ^ 2 -
    (1 - R) / (2 * (1 - R * v ^ 2)) +
    4 * (lrWKernel R 1 - (1 - R) * lrNormalizedEnergy R 1) /
      (1 + v) ^ 2

lemma lrFlowEllDeriv_at_lrFlowM
    {R v : ℝ} (hv : 0 < v) :
    lrFlowEllDeriv R (lrFlowM v) / (1 + v) ^ 2 =
      -(1 - R) * Real.log (1 + v) / v ^ 2 -
        4 * (R * Real.log 2 - topPhi (Real.sqrt R)) / (1 + v) ^ 2 := by
  have hvne : v ≠ 0 := hv.ne'
  have hplus : 1 + v ≠ 0 := by linarith
  have hone : 1 - lrFlowM v = (1 + v)⁻¹ := by
    unfold lrFlowM
    field_simp [hplus]
    ring
  unfold lrFlowEllDeriv
  rw [hone, Real.log_inv]
  unfold lrFlowM
  field_simp [hvne, hplus]

lemma one_sub_mul_normalizedEnergy_one
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    (1 - R) * lrNormalizedEnergy R 1 =
      R * Real.log 2 - topPhi (Real.sqrt R) := by
  have hs : 1 - R ≠ 0 := sub_ne_zero.mpr hR.2.ne'
  unfold lrNormalizedEnergy
  simp only [topPhi_one, mul_one]
  field_simp [hs]

lemma lrFlowGapReserve_v_raw_eq
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    lrBVCDerivRaw R v - lrFlowGapVDerivRaw R v =
      lrFlowGapReserveVDeriv R v := by
  have hbalance := lrWKernel_deriv_balance hR hv
  have hEll := lrFlowEllDeriv_at_lrFlowM (R := R) hv.1
  have henergy := one_sub_mul_normalizedEnergy_one hR
  have hplus : 1 + v ≠ 0 := by linarith [hv.1]
  have hRden : 1 - R * v ^ 2 ≠ 0 := by
    have hvSq : v ^ 2 < 1 := by nlinarith [hv.1, hv.2]
    have hmul : R * v ^ 2 < 1 := calc
      R * v ^ 2 < 1 * v ^ 2 :=
        mul_lt_mul_of_pos_right hR.2 (sq_pos_of_pos hv.1)
      _ < 1 := by simpa using hvSq
    linarith
  unfold lrBVCDerivRaw lrFlowGapVDerivRaw lrFlowGapReserveVDeriv
  rw [hbalance, hEll, henergy]
  field_simp [hv.1.ne', hplus, hRden]
  ring

theorem hasDerivAt_lrFlowGapReserve_v_one
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ ↦ lrFlowGapReserve R x 1)
      (lrFlowGapReserveVDeriv R v) v := by
  unfold lrFlowGapReserve
  convert (hasDerivAt_lrFlowC_v_one hR hv).sub
    (hasDerivAt_lrFlowGap_v_one hR hv) using 1
  exact (lrFlowGapReserve_v_raw_eq hR hv).symm

lemma sq_div_sq_le_log_one_add
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    v ^ 2 / (1 + v) ^ 2 ≤ Real.log (1 + v) := by
  have hplus : 0 < 1 + v := by linarith [hv.1]
  have hlog := Real.one_sub_inv_le_log_of_pos hplus
  have hratio : 1 - (1 + v)⁻¹ = v / (1 + v) := by
    field_simp [hplus.ne']
    ring
  have hunit : v / (1 + v) ≤ 1 := by
    rw [div_le_one hplus]
    linarith
  have hratioNonneg : 0 ≤ v / (1 + v) := div_nonneg hv.1.le hplus.le
  have hsquare : (v / (1 + v)) ^ 2 ≤ v / (1 + v) := by
    nlinarith [mul_nonneg hratioNonneg (sub_nonneg.mpr hunit)]
  rw [hratio] at hlog
  calc
    v ^ 2 / (1 + v) ^ 2 = (v / (1 + v)) ^ 2 := by
      field_simp [hplus.ne']
    _ ≤ v / (1 + v) := hsquare
    _ ≤ Real.log (1 + v) := hlog

lemma lrNormalizedEnergy_one_nonneg
    {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrNormalizedEnergy R 1 := by
  rw [lrNormalizedEnergy_eq_topEnergy_div hR.1.le]
  exact div_nonneg
    (topEnergy_nonneg
      (show Real.sqrt R ∈ Icc (0 : ℝ) 1 from
        ⟨Real.sqrt_nonneg R, (lrB_sqrt_mem_Ioo hR).2.le⟩)
      (show (1 : ℝ) ∈ Icc 0 1 by norm_num))
    (topS_nonneg
      (show Real.sqrt R ∈ Icc (0 : ℝ) 1 from
        ⟨Real.sqrt_nonneg R, (lrB_sqrt_mem_Ioo hR).2.le⟩))

lemma lrFlowGapReserve_v_deriv_nonpos
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioc (0 : ℝ) 1) :
    lrFlowGapReserveVDeriv R v ≤ 0 := by
  have hs : 0 < 1 - R := sub_pos.mpr hR.2
  have hvpos : 0 < v := hv.1
  have hplus : 0 < 1 + v := by linarith [hv.1]
  have hRden : 0 < 1 - R * v ^ 2 := by
    have hvSq : v ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
    have hmul : R * v ^ 2 ≤ R :=
      mul_le_of_le_one_right hR.1.le hvSq
    linarith [hR.2]
  have henergy := lrNormalizedEnergy_one_nonneg hR
  have hW := four_mul_lrWKernel_one_le_one_sub hR
  have hWE :
      4 * (lrWKernel R 1 - (1 - R) * lrNormalizedEnergy R 1) ≤ 1 - R := by
    nlinarith [mul_nonneg hs.le henergy]
  have hlast :
      4 * (lrWKernel R 1 - (1 - R) * lrNormalizedEnergy R 1) /
          (1 + v) ^ 2 ≤
        (1 - R) / (1 + v) ^ 2 := by
    exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hplus)).2 hWE
  have hlog := sq_div_sq_le_log_one_add hv
  have hfirst :
      (1 - R) / (1 + v) ^ 2 ≤
        (1 - R) * Real.log (1 + v) / v ^ 2 := by
    have hlogCross : v ^ 2 ≤ Real.log (1 + v) * (1 + v) ^ 2 :=
      (div_le_iff₀ (sq_pos_of_pos hplus)).mp hlog
    have hscaled := mul_le_mul_of_nonneg_left hlogCross hs.le
    rw [div_le_div_iff₀ (sq_pos_of_pos hplus) (sq_pos_of_pos hvpos)]
    nlinarith
  have hmiddle : 0 ≤ (1 - R) / (2 * (1 - R * v ^ 2)) := by positivity
  have hcancel := hlast.trans hfirst
  unfold lrFlowGapReserveVDeriv
  rw [show -(1 - R) * Real.log (1 + v) / v ^ 2 =
      -((1 - R) * Real.log (1 + v) / v ^ 2) by ring]
  linarith [hcancel]

lemma lrFlowGapReserve_one_one (R : ℝ) :
    lrFlowGapReserve R 1 1 = 0 := by
  unfold lrFlowGapReserve lrFlowC lrFlowGap lrSquareTarget lrFlowPW
    lrFlowM lrPrefixEll
  simp only [lrGShape_one, topPhi_one]
  norm_num [Real.binEntropy_two_inv]
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
    Real.binEntropy_two_inv]
  ring

theorem lrFlowGapReserve_at_one_nonneg
    {R v : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrFlowGapReserve R v 1 := by
  have hanti : AntitoneOn (fun x : ℝ ↦ lrFlowGapReserve R x 1)
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
      have hGOne : ContinuousAt (fun y : ℝ ↦ lrGShape 1 y) x := by
        unfold lrGShape
        simpa using (hlrG.sub continuousAt_const).sub hphiDiv
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
          (fun y : ℝ ↦ 4 * lrWKernel R 1 / (1 + y)) x :=
        continuousAt_const.div hplus.continuousAt (by linarith [hxpos])
      have hC : ContinuousAt (fun y : ℝ ↦ lrFlowC R y 1) x := by
        unfold lrFlowC lrFlowPW
        simp only [mul_one]
        exact (hGOne.add (continuousAt_const.add hWdiv)).sub hcorr
      have hshape : Real.sqrt R * x < 1 :=
        lt_of_le_of_lt
          (mul_le_mul_of_nonneg_left hx.2 hsqrt.1.le) (by simpa using hsqrt.2)
      have hGroot := (hasDerivAt_lrGShape hxpos hsqrt.1.le hshape).continuousAt
      have hM := hasDerivAt_lrFlowM (v := x) (by linarith [hxpos])
      have hMmem := lrFlowM_mem_Ioc
        (show x ∈ Ioc (0 : ℝ) 1 from ⟨hxpos, hx.2⟩)
      have hEll := (hasDerivAt_lrPrefixEll (R := R)
        (show lrFlowM x ∈ Ioo (0 : ℝ) 1 from
          ⟨hMmem.1, hMmem.2.trans_lt (by norm_num)⟩)).comp x hM
      have hgap : ContinuousAt (fun y : ℝ ↦ lrFlowGap R y 1) x := by
        unfold lrFlowGap lrSquareTarget
        simp only [mul_one]
        exact hGroot.sub hEll.continuousAt
      unfold lrFlowGapReserve
      exact (hC.sub hgap).continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxPhysical : x ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_trans hv.1 hx.1, hx.2⟩
      exact (hasDerivAt_lrFlowGapReserve_v_one hR hxPhysical).differentiableAt
        |>.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxPhysical : x ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_trans hv.1 hx.1, hx.2⟩
      rw [(hasDerivAt_lrFlowGapReserve_v_one hR hxPhysical).deriv]
      exact lrFlowGapReserve_v_deriv_nonpos hR
        (show x ∈ Ioc (0 : ℝ) 1 from ⟨hxPhysical.1, hxPhysical.2.le⟩)
  have h := hanti ⟨le_rfl, hv.2.le⟩ ⟨hv.2.le, le_rfl⟩ hv.2.le
  change lrFlowGapReserve R 1 1 ≤ lrFlowGapReserve R v 1 at h
  rw [lrFlowGapReserve_one_one] at h
  exact h

/-- The quantitative midpoint-gap comparison used in the negative chart. -/
theorem lrFlowGap_le_lrFlowC
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrFlowGap R v t ≤ lrFlowC R v t := by
  have hanti : AntitoneOn (lrFlowGapReserve R v) (Icc t 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc t 1)
    · intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le ht.1 hx.1
      have hsqrt := lrB_sqrt_mem_Ioo hR
      have hrx : Real.sqrt R * x ∈ Ioo (-1 : ℝ) 1 := by
        constructor
        · nlinarith [mul_pos hsqrt.1 hxpos]
        · exact lt_of_le_of_lt
            (mul_le_mul_of_nonneg_left hx.2 hsqrt.1.le) (by simpa using hsqrt.2)
      have hrvx : Real.sqrt R * (v * x) ∈ Ioo (-1 : ℝ) 1 := by
        constructor
        · nlinarith [mul_pos hsqrt.1 (mul_pos hv.1 hxpos)]
        · have hvx : v * x ≤ v * 1 :=
            mul_le_mul_of_nonneg_left hx.2 hv.1.le
          exact lt_of_le_of_lt
            (mul_le_mul_of_nonneg_left hvx hsqrt.1.le)
            (by
              have hrv : Real.sqrt R * v < 1 := by
                nlinarith [mul_lt_mul_of_pos_right hsqrt.2 hv.1,
                  mul_lt_mul_of_pos_left hv.2 hsqrt.1]
              simpa using hrv)
      have hW := continuousAt_lrWKernel_z hrx
      have hargV : ContinuousAt (fun y : ℝ ↦ v * y) x := by fun_prop
      have hWv := (continuousAt_lrWKernel_z hrvx).comp hargV
      have hG : ContinuousAt (fun y : ℝ ↦ lrGShape y v) x := by
        unfold lrGShape
        exact (continuousAt_const.sub continuous_topPhi.continuousAt).sub
          ((continuous_topPhi.continuousAt.comp hargV).div_const v)
      have hC : ContinuousAt (lrFlowC R v) x := by
        unfold lrFlowC lrFlowPW
        exact (hG.add (hW.add (hWv.div_const v))).sub continuousAt_const
      have hargRoot : ContinuousAt (fun y : ℝ ↦ Real.sqrt R * y) x := by
        fun_prop
      have hargRootV : ContinuousAt
          (fun y : ℝ ↦ v * (Real.sqrt R * y)) x := by fun_prop
      have hGroot : ContinuousAt
          (fun y : ℝ ↦ lrGShape (Real.sqrt R * y) v) x := by
        unfold lrGShape
        exact (continuousAt_const.sub
          (continuous_topPhi.continuousAt.comp hargRoot)).sub
          ((continuous_topPhi.continuousAt.comp hargRootV).div_const v)
      have hgap : ContinuousAt (lrFlowGap R v) x := by
        unfold lrFlowGap lrSquareTarget
        exact hGroot.sub continuousAt_const
      unfold lrFlowGapReserve
      exact (hC.sub hgap).continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxPhysical : x ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_trans ht.1 hx.1, hx.2⟩
      exact (hasDerivAt_lrFlowGapReserve_t hR hv hxPhysical).differentiableAt
        |>.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxPhysical : x ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_trans ht.1 hx.1, hx.2⟩
      rw [(hasDerivAt_lrFlowGapReserve_t hR hv hxPhysical).deriv]
      exact lrFlowGapReserve_t_deriv_nonpos hR hv hxPhysical
  have htOne := hanti ⟨le_rfl, ht.2.le⟩ ⟨ht.2.le, le_rfl⟩ ht.2.le
  have hAtOne := lrFlowGapReserve_at_one_nonneg hR hv
  unfold lrFlowGapReserve at htOne hAtOne
  linarith

end CourtadeKumar
