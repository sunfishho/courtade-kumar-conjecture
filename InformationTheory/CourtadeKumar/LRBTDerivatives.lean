import InformationTheory.CourtadeKumar.LRBTComparison

/-! Exact derivatives and `t`-monotonicity for the LR `B` comparison. -/

open Set

namespace CourtadeKumar

theorem hasDerivAt_lrL
    {z : ℝ} (hz : 1 - z ^ 2 ≠ 0) :
    HasDerivAt lrL (z / (1 - z ^ 2)) z := by
  have hsq : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * z) z := by
    convert (hasDerivAt_id z).pow 2 using 1
    norm_num
  have harg := (hasDerivAt_const z 1).sub hsq
  have hlog := harg.log hz
  have h := hlog.const_mul (-(1 / 2 : ℝ))
  unfold lrL
  convert h using 1
  simp only [Pi.sub_apply]
  field_simp [hz]
  ring

/-- The derivative cancellation `W'_R(z) = atanh(z) - z K_R(z)`. -/
theorem hasDerivAt_lrWKernel_z
    {R z : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (lrWKernel R)
      (Real.artanh z - z * lrBKernelK R z) z := by
  have hsqrt := lrB_sqrt_mem_Ioo hR
  have hrhoz : Real.sqrt R * z ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_pos hsqrt.1 hz.1]
    · nlinarith [mul_lt_mul_of_pos_right hsqrt.2 hz.1,
        mul_lt_mul_of_pos_left hz.2 hsqrt.1]
  have harg : HasDerivAt (fun x : ℝ ↦ Real.sqrt R * x)
      (Real.sqrt R) z := by
    simpa using (hasDerivAt_id z).const_mul (Real.sqrt R)
  have hphiZ := hasDerivAt_topPhi
    (show z ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [hz.1], hz.2⟩)
  have hphiRZ := (hasDerivAt_topPhi hrhoz).comp z harg
  have hatanhRZ := (hasDerivAt_artanh hrhoz).comp z harg
  have hzatanh : HasDerivAt
      (fun x : ℝ ↦ x * Real.artanh (Real.sqrt R * x))
      (Real.artanh (Real.sqrt R * z) +
        z * (1 / (1 - (Real.sqrt R * z) ^ 2) * Real.sqrt R)) z := by
    convert (hasDerivAt_id z).mul hatanhRZ using 1
    simp only [id_eq, Function.comp_apply, one_mul]
  have hthird := hzatanh.const_mul ((1 - R) / (2 * Real.sqrt R))
  have h := (hphiZ.sub hphiRZ).sub hthird
  have hden : 1 - (Real.sqrt R * z) ^ 2 ≠ 0 := by
    nlinarith [hrhoz.1, hrhoz.2]
  have hRden : 1 - R * z ^ 2 ≠ 0 := by
    rw [show R * z ^ 2 = (Real.sqrt R * z) ^ 2 by
      rw [mul_pow, Real.sq_sqrt hR.1.le]]
    exact hden
  unfold lrWKernel lrBKernelK
  convert h using 1
  · funext x
    simp only [Pi.sub_apply, Function.comp_apply]
    ring
  · dsimp only [Function.comp_apply]
    rw [show (Real.sqrt R * z) ^ 2 = R * z ^ 2 by
      rw [mul_pow, Real.sq_sqrt hR.1.le]]
    field_simp [hsqrt.1.ne', hz.1.ne', hRden]
    ring_nf
    rw [Real.sq_sqrt hR.1.le]
    ring

lemma continuousAt_lrWKernel_z
    {R z : ℝ} (hz : Real.sqrt R * z ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt (lrWKernel R) z := by
  have harg : ContinuousAt (fun x : ℝ ↦ Real.sqrt R * x) z := by
    fun_prop
  have hphi : ContinuousAt (fun x : ℝ ↦ topPhi (Real.sqrt R * x)) z :=
    continuous_topPhi.continuousAt.comp harg
  have hartanh : ContinuousAt
      (fun x : ℝ ↦ Real.artanh (Real.sqrt R * x)) z :=
    (hasDerivAt_artanh hz).continuousAt.comp harg
  have hcoef : ContinuousAt
      (fun x : ℝ ↦ (1 - R) * x / (2 * Real.sqrt R)) z := by
    fun_prop
  unfold lrWKernel
  exact (continuous_topPhi.continuousAt.sub hphi).sub (hcoef.mul hartanh)

/-- The flow quantity `C` differentiates to the two scalar kernels. -/
theorem hasDerivAt_lrFlowC_t
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ ↦ lrFlowC R v x)
      (-t * (lrBKernelK R t + v * lrBKernelK R (v * t))) t := by
  have hvt : v * t ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos hv.1 ht.1
    · nlinarith [mul_lt_mul_of_pos_right hv.2 ht.1,
        mul_lt_mul_of_pos_left ht.2 hv.1]
  have htMem : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  have hvtMem : v * t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hvt.1], hvt.2⟩
  have harg : HasDerivAt (fun x : ℝ ↦ v * x) v t := by
    simpa using (hasDerivAt_id t).const_mul v
  have hG : HasDerivAt (fun x : ℝ ↦ lrGShape x v)
      (-Real.artanh t - Real.artanh (v * t)) t := by
    have hphiT := hasDerivAt_topPhi htMem
    have hphiVT := (hasDerivAt_topPhi hvtMem).comp t harg
    have hquot := hphiVT.const_mul (1 / v)
    have hconst := hasDerivAt_const t (lrG v)
    unfold lrGShape
    convert (hconst.sub hphiT).sub hquot using 1
    · funext x
      simp only [Pi.sub_apply, Function.comp_apply]
      field_simp [hv.1.ne']
    · dsimp only [Function.comp_apply]
      field_simp [hv.1.ne']
      ring
  have hWt := hasDerivAt_lrWKernel_z hR ht
  have hWvt := (hasDerivAt_lrWKernel_z hR hvt).comp t harg
  have hPW : HasDerivAt (fun x : ℝ ↦ lrFlowPW R v x)
      ((Real.artanh t - t * lrBKernelK R t) +
        (Real.artanh (v * t) - (v * t) * lrBKernelK R (v * t))) t := by
    unfold lrFlowPW
    convert hWt.add (hWvt.const_mul (1 / v)) using 1
    · funext x
      simp only [Pi.add_apply, Function.comp_apply]
      field_simp [hv.1.ne']
    · dsimp only [Function.comp_apply]
      field_simp [hv.1.ne']
  have hconst := hasDerivAt_const t (4 * lrWKernel R 1 / (1 + v))
  unfold lrFlowC
  convert (hG.add hPW).sub hconst using 1
  ring

/-- Exact equation `(lr-B-t-derivative)` without division by `t`. -/
theorem hasDerivAt_lrBComparisonReserve_t
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ ↦ lrBComparisonReserve R v x)
      (-t * lrBTDerivativeBracket R v t) t := by
  have hsqrt := lrB_sqrt_mem_Ioo hR
  have hargVal : Real.sqrt R * v * t ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_pos (mul_pos hsqrt.1 hv.1) ht.1]
    · have hrv : Real.sqrt R * v < 1 := by
        nlinarith [mul_lt_mul_of_pos_right hsqrt.2 hv.1,
          mul_lt_mul_of_pos_left hv.2 hsqrt.1]
      nlinarith [mul_lt_mul_of_pos_right hrv ht.1, ht.2]
  have harg : HasDerivAt (fun x : ℝ ↦ Real.sqrt R * v * x)
      (Real.sqrt R * v) t := by
    simpa using (hasDerivAt_id t).const_mul (Real.sqrt R * v)
  have hL := (hasDerivAt_lrL (by
    nlinarith [hargVal.1, hargVal.2] : 1 - (Real.sqrt R * v * t) ^ 2 ≠ 0)).comp t harg
  have hB : HasDerivAt (fun x : ℝ ↦ lrFlowB R v x)
      (R * v ^ 2 * t / (1 - R * v ^ 2 * t ^ 2)) t := by
    have hconst := hasDerivAt_const t (lrFlowBeta v)
    unfold lrFlowB
    convert hconst.add hL using 1
    rw [show (Real.sqrt R * v * t) ^ 2 = R * v ^ 2 * t ^ 2 by
      rw [mul_pow, mul_pow, Real.sq_sqrt hR.1.le]]
    ring_nf
    rw [Real.sq_sqrt hR.1.le]
    ring
  have hq : HasDerivAt (fun x : ℝ ↦ lrFlowQWeight v x)
      (-(1 + v) * t) t := by
    unfold lrFlowQWeight
    convert (hasDerivAt_const t (1 - v)).add
      (((hasDerivAt_const t 1).sub ((hasDerivAt_id t).pow 2)).const_mul
        ((1 + v) / 2)) using 1
    simp only [id_eq]
    ring
  have hC := hasDerivAt_lrFlowC_t hR hv ht
  unfold lrBComparisonReserve
  convert (hC.const_mul (lrBGamma R)).sub (hB.mul hq) using 1
  unfold lrBTDerivativeBracket lrFlowB lrFlowBeta
  ring

/-- For fixed `R,v`, the comparison reserve decreases as `t` moves to one. -/
theorem lrBComparisonReserve_ge_at_one
    {R v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    lrBComparisonReserve R v 1 ≤ lrBComparisonReserve R v t := by
  have hanti : AntitoneOn (lrBComparisonReserve R v) (Icc t 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc t 1)
    · intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le ht.1 hx.1
      have hsqrt := lrB_sqrt_mem_Ioo hR
      have hsx : Real.sqrt R * x ∈ Ioo (-1 : ℝ) 1 := by
        constructor
        · nlinarith [mul_pos hsqrt.1 hxpos]
        · calc
            Real.sqrt R * x ≤ Real.sqrt R * 1 :=
              mul_le_mul_of_nonneg_left hx.2 hsqrt.1.le
            _ < 1 := by simpa using hsqrt.2
      have hsvx : Real.sqrt R * (v * x) ∈ Ioo (-1 : ℝ) 1 := by
        constructor
        · nlinarith [mul_pos hsqrt.1 (mul_pos hv.1 hxpos)]
        · have hvx : v * x ≤ 1 := by
            nlinarith [mul_le_mul hv.2.le hx.2 (by linarith [hxpos])
              (by norm_num : (0 : ℝ) ≤ 1)]
          exact lt_of_le_of_lt
            (mul_le_mul_of_nonneg_left hvx hsqrt.1.le) (by simpa using hsqrt.2)
      have hWt := continuousAt_lrWKernel_z hsx
      have hargV : ContinuousAt (fun y : ℝ ↦ v * y) x := by fun_prop
      have hWvt : ContinuousAt (fun y : ℝ ↦ lrWKernel R (v * y)) x :=
        (continuousAt_lrWKernel_z hsvx).comp hargV
      have hG : ContinuousAt (fun y : ℝ ↦ lrGShape y v) x := by
        unfold lrGShape
        exact (continuousAt_const.sub continuous_topPhi.continuousAt).sub
          ((continuous_topPhi.continuousAt.comp hargV).div_const v)
      have hC : ContinuousAt (fun y : ℝ ↦ lrFlowC R v y) x := by
        unfold lrFlowC lrFlowPW
        fun_prop
      have hargB : HasDerivAt (fun y : ℝ ↦ Real.sqrt R * v * y)
          (Real.sqrt R * v) x := by
        simpa using (hasDerivAt_id x).const_mul (Real.sqrt R * v)
      have hL : ContinuousAt
          (fun y : ℝ ↦ lrL (Real.sqrt R * v * y)) x :=
        ((hasDerivAt_lrL (by
          have hsvx' : Real.sqrt R * v * x ∈ Ioo (-1 : ℝ) 1 := by
            simpa [mul_assoc] using hsvx
          nlinarith [hsvx'.1, hsvx'.2] :
            1 - (Real.sqrt R * v * x) ^ 2 ≠ 0)).comp x hargB).continuousAt
      have hB : ContinuousAt (fun y : ℝ ↦ lrFlowB R v y) x := by
        unfold lrFlowB
        fun_prop
      have hq : ContinuousAt (fun y : ℝ ↦ lrFlowQWeight v y) x := by
        unfold lrFlowQWeight
        fun_prop
      unfold lrBComparisonReserve
      have hreserve : ContinuousAt
          (fun y : ℝ ↦ lrBGamma R * lrFlowC R v y -
            lrFlowB R v y * lrFlowQWeight v y) x :=
        (hC.const_mul (lrBGamma R)).sub (hB.mul hq)
      exact hreserve.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxPhysical : x ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_trans ht.1 hx.1, hx.2⟩
      exact (hasDerivAt_lrBComparisonReserve_t hR hv hxPhysical).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxPhysical : x ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_trans ht.1 hx.1, hx.2⟩
      rw [(hasDerivAt_lrBComparisonReserve_t hR hv hxPhysical).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hxPhysical.1.le)
        (lrBTDerivativeBracket_nonneg hR
          (show v ∈ Ioc (0 : ℝ) 1 from ⟨hv.1, hv.2.le⟩)
          (show x ∈ Ioc (0 : ℝ) 1 from ⟨hxPhysical.1, hxPhysical.2.le⟩))
  exact hanti ⟨le_rfl, ht.2.le⟩ ⟨ht.2.le, le_rfl⟩ ht.2.le

end CourtadeKumar
