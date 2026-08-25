import InformationTheory.CourtadeKumar.LRFlow

open Set

namespace CourtadeKumar

noncomputable def lrRawTargetVelocity (R u v t : ℝ) : ℝ :=
  v ^ 2 / lrFlowB R v t *
    (lrG u - 4 * (Real.log 2 - topPsiDeriv R) / (1 + u) -
      t / (2 * Real.sqrt R) *
        (Real.artanh (Real.sqrt R * t) +
          Real.artanh (Real.sqrt R * v * t)))

lemma lrRawTargetVelocity_eq_target
    {R u v t : ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (hu : 0 < u) (hv : 0 < v)
    (hB : lrFlowB R v t ≠ 0)
    (hroot : lrGShape (Real.sqrt R * t) v =
      lrObjectiveTarget (Real.sqrt R) u) :
    lrRawTargetVelocity R u v t = lrTargetRootVelocity R u v t := by
  have hsqrtPos := Real.sqrt_pos.2 hR.1
  have hsqrtSq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.1.le
  have hs : 1 - R ≠ 0 := sub_ne_zero.mpr hR.2.ne'
  have huDen : 1 + u ≠ 0 := by positivity
  unfold lrRawTargetVelocity lrTargetRootVelocity
  rw [show v ^ 2 / (lrFlowB R v t * (1 - R)) *
        (lrGShape t v + lrFlowPW R v t -
          4 * lrWKernel R 1 / (1 + u)) =
      v ^ 2 / lrFlowB R v t *
        ((lrGShape t v + lrFlowPW R v t -
          4 * lrWKernel R 1 / (1 + u)) / (1 - R)) by
    field_simp [hB, hs]]
  apply congrArg (fun z : ℝ ↦ v ^ 2 / lrFlowB R v t * z)
  unfold lrFlowPW lrWKernel topPsiDeriv lrGShape
  unfold lrGShape lrObjectiveTarget lrMu topEnergy topS topR at hroot
  rw [hsqrtSq, topPhi_one] at hroot
  rw [topPhi_one]
  field_simp [hsqrtPos.ne', hs, huDen] at hroot ⊢
  linear_combination -(2 * Real.sqrt R) * hroot

noncomputable def lrSquareObjective (R u : ℝ) : ℝ :=
  (1 - R) * lrG u +
    4 * (R * Real.log 2 - topPhi (Real.sqrt R)) / (1 + u)

lemma lrSquareObjective_eq
    {R u : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    lrSquareObjective R u = lrObjectiveTarget (Real.sqrt R) u := by
  have hsqrtSq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.1.le
  have hs : 1 - R ≠ 0 := sub_ne_zero.mpr hR.2.ne'
  unfold lrSquareObjective lrObjectiveTarget lrMu topEnergy topS topR
  rw [hsqrtSq, topPhi_one]
  field_simp [hs]

theorem hasDerivAt_lrSquareObjective
    {R u : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y : ℝ ↦ lrSquareObjective y u)
      (-lrG u + 4 * (Real.log 2 - topPsiDeriv R) / (1 + u)) R := by
  have hfirst := ((hasDerivAt_const R 1).sub (hasDerivAt_id R)).mul_const
    (lrG u)
  have hnum := ((hasDerivAt_id R).mul_const (Real.log 2)).sub
    (hasDerivAt_topPsi hR)
  have hsecond := (hnum.const_mul 4).div_const (1 + u)
  unfold lrSquareObjective
  convert hfirst.add hsecond using 1
  ring

noncomputable def lrSquareTarget (R v t : ℝ) : ℝ :=
  lrGShape (Real.sqrt R * t) v

theorem hasDerivAt_lrSquareTarget_comp
    {R v v' t : ℝ} {vfun : ℝ → ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : 0 < v) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hvt : v * t < 1)
    (hvval : vfun R = v)
    (hvfun : HasDerivAt vfun v' R) :
    HasDerivAt (fun y : ℝ ↦ lrSquareTarget y (vfun y) t)
      (-lrFlowB R v t / v ^ 2 * v' -
        t / (2 * Real.sqrt R) *
          (Real.artanh (Real.sqrt R * t) +
            Real.artanh (Real.sqrt R * v * t))) R := by
  have hsqrt := Real.hasDerivAt_sqrt hR.1.ne'
  have hsqrtPos := Real.sqrt_pos.2 hR.1
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hvActual : 0 < vfun R := by simpa [hvval] using hv
  have hG := (hasDerivAt_lrG hvActual).comp R hvfun
  have ha : HasDerivAt (fun y : ℝ ↦ Real.sqrt y * t)
      (t / (2 * Real.sqrt R)) R := by
    convert hsqrt.mul_const t using 1
    field_simp [hsqrtPos.ne']
  have haVal : Real.sqrt R * t ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_pos hsqrtPos ht.1]
    · calc
        Real.sqrt R * t < 1 * t := mul_lt_mul_of_pos_right hsqrtLt ht.1
        _ < 1 := by simpa using ht.2
  have hphiA := (hasDerivAt_topPhi haVal).comp R ha
  have havLt : Real.sqrt R * v * t < 1 := by
    rw [mul_assoc]
    calc
      Real.sqrt R * (v * t) < 1 * (v * t) :=
        mul_lt_mul_of_pos_right hsqrtLt (mul_pos hv ht.1)
      _ < 1 := by simpa using hvt
  have havVal : Real.sqrt R * v * t ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by nlinarith [mul_pos hsqrtPos (mul_pos hv ht.1)], havLt⟩
  have havDeriv := ha.mul hvfun
  have havActual :
      (fun y : ℝ ↦ Real.sqrt y * t) R * vfun R =
        Real.sqrt R * v * t := by rw [hvval]; ring
  have havMem :
      (fun y : ℝ ↦ Real.sqrt y * t) R * vfun R ∈
        Ioo (-1 : ℝ) 1 := by simpa [havActual] using havVal
  have hphiAV := (hasDerivAt_topPhi havMem).comp R havDeriv
  have hquot := hphiAV.div hvfun hvActual.ne'
  have h := (hG.sub hphiA).sub hquot
  unfold lrSquareTarget lrGShape lrFlowB lrFlowBeta
  convert h using 1
  · funext y
    simp only [Function.comp_apply, Pi.sub_apply, Pi.div_apply, Pi.mul_apply]
    rw [mul_comm (vfun y) (Real.sqrt y * t)]
  · simp only [Function.comp_apply, Pi.mul_apply, hvval]
    have hL := mul_artanh_sub_topPhi_eq_lrL havVal
    have hassoc : Real.sqrt R * v * t = Real.sqrt R * (v * t) := by ring
    have hcomm : Real.sqrt R * t * v = Real.sqrt R * (v * t) := by ring
    rw [hassoc] at hL
    rw [hassoc, hcomm]
    rw [← hL]
    field_simp [hsqrtPos.ne', hv.ne']
    ring

/-- Implicit differentiation of the target equation gives exactly the
velocity displayed in the audited flow proof. -/
theorem hasDerivAt_targetRootVelocity
    {R u v v' t : ℝ} {vfun : ℝ → ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (hu : 0 < u) (hv : 0 < v)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hvt : v * t < 1)
    (hvval : vfun R = v)
    (hvfun : HasDerivAt vfun v' R)
    (hroot : lrGShape (Real.sqrt R * t) v =
      lrObjectiveTarget (Real.sqrt R) u)
    (hcurve : (fun y : ℝ ↦ lrSquareTarget y (vfun y) t) =ᶠ[nhds R]
      (fun y : ℝ ↦ lrSquareObjective y u)) :
    HasDerivAt vfun (lrTargetRootVelocity R u v t) R := by
  have hleft := hasDerivAt_lrSquareTarget_comp
    hR hv ht hvt hvval hvfun
  have hright := hasDerivAt_lrSquareObjective (u := u) hR
  have hrightLeft := hright.congr_of_eventuallyEq hcurve
  have hderivEq := hleft.unique hrightLeft
  have hsqrtPos := Real.sqrt_pos.2 hR.1
  have hshape : Real.sqrt R * v * t < 1 := by
    have hsqrtLt : Real.sqrt R < 1 := by
      simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
    rw [mul_assoc]
    calc
      Real.sqrt R * (v * t) < 1 * (v * t) :=
        mul_lt_mul_of_pos_right hsqrtLt (mul_pos hv ht.1)
      _ < 1 := by simpa using hvt
  have hBpos := lrFlowB_pos hv ht.1.le hshape
  have hvRaw : v' = lrRawTargetVelocity R u v t := by
    unfold lrRawTargetVelocity
    rw [div_mul_eq_mul_div, eq_div_iff hBpos.ne']
    have huDen : 1 + u ≠ 0 := by positivity
    field_simp [hv.ne', hsqrtPos.ne', huDen] at hderivEq ⊢
    linear_combination -hderivEq
  have hrawTarget := lrRawTargetVelocity_eq_target
    hR hu hv hBpos.ne' hroot
  exact hvfun.congr_deriv (hvRaw.trans hrawTarget)

/-- The boxed flow identity as a derivative theorem for an actual regular
target-root trajectory. -/
theorem hasDerivAt_lrReserve_exactFlow
    {R u v v' t : ℝ} {vfun : ℝ → ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (hu : 0 < u) (hv : 0 < v)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hvt : v * t < 1)
    (hvval : vfun R = v)
    (hvfun : HasDerivAt vfun v' R)
    (hroot : lrGShape (Real.sqrt R * t) v =
      lrObjectiveTarget (Real.sqrt R) u)
    (hcurve : (fun y : ℝ ↦ lrSquareTarget y (vfun y) t) =ᶠ[nhds R]
      (fun y : ℝ ↦ lrSquareObjective y u)) :
    HasDerivAt (fun y : ℝ ↦ lrSquareReserve y u (vfun y) t)
      (lrFlowNumerator R u v t /
        (lrFlowB R v t * (1 - R) ^ 2 * t ^ 2)) R := by
  have hvTarget := hasDerivAt_targetRootVelocity
    hR hu hv ht hvt hvval hvfun hroot hcurve
  have hreserve := hasDerivAt_lrSquareReserve_targetFlow
    hR (by linarith [hu] : u ≠ -1) hv ht hvt hvval hvTarget
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hshape : Real.sqrt R * v * t < 1 := by
    rw [mul_assoc]
    calc
      Real.sqrt R * (v * t) < 1 * (v * t) :=
        mul_lt_mul_of_pos_right hsqrtLt (mul_pos hv ht.1)
      _ < 1 := by simpa using hvt
  have hBpos := lrFlowB_pos hv ht.1.le hshape
  have hfactor : lrFlowB R v t * (1 - R) ^ 2 * t ^ 2 ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero hBpos.ne'
        (pow_ne_zero 2 (sub_ne_zero.mpr hR.2.ne')))
      (pow_ne_zero 2 ht.1.ne')
  have hid := lr_exact_flow_identity hR.2.ne
    (by linarith [hu] : u ≠ -1) hv.ne' ht.1.ne' hBpos.ne'
  have hderiv : lrReserveFlowDeriv R u v t =
      lrFlowNumerator R u v t /
        (lrFlowB R v t * (1 - R) ^ 2 * t ^ 2) := by
    apply (eq_div_iff hfactor).2
    simpa [mul_comm] using hid
  exact hreserve.congr_deriv hderiv

end CourtadeKumar
