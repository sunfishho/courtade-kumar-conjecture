import InformationTheory.CourtadeKumar.LRPrefixPhysicality

/-! Exact differential identities for the audited LR target-root flow. -/

open Set

namespace CourtadeKumar

/-- The manuscript's normalized channel energy `E_rho(z) / (1-R)`. -/
noncomputable def lrNormalizedEnergy (R z : ℝ) : ℝ :=
  (R * topPhi z - topPhi (Real.sqrt R * z)) / (1 - R)

/-- The scaled `R`-derivative kernel of the normalized channel energy. -/
noncomputable def lrWKernel (R z : ℝ) : ℝ :=
  topPhi z - topPhi (Real.sqrt R * z) -
    (1 - R) * z / (2 * Real.sqrt R) *
      Real.artanh (Real.sqrt R * z)

lemma lrNormalizedEnergy_eq_topEnergy_div
    {R z : ℝ} (hR : 0 ≤ R) :
    lrNormalizedEnergy R z =
      topEnergy (Real.sqrt R) z / topS (Real.sqrt R) := by
  have hsqrt : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR
  unfold lrNormalizedEnergy topEnergy topS topR
  rw [hsqrt]

/-- Equation (lr-W-def): `W_R(z) = (1-R)^2 ∂_R Ebar_R(z)`. -/
theorem hasDerivAt_lrNormalizedEnergy
    {R z : ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun y : ℝ ↦ lrNormalizedEnergy y z)
      (lrWKernel R z / (1 - R) ^ 2) R := by
  have hsqrt := Real.hasDerivAt_sqrt hR.1.ne'
  have hsqrtPos := Real.sqrt_pos.2 hR.1
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have harg : HasDerivAt (fun y : ℝ ↦ Real.sqrt y * z)
      (z / (2 * Real.sqrt R)) R := by
    convert hsqrt.mul_const z using 1
    field_simp [hsqrtPos.ne']
  have hargMem : Real.sqrt R * z ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [hsqrtPos, hz.1]
    · calc
        Real.sqrt R * z ≤ Real.sqrt R * 1 :=
          mul_le_mul_of_nonneg_left hz.2 hsqrtPos.le
        _ < 1 := by simpa using hsqrtLt
  have hphiArg := (hasDerivAt_topPhi hargMem).comp R harg
  have hlinear := (hasDerivAt_id R).mul_const (topPhi z)
  have hnum := hlinear.sub hphiArg
  have hden := (hasDerivAt_const R 1).sub (hasDerivAt_id R)
  have hdenNe : 1 - R ≠ 0 := sub_ne_zero.mpr hR.2.ne'
  unfold lrNormalizedEnergy lrWKernel
  convert hnum.div hden hdenNe using 1
  simp only [id_eq, Pi.sub_apply, Function.comp_apply]
  field_simp [hsqrtPos.ne', hdenNe]
  ring

noncomputable def lrNormalizedEnergyZDeriv (R z : ℝ) : ℝ :=
  (R * Real.artanh z -
    Real.sqrt R * Real.artanh (Real.sqrt R * z)) / (1 - R)

theorem hasDerivAt_lrNormalizedEnergy_comp
    {R z z' : ℝ} {zfun : ℝ → ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (-1 : ℝ) 1)
    (hrhoz : Real.sqrt R * z ∈ Ioo (-1 : ℝ) 1)
    (hzval : zfun R = z)
    (hzfun : HasDerivAt zfun z' R) :
    HasDerivAt (fun y : ℝ ↦ lrNormalizedEnergy y (zfun y))
      (lrWKernel R z / (1 - R) ^ 2 +
        lrNormalizedEnergyZDeriv R z * z') R := by
  have hsqrt := Real.hasDerivAt_sqrt hR.1.ne'
  have hsqrtPos := Real.sqrt_pos.2 hR.1
  have hzActual : zfun R ∈ Ioo (-1 : ℝ) 1 := by simpa [hzval] using hz
  have hphiZ := (hasDerivAt_topPhi hzActual).comp R hzfun
  have hlinear := (hasDerivAt_id R).mul hphiZ
  have harg := hsqrt.mul hzfun
  have hrhozActual : Real.sqrt R * zfun R ∈ Ioo (-1 : ℝ) 1 := by
    simpa [hzval] using hrhoz
  have hphiArg := (hasDerivAt_topPhi hrhozActual).comp R harg
  have hnum := hlinear.sub hphiArg
  have hden := (hasDerivAt_const R 1).sub (hasDerivAt_id R)
  have hdenNe : 1 - R ≠ 0 := sub_ne_zero.mpr hR.2.ne'
  unfold lrNormalizedEnergy lrNormalizedEnergyZDeriv lrWKernel
  convert hnum.div hden hdenNe using 1
  simp only [id_eq, Pi.sub_apply, Pi.mul_apply, Function.comp_apply, hzval]
  field_simp [hsqrtPos.ne', hdenNe]
  ring

noncomputable def lrPhiPerspective (v t : ℝ) : ℝ :=
  topPhi (v * t) / v

theorem hasDerivAt_lrPhiPerspective
    {v t : ℝ} (hv : 0 < v) (ht : 0 ≤ t) (hvt : v * t < 1) :
    HasDerivAt (fun q : ℝ ↦ lrPhiPerspective q t)
      (lrL (v * t) / v ^ 2) v := by
  have harg : HasDerivAt (fun q : ℝ ↦ q * t) t v :=
    by simpa only [id_eq, one_mul] using (hasDerivAt_id v).mul_const t
  have hvtMem : v * t ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by nlinarith [hv, ht], hvt⟩
  have hphi := (hasDerivAt_topPhi hvtMem).comp v harg
  have hquot := hphi.div (hasDerivAt_id v) hv.ne'
  unfold lrPhiPerspective
  convert hquot using 1
  simp only [id_eq, Function.comp_apply]
  rw [← mul_artanh_sub_topPhi_eq_lrL hvtMem]
  field_simp [hv.ne']

noncomputable def lrFlowBeta (v : ℝ) : ℝ := Real.log (1 + v)

noncomputable def lrFlowA (v t : ℝ) : ℝ :=
  lrFlowBeta v + lrL (v * t)

noncomputable def lrFlowB (R v t : ℝ) : ℝ :=
  lrFlowBeta v + lrL (Real.sqrt R * v * t)

lemma lrFlowB_pos
    {R v t : ℝ}
    (hv : 0 < v) (ht : 0 ≤ t)
    (hshape : Real.sqrt R * v * t < 1) :
    0 < lrFlowB R v t := by
  have hlog : 0 < Real.log (1 + v) := Real.log_pos (by linarith)
  have hshape0 : 0 ≤ Real.sqrt R * v * t := by positivity
  have hL := lrL_nonneg hshape0 hshape
  unfold lrFlowB lrFlowBeta
  linarith

noncomputable def lrFlowD (R v t : ℝ) : ℝ :=
  lrFlowA v t - lrFlowB R v t

noncomputable def lrFlowPW (R v t : ℝ) : ℝ :=
  lrWKernel R t + lrWKernel R (v * t) / v

noncomputable def lrFlowP (u : ℝ) : ℝ := u / (1 + u)

noncomputable def lrFlowNumerator (R u v t : ℝ) : ℝ :=
  lrFlowD R v t * lrGShape t v +
    lrFlowA v t * lrFlowPW R v t -
      4 * lrWKernel R 1 *
        ((1 - lrFlowP u) * lrFlowD R v t +
          lrFlowP u * t ^ 2 * lrFlowB R v t)

/-- The `Q-kappa` reserve written in squared channel coordinates. -/
noncomputable def lrQSquare (R u v t : ℝ) : ℝ :=
  1 / t ^ 2 *
      (lrPhiPerspective v t - lrPhiPerspective u t) +
    1 / t ^ 2 *
      (lrNormalizedEnergy R t +
        lrNormalizedEnergy R (v * t) / v)

noncomputable def lrSquareReserve (R u v t : ℝ) : ℝ :=
  lrQSquare R u v t -
    4 * lrNormalizedEnergy R 1 * u / (1 + u)

lemma lrSquareReserve_eq_lrReserve
    {R u v t : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    lrSquareReserve R u v t =
      lrReserve (Real.sqrt R) u v t := by
  have hsqrt : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.1.le
  have hs : 1 - R ≠ 0 := sub_ne_zero.mpr hR.2.ne'
  unfold lrSquareReserve lrQSquare lrPhiPerspective lrNormalizedEnergy
    lrReserve lrQClosed lrKappa lrMu topEnergy topS topR
  rw [hsqrt, topPhi_one]
  field_simp [hs]

/-- Differentiating the squared-coordinate `Q` along an arbitrary regular
root curve produces the `D` and `P_W` terms of the manuscript. -/
theorem hasDerivAt_lrQSquare_comp
    {R u v v' t : ℝ} {vfun : ℝ → ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (hv : 0 < v) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hvt : v * t < 1)
    (hvval : vfun R = v)
    (hvfun : HasDerivAt vfun v' R) :
    HasDerivAt (fun y : ℝ ↦ lrQSquare y u (vfun y) t)
      (lrFlowD R v t * v' / ((1 - R) * v ^ 2 * t ^ 2) +
        lrFlowPW R v t / ((1 - R) ^ 2 * t ^ 2)) R := by
  have hsqrtPos := Real.sqrt_pos.2 hR.1
  have hsqrtLt : Real.sqrt R < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hvtMem : v * t ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by nlinarith [mul_pos hv ht.1], hvt⟩
  have hrhovtLt : Real.sqrt R * (v * t) < 1 := by
    calc
      Real.sqrt R * (v * t) < 1 * (v * t) :=
        mul_lt_mul_of_pos_right hsqrtLt (mul_pos hv ht.1)
      _ < 1 := by simpa using hvt
  have hrhovtMem : Real.sqrt R * (v * t) ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by nlinarith [mul_pos hsqrtPos (mul_pos hv ht.1)], hrhovtLt⟩
  have hperspBase := hasDerivAt_lrPhiPerspective
    (v := vfun R) (by simpa [hvval] using hv) ht.1.le
    (by simpa [hvval] using hvt)
  have hpersp := hperspBase.comp R hvfun
  have hpersp' : HasDerivAt
      (fun y : ℝ ↦ lrPhiPerspective (vfun y) t)
      (lrL (v * t) / v ^ 2 * v') R := by
    simpa only [Function.comp_apply, hvval] using hpersp
  have hperspDiff := hpersp'.sub_const (lrPhiPerspective u t)
  have hfixed := hasDerivAt_lrNormalizedEnergy hR ⟨ht.1.le, ht.2.le⟩
  have hzfun : HasDerivAt (fun y : ℝ ↦ vfun y * t) (v' * t) R := by
    simpa only [one_mul] using hvfun.mul_const t
  have hzval : vfun R * t = v * t := by rw [hvval]
  have hvariable := hasDerivAt_lrNormalizedEnergy_comp hR hvtMem
    hrhovtMem hzval hzfun
  have hquot := hvariable.div hvfun (by simpa [hvval] using hv.ne')
  have hquot' : HasDerivAt
      (fun y : ℝ ↦ lrNormalizedEnergy y (vfun y * t) / vfun y)
      (((lrWKernel R (v * t) / (1 - R) ^ 2 +
          lrNormalizedEnergyZDeriv R (v * t) * (v' * t)) * v -
        lrNormalizedEnergy R (v * t) * v') / v ^ 2) R := by
    simpa only [hvval] using hquot
  have henergy := hfixed.add hquot'
  have hfirst := hperspDiff.const_mul (1 / t ^ 2)
  have hsecond := henergy.const_mul (1 / t ^ 2)
  have htotal := hfirst.add hsecond
  unfold lrQSquare
  convert htotal using 1
  have hsqrtSq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.1.le
  have hs : 1 - R ≠ 0 := sub_ne_zero.mpr hR.2.ne'
  have hLvt := mul_artanh_sub_topPhi_eq_lrL hvtMem
  have hLrho := mul_artanh_sub_topPhi_eq_lrL hrhovtMem
  unfold lrFlowD lrFlowA lrFlowB lrFlowPW lrFlowBeta
    lrNormalizedEnergyZDeriv lrNormalizedEnergy lrWKernel
  rw [show Real.sqrt R * v * t = Real.sqrt R * (v * t) by ring]
  rw [← hLvt, ← hLrho]
  field_simp [hs, hv.ne', ht.1.ne']
  nlinarith [hsqrtSq]

theorem hasDerivAt_lrSquareReserve_comp
    {R u v v' t : ℝ} {vfun : ℝ → ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (hu : u ≠ -1)
    (hv : 0 < v) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hvt : v * t < 1)
    (hvval : vfun R = v)
    (hvfun : HasDerivAt vfun v' R) :
    HasDerivAt (fun y : ℝ ↦ lrSquareReserve y u (vfun y) t)
      (lrFlowD R v t * v' / ((1 - R) * v ^ 2 * t ^ 2) +
        lrFlowPW R v t / ((1 - R) ^ 2 * t ^ 2) -
          4 * lrWKernel R 1 * lrFlowP u / (1 - R) ^ 2) R := by
  have hq := hasDerivAt_lrQSquare_comp (u := u) hR hv ht hvt hvval hvfun
  have hE1 := hasDerivAt_lrNormalizedEnergy hR
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  have hcorr := (hE1.const_mul 4 |>.mul_const u).div_const (1 + u)
  have h := hq.sub hcorr
  unfold lrSquareReserve lrFlowP
  convert h using 1
  have huDen : 1 + u ≠ 0 := by
    intro hzero
    apply hu
    linear_combination hzero
  field_simp [huDen]

/-- The implicit target-root velocity, in the simplified exact form used
inside the flow cancellation. -/
noncomputable def lrTargetRootVelocity (R u v t : ℝ) : ℝ :=
  v ^ 2 / (lrFlowB R v t * (1 - R)) *
    (lrGShape t v + lrFlowPW R v t -
      4 * lrWKernel R 1 / (1 + u))

/-- The derivative obtained by differentiating `Q-kappa` and substituting
the target-root velocity, before the final cancellation. -/
noncomputable def lrReserveFlowDeriv (R u v t : ℝ) : ℝ :=
  lrFlowD R v t * lrTargetRootVelocity R u v t /
      ((1 - R) * v ^ 2 * t ^ 2) +
    lrFlowPW R v t / ((1 - R) ^ 2 * t ^ 2) -
      4 * lrWKernel R 1 * lrFlowP u / (1 - R) ^ 2

theorem hasDerivAt_lrSquareReserve_targetFlow
    {R u v t : ℝ} {vfun : ℝ → ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1)
    (hu : u ≠ -1)
    (hv : 0 < v) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hvt : v * t < 1)
    (hvval : vfun R = v)
    (hvfun : HasDerivAt vfun (lrTargetRootVelocity R u v t) R) :
    HasDerivAt (fun y : ℝ ↦ lrSquareReserve y u (vfun y) t)
      (lrReserveFlowDeriv R u v t) R := by
  simpa [lrReserveFlowDeriv] using
    hasDerivAt_lrSquareReserve_comp hR hu hv ht hvt hvval hvfun

/-- Equation (lr-exact-flow), as an exact algebraic cancellation after
implicit differentiation. -/
theorem lr_exact_flow_identity
    {R u v t : ℝ}
    (hR : R ≠ 1) (hu : u ≠ -1) (hv : v ≠ 0) (ht : t ≠ 0)
    (hB : lrFlowB R v t ≠ 0) :
    lrFlowB R v t * (1 - R) ^ 2 * t ^ 2 *
        lrReserveFlowDeriv R u v t =
      lrFlowNumerator R u v t := by
  unfold lrReserveFlowDeriv lrTargetRootVelocity lrFlowNumerator lrFlowP
    lrFlowD
  have hs : 1 - R ≠ 0 := sub_ne_zero.mpr hR.symm
  have huDen : 1 + u ≠ 0 := by
    intro h
    apply hu
    linear_combination h
  field_simp [hs, huDen, hv, ht, hB]
  ring

lemma lrReserve_zeroChannel_sameRoot
    {u t : ℝ} (hu : u ≠ 0) (ht : t ≠ 0) :
    lrReserve 0 u u t = 0 := by
  unfold lrReserve lrQClosed lrKappa lrMu topEnergy topS topR
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero,
    zero_mul, topPhi_zero, zero_div]
  field_simp [hu, ht]
  ring

end CourtadeKumar
