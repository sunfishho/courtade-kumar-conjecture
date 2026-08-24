import InformationTheory.CourtadeKumar.TopCapComparison
import InformationTheory.CourtadeKumar.CapClosure

/-! The normalized corrected TOP reserve and its exact relation to the
manuscript's channel coordinates. -/

open Set

namespace CourtadeKumar

/-- The perspective quotient `Q(c,q)` in the normalized reserve. -/
noncomputable def topNormalizedQ (c q : ℝ) : ℝ :=
  topPerspectiveTerm c (Real.sqrt q) / (c * q)

/-- The positive density whose integral from `c` to `1` is `Q(c,q)`. -/
noncomputable def topChannelP (c q : ℝ) : ℝ :=
  -Real.log (1 - q * (c / (2 - c)) ^ 2) / (2 * q * c ^ 2)

/-- The channel coefficient `w(R) = (R log 2 - Phi(sqrt R))/(1-R)`. -/
noncomputable def topChannelW (R : ℝ) : ℝ :=
  (R * Real.log 2 - topPhi (Real.sqrt R)) / (1 - R)

/-- The normalized energy term `k(R,q)`. -/
noncomputable def topChannelK (R q : ℝ) : ℝ :=
  (R * topPhi (Real.sqrt q) -
      topPhi (Real.sqrt R * Real.sqrt q)) / ((1 - R) * q)

/-- The normalized corrected reserve with `(R,q)` held fixed. -/
noncomputable def topChannelH (R c q : ℝ) : ℝ :=
  topNormalizedQ c q - c * topChannelW R + topChannelK R q

/-- Multiplying the normalized reserve by its positive scale recovers the
corrected TOP reserve exactly. -/
theorem topReserve_eq_scale_mul_topChannelH
    {R c q : ℝ} (hR0 : 0 ≤ R) (hq0 : 0 ≤ q)
    (hR1 : R ≠ 1) (hc : c ≠ 0) (hq : q ≠ 0) :
    topReserve (Real.sqrt R) c (Real.sqrt q) =
      (1 - R) * c * q * topChannelH R c q := by
  have hsqrtR : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR0
  have hsqrtq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0
  have hs : 1 - R ≠ 0 := sub_ne_zero.mpr hR1.symm
  unfold topReserve topS topEll topEnergy topChannelH
    topNormalizedQ topChannelW topChannelK
  simp only [topR, hsqrtR, hsqrtq]
  field_simp [hs, hc, hq]
  ring

theorem topReserve_eq_scale_mul_topChannelH_sqCoordinates
    {rho c r : ℝ} (hrho : rho ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) :
    topReserve rho c r =
      topS rho * c * r ^ 2 * topChannelH (rho ^ 2) c (r ^ 2) := by
  have hrhoSqNe : rho ^ 2 ≠ 1 := by nlinarith [hrho.1, hrho.2]
  have h := topReserve_eq_scale_mul_topChannelH
    (R := rho ^ 2) (c := c) (q := r ^ 2)
    (sq_nonneg rho) (sq_nonneg r) hrhoSqNe hc (pow_ne_zero 2 hr.1.ne')
  simpa [topS, topR, Real.sqrt_sq_eq_abs, abs_of_pos hrho.1,
    abs_of_pos hr.1] using h

lemma topPhi_eq_mul_artanh_add_log {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    topPhi x =
      x * Real.artanh x + Real.log (1 - x ^ 2) / 2 := by
  have hp : 0 < 1 + x := by linarith [hx.1]
  have hm : 0 < 1 - x := by linarith [hx.2]
  rw [topPhi_eq_log_formula hx]
  rw [Real.artanh_eq_half_log ⟨hx.1.le, hx.2.le⟩]
  rw [Real.log_div hp.ne' hm.ne']
  rw [show 1 - x ^ 2 = (1 + x) * (1 - x) by ring,
    Real.log_mul hp.ne' hm.ne']
  ring

/-- Exact differentiation of the perspective quotient. -/
theorem hasDerivAt_topNormalizedQ {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun u : ℝ ↦ topNormalizedQ u q) (-topChannelP c q) c := by
  let r := Real.sqrt q
  let x := c * r / (2 - c)
  have hr0 : 0 < r := by simpa [r] using Real.sqrt_pos.2 hq.1
  have hrsq : r ^ 2 = q := by simpa [r] using Real.sq_sqrt hq.1.le
  have hr1 : r < 1 := by
    dsimp [r]
    simpa using (Real.sqrt_lt_sqrt_iff hq.1.le).2 hq.2
  have htwo : 2 - c ≠ 0 := by linarith [hc.2]
  have hx0 : 0 < x := by
    dsimp [x]
    exact div_pos (mul_pos hc.1 hr0) (by linarith [hc.2])
  have hx1 : x < 1 := by
    dsimp [x]
    rw [div_lt_one (by linarith [hc.2] : 0 < 2 - c)]
    have hcr : c * r < c := by
      simpa using mul_lt_mul_of_pos_left hr1 hc.1
    linarith [hc.2]
  have hx : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hx1⟩
  have harg0 := ((hasDerivAt_id c).mul_const r).div
    ((hasDerivAt_const c 2).sub (hasDerivAt_id c)) htwo
  have harg : HasDerivAt (fun u : ℝ ↦ u * r / (2 - u))
      (2 * r / (2 - c) ^ 2) c := by
    convert harg0 using 1
    simp only [id_eq, Pi.sub_apply]
    field_simp [htwo]
    ring
  have hphiArg := (hasDerivAt_topPhi hx).comp c harg
  have hleft := ((hasDerivAt_id c).div_const 2).mul_const (topPhi r)
  have hwidth := ((hasDerivAt_const c 2).sub (hasDerivAt_id c)).div_const 2
  have hright := hwidth.mul hphiArg
  have hperspective := hleft.sub hright
  have hden := (hasDerivAt_id c).mul_const q
  have hquot := hperspective.div hden (mul_ne_zero hc.1.ne' hq.1.ne')
  have hphiX := topPhi_eq_mul_artanh_add_log hx
  convert hquot using 1
  · unfold topChannelP
    simp only [id_eq, Pi.sub_apply, Function.comp_apply]
    dsimp [x] at hphiX ⊢
    rw [hphiX]
    field_simp [hc.1.ne', hq.1.ne', htwo]
    rw [hrsq]
    ring

lemma topChannelP_pos {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    0 < topChannelP c q := by
  have htwo : 0 < 2 - c := by linarith [hc.2]
  have ht0 : 0 < c / (2 - c) := div_pos hc.1 htwo
  have ht1 : c / (2 - c) < 1 := by
    rw [div_lt_one htwo]
    linarith [hc.2]
  have ht2 : (c / (2 - c)) ^ 2 < 1 := by nlinarith
  have hprod : q * (c / (2 - c)) ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hq.2) (sub_pos.mpr ht2)]
  have hden : 0 < 1 - q * (c / (2 - c)) ^ 2 := by linarith
  have hlt : 1 - q * (c / (2 - c)) ^ 2 < 1 := by
    nlinarith [mul_pos hq.1 (sq_pos_of_pos ht0)]
  have hlog := Real.log_neg hden hlt
  unfold topChannelP
  exact div_pos (neg_pos.mpr hlog)
    (mul_pos (mul_pos (by norm_num) hq.1) (sq_pos_of_pos hc.1))

lemma topChannelW_nonneg {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    0 ≤ topChannelW R := by
  have hsqrt0 : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
  have hsqrt1 : Real.sqrt R ≤ 1 := by
    simpa using (Real.sqrt_le_one.mpr hR.2.le)
  have hell := topEll_nonneg (show Real.sqrt R ∈ Icc (0 : ℝ) 1 from
    ⟨hsqrt0, hsqrt1⟩)
  unfold topChannelW
  apply div_nonneg
  · simpa [topEll, topR, Real.sq_sqrt hR.1.le] using hell
  · exact sub_nonneg.mpr hR.2.le

/-- With `(R,q)` fixed, the normalized corrected reserve has the simple
strictly negative derivative stated in the manuscript. -/
theorem hasDerivAt_topChannelH {R c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun u : ℝ ↦ topChannelH R u q)
      (-topChannelP c q - topChannelW R) c := by
  have hQ := hasDerivAt_topNormalizedQ hc hq
  have hlinear := (hasDerivAt_id c).mul_const (topChannelW R)
  have hconstant := hasDerivAt_const c (topChannelK R q)
  unfold topChannelH
  convert (hQ.sub hlinear).add hconstant using 1 <;> ring

theorem topChannelH_strictAntiOn {R q : ℝ}
    (hR : R ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (fun c : ℝ ↦ topChannelH R c q) (Ioo (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo (0 : ℝ) 1)
  · intro c hc
    exact (hasDerivAt_topChannelH hc hq).continuousAt.continuousWithinAt
  · intro c hc
    rw [(hasDerivAt_topChannelH (by simpa using hc) hq).deriv]
    have hp := topChannelP_pos (by simpa using hc) hq
    have hw := topChannelW_nonneg hR
    linarith

lemma balancedCap_mem_Ioo_strict {rho r : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    balancedCap rho r ∈ Ioo (0 : ℝ) 1 := by
  have hden := balancedCapDen_pos hrho hr
  have hr2lt : r ^ 2 < 1 := by nlinarith [hr.1, hr.2]
  have hgap : 0 < rho ^ 2 * (1 - r ^ 2) :=
    mul_pos (sq_pos_of_pos hrho.1) (sub_pos.mpr hr2lt)
  have hslt : topS rho < balancedCapDen rho r := by
    unfold topS topR balancedCapDen
    nlinarith
  have hratio : topS rho / balancedCapDen rho r < 1 :=
    (div_lt_one hden).2 hslt
  have hsq := balancedCap_sq hrho hr
  exact ⟨balancedCap_pos hrho hr, by
    nlinarith [sq_nonneg (balancedCap rho r - 1)]⟩

/-- The already verified balanced-root cap and fixed-channel monotonicity
transfer any cap lower bound to the actual corrected entropy root. -/
theorem topChannelH_balancedRoot_ge_cap
    {rho r c : ℝ}
    (hrho : rho ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hroot : balancedResidual rho c r = 0) :
    topChannelH (rho ^ 2) (balancedCap rho r) (r ^ 2) ≤
      topChannelH (rho ^ 2) c (r ^ 2) := by
  have hR : rho ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith [hrho.1, hrho.2]
  have hq : r ^ 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith [hr.1, hr.2]
  have hcap := balancedCap_mem_Ioo_strict hrho hr
  have hsq := balancedRoot_sq_le_capRatio hrho hr
    ⟨hc.1.le, hc.2.le⟩ hroot
  rw [← balancedCap_sq hrho hr] at hsq
  have hle : c ≤ balancedCap rho r := by
    nlinarith [hc.1, balancedCap_pos hrho hr]
  exact (topChannelH_strictAntiOn hR hq).antitoneOn hc hcap hle

/-- The logarithmic cross-ratio appearing in the full-tail comparison. -/
noncomputable def topCapCrossRatio (c q : ℝ) : ℝ :=
  (1 - c ^ 2 * q) / (1 - q * (c / (2 - c)) ^ 2)

lemma topCapCrossRatio_den_pos {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    0 < 1 - q * (c / (2 - c)) ^ 2 := by
  have htwo : 0 < 2 - c := by linarith [hc.2]
  have ht0 : 0 < c / (2 - c) := div_pos hc.1 htwo
  have ht1 : c / (2 - c) < 1 := by
    rw [div_lt_one htwo]
    linarith [hc.2]
  have ht2 : (c / (2 - c)) ^ 2 < 1 := by nlinarith
  have hprod : q * (c / (2 - c)) ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hq.2) (sub_pos.mpr ht2)]
  linarith

lemma topCapCrossRatio_pos {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    0 < topCapCrossRatio c q := by
  exact div_pos (topCapDen_pos hc hq) (topCapCrossRatio_den_pos hc hq)

/-- The rational cross-ratio already verified by the finite certificate is
exactly the analytic cap cross-ratio. -/
theorem topCertX_capCoordinates {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    topCertX c (topCapZeta c q) = topCapCrossRatio c q := by
  have hcapDen := topCapDen_pos hc hq
  have htwo : 2 - c ≠ 0 := by linarith [hc.2]
  have hcrossDen := topCapCrossRatio_den_pos hc hq
  have hz := topCapZeta_mem_Ioo hc hq
  have hcertDen : topCertD c + topCertB c (topCapZeta c q) ≠ 0 :=
    (add_pos (topCertD_pos hc) (topCertB_pos hc hz)).ne'
  unfold topCertX topCapCrossRatio
  rw [div_eq_div_iff hcertDen hcrossDen.ne']
  unfold topCertD topCertB topCapZeta topCapR
  field_simp [hcapDen.ne', htwo]
  ring

/-- The certificate lower expression in cap coordinates, with its
logarithmic factor displayed in the manuscript's analytic form. -/
theorem topCapJLower_eq_crossRatio {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    topCapJLower c q =
      topChannelW (topCapR c q) +
        Real.log (topCapCrossRatio c q) / (2 * c ^ 2 * q) +
          topCapETail c (topCapZeta c q) := by
  unfold topCapJLower topChannelW
  dsimp only
  rw [topCertX_capCoordinates hc hq]

end CourtadeKumar
