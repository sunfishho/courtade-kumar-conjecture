import InformationTheory.CourtadeKumar.AnalyticExtension.RadialBounds

/-! Cancellation of the radial restoration payment for the near-endpoint
half-midpoint. The positive-J hypothesis pays the change in the midpoint
weight, and the positive logarithmic entropy term pays the radial g0 term. -/
open Set
namespace CourtadeKumar.LRAnalyticMidpoint

lemma g0_weighted_lower {v : ℝ} (hv : 0 < v) :
    -((1 - v) ^ 2 / v) ≤ lrCertificateG0 v := by
  have hp : 0 < (1 + v) / 2 := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  have hscaled := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ 1 + 1 / v by positivity)
  have hid : (1 + 1 / v) * (1 - ((1 + v) / 2)⁻¹) =
      -(1 - v) / v := by
    field_simp [hv.ne', (by linarith : 1 + v ≠ 0)]
    ring
  rw [hid, Real.log_div (by linarith : 1 + v ≠ 0)
    (by norm_num : (2 : ℝ) ≠ 0)] at hscaled
  have hlogv := Real.log_le_sub_one_of_pos hv
  have hquot : -(1 - v) / v + (1 - v) = -((1 - v) ^ 2 / v) := by
    field_simp [hv.ne']
    ring
  rw [← hquot]
  unfold lrCertificateG0
  linarith

lemma e_upper {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    lrCertificateE p ≤ 2 / 5 := by
  have h := mul_le_mul_of_nonneg_left hk hi.1.1.le
  change p.s * p.k ≤ 2 / 5
  nlinarith

lemma v_lower {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    (3 / 4 : ℝ) ≤ lrCertificateV p := by
  have hv := lrCertificateV_mem_Ioo hi
  have he := e_upper hi hs hk
  have hsq := LRLowRatioAnalyticExtension.one_sub_v_sq_le_e hi
  nlinarith [hv.1]

lemma q0_lower {e : ℝ} (he : e ∈ Ioc (0 : ℝ) (2 / 5)) :
    (3 / 4 : ℝ) * e ≤ lrLowerFaceQ0 e := by
  have harg : (8 : ℝ) ≤ 4 / e := by
    rw [le_div_iff₀ he.1]
    linarith [he.2]
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 8) harg
  have heq : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [heq] at hlog
  have hl : 2 ≤ Real.log (4 / e) := by nlinarith [Real.log_two_gt_d9]
  have hmul := mul_le_mul_of_nonneg_left hl he.1.le
  unfold lrLowerFaceQ0
  nlinarith

/-- The positive q0 weight more than pays the adverse g0 correction. -/
lemma deltaG_nonnegative {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    0 ≤ lrSmallSBridgeQ0DeltaG p := by
  let v := lrCertificateV p
  let e := lrCertificateE p
  let d := 1 - v
  have hv : v ∈ Ioo (0 : ℝ) 1 := lrCertificateV_mem_Ioo hi
  have hvLo : (3 / 4 : ℝ) ≤ v := v_lower hi hs hk
  have he := e_upper hi hs hk
  have hq : (3 / 4 : ℝ) * e ≤ lrLowerFaceQ0 e := q0_lower ⟨hi.2.1.1, he⟩
  have hgeom := LRLowRatioAnalyticExtension.one_sub_v_sq_le_e hi
  have hd0 : 0 ≤ d := sub_nonneg.mpr hv.2.le
  have hg := g0_weighted_lower hv.1
  have hw : 0 ≤ 1 / v - 1 := by
    rw [sub_nonneg, one_le_div₀ hv.1]
    exact hv.2.le
  have hscaled := mul_le_mul_of_nonneg_right hq hw
  have hpay : (1 - v) ^ 2 / v ≤ (3 / 4 : ℝ) * e * (1 / v - 1) := by
    rw [div_le_iff₀ hv.1]
    have hid : ((3 / 4 : ℝ) * e * (1 / v - 1)) * v = (3 / 4 : ℝ) * e * d := by
      dsimp [d]
      field_simp [hv.1.ne']
    rw [hid]
    have hge : d * (1 + v) ≤ e := by dsimp [d, e, v]; nlinarith [hgeom]
    have hprod := mul_le_mul_of_nonneg_left hge hd0
    have hden := mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hvLo)
    change d ^ 2 ≤ 3 / 4 * e * d
    nlinarith
  unfold lrSmallSBridgeQ0DeltaG
  change 0 ≤ lrCertificateG0 v + lrLowerFaceQ0 e * (1 / v - 1)
  linarith

lemma deltaP_nonnegative {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    0 ≤ lrSmallSBridgeQ0DeltaP p := by
  have hv := lrCertificateV_mem_Ioo hi
  have hw : 0 ≤ 1 / lrCertificateV p - 1 := by
    rw [sub_nonneg, one_le_div₀ hv.1]
    exact hv.2.le
  exact mul_nonneg (lrLowerFaceOmegaQ0_nonneg hi.1 hi.2.1) hw

/-- The full midpoint weight correction has favorable sign when B ≥ D. -/
lemma channel_frozen_le {D B v x W G P dG dP : ℝ}
    (hv : 0 < v) (hv1 : v ≤ 1) (hx : x ≤ 1)
    (hD : 0 ≤ D) (hBD : D ≤ B) (hW : 0 ≤ W)
    (hG : 0 ≤ dG) (hP : 0 ≤ dP) :
    lrSmallSBridgeFrozenChannelReserve D B W G P ≤
      lrSmallSBridgeChannelReserve D B v x W (G + dG) (P + dP) := by
  let a := (1 - v) / (1 + v)
  have hp : 0 < 1 + v := by linarith
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hv1) hp.le
  have hB : 0 ≤ B := hD.trans hBD
  have hM : 0 ≤ v / (1 + v) := div_nonneg hv.le hp.le
  have hid : 1 - 2 * (v / (1 + v)) * x = a + 2 * (v / (1 + v)) * (1 - x) := by
    dsimp [a]
    field_simp [hp.ne']
    ring
  have h := lrSmallSBridgeChannelReserve_sub_frozen
    (D := D) (B := B) (x := x) (W := W) (G₀ := G) (P₀ := P)
    (deltaG := dG) (deltaP := dP) (a := a) (by linarith : v ≠ -1) rfl
  rw [hid] at h
  have h1 := mul_nonneg hD hG
  have h2 := mul_nonneg (add_nonneg hD hB) hP
  have h3 := mul_nonneg (mul_nonneg (sub_nonneg.mpr hBD) ha) hW
  have h4 := mul_nonneg (mul_nonneg (mul_nonneg hB hM) (sub_nonneg.mpr hx)) hW
  nlinarith

/-- No radial restoration payment is needed on the whole midpoint domain. -/
theorem q0_restoration {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hr : LRHighShapeVRelevant p) (hs : p.s ≤ 1 / 10) (hk : p.k ≤ 4) :
    lrSmallSBridgeFrozenChannelReserve (lrCertificateD p) (lrCertificateBFlow p)
      (lrLowerFaceOmegaQ0 p.s 0)
      (lrLowerFaceQ0 (lrCertificateY0 p) + lrLowerFaceQ0 (lrCertificateE p))
      (lrLowerFacePWQ0 p.s p.k p.chi 1) ≤
    lrSmallSBridgeChannelReserve (lrCertificateD p) (lrCertificateBFlow p)
      (lrCertificateV p) (lrCertificateX p) (lrLowerFaceOmegaQ0 p.s 0)
      (lrSmallSBridgeQ0G p) (lrLowerFacePWQ0 p.s p.k p.chi (lrCertificateV p)) := by
  have hv := lrCertificateV_mem_Ioo hi
  have hx : lrCertificateX p ≤ 1 := by
    exact sub_le_self _ (mul_nonneg hi.2.2.1.le hi.2.1.1.le)
  have hB := (lrCertificateBFlow_pos hi).le
  have hJ := hr.2
  have hBD : lrCertificateD p ≤ lrCertificateBFlow p := by
    unfold lrCertificateJ at hJ
    have hprod := mul_le_mul_of_nonneg_left hx hB
    linarith
  have hD := (lrDeterminantD1_nonnegative hi).trans (lrDeterminantD1_le_D hi)
  have hW : 0 ≤ lrLowerFaceOmegaQ0 p.s 0 := by
    rw [lrLowerFaceOmegaQ0_zero hi.1.1]
    exact div_nonneg hi.1.1.le (by norm_num)
  rw [lrSmallSBridgeQ0G_eq_frozen_add_delta, lrSmallSBridgePWQ0_eq_frozen_add_delta]
  exact channel_frozen_le hv.1 hv.2.le hx hD hBD hW
    (deltaG_nonnegative hi hs hk) (deltaP_nonnegative hi)

end CourtadeKumar.LRAnalyticMidpoint
