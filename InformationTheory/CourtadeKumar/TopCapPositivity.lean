import InformationTheory.CourtadeKumar.TopDerivativeComparison

/-! Integration of the certified derivative margin from the cap endpoint. -/

open Set

namespace CourtadeKumar

lemma topCapDen_pos_Icc_right {c q u : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Icc c 1) :
    0 < 1 - u ^ 2 * q := by
  have hu0 : 0 < u := hc.1.trans_le hu.1
  have huSq : u ^ 2 ≤ 1 := by nlinarith [hu.2]
  have hmul : 0 ≤ q * (1 - u ^ 2) :=
    mul_nonneg hq.1.le (sub_nonneg.mpr huSq)
  nlinarith [hq.2]

lemma one_sub_topCapR_pos_Icc_right {c q u : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Icc c 1) :
    0 < 1 - topCapR u q := by
  have hu0 : 0 < u := hc.1.trans_le hu.1
  have hden := topCapDen_pos_Icc_right hc hq hu
  have hid : 1 - topCapR u q =
      u ^ 2 * (1 - q) / (1 - u ^ 2 * q) := by
    unfold topCapR
    field_simp [hden.ne']
    ring
  rw [hid]
  exact div_pos
    (mul_pos (sq_pos_of_pos hu0) (sub_pos.mpr hq.2)) hden

theorem continuousOn_topCapH_Icc_right {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun u : ℝ ↦ topCapH u q) (Icc c 1) := by
  intro u hu
  have hu0 : 0 < u := hc.1.trans_le hu.1
  have htwo : 2 - u ≠ 0 := by linarith [hu.2]
  have hcapDen := topCapDen_pos_Icc_right hc hq hu
  have hs := one_sub_topCapR_pos_Icc_right hc hq hu
  have hRcont : ContinuousAt (fun v : ℝ ↦ topCapR v q) u := by
    unfold topCapR
    exact (continuousAt_const.sub (continuousAt_id.pow 2)).div
      (continuousAt_const.sub ((continuousAt_id.pow 2).mul_const q)) hcapDen.ne'
  have hsqrtRcont : ContinuousAt (fun v : ℝ ↦ Real.sqrt (topCapR v q)) u :=
    Real.continuous_sqrt.continuousAt.comp hRcont
  have hphiRcont : ContinuousAt
      (fun v : ℝ ↦ topPhi (Real.sqrt (topCapR v q))) u :=
    continuous_topPhi.continuousAt.comp hsqrtRcont
  have hWcont : ContinuousAt
      (fun v : ℝ ↦ topChannelW (topCapR v q)) u := by
    unfold topChannelW
    exact ((hRcont.mul_const (Real.log 2)).sub hphiRcont).div
      (continuousAt_const.sub hRcont) hs.ne'
  have harg : ContinuousAt
      (fun v : ℝ ↦ v * Real.sqrt q / (2 - v)) u := by
    exact (continuousAt_id.mul_const (Real.sqrt q)).div
      (continuousAt_const.sub continuousAt_id) htwo
  have hphiArg : ContinuousAt
      (fun v : ℝ ↦ topPhi (v * Real.sqrt q / (2 - v))) u :=
    continuous_topPhi.continuousAt.comp harg
  have hpersp : ContinuousAt
      (fun v : ℝ ↦ topPerspectiveTerm v (Real.sqrt q)) u := by
    unfold topPerspectiveTerm
    exact ((continuousAt_id.div_const 2).mul_const (topPhi (Real.sqrt q))).sub
      (((continuousAt_const.sub continuousAt_id).div_const 2).mul hphiArg)
  have hQcont : ContinuousAt (fun v : ℝ ↦ topNormalizedQ v q) u := by
    unfold topNormalizedQ
    exact hpersp.div (continuousAt_id.mul_const q)
      (mul_ne_zero hu0.ne' hq.1.ne')
  have henergyArg : ContinuousAt
      (fun v : ℝ ↦ Real.sqrt (topCapR v q) * Real.sqrt q) u :=
    hsqrtRcont.mul_const (Real.sqrt q)
  have hphiEnergy : ContinuousAt
      (fun v : ℝ ↦ topPhi (Real.sqrt (topCapR v q) * Real.sqrt q)) u :=
    continuous_topPhi.continuousAt.comp henergyArg
  have hKcont : ContinuousAt
      (fun v : ℝ ↦ topChannelK (topCapR v q) q) u := by
    unfold topChannelK
    exact ((hRcont.mul_const (topPhi (Real.sqrt q))).sub hphiEnergy).div
      ((continuousAt_const.sub hRcont).mul_const q)
      (mul_ne_zero hs.ne' hq.1.ne')
  unfold topCapH topChannelH
  exact (hQcont.sub (continuousAt_id.mul hWcont)).add hKcont |>.continuousWithinAt

noncomputable def topCapMarginGap (c q : ℝ) : ℝ :=
  topCapH c q - (1 - c) / 100

lemma hasDerivAt_topCapMarginGap {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun u : ℝ ↦ topCapMarginGap u q)
      (-topCapJ c q + (1 : ℝ) / 100) c := by
  have hlinear := ((hasDerivAt_const c 1).sub (hasDerivAt_id c)).div_const 100
  unfold topCapMarginGap
  convert (hasDerivAt_topCapH hc hq).sub hlinear using 1 <;> ring

/-- Quantitative cap positivity obtained by integrating the audited
derivative margin from the endpoint `c=1`. -/
theorem topCapH_ge_margin_line {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    (1 - c) / 100 ≤ topCapH c q := by
  have hcont : ContinuousOn (fun u : ℝ ↦ topCapMarginGap u q) (Icc c 1) := by
    intro u hu
    unfold topCapMarginGap
    exact ((continuousOn_topCapH_Icc_right hc hq u hu).sub
      ((continuousAt_const.sub continuousAt_id).div_const 100).continuousWithinAt)
  have hanti : AntitoneOn (fun u : ℝ ↦ topCapMarginGap u q) (Icc c 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc c 1) hcont
    · intro u hu
      rw [interior_Icc] at hu
      have huUnit : u ∈ Ioo (0 : ℝ) 1 :=
        ⟨hc.1.trans hu.1, hu.2⟩
      exact (hasDerivAt_topCapMarginGap huUnit hq).hasDerivWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have huUnit : u ∈ Ioo (0 : ℝ) 1 :=
        ⟨hc.1.trans hu.1, hu.2⟩
      have hmargin := topCapJ_ge_margin huUnit hq
      linarith
  have h := hanti
    (show c ∈ Icc c 1 by exact ⟨le_rfl, hc.2.le⟩)
    (show (1 : ℝ) ∈ Icc c 1 by exact ⟨hc.2.le, le_rfl⟩) hc.2.le
  have hend : topCapMarginGap 1 q = 0 := by
    simp [topCapMarginGap]
  change topCapMarginGap 1 q ≤ topCapMarginGap c q at h
  rw [hend] at h
  unfold topCapMarginGap at h
  linarith

theorem topCapH_nonneg {c q : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    0 ≤ topCapH c q := by
  have h := topCapH_ge_margin_line hc hq
  linarith [hc.2]

end CourtadeKumar
