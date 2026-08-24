import InformationTheory.CourtadeKumar.BalancedRoot
import Mathlib.Analysis.Convex.Deriv

/-! The channel-only analytic bound used in the corrected balanced-root cap. -/

open Set

namespace CourtadeKumar

theorem artanh_sub_id_strictMonoOn :
    StrictMonoOn (fun x : ℝ ↦ Real.artanh x - x) (Ico (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico 0 1)
  · intro x hx
    have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    exact ((hasDerivAt_artanh hx').sub (hasDerivAt_id x)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ico] at hx
    have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    have hd : HasDerivAt (fun y : ℝ ↦ Real.artanh y - y)
        (1 / (1 - x ^ 2) - 1) x := by
      simpa only [id_eq] using (hasDerivAt_artanh hx').sub (hasDerivAt_id x)
    rw [hd.deriv]
    have hden : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    rw [sub_pos, one_div]
    exact (one_lt_inv₀ hden).2 (by nlinarith [sq_pos_of_pos hx.1])

lemma self_lt_artanh {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    x < Real.artanh x := by
  have h := artanh_sub_id_strictMonoOn
    (show (0 : ℝ) ∈ Ico 0 1 by simp) ⟨hx.1.le, hx.2⟩ hx.1
  simpa using h

noncomputable def channelCapK (R : ℝ) : ℝ :=
  Real.negMulLog (1 - R) / 4 - (R * Real.log 2 - topPhi (Real.sqrt R))

noncomputable def channelCapKDeriv (R : ℝ) : ℝ :=
  (Real.log (1 - R) + 1) / 4 - Real.log 2 +
    Real.artanh (Real.sqrt R) / (2 * Real.sqrt R)

noncomputable def channelCapKDeriv2 (R : ℝ) : ℝ :=
  (Real.sqrt R - Real.artanh (Real.sqrt R)) / (4 * R * Real.sqrt R)

lemma continuous_channelCapK : Continuous channelCapK := by
  unfold channelCapK
  exact (Real.continuous_negMulLog.comp (continuous_const.sub continuous_id) |>.div_const 4).sub
    ((continuous_id.mul continuous_const).sub
      (continuous_topPhi.comp Real.continuous_sqrt))

theorem hasDerivAt_channelCapK {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt channelCapK (channelCapKDeriv R) R := by
  have hs_ne : 1 - R ≠ 0 := by linarith [hR.2]
  have hsarg : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) R := by
    simpa [id_eq] using (hasDerivAt_const R 1).sub (hasDerivAt_id R)
  have hneg := (Real.hasDerivAt_negMulLog hs_ne).comp R hsarg |>.div_const 4
  have hlinear := (hasDerivAt_id R).mul_const (Real.log 2)
  have hsqrt := Real.hasDerivAt_sqrt (ne_of_gt hR.1)
  have hsqrtIoo : Real.sqrt R ∈ Ioo (-1 : ℝ) 1 := by
    have hsqrt_pos := Real.sqrt_pos.2 hR.1
    have hsqrt_lt : Real.sqrt R < 1 :=
      (Real.sqrt_lt' (show (0 : ℝ) < 1 by norm_num)).2 (by simpa using hR.2)
    exact ⟨by linarith, hsqrt_lt⟩
  have hphi := (hasDerivAt_topPhi hsqrtIoo).comp R hsqrt
  unfold channelCapK channelCapKDeriv
  convert hneg.sub (hlinear.sub hphi) using 1
  ring_nf

theorem hasDerivAt_channelCapKDeriv {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt channelCapKDeriv (channelCapKDeriv2 R) R := by
  have hs_ne : 1 - R ≠ 0 := by linarith [hR.2]
  have hsarg : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) R := by
    simpa [id_eq] using (hasDerivAt_const R 1).sub (hasDerivAt_id R)
  have hlog := (Real.hasDerivAt_log hs_ne).comp R hsarg
  have hlogquarter := (hlog.add_const 1).div_const 4
  have hsqrt := Real.hasDerivAt_sqrt (ne_of_gt hR.1)
  have hsqrt_pos := Real.sqrt_pos.2 hR.1
  have hsqrt_lt : Real.sqrt R < 1 :=
    (Real.sqrt_lt' (show (0 : ℝ) < 1 by norm_num)).2 (by simpa using hR.2)
  have hsqrtIoo : Real.sqrt R ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hsqrt_lt⟩
  have hartanh := (hasDerivAt_artanh hsqrtIoo).comp R hsqrt
  have hden := hsqrt.const_mul 2
  have hquot := hartanh.div hden (by positivity : 2 * Real.sqrt R ≠ 0)
  have htotal := (hlogquarter.sub (hasDerivAt_const R (Real.log 2))).add hquot
  have hsqrtden_ne : 1 - Real.sqrt R ^ 2 ≠ 0 := by
    rw [Real.sq_sqrt hR.1.le]
    exact hs_ne
  unfold channelCapKDeriv channelCapKDeriv2
  convert htotal using 1
  simp only [Function.comp_apply]
  field_simp [ne_of_gt hR.1, ne_of_gt hsqrt_pos, hs_ne, hsqrtden_ne]
  linear_combination
    (4 * (-(Real.sqrt R * (R + Real.sqrt R ^ 2) -
      Real.artanh (Real.sqrt R) * Real.sqrt R ^ 2 * (1 - R)) +
      Real.sqrt R + Real.artanh (Real.sqrt R) * (R - 1))) *
      (Real.sq_sqrt hR.1.le)

theorem channelCapK_concaveOn :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) channelCapK := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
    continuous_channelCapK.continuousOn
  · intro R hR
    rw [interior_Icc] at hR
    exact (hasDerivAt_channelCapK hR).hasDerivWithinAt
  · intro R hR
    rw [interior_Icc] at hR
    exact (hasDerivAt_channelCapKDeriv hR).hasDerivWithinAt
  · intro R hR
    rw [interior_Icc] at hR
    unfold channelCapKDeriv2
    have hsqrt_pos := Real.sqrt_pos.2 hR.1
    have hsqrt_lt : Real.sqrt R < 1 :=
      (Real.sqrt_lt' (show (0 : ℝ) < 1 by norm_num)).2 (by simpa using hR.2)
    have hden : 0 < 4 * R * Real.sqrt R :=
      mul_pos (mul_pos (by norm_num) hR.1) hsqrt_pos
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (self_lt_artanh ⟨hsqrt_pos, hsqrt_lt⟩).le) hden.le

@[simp] lemma channelCapK_zero : channelCapK 0 = 0 := by
  simp [channelCapK]

@[simp] lemma channelCapK_one : channelCapK 1 = 0 := by
  simp [channelCapK]

theorem channelCapK_nonneg {R : ℝ} (hR : R ∈ Icc (0 : ℝ) 1) :
    0 ≤ channelCapK R := by
  have h := channelCapK_concaveOn.2
    (show (0 : ℝ) ∈ Icc 0 1 by simp) (show (1 : ℝ) ∈ Icc 0 1 by simp)
    (sub_nonneg.mpr hR.2) hR.1 (by linarith [hR.1, hR.2])
  simpa using h

theorem topEll_le_channelCap {rho : ℝ} (hrho : rho ∈ Icc (0 : ℝ) 1) :
    topEll rho ≤ -(topS rho) / 4 * Real.log (topS rho) := by
  by_cases hrho1 : rho = 1
  · subst rho
    simp [topEll, topS, topR]
  have hR : rho ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [mul_nonneg (sub_nonneg.mpr hrho.2) (add_nonneg hrho.1 zero_le_one)]
  have h := channelCapK_nonneg hR
  have hsqrt : Real.sqrt (rho ^ 2) = rho := Real.sqrt_sq_eq_abs rho |>.trans (abs_of_nonneg hrho.1)
  have hrholt : rho < 1 := lt_of_le_of_ne hrho.2 hrho1
  have hspos : 0 < 1 - rho ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hrholt) (by linarith [hrho.1] : 0 < rho + 1)]
  unfold channelCapK at h
  rw [hsqrt] at h
  simp only [topEll, topS, topR]
  calc
    rho ^ 2 * Real.log 2 - topPhi rho ≤ Real.negMulLog (1 - rho ^ 2) / 4 := by
      linarith
    _ = -(1 - rho ^ 2) / 4 * Real.log (1 - rho ^ 2) := by
      rw [Real.negMulLog_eq_neg]
      ring

end CourtadeKumar
