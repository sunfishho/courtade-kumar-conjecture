import InformationTheory.CourtadeKumar.TopFiniteClaim

/-! Rational upper bound for `artanh` and the logarithmic term in the TOP
full-cap comparison. -/

open Set

namespace CourtadeKumar

noncomputable def topAtanhPadeGap (u : ℝ) : ℝ :=
  u + u ^ 3 / (3 * (1 - u ^ 2)) - Real.artanh u

lemma hasDerivAt_topAtanhPadeGap {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt topAtanhPadeGap
      (2 * u ^ 4 / (3 * (1 - u ^ 2) ^ 2)) u := by
  have hid := hasDerivAt_id u
  have hnum : HasDerivAt (fun x : ℝ ↦ x ^ 3) (3 * u ^ 2) u := by
    convert hid.pow 3 using 1 <;> simp only [id_eq] <;> ring
  have hden : HasDerivAt (fun x : ℝ ↦ 3 * (1 - x ^ 2)) (-6 * u) u := by
    convert (hasDerivAt_const u 1).sub (hid.pow 2) |>.const_mul 3 using 1 <;>
      simp only [id_eq] <;> ring
  have hbase_pos : 0 < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have hbase_ne : 1 - u ^ 2 ≠ 0 := hbase_pos.ne'
  have hden_ne : 3 * (1 - u ^ 2) ≠ 0 := mul_ne_zero (by norm_num) hbase_ne
  have hfrac := hnum.div hden hden_ne
  have hart := hasDerivAt_artanh hu
  have htotal := (hid.add hfrac).sub hart
  convert htotal using 1
  field_simp [hden_ne, hbase_ne]
  ring

lemma topAtanhPadeGap_deriv_nonneg {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ 2 * u ^ 4 / (3 * (1 - u ^ 2) ^ 2) := by
  positivity

/-- The positive-series Padé bound used in the finite TOP certificate,
proved here by a derivative cancellation. -/
theorem artanh_le_cubicPade {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (1 / 3)) :
    Real.artanh u ≤ u + u ^ 3 / (3 * (1 - u ^ 2)) := by
  have hdomain : ∀ x ∈ Icc (0 : ℝ) (1 / 3), x ∈ Ioo (-1 : ℝ) 1 := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hmono : MonotoneOn topAtanhPadeGap (Icc (0 : ℝ) (1 / 3)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (1 / 3))
    · intro x hx
      exact (hasDerivAt_topAtanhPadeGap (hdomain x hx)).continuousAt.continuousWithinAt
    · intro x hx
      have hxin := interior_subset hx
      exact (hasDerivAt_topAtanhPadeGap (hdomain x hxin)).hasDerivWithinAt
    · intro x hx
      exact topAtanhPadeGap_deriv_nonneg (hdomain x (interior_subset hx))
  have h0 := hmono
    (show (0 : ℝ) ∈ Icc 0 (1 / 3) by norm_num)
    hu hu.1
  have hgap0 : topAtanhPadeGap 0 = 0 := by
    simp [topAtanhPadeGap]
  rw [hgap0] at h0
  unfold topAtanhPadeGap at h0
  linarith

noncomputable def topCertX (c z : ℝ) : ℝ :=
  topCertD c / (topCertD c + topCertB c z)

noncomputable def topCertU (c z : ℝ) : ℝ :=
  topCertB c z / topCertH c z

noncomputable def topCapQ (c z : ℝ) : ℝ :=
  z / topCertR c z

lemma topCertB_le_D {c z : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    topCertB c z ≤ topCertD c := by
  have hcprod : 0 ≤ c * (1 - c) := mul_nonneg hc.1 (sub_nonneg.mpr hc.2)
  have hpoly : c ^ 2 - 2 * c - 2 ≤ 0 := by nlinarith
  have hprod : 0 ≤ (c - 1) * (c ^ 2 - 2 * c - 2) :=
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hc.2) hpoly
  have hbase : c ^ 2 * (3 - c) ≤ (1 + c) * (2 - c) ^ 2 := by
    nlinarith [hprod]
  have hfactor : 0 ≤ c ^ 2 * (3 - c) :=
    mul_nonneg (sq_nonneg c) (by linarith [hc.2])
  have hzmul : z * (c ^ 2 * (3 - c)) ≤ c ^ 2 * (3 - c) :=
    by simpa only [one_mul] using mul_le_mul_of_nonneg_right hz.2 hfactor
  unfold topCertB topCertD
  nlinarith

lemma topCertU_mem_Icc {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    topCertU c z ∈ Icc (0 : ℝ) (1 / 3) := by
  have hb := (topCertB_pos hc hz).le
  have hh := topCertH_pos hc hz
  have hbd := topCertB_le_D ⟨hc.1.le, hc.2.le⟩ ⟨hz.1.le, hz.2.le⟩
  constructor
  · exact div_nonneg hb hh.le
  · unfold topCertU
    rw [div_le_iff₀ hh]
    unfold topCertH
    nlinarith

lemma topCertX_eq_one_sub_U_div_one_add_U {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    topCertX c z = (1 - topCertU c z) / (1 + topCertU c z) := by
  have hd := topCertD_pos hc
  have hb := topCertB_pos hc hz
  have hh := topCertH_pos hc hz
  unfold topCertX topCertU topCertH
  field_simp [hd.ne', hb.ne', hh.ne']
  ring

lemma topCert_logX_eq_neg_two_artanh_U {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    Real.log (topCertX c z) = -2 * Real.artanh (topCertU c z) := by
  have hu := topCertU_mem_Icc hc hz
  have hufull : topCertU c z ∈ Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith [hu.1, hu.2]
  have hm : 0 < 1 - topCertU c z := by linarith [hufull.2]
  have hp : 0 < 1 + topCertU c z := by linarith [hufull.1]
  rw [topCertX_eq_one_sub_U_div_one_add_U hc hz]
  rw [Real.artanh_eq_half_log ⟨hufull.1.le, hufull.2.le⟩]
  rw [Real.log_div hm.ne' hp.ne', Real.log_div hp.ne' hm.ne']
  ring

lemma topCapQ_pos {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    0 < topCapQ c z :=
  div_pos hz.1 (topCertR_mem_Ioo hc hz).1

private lemma pade_rational_identity
    {R c z d b h : ℝ}
    (hR : R ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0)
    (hd : d ≠ 0) (hh : h ≠ 0) (hdb : d + b ≠ 0)
    (hb : b = z * c ^ 2 * (3 - c)) (hH : h = 2 * d + b) :
    (-2 * (b / h + (b / h) ^ 3 / (3 * (1 - (b / h) ^ 2)))) /
        (2 * c ^ 2 * (z / R)) =
      (-R * (3 - c) * (3 * h ^ 2 - 2 * b ^ 2)) /
        (12 * d * h * (d + b)) := by
  have hratio : 1 - (b / h) ^ 2 = (h ^ 2 - b ^ 2) / h ^ 2 := by
    field_simp [hh]
  have hsq : h ^ 2 - b ^ 2 = 4 * d * (d + b) := by
    rw [hH]
    ring
  rw [hratio, hsq]
  field_simp [hR, hc, hz, hd, hh, hdb]
  rw [hH, hb]
  ring

lemma topCert_pade_eq_ZStar {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    (-2 * (topCertU c z +
        topCertU c z ^ 3 / (3 * (1 - topCertU c z ^ 2)))) /
        (2 * c ^ 2 * topCapQ c z) =
      topCertZNum c z / topCertZDen c z := by
  have hcne : c ≠ 0 := hc.1.ne'
  have hzne : z ≠ 0 := hz.1.ne'
  have hR := topCertR_mem_Ioo hc hz
  have hd := topCertD_pos hc
  have hb := topCertB_pos hc hz
  have hh := topCertH_pos hc hz
  have hdb : 0 < topCertD c + topCertB c z := add_pos hd hb
  unfold topCertU topCapQ topCertZNum topCertZDen
  exact pade_rational_identity hR.1.ne' hcne hzne hd.ne' hh.ne' hdb.ne'
    (by rfl) (by rfl)

/-- The logarithmic cap term is bounded below by the exact rational
`Z_*` term consumed by the Bernstein certificate. -/
theorem topCapLogTerm_ge_ZStar {c z : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    topCertZNum c z / topCertZDen c z ≤
      Real.log (topCertX c z) / (2 * c ^ 2 * topCapQ c z) := by
  have hu := topCertU_mem_Icc hc hz
  have hpade := artanh_le_cubicPade hu
  have hden : 0 < 2 * c ^ 2 * topCapQ c z := by
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hc.1)) (topCapQ_pos hc hz)
  have hneg :
      -2 * (topCertU c z +
          topCertU c z ^ 3 / (3 * (1 - topCertU c z ^ 2))) ≤
        -2 * Real.artanh (topCertU c z) := by
    linarith
  have hquot := div_le_div_of_nonneg_right hneg hden.le
  rw [← topCert_logX_eq_neg_two_artanh_U hc hz] at hquot
  rw [topCert_pade_eq_ZStar hc hz] at hquot
  exact hquot

/-- Lift the exact finite certificate to any analytic comparison whose
`w` and tail terms dominate the certified truncations. -/
theorem topFiniteClaim_of_analytic_bounds {c z w e : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1)
    (hw : topCertW8 c z ≤ w)
    (he : topCertEnum c z / topCertR c z ^ 9 ≤ e) :
    (1 : ℝ) / 100 ≤
      w + Real.log (topCertX c z) / (2 * c ^ 2 * topCapQ c z) + e := by
  have hfinite := topFiniteClaim hc hz
  have hlog := topCapLogTerm_ge_ZStar hc hz
  linarith

end CourtadeKumar
