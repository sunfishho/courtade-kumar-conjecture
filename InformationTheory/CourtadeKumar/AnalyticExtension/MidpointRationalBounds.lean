import InformationTheory.CourtadeKumar.AnalyticExtension.MidpointSmallK
import InformationTheory.CourtadeKumar.LRDeterminantIdealHSlopeBounds

/-! Rational bounds for the combined logarithms of the midpoint core.
The weighted ratio bound remains finite as chi tends to zero. -/
open Set
namespace CourtadeKumar.LRAnalyticMidpoint

noncomputable def rationalT (s k c : ℝ) : ℝ :=
  (1 - c) / (2 * (1 + (1 - s) * k)) +
    c * (1 - c) / (2 * (1 + (1 - s) * k * c))

noncomputable def rationalAlpha (s k c : ℝ) : ℝ :=
  c / (1 + c) * (2 * ((1 - s) * k) * (1 - c)) /
    (2 + ((1 - s) * k) * (1 + c))

noncomputable def rationalD (s k : ℝ) : ℝ :=
  (1 - s * k) / (2 * k + 1 - s * k)

lemma log_ratio_trapezoid {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) :
    Real.log (a / b) ≤ (a - b) * (a + b) / (2 * a * b) := by
  have ha : 0 < a := hb.trans_le hba
  have ht : 0 ≤ a / b - 1 := by rw [sub_nonneg, one_le_div₀ hb]; exact hba
  have h := lrIdealH_log_one_add_upper ht
  rw [show 1 + (a / b - 1) = a / b by ring] at h
  have hid : a / b - 1 - (a / b - 1) ^ 2 / (2 * (a / b)) =
      (a - b) * (a + b) / (2 * a * b) := by
    field_simp [ha.ne', hb.ne']
    ring
  rwa [hid] at h

lemma weighted_log_ratio_upper {A c : ℝ} (hA : 0 ≤ A) (hc : c ∈ Ioc (0 : ℝ) 1) :
    c * Real.log ((1 + A * c) / (c * (1 + A))) ≤
      (1 - c) / (2 * (1 + A)) + c * (1 - c) / (2 * (1 + A * c)) := by
  have h1 : 0 < 1 + A := by linarith
  have h2 : 0 < 1 + A * c := by nlinarith [mul_nonneg hA hc.1.le]
  have h3 : 0 < c * (1 + A) := mul_pos hc.1 h1
  have hle : c * (1 + A) ≤ 1 + A * c := by nlinarith [hc.2]
  have h := mul_le_mul_of_nonneg_left (log_ratio_trapezoid h3 hle) hc.1.le
  have hid : c * ((1 + A * c - c * (1 + A)) * (1 + A * c + c * (1 + A)) /
      (2 * (1 + A * c) * (c * (1 + A)))) =
      (1 - c) / (2 * (1 + A)) + c * (1 - c) / (2 * (1 + A * c)) := by
    field_simp [hc.1.ne', h1.ne', h2.ne']
    ring_nf
    field_simp [show 1 + c * A ≠ 0 by nlinarith [mul_nonneg hA hc.1.le]] <;> ring
  rwa [hid] at h

lemma weighted_log_ratio_lower {A c : ℝ} (hA : 0 ≤ A) (hc : c ∈ Ioc (0 : ℝ) 1) :
    c / (1 + c) * (2 * A * (1 - c)) / (2 + A * (1 + c)) ≤
      c / (1 + c) * (Real.log (1 + A) - Real.log (1 + A * c)) := by
  have h1 : 0 < 1 + A := by linarith
  have h2 : 0 < 1 + A * c := by nlinarith [mul_nonneg hA hc.1.le]
  have h3 : 0 < 2 + A * (1 + c) := by nlinarith [mul_nonneg hA hc.1.le]
  let t := A * (1 - c) / (1 + A * c)
  have ht : 0 ≤ t := div_nonneg (mul_nonneg hA (sub_nonneg.mpr hc.2)) h2.le
  have h := lr_log_one_add_lower ht
  have harg : 1 + t = (1 + A) / (1 + A * c) := by
    dsimp [t]
    field_simp [h2.ne']
    ring
  have hrat : 2 * t / (2 + t) = (2 * A * (1 - c)) / (2 + A * (1 + c)) := by
    dsimp [t]
    field_simp [h2.ne', h3.ne']
    ring_nf
    field_simp [h3.ne', show 2 + A + A * c ≠ 0 by nlinarith [mul_nonneg hA hc.1.le]] <;> ring
  rw [harg, hrat, Real.log_div h1.ne' h2.ne'] at h
  have hscaled := mul_le_mul_of_nonneg_left h
    (div_nonneg hc.1.le (by linarith [hc.1] : 0 ≤ 1 + c))
  simpa [mul_div_assoc] using hscaled

lemma rationalD_lower {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    rationalD p.s p.k ≤ lrCertificateD p := by
  have hk : 0 < p.k := (mul_pos_iff_of_pos_left hi.1.1).mp hi.2.1.1
  have he : p.s * p.k < 1 := hi.2.1.2
  have ha : 0 < 1 + (1 - p.s) * p.k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hi.1.2.le) hk.le]
  have h := lr_log_one_add_lower
    (div_nonneg (by linarith : 0 ≤ 1 - p.s * p.k) hk.le)
  have harg : 1 + (1 - p.s * p.k) / p.k = (1 + (1 - p.s) * p.k) / p.k := by
    field_simp [hk.ne']
    ring
  have hrat : 2 * ((1 - p.s * p.k) / p.k) / (2 + (1 - p.s * p.k) / p.k) =
      2 * rationalD p.s p.k := by
    unfold rationalD
    field_simp (disch := nlinarith [he, hk])
    ring
  rw [harg, hrat, Real.log_div ha.ne' hk.ne'] at h
  rw [d_formula hi]
  linarith

lemma beta_gap_lower {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    p.s * p.k * (1 - p.chi) / 2 ≤
      2 * (Real.log 2 - Real.log (1 + lrCertificateV p)) := by
  let e := lrCertificateE p
  let x := lrCertificateX p
  let v := lrCertificateV p
  have hv : v ∈ Ioo (0 : ℝ) 1 := lrCertificateV_mem_Ioo hi
  have hx : 0 < x := by
    dsimp [x, lrCertificateX]
    nlinarith [mul_lt_mul_of_pos_right hi.2.2.2 hi.2.1.1, hi.2.1.2]
  have hx1 : x ≤ 1 := sub_le_self _ (mul_nonneg hi.2.2.1.le hi.2.1.1.le)
  have hvsq : v ^ 2 = (1 - e) / x :=
    Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hi.2.1.2.le) hx.le)
  have hgeom : e * (1 - p.chi) ≤ 1 - v ^ 2 := by
    have hid : 1 - v ^ 2 = e * (1 - p.chi) / x := by
      rw [hvsq]
      change 1 - (1 - e) / (1 - p.chi * e) = e * (1 - p.chi) / (1 - p.chi * e)
      have hden : 0 < 1 - e * p.chi := by
        change 0 < 1 - p.chi * e at hx
        nlinarith
      field_simp (disch := nlinarith [hden])
      ring
    rw [hid, le_div_iff₀ hx]
    exact mul_le_of_le_one_right (mul_nonneg hi.2.1.1.le (sub_nonneg.mpr hi.2.2.2.le)) hx1
  have hlog := Real.one_sub_inv_le_log_of_pos
    (div_pos (by norm_num : (0 : ℝ) < 2) (by linarith [hv.1] : 0 < 1 + v))
  rw [inv_div, Real.log_div (by norm_num : (2 : ℝ) ≠ 0)
    (by linarith [hv.1] : 1 + v ≠ 0)] at hlog
  change e * (1 - p.chi) / 2 ≤ 2 * (Real.log 2 - Real.log (1 + v))
  nlinarith [sq_nonneg (1 - v)]

end CourtadeKumar.LRAnalyticMidpoint
