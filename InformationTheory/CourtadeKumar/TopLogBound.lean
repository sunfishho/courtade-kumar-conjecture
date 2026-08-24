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

end CourtadeKumar
