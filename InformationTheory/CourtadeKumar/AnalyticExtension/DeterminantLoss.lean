import InformationTheory.CourtadeKumar.LRDeterminantWronskianConcrete
import InformationTheory.CourtadeKumar.LRDeterminantLowRatio
import InformationTheory.CourtadeKumar.LRDeterminantRegionInterfaces

/-! A uniform analytic error bound for replacing exact D by the determinant
model D1. The compensated target retains its cancellation before this single
small loss is paid. This is a sufficient alternative target, not a proof of
the remaining determinant region. -/
open Set
namespace CourtadeKumar.LRAnalyticDeterminant

lemma log_model_gap_upper {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    Real.log (1 + z) / 2 - z / (2 + z) ≤ Real.log 2 / 2 - 1 / 3 := by
  have h1 : 0 < 1 + z := by linarith [hz.1]
  have h2 : 0 < 2 + z := by linarith [hz.1]
  have h3 : 0 < 3 + z := by linarith [hz.1]
  let u := (1 - z) / (1 + z)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hz.2) h1.le
  have hlog := lr_log_one_add_lower hu
  have harg : 1 + u = 2 / (1 + z) := by
    dsimp [u]
    field_simp [h1.ne']
    ring
  have hrat : 2 * u / (2 + u) = 2 * (1 - z) / (3 + z) := by
    dsimp [u]
    field_simp [h1.ne', h3.ne']
    ring_nf
    field_simp [h3.ne'] <;> ring
  rw [harg, hrat, Real.log_div (by norm_num : (2 : ℝ) ≠ 0) h1.ne'] at hlog
  rw [mul_div_assoc] at hlog
  have hsmall : 1 / 3 - z / (2 + z) ≤ (1 - z) / (3 + z) := by
    have hid : (1 - z) / (3 + z) - (1 / 3 - z / (2 + z)) =
        z * (1 - z) / (3 * (3 + z) * (2 + z)) := by
      field_simp [h2.ne', h3.ne']
      ring
    rw [← sub_nonneg, hid]
    exact div_nonneg (mul_nonneg hz.1 (sub_nonneg.mpr hz.2)) (by positivity)
  linarith

theorem d_gap_upper {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrCertificateD p - lrDeterminantD1 p ≤ Real.log 2 / 2 - 1 / 3 := by
  let Y := lrDeterminantY p
  let z := (Y - 1) / (Y + 1)
  have hY : 1 ≤ Y := lrDeterminantY_one_le hi
  have hp : 0 < Y + 1 := by linarith
  have hY0 : 0 < Y := by linarith
  have hz : z ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (by linarith) hp.le, ?_⟩
    rw [div_le_one hp]
    linarith
  have hratio : Y / ((1 + Y) / 2) = 1 + z := by
    dsimp [z]
    field_simp [hp.ne']
    ring
  have hrat : (Y - 1) / (3 * Y + 1) = z / (2 + z) := by
    dsimp [z]
    field_simp [hp.ne', show 3 * Y + 1 ≠ 0 by linarith,
      show 1 + Y * 3 ≠ 0 by linarith]
    ring_nf
    field_simp [show 1 + Y * 3 ≠ 0 by linarith] <;> ring
  have hlog : Real.log Y - Real.log ((1 + Y) / 2) = Real.log (1 + z) := by
    rw [← Real.log_div hY0.ne' (show (1 + Y) / 2 ≠ 0 by linarith), hratio]
  have h := log_model_gap_upper hz
  rw [lrCertificateD_eq_half_log_determinantY hi]
  unfold lrDeterminantD1
  change 1 / 2 * Real.log Y - (1 / 2 * Real.log ((1 + Y) / 2) +
    (Y - 1) / (3 * Y + 1)) ≤ _
  rw [hrat]
  linarith

/-- A uniform rational bound, independent of the finite region coordinates. -/
theorem d_gap_lt {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    0 ≤ lrCertificateD p - lrDeterminantD1 p ∧
      lrCertificateD p - lrDeterminantD1 p < (1 / 75 : ℝ) := by
  refine ⟨sub_nonneg.mpr (lrDeterminantD1_le_D hi), ?_⟩
  have h := d_gap_upper hi
  have hlog := Real.log_two_lt_d9
  linarith

noncomputable def exactCompensated (p : CertificatePoint) : ℝ :=
  lrCertificateVTarget p + lrDeterminantC0 p * lrCertificateJ p * lrDeterminantT p

lemma cleared_identity {p : CertificatePoint} (hi : LRHighShapeInterior p) :
    lrDeterminantClearedSingular (lrCertificateBFlow p) (lrDeterminantD1 p)
      (lrCertificateGShape p) (lrDeterminantPsi p) (lrDeterminantDelta p)
      (lrCertificateW p) (lrDeterminantC0 p) (lrCertificateX p) (lrDeterminantT p) =
    exactCompensated p - (lrCertificateD p - lrDeterminantD1 p) *
      (lrDeterminantPsi p - lrDeterminantC0 p * lrDeterminantT p) := by
  unfold exactCompensated
  rw [lrCertificateVTarget_eq_firstBracket_add
    (by linarith [(lrCertificateV_mem_Ioo hi).1] : 1 + lrCertificateV p ≠ 0)]
  unfold lrDeterminantClearedSingular lrDeterminantFirstBracket lrCertificateJ
  ring

/-- Preserve the full compensation and pay only the positive part of the
small D-model error. The maximum prevents a sign-unsafe replacement. -/
theorem cleared_of_exact_margin {p : CertificatePoint} (hi : LRHighShapeInterior p)
    (hm : (1 / 75 : ℝ) * max 0 (lrDeterminantPsi p - lrDeterminantC0 p * lrDeterminantT p) ≤
      exactCompensated p) : LRDeterminantClearedSingularAt p := by
  let g := lrCertificateD p - lrDeterminantD1 p
  let q := lrDeterminantPsi p - lrDeterminantC0 p * lrDeterminantT p
  have hg := d_gap_lt hi
  have hmul : g * q ≤ (1 / 75 : ℝ) * max 0 q :=
    (mul_le_mul_of_nonneg_left (le_max_right 0 q) hg.1).trans
      (mul_le_mul_of_nonneg_right hg.2.le (le_max_left 0 q))
  change 0 ≤ lrDeterminantClearedSingular _ _ _ _ _ _ _ _ _
  rw [cleared_identity hi]
  change 0 ≤ exactCompensated p - g * q
  exact sub_nonneg.mpr (hmul.trans hm)

end CourtadeKumar.LRAnalyticDeterminant
