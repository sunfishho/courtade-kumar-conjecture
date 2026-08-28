import InformationTheory.CourtadeKumar.LRHighShapeRelevantKLower
import InformationTheory.CourtadeKumar.LRAbelElementaryBounds

/-!
# The audited determinant lower logarithm D1

The determinant proof replaces the exact radial logarithm `D` by the
explicit lower model

`D1(Y) = log ((1 + Y) / 2) / 2 + (Y - 1) / (3Y + 1)`.

This file defines the model directly in cancellation coordinates and proves
the manuscript inequalities `0 ≤ D1 ≤ D` (the scalar input to (D3)).
-/

open Set

namespace CourtadeKumar

noncomputable def lrDeterminantY (point : CertificatePoint) : ℝ :=
  lrCertificateB point.s (lrCertificateE point) / lrCertificateE point

noncomputable def lrDeterminantD1 (point : CertificatePoint) : ℝ :=
  let Y := lrDeterminantY point
  (1 / 2 : ℝ) * Real.log ((1 + Y) / 2) + (Y - 1) / (3 * Y + 1)

theorem lrDeterminantY_one_le {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    1 ≤ lrDeterminantY point := by
  have hs := hinterior.1
  have he := hinterior.2.1
  unfold lrDeterminantY
  rw [one_le_div₀ he.1]
  unfold lrCertificateB
  nlinarith [mul_nonneg (sub_nonneg.mpr hs.2.le) he.1.le,
    mul_nonneg hs.1.le (sub_nonneg.mpr he.2.le)]

/-- The exact coordinate logarithm `D` is `log Y / 2`. -/
theorem lrCertificateD_eq_half_log_determinantY
    {point : CertificatePoint} (hinterior : LRHighShapeInterior point) :
    lrCertificateD point = (1 / 2 : ℝ) * Real.log (lrDeterminantY point) := by
  have he := hinterior.2.1
  have hb := lrCertificateB_mem_Ioo hinterior.1 he
  unfold lrCertificateD lrCertificateA lrCertificateAValue
    lrCertificateBFlow lrCertificateBFlowValue lrDeterminantY
  rw [Real.log_div hb.1.ne' he.1.ne']
  ring

theorem lrDeterminantD1_nonnegative {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    0 ≤ lrDeterminantD1 point := by
  let Y := lrDeterminantY point
  have hY : 1 ≤ Y := by
    simpa [Y] using lrDeterminantY_one_le hinterior
  have hmean : 1 ≤ (1 + Y) / 2 := by linarith
  have hlog : 0 ≤ Real.log ((1 + Y) / 2) := Real.log_nonneg hmean
  have hden : 0 < 3 * Y + 1 := by linarith
  have hfrac : 0 ≤ (Y - 1) / (3 * Y + 1) :=
    div_nonneg (sub_nonneg.mpr hY) hden.le
  unfold lrDeterminantD1
  dsimp only
  exact add_nonneg (mul_nonneg (by norm_num) hlog) hfrac

/-- The rationally corrected logarithm is a global lower bound for `D` on
the physical interior.  This is the inequality preceding (D3). -/
theorem lrDeterminantD1_le_D {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDeterminantD1 point ≤ lrCertificateD point := by
  let Y := lrDeterminantY point
  let z := (Y - 1) / (Y + 1)
  have hY : 1 ≤ Y := by
    simpa [Y] using lrDeterminantY_one_le hinterior
  have hYPos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hYPlus : 0 < Y + 1 := by linarith
  have hmeanPos : 0 < (1 + Y) / 2 := by linarith
  have hthreeYPos : 0 < 3 * Y + 1 := by linarith
  have hthreeYPos' : 0 < 1 + Y * 3 := by nlinarith
  have hz : 0 ≤ z := div_nonneg (sub_nonneg.mpr hY) hYPlus.le
  have hzDen : 0 < 2 + z := by linarith
  have hratio : Y / ((1 + Y) / 2) = 1 + z := by
    dsimp [z]
    field_simp [hYPlus.ne']
    ring
  have hzDenEq : 2 + z = (3 * Y + 1) / (Y + 1) := by
    dsimp [z]
    field_simp [hYPlus.ne']
    ring
  have hfrac : (Y - 1) / (3 * Y + 1) = z / (2 + z) := by
    rw [hzDenEq]
    dsimp [z]
    field_simp [hYPlus.ne', hthreeYPos.ne', hthreeYPos'.ne']
  have hlogDiv :
      Real.log Y - Real.log ((1 + Y) / 2) = Real.log (1 + z) := by
    rw [← Real.log_div hYPos.ne' hmeanPos.ne', hratio]
  have hlogLower := lr_log_one_add_lower hz
  have hhalf : z / (2 + z) ≤ (1 / 2 : ℝ) * Real.log (1 + z) := by
    have htwo : 2 * z / (2 + z) = 2 * (z / (2 + z)) := by ring
    rw [htwo] at hlogLower
    nlinarith [hlogLower]
  rw [← hfrac, ← hlogDiv] at hhalf
  rw [lrCertificateD_eq_half_log_determinantY hinterior]
  unfold lrDeterminantD1
  dsimp only
  change (1 / 2 : ℝ) * Real.log ((1 + Y) / 2) +
      (Y - 1) / (3 * Y + 1) ≤ (1 / 2 : ℝ) * Real.log Y
  linarith

/-- The lower logarithm lies in the exact interval used by the determinant
replacement step. -/
theorem lrDeterminantD1_mem_Icc {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point) :
    lrDeterminantD1 point ∈ Set.Icc 0 (lrCertificateD point) :=
  ⟨lrDeterminantD1_nonnegative hinterior,
    lrDeterminantD1_le_D hinterior⟩

/-- On the relevant branch, the factor `B*x - D1` in (D5) is strictly
positive.  This is the exact consequence of `J = B*x - D > 0` and
`D1 ≤ D`; it removes that factor from the remaining determinant ledger. -/
theorem lrCertificateBFlow_mul_X_sub_D1_pos {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point) :
    0 < lrCertificateBFlow point * lrCertificateX point -
      lrDeterminantD1 point := by
  have hD := lrDeterminantD1_le_D hinterior
  have hJ := hrelevant.2
  unfold lrCertificateJ at hJ
  linarith

end CourtadeKumar
