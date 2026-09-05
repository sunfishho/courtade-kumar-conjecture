import InformationTheory.CourtadeKumar.LRDeterminantScalarTargetCore
import InformationTheory.CourtadeKumar.LRDeterminantD1
import InformationTheory.CourtadeKumar.LRDeterminantSignAlgebra

/-!
# Exact flow coordinates for the audited determinant

This file identifies the abstract quantities in (D1)--(D2) with the
already formalized high-shape cancellation coordinates.  In particular,
the existing tangent target is exactly `s³` times the original determinant,
and the compensated determinant satisfies the normalized identity (D2).
-/

namespace CourtadeKumar

/-- The manuscript factor `H_d = m(M/2) / s`. -/
noncomputable def lrDeterminantHd (point : CertificatePoint) : ℝ :=
  lrCertificateHalfSlope point / point.s

/-- The manuscript reserve `V = N(M) / s²`. -/
noncomputable def lrDeterminantV (point : CertificatePoint) : ℝ :=
  lrCertificateMidpointNumerator point / point.s ^ 2

/-- The radial derivative `mu' = 4 W₁ / s²`. -/
noncomputable def lrDeterminantMuPrime (point : CertificatePoint) : ℝ :=
  4 * lrCertificateW point / point.s ^ 2

/-- The normalized target gap `F = S / s`. -/
noncomputable def lrDeterminantF (point : CertificatePoint) : ℝ :=
  lrCertificateGap point / point.s



/-- The scaled gap `T = sF/R = S/R`. -/
noncomputable def lrDeterminantT (point : CertificatePoint) : ℝ :=
  lrCertificateGap point / lrCertificateR point

/-- The coefficient `c₀ = 4 R W₁ / (3 s H_d)`. -/
noncomputable def lrDeterminantC0 (point : CertificatePoint) : ℝ :=
  4 * lrCertificateR point * lrCertificateW point /
    (3 * point.s * lrDeterminantHd point)

/-- Exact collection of the outer-midpoint numerator into the two brackets
used in (D2). -/
theorem lrCertificateMidpointNumerator_eq_determinant_brackets
    {point : CertificatePoint}
    (hvPlus : 1 + lrCertificateV point ≠ 0) :
    lrCertificateMidpointNumerator point =
      lrCertificateD point * lrDeterminantPsi point +
        lrCertificateBFlow point *
          (lrDeterminantPsi point - lrCertificateGShape point +
            4 * lrDeterminantDelta point * lrCertificateW point) := by
  unfold lrCertificateMidpointNumerator lrCertificateMidpointBracket
    lrDeterminantPsi lrDeterminantDelta lrCertificateM
    lrCertificateD
  field_simp [hvPlus]
  ring

/-- The high-shape tangent target is precisely `s³` times the original
determinant in (D7). -/
theorem lrCertificateTTarget_eq_scaled_originalDeterminant
    {point : CertificatePoint} (hs : point.s ≠ 0) :
    lrCertificateTTarget point = point.s ^ 3 *
      lrOriginalTangentDeterminant
        (lrDeterminantHd point) (lrDeterminantV point)
        (lrCertificateJ point) (lrDeterminantMuPrime point)
        (lrDeterminantF point) := by
  unfold lrCertificateTTarget lrOriginalTangentDeterminant
    lrDeterminantHd lrDeterminantV lrDeterminantMuPrime lrDeterminantF
  field_simp [hs]
  ring

/-- Exact normalized determinant identity (D2) in certificate coordinates. -/
theorem lrCertificateCompensatedDeterminant_scaled
    {point : CertificatePoint}
    (hs : point.s ≠ 0) (hR : lrCertificateR point ≠ 0)
    (hB : lrCertificateBFlow point ≠ 0)
    (hG : lrCertificateGShape point ≠ 0)
    (hHd : lrDeterminantHd point ≠ 0)
    (hvPlus : 1 + lrCertificateV point ≠ 0) :
    point.s ^ 2 *
        lrCompensatedDeterminant
          (lrDeterminantHd point) (lrDeterminantV point)
          (lrCertificateJ point) (lrDeterminantMuPrime point)
          (lrDeterminantF point) =
      lrCertificateBFlow point * lrDeterminantHd point *
        lrCertificateGShape point *
          lrDeterminantNormalized
            (lrCertificateBFlow point) (lrCertificateD point)
            (lrDeterminantPsi point / lrCertificateGShape point)
            (4 * lrDeterminantDelta point * lrCertificateW point /
              lrCertificateGShape point)
            (lrDeterminantC0 point) (lrCertificateX point)
            (lrDeterminantT point / lrCertificateGShape point) := by
  have hnum := lrCertificateMidpointNumerator_eq_determinant_brackets
    (point := point) hvPlus
  unfold lrCompensatedDeterminant lrDeterminantV
    lrDeterminantMuPrime lrDeterminantF
  rw [hnum]
  unfold lrDeterminantC0 lrDeterminantT lrDeterminantNormalized
    lrCertificateJ
  field_simp [hs, hR, hB, hG, hHd]
  ring

theorem lrDeterminantMuPrime_nonnegative {point : CertificatePoint}
    (hW : 0 ≤ lrCertificateW point) :
    0 ≤ lrDeterminantMuPrime point := by
  unfold lrDeterminantMuPrime
  exact div_nonneg (mul_nonneg (by norm_num) hW) (sq_nonneg point.s)

theorem lrDeterminantF_nonnegative {point : CertificatePoint}
    (hs : 0 < point.s) (hgap : 0 ≤ lrCertificateGap point) :
    0 ≤ lrDeterminantF point := by
  exact div_nonneg hgap hs.le

theorem lrDeterminantT_nonnegative {point : CertificatePoint}
    (hR : 0 < lrCertificateR point)
    (hgap : 0 ≤ lrCertificateGap point) :
    0 ≤ lrDeterminantT point := by
  exact div_nonneg hgap hR.le

theorem lrDeterminantC0_nonnegative {point : CertificatePoint}
    (hs : 0 < point.s) (hHd : 0 < lrDeterminantHd point)
    (hR : 0 ≤ lrCertificateR point)
    (hW : 0 ≤ lrCertificateW point) :
    0 ≤ lrDeterminantC0 point := by
  unfold lrDeterminantC0
  exact div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hR) hW)
    (mul_nonneg (mul_nonneg (by norm_num) hs.le) hHd.le)

/-- Certificate-coordinate form of the first-bracket implication in (D5). -/
theorem lrCertificateClearedSingular_nonnegative_of_firstBracket
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hfirst : 0 ≤ lrDeterminantFirstBracket
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrCertificateGShape point) (lrDeterminantPsi point)
      (lrDeterminantDelta point) (lrCertificateW point))
    (hc0 : 0 ≤ lrDeterminantC0 point)
    (hT : 0 ≤ lrDeterminantT point) :
    0 ≤ lrDeterminantClearedSingular
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrCertificateGShape point) (lrDeterminantPsi point)
      (lrDeterminantDelta point) (lrCertificateW point)
      (lrDeterminantC0 point) (lrCertificateX point)
      (lrDeterminantT point) := by
  apply lrDeterminantClearedSingular_nonnegative_of_firstBracket
    hfirst hc0 hT
  exact (lrCertificateBFlow_mul_X_sub_D1_pos hinterior hrelevant).le

/-- A nonnegative original determinant gives the already existing tangent
certificate target after multiplication by the positive scale `s³`. -/
theorem lrCertificateTTarget_nonnegative_of_originalDeterminant
    {point : CertificatePoint} (hs : 0 < point.s)
    (hdet : 0 ≤ lrOriginalTangentDeterminant
      (lrDeterminantHd point) (lrDeterminantV point)
      (lrCertificateJ point) (lrDeterminantMuPrime point)
      (lrDeterminantF point)) :
    0 ≤ lrCertificateTTarget point := by
  rw [lrCertificateTTarget_eq_scaled_originalDeterminant hs.ne']
  exact mul_nonneg (pow_nonneg hs.le _) hdet

/-- Full certificate-coordinate sign chain (D2)--(D7).  The remaining
analytic or finite determinant work need only provide the coefficient
Wronskian sign and a nonnegative cleared singular target. -/
theorem lrCertificateTTarget_nonnegative_of_clearedSingular
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hB : 0 < lrCertificateBFlow point)
    (hG : 0 < lrCertificateGShape point)
    (hHd : 0 < lrDeterminantHd point)
    (hW : 0 ≤ lrCertificateW point)
    (hgap : 0 ≤ lrCertificateGap point)
    (hcoeff : 0 ≤
      lrDeterminantPsi point / lrCertificateGShape point -
        lrDeterminantC0 point *
          (lrDeterminantT point / lrCertificateGShape point))
    (hcleared : 0 ≤ lrDeterminantClearedSingular
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrCertificateGShape point) (lrDeterminantPsi point)
      (lrDeterminantDelta point) (lrCertificateW point)
      (lrDeterminantC0 point) (lrCertificateX point)
      (lrDeterminantT point)) :
    0 ≤ lrCertificateTTarget point := by
  have hs : 0 < point.s := hinterior.1.1
  have hR : 0 < lrCertificateR point := by
    unfold lrCertificateR
    linarith [hinterior.1.2]
  have hvPlus : 0 < 1 + lrCertificateV point := by
    have hvNonnegative : 0 ≤ lrCertificateV point := by
      unfold lrCertificateV
      exact Real.sqrt_nonneg _
    linarith
  have hscaled := lrCertificateCompensatedDeterminant_scaled
    (point := point) hs.ne' hR.ne' hB.ne' hG.ne' hHd.ne' hvPlus.ne'
  have hcomp : 0 ≤ lrCompensatedDeterminant
      (lrDeterminantHd point) (lrDeterminantV point)
      (lrCertificateJ point) (lrDeterminantMuPrime point)
      (lrDeterminantF point) :=
    lrCompensatedDeterminant_nonnegative_of_cleared
      hB hG hs hHd (lrDeterminantD1_le_D hinterior) hcoeff hcleared hscaled
  have hmu := lrDeterminantMuPrime_nonnegative hW
  have hF := lrDeterminantF_nonnegative hs hgap
  have horiginal : 0 ≤ lrOriginalTangentDeterminant
      (lrDeterminantHd point) (lrDeterminantV point)
      (lrCertificateJ point) (lrDeterminantMuPrime point)
      (lrDeterminantF point) :=
    lrOriginalTangentDeterminant_nonnegative
      hcomp hrelevant.2.le hmu hF
  exact lrCertificateTTarget_nonnegative_of_originalDeterminant hs horiginal

/-- First-bracket version of the complete sign chain.  This is the direct
interface consumed by the cheaper exact ledgers in (D9). -/
theorem lrCertificateTTarget_nonnegative_of_firstBracket
    {point : CertificatePoint}
    (hinterior : LRHighShapeInterior point)
    (hrelevant : LRHighShapeVRelevant point)
    (hB : 0 < lrCertificateBFlow point)
    (hG : 0 < lrCertificateGShape point)
    (hHd : 0 < lrDeterminantHd point)
    (hW : 0 ≤ lrCertificateW point)
    (hgap : 0 ≤ lrCertificateGap point)
    (hcoeff : 0 ≤
      lrDeterminantPsi point / lrCertificateGShape point -
        lrDeterminantC0 point *
          (lrDeterminantT point / lrCertificateGShape point))
    (hfirst : 0 ≤ lrDeterminantFirstBracket
      (lrCertificateBFlow point) (lrDeterminantD1 point)
      (lrCertificateGShape point) (lrDeterminantPsi point)
      (lrDeterminantDelta point) (lrCertificateW point)) :
    0 ≤ lrCertificateTTarget point := by
  have hs : 0 < point.s := hinterior.1.1
  have hR : 0 < lrCertificateR point := by
    unfold lrCertificateR
    linarith [hinterior.1.2]
  have hc0 := lrDeterminantC0_nonnegative hs hHd hR.le hW
  have hT := lrDeterminantT_nonnegative hR hgap
  have hcleared := lrCertificateClearedSingular_nonnegative_of_firstBracket
    hinterior hrelevant hfirst hc0 hT
  exact lrCertificateTTarget_nonnegative_of_clearedSingular
    hinterior hrelevant hB hG hHd hW hgap hcoeff hcleared

end CourtadeKumar
