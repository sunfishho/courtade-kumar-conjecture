import InformationTheory.CourtadeKumar.LRPositiveChartAssembly

/-!
# Sign-safe algebra for the audited compensated determinant

This file kernel-checks the algebraic arrows (D2)--(D7) used by the audited
determinant proof.  The analytic and finite ledgers only have to establish
the indicated scalar inequalities; sign propagation and normalization are
handled here once and for all.
-/

namespace CourtadeKumar

/-- The normalized determinant in (D2). -/
noncomputable def lrDeterminantNormalized
    (B D psi rd c0 x theta : ℝ) : ℝ :=
  psi - 1 + rd + c0 * x * theta + D / B * (psi - c0 * theta)

/-- The cleared singular target in (D4). -/
noncomputable def lrDeterminantClearedSingular
    (B D1 G psi delta W c0 x T : ℝ) : ℝ :=
  B * (psi - G + 4 * delta * W + c0 * x * T) +
    D1 * (psi - c0 * T)

/-- The cheaper first-bracket target used in (D5). -/
noncomputable def lrDeterminantFirstBracket
    (B D1 G psi delta W : ℝ) : ℝ :=
  B * (psi - G + 4 * delta * W) + D1 * psi

/-- The reduced cleared numerator (A1), obtained by removing the favorable
atom `4 * delta * B * W` from the fully cleared determinant. -/
noncomputable def lrDeterminantReducedCleared
    (B D1 G psi c0 x T : ℝ) : ℝ :=
  D1 * G + (B + D1) * (psi - G) + c0 * (B * x - D1) * T

/-- Exact reduced-target decomposition (A1).  Keeping the coefficient
`B + D1` here is essential for the entropy-remainder payment. -/
theorem lrDeterminantClearedSingular_eq_reduced
    (B D1 G psi delta W c0 x T : ℝ) :
    lrDeterminantClearedSingular B D1 G psi delta W c0 x T =
      lrDeterminantReducedCleared B D1 G psi c0 x T +
        4 * delta * B * W := by
  unfold lrDeterminantClearedSingular lrDeterminantReducedCleared
  ring

/-- It is sign-safe to prove only the reduced cleared numerator whenever
the discarded atom has nonnegative factors. -/
theorem lrDeterminantClearedSingular_nonnegative_of_reduced
    {B D1 G psi delta W c0 x T : ℝ}
    (hreduced : 0 ≤ lrDeterminantReducedCleared B D1 G psi c0 x T)
    (hdelta : 0 ≤ delta) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    0 ≤ lrDeterminantClearedSingular B D1 G psi delta W c0 x T := by
  rw [lrDeterminantClearedSingular_eq_reduced]
  exact add_nonneg hreduced
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hdelta) hB) hW)

/-- Exact difference (D3) between the full and singular normalized
determinants. -/
theorem lrDeterminantNormalized_sub_singular
    {B D D1 psi rd c0 x theta : ℝ} (hB : B ≠ 0) :
    lrDeterminantNormalized B D psi rd c0 x theta -
        lrDeterminantNormalized B D1 psi rd c0 x theta =
      (D - D1) / B * (psi - c0 * theta) := by
  unfold lrDeterminantNormalized
  field_simp [hB]
  ring

/-- The sign arrow in (D3). -/
theorem lrDeterminantNormalized_singular_le
    {B D D1 psi rd c0 x theta : ℝ}
    (hB : 0 < B) (hD : D1 ≤ D) (hcoeff : 0 ≤ psi - c0 * theta) :
    lrDeterminantNormalized B D1 psi rd c0 x theta ≤
      lrDeterminantNormalized B D psi rd c0 x theta := by
  have hdiff : 0 ≤ (D - D1) / B * (psi - c0 * theta) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hD) hB.le) hcoeff
  rw [← lrDeterminantNormalized_sub_singular hB.ne'] at hdiff
  linarith

/-- Identity (D4), relating the cleared singular expression to its
normalized form. -/
theorem lrDeterminantClearedSingular_eq_normalized
    {B D1 G psi delta W c0 x T : ℝ} (hB : B ≠ 0) (hG : G ≠ 0) :
    lrDeterminantClearedSingular B D1 G psi delta W c0 x T =
      B * G * lrDeterminantNormalized B D1 (psi / G)
        (4 * delta * W / G) c0 x (T / G) := by
  unfold lrDeterminantClearedSingular lrDeterminantNormalized
  field_simp [hB, hG]

/-- Unscaled form of the first-bracket decomposition (D5). -/
theorem lrDeterminantClearedSingular_eq_firstBracket
    (B D1 G psi delta W c0 x T : ℝ) :
    lrDeterminantClearedSingular B D1 G psi delta W c0 x T =
      lrDeterminantFirstBracket B D1 G psi delta W +
        c0 * T * (B * x - D1) := by
  unfold lrDeterminantClearedSingular lrDeterminantFirstBracket
  ring

/-- Sign form of (D5): once the cheaper first bracket and the four factors
of its correction term are nonnegative, the full cleared singular target
is nonnegative. -/
theorem lrDeterminantClearedSingular_nonnegative_of_firstBracket
    {B D1 G psi delta W c0 x T : ℝ}
    (hfirst : 0 ≤ lrDeterminantFirstBracket B D1 G psi delta W)
    (hc0 : 0 ≤ c0) (hT : 0 ≤ T) (hfactor : 0 ≤ B * x - D1) :
    0 ≤ lrDeterminantClearedSingular B D1 G psi delta W c0 x T := by
  rw [lrDeterminantClearedSingular_eq_firstBracket]
  exact add_nonneg hfirst (mul_nonneg (mul_nonneg hc0 hT) hfactor)

/-- The exact scaled identity (D5). -/
theorem lrDeterminantClearedSingular_scaled_firstBracket
    {B D1 G psi delta W c0 x T R s H : ℝ}
    (hs : s ≠ 0) (hH : H ≠ 0)
    (hc0 : c0 = 4 * R * W / (3 * s * H)) :
    3 * s * H * lrDeterminantClearedSingular
        B D1 G psi delta W c0 x T =
      3 * s * H * lrDeterminantFirstBracket B D1 G psi delta W +
        4 * R * W * T * (B * x - D1) := by
  rw [lrDeterminantClearedSingular_eq_firstBracket, hc0]
  field_simp [hs, hH]

/-- The compensated determinant in (D1). -/
noncomputable def lrCompensatedDeterminant
    (H V J muPrime F : ℝ) : ℝ :=
  H * V + (1 / 3 : ℝ) * J * muPrime * F

/-- The original tangent determinant on the left side of (D7). -/
noncomputable def lrOriginalTangentDeterminant
    (H V J muPrime F : ℝ) : ℝ :=
  H * V + J * muPrime * F

/-- Exact identity (D7). -/
theorem lrOriginalTangentDeterminant_eq_compensated
    (H V J muPrime F : ℝ) :
    lrOriginalTangentDeterminant H V J muPrime F =
      lrCompensatedDeterminant H V J muPrime F +
        (2 / 3 : ℝ) * J * muPrime * F := by
  unfold lrOriginalTangentDeterminant lrCompensatedDeterminant
  ring

/-- The sign conclusion in (D7). -/
theorem lrOriginalTangentDeterminant_nonnegative
    {H V J muPrime F : ℝ}
    (hcomp : 0 ≤ lrCompensatedDeterminant H V J muPrime F)
    (hJ : 0 ≤ J) (hmu : 0 ≤ muPrime) (hF : 0 ≤ F) :
    0 ≤ lrOriginalTangentDeterminant H V J muPrime F := by
  rw [lrOriginalTangentDeterminant_eq_compensated]
  exact add_nonneg hcomp
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hJ) hmu) hF)

/-- Sign-safe chain (D3)--(D6): a nonnegative cleared singular target
implies a nonnegative compensated determinant once the audited positive
factors and the Wronskian coefficient sign are supplied. -/
theorem lrCompensatedDeterminant_nonnegative_of_cleared
    {B D D1 G psi delta W c0 x T s H determinant : ℝ}
    (hB : 0 < B) (hG : 0 < G) (hs : 0 < s) (hH : 0 < H)
    (hD : D1 ≤ D)
    (hcoeff : 0 ≤ psi / G - c0 * (T / G))
    (hcleared : 0 ≤
      lrDeterminantClearedSingular B D1 G psi delta W c0 x T)
    (hscaled : s ^ 2 * determinant =
      B * H * G * lrDeterminantNormalized B D (psi / G)
        (4 * delta * W / G) c0 x (T / G)) :
    0 ≤ determinant := by
  have hsingularProduct : 0 ≤ B * G *
      lrDeterminantNormalized B D1 (psi / G)
        (4 * delta * W / G) c0 x (T / G) := by
    rw [← lrDeterminantClearedSingular_eq_normalized hB.ne' hG.ne']
    exact hcleared
  have hBG : 0 < B * G := mul_pos hB hG
  have hsingular : 0 ≤ lrDeterminantNormalized B D1 (psi / G)
      (4 * delta * W / G) c0 x (T / G) := by
    exact (mul_nonneg_iff_of_pos_left hBG).mp (by
      simpa [mul_assoc] using hsingularProduct)
  have hnormalized :
      lrDeterminantNormalized B D1 (psi / G) (4 * delta * W / G)
          c0 x (T / G) ≤
        lrDeterminantNormalized B D (psi / G) (4 * delta * W / G)
          c0 x (T / G) :=
    lrDeterminantNormalized_singular_le
      (D := D) (D1 := D1) (rd := 4 * delta * W / G) (x := x)
      hB hD hcoeff
  have hfull : 0 ≤ lrDeterminantNormalized B D (psi / G)
      (4 * delta * W / G) c0 x (T / G) :=
    hsingular.trans hnormalized
  have hscale : 0 ≤ B * H * G *
      lrDeterminantNormalized B D (psi / G)
        (4 * delta * W / G) c0 x (T / G) := by
    positivity
  have hsSq : 0 < s ^ 2 := sq_pos_of_pos hs
  have hscaledNonnegative : 0 ≤ s ^ 2 * determinant := by
    rw [hscaled]
    exact hscale
  exact (mul_nonneg_iff_of_pos_left hsSq).mp hscaledNonnegative

end CourtadeKumar
