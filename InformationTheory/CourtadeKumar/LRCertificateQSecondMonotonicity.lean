import InformationTheory.CourtadeKumar.LRCertificateQ
import InformationTheory.CourtadeKumar.LRScalarComparison

/-!
# Monotonicity of the LR certificate curvature

This module proves that `lrCertificateQSecond` is increasing on its
open physical domain.  The proof works first in the radial coordinate
`z = sqrt R`.  If

`S(z) = z / (1 - z^2) - artanh z`,

then `topPsiDeriv2 R = S(sqrt R) / (4 * sqrt R ^ 3)`.  The derivative of the
radial quotient has numerator

`2*z^3/(1-z^2)^2 - 3*S(z)`.

The already-proved cubic lower bound for `artanh` makes this numerator
strictly positive without introducing a third derivative.  Strict
monotonicity survives composition with `sqrt`; the definition
`lrCertificateQSecond y = -topPsiDeriv2 (1-y)` then reverses order twice.
-/

noncomputable section

open Set

namespace CourtadeKumar

/-- Numerator controlling the derivative of the radial form of
`topPsiDeriv2`. -/
noncomputable def topPsiDeriv2RadialGap (z : ℝ) : ℝ :=
  2 * z ^ 3 / (1 - z ^ 2) ^ 2 - 3 * topPsiSlopeGap z

/-- Radial form of `topPsiDeriv2`: definitionally,
`topPsiDeriv2 R = topPsiDeriv2Radial (sqrt R)`. -/
noncomputable def topPsiDeriv2Radial (z : ℝ) : ℝ :=
  topPsiSlopeGap z / (4 * z ^ 3)

/-- The radial derivative numerator is strictly positive throughout the
open unit interval. -/
theorem topPsiDeriv2RadialGap_pos
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    0 < topPsiDeriv2RadialGap z := by
  have hdenPos : 0 < 1 - z ^ 2 := by
    have hfactor : 0 < (1 - z) * (1 + z) :=
      mul_pos (sub_pos.mpr hz.2) (by linarith [hz.1])
    nlinarith
  have hart : z + z ^ 3 / 3 ≤ Real.artanh z :=
    artanh_cubic_lower ⟨hz.1.le, hz.2⟩
  have hbase :
      0 < 2 * z ^ 3 / (1 - z ^ 2) ^ 2 -
        3 * (z / (1 - z ^ 2) - (z + z ^ 3 / 3)) := by
    have hid :
        2 * z ^ 3 / (1 - z ^ 2) ^ 2 -
            3 * (z / (1 - z ^ 2) - (z + z ^ 3 / 3)) =
          z ^ 5 * (1 + z ^ 2) / (1 - z ^ 2) ^ 2 := by
      field_simp [hdenPos.ne']
      ring
    rw [hid]
    exact div_pos
      (mul_pos (pow_pos hz.1 5) (by positivity))
      (sq_pos_of_pos hdenPos)
  unfold topPsiDeriv2RadialGap topPsiSlopeGap
  linarith

/-- Exact derivative of the radial form of `topPsiDeriv2`. -/
theorem hasDerivAt_topPsiDeriv2Radial
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt topPsiDeriv2Radial
      (topPsiDeriv2RadialGap z / (4 * z ^ 4)) z := by
  have hzOpen : z ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hz.1], hz.2⟩
  have hzNe : z ≠ 0 := hz.1.ne'
  have hgapDenNe : 1 - z ^ 2 ≠ 0 := by
    nlinarith [hz.1, hz.2]
  have hden : HasDerivAt (fun x : ℝ => 4 * x ^ 3) (12 * z ^ 2) z := by
    convert ((hasDerivAt_id z).pow 3).const_mul 4 using 1 <;>
      simp only [id_eq] <;> ring
  have hquot := (hasDerivAt_topPsiSlopeGap hzOpen).div hden (by positivity)
  unfold topPsiDeriv2Radial
  convert hquot using 1
  unfold topPsiDeriv2RadialGap
  field_simp [hzNe, hgapDenNe]
  ring

/-- The radial form of `topPsiDeriv2` is strictly increasing. -/
theorem topPsiDeriv2Radial_strictMonoOn :
    StrictMonoOn topPsiDeriv2Radial (Ioo (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) 1)
  · intro z hz
    exact
      (hasDerivAt_topPsiDeriv2Radial hz).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ioo] at hz
    rw [(hasDerivAt_topPsiDeriv2Radial hz).deriv]
    exact div_pos (topPsiDeriv2RadialGap_pos hz)
      (mul_pos (by norm_num) (pow_pos hz.1 4))

/-- The second derivative of the radial entropy primitive is strictly
increasing in the square-radius coordinate. -/
theorem topPsiDeriv2_strictMonoOn :
    StrictMonoOn topPsiDeriv2 (Ioo (0 : ℝ) 1) := by
  intro R hR T hT hRT
  have hsqrtR : Real.sqrt R ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 hR.1
    · simpa using (Real.sqrt_lt_sqrt_iff hR.1.le).2 hR.2
  have hsqrtT : Real.sqrt T ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 hT.1
    · simpa using (Real.sqrt_lt_sqrt_iff hT.1.le).2 hT.2
  have hsqrtRT : Real.sqrt R < Real.sqrt T :=
    Real.sqrt_lt_sqrt hR.1.le hRT
  simpa [topPsiDeriv2, topPsiDeriv2Radial] using
    topPsiDeriv2Radial_strictMonoOn hsqrtR hsqrtT hsqrtRT

/-- The manuscript curvature `Q''` is strictly increasing on its open
physical domain. -/
theorem lrCertificateQSecond_strictMonoOn :
    StrictMonoOn lrCertificateQSecond (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hOneSubY : 1 - y ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2]
  have hOneSubX : 1 - x ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hradial := topPsiDeriv2_strictMonoOn
    hOneSubY hOneSubX (by linarith)
  simpa [lrCertificateQSecond] using neg_lt_neg hradial

/-- Non-strict form used by interval endpoint enclosures. -/
theorem lrCertificateQSecond_monotoneOn :
    MonotoneOn lrCertificateQSecond (Ioo (0 : ℝ) 1) :=
  lrCertificateQSecond_strictMonoOn.monotoneOn

end CourtadeKumar
