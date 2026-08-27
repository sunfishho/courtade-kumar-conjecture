import InformationTheory.CourtadeKumar.LRLowerFaceQ0Bound
import InformationTheory.CourtadeKumar.LRUniformTailCurvature
import InformationTheory.CourtadeKumar.LRHighShapeKernelAssembly

/-!
# Entropy remainder on the small-`k` midpoint face

This formalizes the differential decomposition `Q = q₀ + r₀`.  In
particular, the remainder is convex and its curvature has the uniform
enclosure needed for the lower-face estimates.
-/

open Set

namespace CourtadeKumar

noncomputable def lrLowerFaceR0Prime (y : ℝ) : ℝ :=
  lrCertificateQPrime y - lrLowerFaceQ0Prime y

noncomputable def lrLowerFaceR0Second (y : ℝ) : ℝ :=
  lrCertificateQSecond y - lrLowerFaceQ0Second y

noncomputable def lrLowerFaceR0CurvatureZ (z : ℝ) : ℝ :=
  (Real.artanh z - z) / (4 * z ^ 3)

noncomputable def lrLowerFaceR0CurvatureZDeriv (z : ℝ) : ℝ :=
  (z ^ 3 / (1 - z ^ 2) - 3 * (Real.artanh z - z)) /
    (4 * z ^ 4)

noncomputable def lrLowerFaceOmegaR0 (s y : ℝ) : ℝ :=
  lrLowerFaceR0 (lrCertificateB s y) - lrLowerFaceR0 y -
    s * (1 - y) * lrLowerFaceR0Prime (lrCertificateB s y)

noncomputable def lrLowerFaceOmegaR0Deriv (s y : ℝ) : ℝ :=
  lrLowerFaceR0Prime (lrCertificateB s y) - lrLowerFaceR0Prime y -
    s * (1 - s) * (1 - y) *
      lrLowerFaceR0Second (lrCertificateB s y)

noncomputable def lrLowerFacePWR0 (s k chi v : ℝ) : ℝ :=
  lrLowerFaceOmegaR0 s (chi * (s * k)) +
    lrLowerFaceOmegaR0 s (s * k) / v

theorem hasDerivAt_lrLowerFaceR0
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt lrLowerFaceR0 (lrLowerFaceR0Prime y) y := by
  unfold lrLowerFaceR0 lrLowerFaceR0Prime
  exact (hasDerivAt_lrCertificateQ hy).sub
    (hasDerivAt_lrLowerFaceQ0 hy.1)

theorem hasDerivAt_lrLowerFaceR0Prime
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt lrLowerFaceR0Prime (lrLowerFaceR0Second y) y := by
  unfold lrLowerFaceR0Prime lrLowerFaceR0Second
  exact (hasDerivAt_lrCertificateQPrime hy).sub
    (hasDerivAt_lrLowerFaceQ0Prime hy.1)

lemma lrLowerFaceR0Second_nonneg
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrLowerFaceR0Second y := by
  have hcurv := lrCertificateQSecond_lower hy
  unfold lrLowerFaceR0Second lrLowerFaceQ0Second
  linarith

lemma lrLowerFaceR0Second_upper
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    lrLowerFaceR0Second y ≤ 1 / (12 * y) := by
  have hcurv := lrCertificateQSecond_upper_six hy
  unfold lrLowerFaceR0Second lrLowerFaceQ0Second
  have hyNe := hy.1.ne'
  have hadd := add_le_add_right hcurv (1 / (4 * y))
  calc
    lrCertificateQSecond y - (-1 / (4 * y)) =
        lrCertificateQSecond y + 1 / (4 * y) := by ring
    _ ≤ -1 / (6 * y) + 1 / (4 * y) := by
      simpa [add_comm] using hadd
    _ = 1 / (12 * y) := by field_simp [hyNe]; ring

lemma lrLowerFaceR0Second_eq_curvatureZ
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    lrLowerFaceR0Second y =
      lrLowerFaceR0CurvatureZ (Real.sqrt (1 - y)) := by
  let z := Real.sqrt (1 - y)
  have hzPos : 0 < z := Real.sqrt_pos.2 (by linarith [hy.2])
  have hzSq : z ^ 2 = 1 - y := by
    dsimp [z]
    exact Real.sq_sqrt (by linarith [hy.2])
  have hyNe := hy.1.ne'
  have hzNe := hzPos.ne'
  unfold lrLowerFaceR0Second lrLowerFaceQ0Second
    lrLowerFaceR0CurvatureZ
  rw [lrCertificateQSecond_eq hy]
  change (Real.artanh z - z / y) / (4 * z ^ 3) -
      (-1 / (4 * y)) = (Real.artanh z - z) / (4 * z ^ 3)
  field_simp [hyNe, hzNe]
  nlinarith [hzSq]

theorem hasDerivAt_lrLowerFaceR0CurvatureZ
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt lrLowerFaceR0CurvatureZ
      (lrLowerFaceR0CurvatureZDeriv z) z := by
  have hnum := (hasDerivAt_artanh
    (show z ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [hz.1], hz.2⟩)).sub
      (hasDerivAt_id z)
  have hden := ((hasDerivAt_id z).pow 3).const_mul 4
  have hdenNe : 4 * z ^ 3 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 3 hz.1.ne')
  have hzGap : 0 < z * (1 - z) := mul_pos hz.1 (sub_pos.mpr hz.2)
  have hbasePos : 0 < 1 - z ^ 2 := by nlinarith
  have hbaseNe : 1 - z ^ 2 ≠ 0 := hbasePos.ne'
  have h := hnum.div hden hdenNe
  unfold lrLowerFaceR0CurvatureZ lrLowerFaceR0CurvatureZDeriv
  convert h using 1
  simp only [Pi.sub_apply, Pi.div_apply, Pi.pow_apply, id_eq]
  field_simp [hz.1.ne', hbaseNe]
  ring

lemma lrLowerFaceR0CurvatureZDeriv_nonneg
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrLowerFaceR0CurvatureZDeriv z := by
  have hpade := artanh_le_cubicPade_unit
    (show z ∈ Ico (0 : ℝ) 1 from ⟨hz.1.le, hz.2⟩)
  have hzGap : 0 < z * (1 - z) := mul_pos hz.1 (sub_pos.mpr hz.2)
  have hbase : 0 < 1 - z ^ 2 := by nlinarith
  have hnum : 0 ≤ z ^ 3 / (1 - z ^ 2) -
      3 * (Real.artanh z - z) := by
    have hpade' : Real.artanh z - z ≤
        z ^ 3 / (3 * (1 - z ^ 2)) := by linarith
    have hscaled := mul_le_mul_of_nonneg_left hpade'
      (show (0 : ℝ) ≤ 3 by norm_num)
    have hright : 3 * (z ^ 3 / (3 * (1 - z ^ 2))) =
        z ^ 3 / (1 - z ^ 2) := by
      field_simp [hbase.ne']
    rw [hright] at hscaled
    exact sub_nonneg.mpr hscaled
  unfold lrLowerFaceR0CurvatureZDeriv
  exact div_nonneg hnum (by positivity)

theorem lrLowerFaceR0CurvatureZ_monotoneOn :
    MonotoneOn lrLowerFaceR0CurvatureZ (Ioo (0 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo (0 : ℝ) 1)
  · intro z hz
    exact (hasDerivAt_lrLowerFaceR0CurvatureZ hz).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ioo] at hz
    exact (hasDerivAt_lrLowerFaceR0CurvatureZ hz).differentiableAt
      |>.differentiableWithinAt
  · intro z hz
    rw [interior_Ioo] at hz
    rw [(hasDerivAt_lrLowerFaceR0CurvatureZ hz).deriv]
    exact lrLowerFaceR0CurvatureZDeriv_nonneg hz

/-- The remainder curvature decreases with `y`, equivalently `r₀'''≤0`
in the manuscript. -/
theorem lrLowerFaceR0Second_antitoneOn :
    AntitoneOn lrLowerFaceR0Second (Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  let za := Real.sqrt (1 - a)
  let zb := Real.sqrt (1 - b)
  have hza : za ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 (by linarith [ha.2])
    · simpa [za] using
        (Real.sqrt_lt_sqrt_iff (by linarith [ha.2] : 0 ≤ 1 - a)).2
          (by linarith [ha.1] : 1 - a < 1)
  have hzb : zb ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_pos.2 (by linarith [hb.2])
    · simpa [zb] using
        (Real.sqrt_lt_sqrt_iff (by linarith [hb.2] : 0 ≤ 1 - b)).2
          (by linarith [hb.1] : 1 - b < 1)
  have hzOrder : zb ≤ za := by
    exact Real.sqrt_le_sqrt (by linarith)
  have hmono := lrLowerFaceR0CurvatureZ_monotoneOn hzb hza hzOrder
  rw [lrLowerFaceR0Second_eq_curvatureZ ha,
    lrLowerFaceR0Second_eq_curvatureZ hb]
  exact hmono

theorem hasDerivAt_lrLowerFaceOmegaR0
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (lrLowerFaceOmegaR0 s)
      (lrLowerFaceOmegaR0Deriv s y) y := by
  have hbMem := lrCertificateB_mem_Ioo hs hy
  have hb : HasDerivAt (lrCertificateB s) (1 - s) y := by
    unfold lrCertificateB
    convert (hasDerivAt_const y s).add
      ((hasDerivAt_id y).const_mul (1 - s)) using 1
    ring
  have hrb := (hasDerivAt_lrLowerFaceR0 hbMem).comp y hb
  have hry := hasDerivAt_lrLowerFaceR0 hy
  have hrpb := (hasDerivAt_lrLowerFaceR0Prime hbMem).comp y hb
  have honeMinusY := (hasDerivAt_const y 1).sub (hasDerivAt_id y)
  have hfactor := ((hasDerivAt_const y s).mul honeMinusY).mul hrpb
  have h := (hrb.sub hry).sub hfactor
  unfold lrLowerFaceOmegaR0 lrLowerFaceOmegaR0Deriv
  convert h using 1 <;>
    simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply, id_eq] <;> ring

lemma lrLowerFaceOmegaR0Deriv_nonneg
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    0 ≤ lrLowerFaceOmegaR0Deriv s y := by
  let b := lrCertificateB s y
  have hbEq : b = y + s * (1 - y) := by
    unfold b lrCertificateB
    ring
  have hyb : y < b := by
    rw [hbEq]
    nlinarith [mul_pos hs.1 (sub_pos.mpr hy.2)]
  have hbLt : b < 1 := by
    rw [hbEq]
    nlinarith [mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr hy.2)]
  have hmem : ∀ u ∈ Icc y b, u ∈ Ioo (0 : ℝ) 1 := by
    intro u hu
    exact ⟨hy.1.trans_le hu.1, hu.2.trans_lt hbLt⟩
  have hderiv : ∀ u ∈ Icc y b,
      HasDerivAt lrLowerFaceR0Prime (lrLowerFaceR0Second u) u :=
    fun u hu ↦ hasDerivAt_lrLowerFaceR0Prime (hmem u hu)
  have hconcave : ConcaveOn ℝ (Icc y b) lrLowerFaceR0Prime := by
    apply AntitoneOn.concaveOn_of_deriv (convex_Icc y b)
    · exact continuousOn_of_forall_continuousAt fun u hu ↦
        (hderiv u hu).continuousAt
    · intro u hu
      exact (hderiv u (interior_subset hu)).differentiableAt
        |>.differentiableWithinAt
    · intro u hu w hw huw
      rw [(hderiv u (interior_subset hu)).deriv,
        (hderiv w (interior_subset hw)).deriv]
      exact lrLowerFaceR0Second_antitoneOn
        (hmem u (interior_subset hu)) (hmem w (interior_subset hw)) huw
  have hsupport := hconcave.le_slope_of_hasDerivAt
    (show y ∈ Icc y b from ⟨le_rfl, hyb.le⟩)
    (show b ∈ Icc y b from ⟨hyb.le, le_rfl⟩) hyb
    (hderiv b ⟨hyb.le, le_rfl⟩)
  have hgapPos : 0 < b - y := sub_pos.mpr hyb
  rw [slope_def_field, le_div_iff₀ hgapPos] at hsupport
  have hsecond := lrLowerFaceR0Second_nonneg
    (hmem b ⟨hyb.le, le_rfl⟩)
  unfold lrLowerFaceOmegaR0Deriv
  change 0 ≤ lrLowerFaceR0Prime b - lrLowerFaceR0Prime y -
    s * (1 - s) * (1 - y) * lrLowerFaceR0Second b
  rw [hbEq] at hsupport hsecond ⊢
  have hresidual : 0 ≤ s ^ 2 * (1 - y) *
      lrLowerFaceR0Second (y + s * (1 - y)) :=
    mul_nonneg (mul_nonneg (sq_nonneg s) (sub_pos.mpr hy.2).le) hsecond
  nlinarith [hsupport, hresidual]

/-- The entropy-remainder noise contribution increases with its radial
argument, the derivative-sign assertion used in (M24). -/
theorem lrLowerFaceOmegaR0_monotoneOn
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    MonotoneOn (lrLowerFaceOmegaR0 s) (Ioo (0 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo (0 : ℝ) 1)
  · intro y hy
    exact (hasDerivAt_lrLowerFaceOmegaR0 hs hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    exact (hasDerivAt_lrLowerFaceOmegaR0 hs hy).differentiableAt
      |>.differentiableWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    rw [(hasDerivAt_lrLowerFaceOmegaR0 hs hy).deriv]
    exact lrLowerFaceOmegaR0Deriv_nonneg hs hy

theorem lrLowerFaceR0Prime_monotoneOn :
    MonotoneOn lrLowerFaceR0Prime (Ioo (0 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo (0 : ℝ) 1)
  · intro y hy
    exact (hasDerivAt_lrLowerFaceR0Prime hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    exact (hasDerivAt_lrLowerFaceR0Prime hy).differentiableAt
      |>.differentiableWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    rw [(hasDerivAt_lrLowerFaceR0Prime hy).deriv]
    exact lrLowerFaceR0Second_nonneg hy

/-- Exact splitting of the noise primitive into logarithmic core and
entropy remainder. -/
lemma lrCertificateOmega_eq_lowerFace_split
    {s y : ℝ} :
    lrCertificateOmega s y =
      lrLowerFaceOmegaQ0 s y + lrLowerFaceOmegaR0 s y := by
  unfold lrCertificateOmega lrLowerFaceOmegaQ0 lrLowerFaceOmegaR0
    lrLowerFaceR0 lrLowerFaceR0Prime
  ring

/-- Exact splitting of `P_W` in lower-face coordinates. -/
lemma lrCertificatePWValue_eq_lowerFace_split
    {s k chi v : ℝ} :
    lrCertificatePWValue s (chi * (s * k)) (s * k) v =
      lrLowerFacePWQ0 s k chi v + lrLowerFacePWR0 s k chi v := by
  unfold lrCertificatePWValue lrLowerFacePWQ0 lrLowerFacePWR0
  rw [lrCertificateOmega_eq_lowerFace_split,
    lrCertificateOmega_eq_lowerFace_split]
  ring

end CourtadeKumar
