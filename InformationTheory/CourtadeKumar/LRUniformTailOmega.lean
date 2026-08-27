import InformationTheory.CourtadeKumar.LRUniformTailCurvature
import InformationTheory.CourtadeKumar.LRNegativeChartBounds

/-!
# Uniform cancellation-tail bounds for the noise kernel

This proves manuscript (M18).  The lower bound is obtained without
introducing an improper endpoint integral: after adding the sharp quadratic
correction, (M17) says that the corrected entropy scalar is concave.  Its
supporting-line inequality at the right endpoint is exactly the desired
bound for `omega_s(y)`.
-/

open Set

namespace CourtadeKumar

/-- The lower estimate in manuscript (M18). -/
theorem lrCertificateOmega_lower
    {s y : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    s ^ 2 * (1 - y) ^ 2 / (12 * (y + s)) ≤
      lrCertificateOmega s y := by
  let b := lrCertificateB s y
  let c := 1 / (12 * (y + s))
  let F : ℝ → ℝ := fun u ↦ lrCertificateQ u + c * u ^ 2
  let F' : ℝ → ℝ := fun u ↦ lrCertificateQPrime u + 2 * c * u
  let F'' : ℝ → ℝ := fun u ↦ lrCertificateQSecond u + 2 * c
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
  have hcPos : 0 < c := by
    unfold c
    exact one_div_pos.mpr (mul_pos (by norm_num) (add_pos hy.1 hs.1))
  have hFderiv : ∀ u ∈ Icc y b, HasDerivAt F (F' u) u := by
    intro u hu
    have hq := hasDerivAt_lrCertificateQ (hmem u hu)
    have hquad := ((hasDerivAt_id u).pow 2).const_mul c
    unfold F F'
    convert hq.add hquad using 1 <;> simp only [id_eq] <;> ring
  have hF'deriv : ∀ u ∈ interior (Icc y b),
      HasDerivWithinAt F' (F'' u) (interior (Icc y b)) u := by
    intro u hu
    have huClosed : u ∈ Icc y b := interior_subset hu
    have hq := hasDerivAt_lrCertificateQPrime (hmem u huClosed)
    have hlin := (hasDerivAt_id u).const_mul (2 * c)
    unfold F' F''
    simpa only [Pi.add_apply, Pi.mul_apply, id_eq, mul_one] using
      (hq.add hlin).hasDerivWithinAt
  have hF''nonpos : ∀ u ∈ interior (Icc y b), F'' u ≤ 0 := by
    intro u hu
    have huClosed : u ∈ Icc y b := interior_subset hu
    have huMem := hmem u huClosed
    have hcurv := lrCertificateQSecond_upper_six huMem
    have hub : u ≤ y + s := by
      have hub' : u ≤ b := huClosed.2
      rw [hbEq] at hub'
      nlinarith [mul_le_mul_of_nonneg_left (sub_le_self y hy.1.le) hs.1.le]
    have huPos : 0 < u := huMem.1
    have hysPos : 0 < y + s := add_pos hy.1 hs.1
    have hrecip : 1 / (y + s) ≤ 1 / u := by
      exact one_div_le_one_div_of_le huPos hub
    have hscaled : 1 / (6 * (y + s)) ≤ 1 / (6 * u) := by
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hysPos)
        (mul_pos (by norm_num) huPos)]
      nlinarith
    have hcEq : 2 * c = 1 / (6 * (y + s)) := by
      unfold c
      field_simp [hysPos.ne']
      ring
    unfold F''
    rw [hcEq]
    have hcurv' : lrCertificateQSecond u ≤ -(1 / (6 * u)) := by
      convert hcurv using 1 <;> ring
    linarith
  have hconcave : ConcaveOn ℝ (Icc y b) F := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc y b)
    · exact continuousOn_of_forall_continuousAt fun u hu ↦
        (hFderiv u hu).continuousAt
    · intro u hu
      exact (hFderiv u (interior_subset hu)).hasDerivWithinAt
    · exact hF'deriv
    · exact hF''nonpos
  have hsupport := hconcave.le_slope_of_hasDerivAt
    (show y ∈ Icc y b from ⟨le_rfl, hyb.le⟩)
    (show b ∈ Icc y b from ⟨hyb.le, le_rfl⟩) hyb
    (hFderiv b ⟨hyb.le, le_rfl⟩)
  have hgapPos : 0 < b - y := sub_pos.mpr hyb
  rw [slope_def_field, le_div_iff₀ hgapPos] at hsupport
  unfold F F' at hsupport
  unfold lrCertificateOmega
  have hbCert : lrCertificateB s y = b := rfl
  rw [hbCert]
  rw [hbEq] at hsupport ⊢
  unfold c at hsupport
  have hysPos : 0 < y + s := add_pos hy.1 hs.1
  field_simp [hysPos.ne'] at hsupport
  rw [div_le_iff₀ (mul_pos (by norm_num) hysPos)]
  nlinarith

/-- The endpoint estimate `0 < W ≤ s/4` in manuscript (M18). -/
theorem lrCertificateOmega_zero_mem
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    lrCertificateOmega s 0 ∈ Ioc (0 : ℝ) (s / 4) := by
  have hR : 1 - s ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hs.1, hs.2]
  have heq := lrCertificateOmega_one_sub_sq hs
    (show (1 : ℝ) ∈ Ioc 0 1 by norm_num)
  simp only [one_pow, sub_self] at heq
  rw [heq]
  constructor
  · exact lrWKernel_one_pos hR
  · have h := four_mul_lrWKernel_one_le_one_sub hR
    nlinarith

end CourtadeKumar
