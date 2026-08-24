import InformationTheory.CourtadeKumar.CenteredRadialThreshold

/-! Monotone motion of the canonical radial contact. -/

open Set
open scoped NNReal

namespace CourtadeKumar

/-- The canonical contact location strictly decreases with the ray shape. -/
theorem canonicalRadialContactZ_strictAntiOn
    {alpha : ℝ≥0} {theta : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (canonicalRadialContactZ alpha theta halpha htheta)
      (Ioo (0 : ℝ) 1) := by
  intro r₁ hr₁ r₂ hr₂ hr₁₂
  let rho : ℝ := channelRho (alpha : ℝ)
  let z₁ : ℝ := canonicalRadialContactZ alpha theta halpha htheta r₁
  let z₂ : ℝ := canonicalRadialContactZ alpha theta halpha htheta r₂
  have hrho : rho ∈ Ioo (0 : ℝ) 1 := by
    unfold rho channelRho
    constructor <;> linarith [halpha.1, halpha.2]
  have hz₁spec := canonicalRadialContactZ_spec halpha htheta hr₁.1
  have hz₂spec := canonicalRadialContactZ_spec halpha htheta hr₂.1
  have hz₁ : z₁ ∈ Ioo (0 : ℝ) (1 + r₁)⁻¹ := hz₁spec.1
  have hz₂ : z₂ ∈ Ioo (0 : ℝ) (1 + r₂)⁻¹ := hz₂spec.1
  have hz₁value : radialEulerLogRatio rho r₁ z₁ = theta := hz₁spec.2
  have hz₂value : radialEulerLogRatio rho r₂ z₂ = theta := hz₂spec.2
  by_cases hz₁cap : z₁ < (1 + r₂)⁻¹
  · have hshapeAnti : StrictAntiOn (fun r ↦ radialEulerLogRatio rho r z₁)
        (Icc r₁ r₂) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc r₁ r₂)
      · intro r hr
        have hrpos : 0 < r := hr₁.1.trans_le hr.1
        have h1r₂ : 0 < 1 + r₂ := by linarith [hr₂.1]
        have hupper₂ : (1 + r₂) * z₁ < 1 := by
          calc
            (1 + r₂) * z₁ = z₁ * (1 + r₂) := mul_comm _ _
            _ < (1 + r₂)⁻¹ * (1 + r₂) :=
              mul_lt_mul_of_pos_right hz₁cap h1r₂
            _ = 1 := inv_mul_cancel₀ h1r₂.ne'
        have hupper : (1 + r) * z₁ < 1 :=
          (mul_le_mul_of_nonneg_right (by linarith [hr.2]) hz₁.1.le).trans_lt hupper₂
        obtain ⟨harg1, hargR, _⟩ := radialEulerLogArg_order_physical
          (show rho ∈ Ico (0 : ℝ) 1 from ⟨hrho.1.le, hrho.2⟩)
          hrpos hz₁.1 hupper
        have hz₁lt1 : z₁ < 1 := by nlinarith [mul_pos hrpos hz₁.1]
        have hden := (radialEulerLog_pos_of_arg
          ⟨harg1.1, harg1.2.trans (by linarith [hz₁.1])⟩).ne'
        exact (hasDerivAt_radialEulerLogRatio_shape
          hargR.1.ne' harg1.1.ne' hden).continuousAt.continuousWithinAt
      · intro r hr
        rw [interior_Icc] at hr
        have hrpos : 0 < r := hr₁.1.trans_le hr.1.le
        have h1r₂ : 0 < 1 + r₂ := by linarith [hr₂.1]
        have hupper₂ : (1 + r₂) * z₁ < 1 := by
          calc
            (1 + r₂) * z₁ = z₁ * (1 + r₂) := mul_comm _ _
            _ < (1 + r₂)⁻¹ * (1 + r₂) :=
              mul_lt_mul_of_pos_right hz₁cap h1r₂
            _ = 1 := inv_mul_cancel₀ h1r₂.ne'
        have hupper : (1 + r) * z₁ < 1 :=
          (mul_le_mul_of_nonneg_right (by linarith [hr.2]) hz₁.1.le).trans_lt hupper₂
        exact deriv_radialEulerLogRatio_shape_neg_physical
          hrho hrpos hz₁.1 hupper
    have hshape : radialEulerLogRatio rho r₂ z₁ < theta := by
      rw [← hz₁value]
      exact hshapeAnti (left_mem_Icc.2 hr₁₂.le)
        (right_mem_Icc.2 hr₁₂.le) hr₁₂
    have hzAnti := radialEulerLogRatio_strictAntiOn_physical
      (show rho ∈ Ico (0 : ℝ) 1 from ⟨hrho.1.le, hrho.2⟩) hr₂.1
    have hz₁cell : z₁ ∈ Ioo (0 : ℝ) (1 + r₂)⁻¹ := ⟨hz₁.1, hz₁cap⟩
    by_contra hn
    have hz₁le₂ : z₁ ≤ z₂ := le_of_not_gt hn
    rcases hz₁le₂.eq_or_lt with heq | hlt
    · rw [← heq] at hz₂value
      linarith
    · have := hzAnti hz₁cell hz₂ hlt
      linarith
  · exact hz₂.2.trans_le (le_of_not_gt hz₁cap)

theorem canonicalRadialContactZ_gt_half_before_threshold
    {alpha : ℝ≥0} {theta rstar r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ)) rstar (1 / 2) = theta)
    (hr : r ∈ Ioo (0 : ℝ) 1) (hrrstar : r < rstar) :
    1 / 2 < canonicalRadialContactZ alpha theta halpha htheta r := by
  rw [← canonicalRadialContactZ_eq_half_of_centeredRoot
    halpha htheta hrstar hcenter]
  exact canonicalRadialContactZ_strictAntiOn halpha htheta hr hrstar hrrstar

theorem canonicalRadialContactZ_lt_half_after_threshold
    {alpha : ℝ≥0} {theta rstar r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (hcenter : radialEulerLogRatio (channelRho (alpha : ℝ)) rstar (1 / 2) = theta)
    (hr : r ∈ Ioo (0 : ℝ) 1) (hrstarr : rstar < r) :
    canonicalRadialContactZ alpha theta halpha htheta r < 1 / 2 := by
  rw [← canonicalRadialContactZ_eq_half_of_centeredRoot
    halpha htheta hrstar hcenter]
  exact canonicalRadialContactZ_strictAntiOn halpha htheta hrstar hr hrstarr

end CourtadeKumar
