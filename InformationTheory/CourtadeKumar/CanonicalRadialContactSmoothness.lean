import InformationTheory.CourtadeKumar.RadialContactImplicit
import InformationTheory.CourtadeKumar.CanonicalRadialProfile

/-! Smoothness of the canonical radial contact selector. -/

open Set
open Filter
open scoped NNReal

namespace CourtadeKumar

/-- The globally defined canonical root selector is locally `C²` on every
interior ray. -/
theorem contDiffAt_canonicalRadialContactZ
    {alpha : ℝ≥0} {theta r : ℝ}
    (halpha : (alpha : ℝ) ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (htheta : theta ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ (2 : WithTop ℕ∞)
      (canonicalRadialContactZ alpha theta halpha htheta) r := by
  let rho : ℝ := channelRho (alpha : ℝ)
  let z : ℝ := canonicalRadialContactZ alpha theta halpha htheta r
  have hrho : rho ∈ Ico (0 : ℝ) 1 := by
    dsimp [rho]
    exact channelRho_mem_Ico_of_alpha_interior halpha
  have hzspec := canonicalRadialContactZ_spec halpha htheta hr.1
  have hz : z ∈ Ioo (0 : ℝ) (1 + r)⁻¹ := hzspec.1
  have hroot : radialEulerLogRatio rho r z = theta := hzspec.2
  have h1r : 0 < 1 + r := add_pos_of_pos_of_nonneg zero_lt_one hr.1.le
  have hupper : (1 + r) * z < 1 := by
    calc
      (1 + r) * z = z * (1 + r) := mul_comm _ _
      _ < (1 + r)⁻¹ * (1 + r) := mul_lt_mul_of_pos_right hz.2 h1r
      _ = 1 := inv_mul_cancel₀ h1r.ne'
  obtain ⟨harg1, hargR, _⟩ :=
    radialEulerLogArg_order_physical hrho hr.1 hz.1 hupper
  have hden : radialEulerLog 1 r z ≠ 0 :=
    (radialEulerLog_pos_of_arg
      ⟨harg1.1, harg1.2.trans (by linarith [hz.1])⟩).ne'
  have hcontact : deriv (radialEulerLogRatio rho r) z ≠ 0 :=
    radialEulerLogRatio_contact_deriv_ne_zero hrho hr.1 hz.1 hupper
  obtain ⟨φ, hφdiff, hφr, hφroot⟩ := exists_localContDiff_radialContact
    hargR.1.ne' harg1.1.ne' hden hcontact hroot
  have hφcont : Tendsto φ (nhds r) (nhds z) := by
    rw [← hφr]
    exact hφdiff.continuousAt
  have hspos : ∀ᶠ s in nhds r, 0 < s := lt_mem_nhds hr.1
  have hφpos : ∀ᶠ s in nhds r, 0 < φ s :=
    hφcont.eventually_const_lt hz.1
  have hprod : Tendsto (fun s ↦ (1 + s) * φ s) (nhds r)
      (nhds ((1 + r) * z)) := by
    exact (tendsto_const_nhds.add tendsto_id).mul hφcont
  have hφupper : ∀ᶠ s in nhds r, (1 + s) * φ s < 1 :=
    hprod.eventually_lt_const hupper
  have hlocal :
      (canonicalRadialContactZ alpha theta halpha htheta) =ᶠ[nhds r] φ := by
    filter_upwards [hspos, hφpos, hφupper, hφroot] with s hs hzs hzsupper hsroot
    have h1s : 0 < 1 + s := by linarith
    have hφmem : φ s ∈ Ioo (0 : ℝ) (1 + s)⁻¹ := by
      refine ⟨hzs, ?_⟩
      rw [inv_eq_one_div, lt_div_iff₀ h1s]
      simpa [mul_comm] using hzsupper
    have hcanspec := canonicalRadialContactZ_spec halpha htheta hs
    exact (existsUnique_radialEulerLogRatio_eq hrho htheta hs).unique
      ⟨hcanspec.1, hcanspec.2⟩ ⟨hφmem, hsroot⟩
  exact hφdiff.congr_of_eventuallyEq hlocal

end CourtadeKumar
