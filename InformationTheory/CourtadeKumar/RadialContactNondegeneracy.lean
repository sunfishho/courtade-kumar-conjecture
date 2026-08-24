import InformationTheory.CourtadeKumar.RadialProfileEnvelope
import InformationTheory.CourtadeKumar.RadialEulerCrossSign

/-! Nondegeneracy of the radial Euler equation at physical contacts. -/

open Set

namespace CourtadeKumar

/-- The derivative in the contact variable is strictly negative throughout
the physical radial cell.  This is the invertibility input for the implicit
function theorem. -/
theorem deriv_radialEulerLogRatio_contact_neg_physical
    {rho r z : ℝ}
    (hrho : rho ∈ Ico (0 : ℝ) 1)
    (hr : 0 < r)
    (hz : 0 < z)
    (hupper : (1 + r) * z < 1) :
    deriv (radialEulerLogRatio rho r) z < 0 := by
  obtain ⟨harg1, hargR, _⟩ :=
    radialEulerLogArg_order_physical hrho hr hz hupper
  have hz1 : z < 1 := by nlinarith [mul_pos hr hz]
  have hden : radialEulerLog 1 r z ≠ 0 :=
    (radialEulerLog_pos_of_arg
      ⟨harg1.1, harg1.2.trans (by linarith)⟩).ne'
  rw [deriv_radialEulerLogRatio_lt_zero_iff
    hargR.1.ne' harg1.1.ne' hden]
  rw [radialEulerRatioCrossNumerator_lt_zero_iff_core hargR.1 harg1.1]
  exact radialEulerCrossCore_neg_physical hrho hr hz hupper

theorem radialEulerLogRatio_contact_deriv_ne_zero
    {rho r z : ℝ}
    (hrho : rho ∈ Ico (0 : ℝ) 1)
    (hr : 0 < r)
    (hz : 0 < z)
    (hupper : (1 + r) * z < 1) :
    deriv (radialEulerLogRatio rho r) z ≠ 0 :=
  (deriv_radialEulerLogRatio_contact_neg_physical hrho hr hz hupper).ne

end CourtadeKumar
