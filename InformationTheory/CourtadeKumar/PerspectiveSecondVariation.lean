import InformationTheory.CourtadeKumar.RadialPerspectiveCurvature

/-! Exact second-variation algebra for a stationary perspective quotient. -/

namespace CourtadeKumar

noncomputable def affinePathFirstVariation
    (km ku z r dz dr : ℝ) : ℝ :=
  km * dz + ku * (r * dz + z * dr)

noncomputable def affinePathSecondVariation
    (ku kmm kmu kuu z r dz dr : ℝ) : ℝ :=
  kmm * dz ^ 2 + 2 * kmu * dz * (r * dz + z * dr) +
    kuu * (r * dz + z * dr) ^ 2 + 2 * ku * dz * dr

noncomputable def quotientSecondVariation
    (k kfirst ksecond z dz : ℝ) : ℝ :=
  ksecond / z - 2 * dz * kfirst / z ^ 2 + 2 * dz ^ 2 * k / z ^ 3

noncomputable def hessianQuadratic
    (kmm kmu kuu x y : ℝ) : ℝ :=
  kmm * x ^ 2 + 2 * kmu * x * y + kuu * y ^ 2

/-- At radial stationarity `k = z(k_m+r k_u)`, all first-order terms cancel
from the second derivative of `k(z,rz)/z`. -/
theorem perspectiveSecondVariation_eq_hessianQuadratic
    {k km ku kmm kmu kuu z r dz dr : ℝ}
    (hz : z ≠ 0)
    (hstationary : k = z * (km + r * ku)) :
    quotientSecondVariation k
        (affinePathFirstVariation km ku z r dz dr)
        (affinePathSecondVariation ku kmm kmu kuu z r dz dr) z dz =
      hessianQuadratic kmm kmu kuu dz (r * dz + z * dr) / z := by
  unfold quotientSecondVariation affinePathFirstVariation
    affinePathSecondVariation hessianQuadratic
  rw [hstationary]
  field_simp [hz]
  ring

/-- The stationary perspective Hessian is positive definite whenever the
original Hessian is positive definite and `z>0`. -/
theorem perspectiveSecondVariation_pos
    {k km ku kmm kmu kuu z r dz dr : ℝ}
    (hz : 0 < z)
    (hstationary : k = z * (km + r * ku))
    (hdir : dz ≠ 0 ∨ dr ≠ 0)
    (hpositive : ∀ x y : ℝ, x ≠ 0 ∨ y ≠ 0 →
      0 < hessianQuadratic kmm kmu kuu x y) :
    0 < quotientSecondVariation k
      (affinePathFirstVariation km ku z r dz dr)
      (affinePathSecondVariation ku kmm kmu kuu z r dz dr) z dz := by
  rw [perspectiveSecondVariation_eq_hessianQuadratic hz.ne' hstationary]
  apply div_pos
  · exact hpositive dz (r * dz + z * dr)
      (perspectiveDirection_ne_zero hz.ne' hdir)
  · exact hz

end CourtadeKumar
