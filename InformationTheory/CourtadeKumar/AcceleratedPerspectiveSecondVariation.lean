import InformationTheory.CourtadeKumar.RadialPerspectiveSecondVariation

/-! Second-variation algebra along curved contact branches. -/

namespace CourtadeKumar

/-- The second derivative of `k(z,r*z)` along a path whose instantaneous
velocity is `(dz,dr)` and acceleration is `(ddz,ddr)`. -/
noncomputable def acceleratedPathSecondVariation
    (km ku kmm kmu kuu z r dz dr ddz ddr : ℝ) : ℝ :=
  affinePathSecondVariation ku kmm kmu kuu z r dz dr +
    km * ddz + ku * (r * ddz + z * ddr)

/-- The second derivative of `k/z` when the numerator has second derivative
`ksecond` and the denominator path has acceleration `ddz`. -/
noncomputable def acceleratedQuotientSecondVariation
    (k kfirst ksecond z dz ddz : ℝ) : ℝ :=
  quotientSecondVariation k kfirst ksecond z dz - ddz * k / z ^ 2

/-- At a stationary perspective contact, the acceleration of the optimizing
contact location cancels completely.  Only the velocity of the contact branch
enters the second derivative of the attained profile. -/
theorem acceleratedPerspectiveSecondVariation_eq_hessianQuadratic
    {k km ku kmm kmu kuu z r dz dr ddz : ℝ}
    (hz : z ≠ 0)
    (hstationary : k = z * (km + r * ku)) :
    acceleratedQuotientSecondVariation k
        (affinePathFirstVariation km ku z r dz dr)
        (acceleratedPathSecondVariation km ku kmm kmu kuu
          z r dz dr ddz 0)
        z dz ddz =
      hessianQuadratic kmm kmu kuu dz (r * dz + z * dr) / z := by
  unfold acceleratedQuotientSecondVariation acceleratedPathSecondVariation
  unfold quotientSecondVariation affinePathFirstVariation
    affinePathSecondVariation hessianQuadratic
  rw [hstationary]
  field_simp [hz]
  ring

/-- Hence positive definiteness of the original Hessian gives a positive
second variation along every nonconstant radial path, independently of its
contact acceleration. -/
theorem acceleratedPerspectiveSecondVariation_pos
    {k km ku kmm kmu kuu z r dz dr ddz : ℝ}
    (hz : 0 < z)
    (hstationary : k = z * (km + r * ku))
    (hdir : dz ≠ 0 ∨ dr ≠ 0)
    (hpositive : ∀ x y : ℝ, x ≠ 0 ∨ y ≠ 0 →
      0 < hessianQuadratic kmm kmu kuu x y) :
    0 < acceleratedQuotientSecondVariation k
      (affinePathFirstVariation km ku z r dz dr)
      (acceleratedPathSecondVariation km ku kmm kmu kuu
        z r dz dr ddz 0)
      z dz ddz := by
  rw [acceleratedPerspectiveSecondVariation_eq_hessianQuadratic hz.ne' hstationary]
  exact div_pos
    (hpositive dz (r * dz + z * dr)
      (perspectiveDirection_ne_zero hz.ne' hdir)) hz

end CourtadeKumar
