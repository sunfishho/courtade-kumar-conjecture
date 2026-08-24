import InformationTheory.CourtadeKumar.AcceleratedPerspectiveSecondVariation

/-! One-variable calculus for a quotient along a curved path. -/

namespace CourtadeKumar

noncomputable def quotientFirstVariation
    (k kfirst z dz : ℝ) : ℝ :=
  kfirst / z - dz * k / z ^ 2

theorem hasDerivAt_quotientPath
    {k z : ℝ → ℝ} {kfirst dz t : ℝ}
    (hk : HasDerivAt k kfirst t)
    (hz : HasDerivAt z dz t)
    (hzt : z t ≠ 0) :
    HasDerivAt (fun s ↦ k s / z s)
      (quotientFirstVariation (k t) kfirst (z t) dz) t := by
  unfold quotientFirstVariation
  convert hk.div hz hzt using 1
  field_simp [hzt]

/-- Differentiating the first-variation formula gives exactly the accelerated
quotient second variation. -/
theorem hasDerivAt_quotientFirstVariation
    {k kfirst z zfirst : ℝ → ℝ} {ksecond zsecond t : ℝ}
    (hk : HasDerivAt k (kfirst t) t)
    (hkfirst : HasDerivAt kfirst ksecond t)
    (hz : HasDerivAt z (zfirst t) t)
    (hzfirst : HasDerivAt zfirst zsecond t)
    (hzt : z t ≠ 0) :
    HasDerivAt
      (fun s ↦ quotientFirstVariation (k s) (kfirst s) (z s) (zfirst s))
      (acceleratedQuotientSecondVariation
        (k t) (kfirst t) ksecond (z t) (zfirst t) zsecond) t := by
  have hleft := hkfirst.div hz hzt
  have hnumerator := hzfirst.mul hk
  have hdenominator := hz.pow 2
  have hright := hnumerator.div hdenominator (pow_ne_zero 2 hzt)
  unfold quotientFirstVariation acceleratedQuotientSecondVariation
    quotientSecondVariation
  convert hleft.sub hright using 1
  simp only [Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat,
    Nat.reduceSubDiff, pow_one]
  field_simp [hzt]
  ring

end CourtadeKumar
