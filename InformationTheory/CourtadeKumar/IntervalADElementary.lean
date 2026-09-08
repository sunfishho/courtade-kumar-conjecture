import InformationTheory.CourtadeKumar.IntervalADElementaryCore
import InformationTheory.CourtadeKumar.IntervalADArithmetic
import InformationTheory.CourtadeKumar.ExactLogEnclosure
import InformationTheory.CourtadeKumar.ExactSqrtEnclosure

/-!
# Elementary functions in verified interval AD

Executable `log` and positive-square-root nodes assembled from the scalar
certificate checkers and the generic unary AD chain rule.
-/

namespace CourtadeKumar
namespace IntervalAD

theorem contains_log
    (terms : ℕ) {certificate : RationalEnclosure.LogIntervalCertificate}
    {a : IntervalAD} {av as ak ac : ℝ}
    (hcheck : certificate.check a.value = true)
    (ha : a.Contains av as ak ac) :
    (log terms certificate a).Contains (Real.log av)
      (as / av) (ak / av) (ac / av) := by
  have hparts :
      (0 : ℚ) < a.value.lower ∧
      certificate.lower.check a.value.lower = true ∧
      certificate.upper.check a.value.upper = true := by
    simpa [RationalEnclosure.LogIntervalCertificate.check] using hcheck
  have hout := certificate.sound terms hcheck ha.1
  have hslope := RationalEnclosure.contains_invPositive hparts.1 ha.1
  have h := contains_unary hout hslope ha
  simpa [log, div_eq_mul_inv, mul_comm] using h

theorem contains_sqrt
    {certificate : RationalEnclosure.SqrtCertificate}
    {a : IntervalAD} {av as ak ac : ℝ}
    (hcheck : sqrtCheck a.value certificate = true)
    (ha : a.Contains av as ak ac) :
    (sqrt certificate a).Contains (Real.sqrt av)
      (as / (2 * Real.sqrt av))
      (ak / (2 * Real.sqrt av))
      (ac / (2 * Real.sqrt av)) := by
  have hparts : certificate.check a.value = true ∧
      (0 : ℚ) < certificate.lower := by
    simpa [sqrtCheck] using hcheck
  have hout := certificate.sound hparts.1 ha.1
  let output := certificate.enclosure
  let twiceOutput := RationalEnclosure.scale 2 output
  have htwice : twiceOutput.Contains (2 * Real.sqrt av) := by
    simpa [twiceOutput, output] using
      RationalEnclosure.contains_scale (2 : ℚ) hout
  have htwiceLower : (0 : ℚ) < twiceOutput.lower := by
    dsimp [twiceOutput, output, RationalEnclosure.scale,
      RationalEnclosure.mul, RationalEnclosure.center,
      RationalEnclosure.radius, RationalEnclosure.point,
      RationalEnclosure.SqrtCertificate.enclosure]
    norm_num
    linarith
  have hslope := RationalEnclosure.contains_invPositive htwiceLower htwice
  have h := contains_unary hout hslope ha
  simpa [sqrt, output, twiceOutput, div_eq_mul_inv, mul_comm] using h

end IntervalAD
end CourtadeKumar
