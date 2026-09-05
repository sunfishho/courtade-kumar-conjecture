import InformationTheory.CourtadeKumar.LRCertificateQPointSound

/-! Natural Q/Q' interval evaluation. The payload type and arithmetic are reused
from point certificates, but the root check encloses the WHOLE input interval.
No interval monotonicity theorem, derivative bounds, or corner argument is used. -/

set_option autoImplicit false
open Set

namespace CourtadeKumar.RootRatioNaturalQ
open LRQPointCertificate

def naturalCheck (input : RationalEnclosure) (certificate : LRQPointCertificate) : Bool :=
  certificate.sqrtOneSub.check
    (RationalEnclosure.sub (RationalEnclosure.point 1) input) &&
  certificate.logLowerProbability.check certificate.lowerProbability &&
  certificate.logUpperProbability.check certificate.upperProbability

theorem sound (terms : ℕ) {input : RationalEnclosure} {y : ℝ}
    {certificate : LRQPointCertificate}
    (hcheck : naturalCheck input certificate = true)
    (hyInput : input.Contains y) :
    (certificate.enclosure terms).Contains (lrCertificateQ y) := by
  have hparts :
      certificate.sqrtOneSub.check ((RationalEnclosure.sub (RationalEnclosure.point 1) input)) = true ∧
      certificate.logLowerProbability.check certificate.lowerProbability = true ∧
      certificate.logUpperProbability.check certificate.upperProbability = true := by
    have hraw :
        (certificate.sqrtOneSub.check ((RationalEnclosure.sub (RationalEnclosure.point 1) input)) = true ∧
          certificate.logLowerProbability.check certificate.lowerProbability = true) ∧
        certificate.logUpperProbability.check certificate.upperProbability = true := by
      simpa [naturalCheck] using hcheck
    exact ⟨hraw.1.1, hraw.1.2, hraw.2⟩
  have hsqrtInput :
      (RationalEnclosure.sub (RationalEnclosure.point 1) input).Contains (1 - y) := by
    have hOne : (RationalEnclosure.point 1).Contains (1 : ℝ) := by
      norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
    exact RationalEnclosure.contains_sub hOne hyInput
  have hsqrt := certificate.sqrtOneSub.sound hparts.1 hsqrtInput
  have hlower : certificate.lowerProbability.Contains
      ((1 - Real.sqrt (1 - y)) / 2) := by
    have hsub := RationalEnclosure.contains_sub
      (RationalEnclosure.contains_point (1 : ℚ)) hsqrt
    have hscale := RationalEnclosure.contains_scale (1 / 2 : ℚ) hsub
    simpa [lowerProbability, sqrtEnclosure, div_eq_mul_inv, mul_comm] using hscale
  have hupper : certificate.upperProbability.Contains
      ((1 + Real.sqrt (1 - y)) / 2) := by
    have hadd := RationalEnclosure.contains_add
      (RationalEnclosure.contains_point (1 : ℚ)) hsqrt
    have hscale := RationalEnclosure.contains_scale (1 / 2 : ℚ) hadd
    simpa [upperProbability, sqrtEnclosure, div_eq_mul_inv, mul_comm] using hscale
  have hlogLower := certificate.logLowerProbability.sound terms
    hparts.2.1 hlower
  have hlogUpper := certificate.logUpperProbability.sound terms
    hparts.2.2 hupper
  have hfirst := RationalEnclosure.contains_mul hlower hlogLower
  have hsecond := RationalEnclosure.contains_mul hupper hlogUpper
  have hsum := RationalEnclosure.contains_add hfirst hsecond
  have hneg := RationalEnclosure.contains_neg hsum
  have hidentity :
      -(((1 - Real.sqrt (1 - y)) / 2) *
          Real.log ((1 - Real.sqrt (1 - y)) / 2) +
        ((1 + Real.sqrt (1 - y)) / 2) *
          Real.log ((1 + Real.sqrt (1 - y)) / 2)) =
        lrCertificateQ y := by
    unfold lrCertificateQ
    rw [topJ_eq_binEntropy, Real.binEntropy, Real.log_inv, Real.log_inv]
    ring_nf
  simpa [enclosure, hidentity] using hneg

theorem prime_sound (terms : ℕ) {input : RationalEnclosure} {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) {certificate : LRQPointCertificate}
    (hcheck : naturalCheck input certificate = true)
    (hpositive : (0 : ℚ) < certificate.sqrtEnclosure.lower)
    (hyInput : input.Contains y) :
    (certificate.primeEnclosure terms).Contains (lrCertificateQPrime y) := by
  have hparts :
      certificate.sqrtOneSub.check ((RationalEnclosure.sub (RationalEnclosure.point 1) input)) = true ∧
      certificate.logLowerProbability.check certificate.lowerProbability = true ∧
      certificate.logUpperProbability.check certificate.upperProbability = true := by
    have hraw :
        (certificate.sqrtOneSub.check ((RationalEnclosure.sub (RationalEnclosure.point 1) input)) = true ∧
          certificate.logLowerProbability.check certificate.lowerProbability = true) ∧
        certificate.logUpperProbability.check certificate.upperProbability = true := by
      simpa [naturalCheck] using hcheck
    exact ⟨hraw.1.1, hraw.1.2, hraw.2⟩
  have hsqrtInput :
      (RationalEnclosure.sub (RationalEnclosure.point 1) input).Contains (1 - y) := by
    have hOne : (RationalEnclosure.point 1).Contains (1 : ℝ) := by
      norm_num [RationalEnclosure.point, RationalEnclosure.Contains]
    exact RationalEnclosure.contains_sub hOne hyInput
  have hsqrt := certificate.sqrtOneSub.sound hparts.1 hsqrtInput
  have hlower : certificate.lowerProbability.Contains
      ((1 - Real.sqrt (1 - y)) / 2) := by
    have hsub := RationalEnclosure.contains_sub
      (RationalEnclosure.contains_point (1 : ℚ)) hsqrt
    have hscale := RationalEnclosure.contains_scale (1 / 2 : ℚ) hsub
    simpa [lowerProbability, sqrtEnclosure, div_eq_mul_inv, mul_comm] using hscale
  have hupper : certificate.upperProbability.Contains
      ((1 + Real.sqrt (1 - y)) / 2) := by
    have hadd := RationalEnclosure.contains_add
      (RationalEnclosure.contains_point (1 : ℚ)) hsqrt
    have hscale := RationalEnclosure.contains_scale (1 / 2 : ℚ) hadd
    simpa [upperProbability, sqrtEnclosure, div_eq_mul_inv, mul_comm] using hscale
  have hlogLower := certificate.logLowerProbability.sound terms
    hparts.2.1 hlower
  have hlogUpper := certificate.logUpperProbability.sound terms
    hparts.2.2 hupper
  have hlogDiff := RationalEnclosure.contains_sub hlogUpper hlogLower
  have hquot := RationalEnclosure.contains_div hpositive hlogDiff hsqrt
  have hscaled := RationalEnclosure.contains_scale (1 / 4 : ℚ) hquot
  let z := Real.sqrt (1 - y)
  have hzPos : 0 < z := Real.sqrt_pos.2 (by exact_mod_cast sub_pos.mpr hy.2)
  have hzLt : z < 1 := by
    have harg : (1 - y) ∈ Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hy.1, hy.2]
    simpa [z] using (Real.sqrt_lt_sqrt_iff harg.1.le).2 harg.2
  have hpNe : (1 - z) / 2 ≠ 0 := by nlinarith
  have hqNe : (1 + z) / 2 ≠ 0 := by nlinarith
  have hlogIdentity :
      Real.log ((1 + z) / 2) - Real.log ((1 - z) / 2) =
        2 * Real.artanh z := by
    rw [Real.artanh_eq_half_log ⟨by linarith, hzLt.le⟩]
    rw [← Real.log_div hqNe hpNe]
    field_simp
  have hvalue :
      (1 / 4 : ℝ) *
          ((Real.log ((1 + z) / 2) - Real.log ((1 - z) / 2)) / z) =
        lrCertificateQPrime y := by
    rw [lrCertificateQPrime_eq]
    change (1 / 4 : ℝ) *
        ((Real.log ((1 + z) / 2) - Real.log ((1 - z) / 2)) / z) =
      Real.artanh z / (2 * z)
    rw [hlogIdentity]
    field_simp [hzPos.ne']
    ring
  dsimp [z] at hvalue
  rw [← hvalue]
  simpa [primeEnclosure] using hscaled


#print axioms CourtadeKumar.RootRatioNaturalQ.sound
#print axioms CourtadeKumar.RootRatioNaturalQ.prime_sound

end CourtadeKumar.RootRatioNaturalQ
