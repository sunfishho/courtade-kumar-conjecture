import InformationTheory.CourtadeKumar.LRCertificateQEnclosureCore
import InformationTheory.CourtadeKumar.LRCertificateQFunctionCore
import Mathlib.Tactic.FieldSimp

/-!
# Lightweight semantic soundness for LR point certificates

This module proves only the two point-containment theorems needed to promote
generated arithmetic facts.  Interval-wide monotonicity and the historical
TOP/channel development remain outside its import closure.
-/

open Set

namespace CourtadeKumar
namespace LRQPointCertificate

theorem sound (terms : ℕ) {y : ℚ} {certificate : LRQPointCertificate}
    (hcheck : certificate.check y = true) :
    (certificate.enclosure terms).Contains (lrCertificateQ (y : ℝ)) := by
  have hparts :
      certificate.sqrtOneSub.check (sqrtInput y) = true ∧
      certificate.logLowerProbability.check certificate.lowerProbability = true ∧
      certificate.logUpperProbability.check certificate.upperProbability = true := by
    have hraw :
        (certificate.sqrtOneSub.check (sqrtInput y) = true ∧
          certificate.logLowerProbability.check certificate.lowerProbability = true) ∧
        certificate.logUpperProbability.check certificate.upperProbability = true := by
      simpa [check] using hcheck
    exact ⟨hraw.1.1, hraw.1.2, hraw.2⟩
  have hsqrtInput : (sqrtInput y).Contains (1 - (y : ℝ)) := by
    simpa [sqrtInput] using RationalEnclosure.contains_point (1 - y)
  have hsqrt := certificate.sqrtOneSub.sound hparts.1 hsqrtInput
  have hlower : certificate.lowerProbability.Contains
      ((1 - Real.sqrt (1 - (y : ℝ))) / 2) := by
    have hsub := RationalEnclosure.contains_sub
      (RationalEnclosure.contains_point (1 : ℚ)) hsqrt
    have hscale := RationalEnclosure.contains_scale (1 / 2 : ℚ) hsub
    simpa [lowerProbability, sqrtEnclosure, div_eq_mul_inv, mul_comm] using hscale
  have hupper : certificate.upperProbability.Contains
      ((1 + Real.sqrt (1 - (y : ℝ))) / 2) := by
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
      -(((1 - Real.sqrt (1 - (y : ℝ))) / 2) *
          Real.log ((1 - Real.sqrt (1 - (y : ℝ))) / 2) +
        ((1 + Real.sqrt (1 - (y : ℝ))) / 2) *
          Real.log ((1 + Real.sqrt (1 - (y : ℝ))) / 2)) =
        lrCertificateQ (y : ℝ) := by
    unfold lrCertificateQ
    rw [topJ_eq_binEntropy, Real.binEntropy, Real.log_inv, Real.log_inv]
    ring_nf
  simpa [enclosure, hidentity] using hneg

theorem prime_sound (terms : ℕ) {y : ℚ}
    (hy : y ∈ Ioo (0 : ℚ) 1) {certificate : LRQPointCertificate}
    (hcheck : certificate.primeCheck y = true) :
    (certificate.primeEnclosure terms).Contains
      (lrCertificateQPrime (y : ℝ)) := by
  have hprimeParts : certificate.check y = true ∧
      (0 : ℚ) < certificate.sqrtEnclosure.lower := by
    simpa [primeCheck] using hcheck
  have hparts :
      certificate.sqrtOneSub.check (sqrtInput y) = true ∧
      certificate.logLowerProbability.check certificate.lowerProbability = true ∧
      certificate.logUpperProbability.check certificate.upperProbability = true := by
    have hraw :
        (certificate.sqrtOneSub.check (sqrtInput y) = true ∧
          certificate.logLowerProbability.check certificate.lowerProbability = true) ∧
        certificate.logUpperProbability.check certificate.upperProbability = true := by
      simpa [check] using hprimeParts.1
    exact ⟨hraw.1.1, hraw.1.2, hraw.2⟩
  have hsqrtInput : (sqrtInput y).Contains (1 - (y : ℝ)) := by
    simpa [sqrtInput] using RationalEnclosure.contains_point (1 - y)
  have hsqrt := certificate.sqrtOneSub.sound hparts.1 hsqrtInput
  have hlower : certificate.lowerProbability.Contains
      ((1 - Real.sqrt (1 - (y : ℝ))) / 2) := by
    have hsub := RationalEnclosure.contains_sub
      (RationalEnclosure.contains_point (1 : ℚ)) hsqrt
    have hscale := RationalEnclosure.contains_scale (1 / 2 : ℚ) hsub
    simpa [lowerProbability, sqrtEnclosure, div_eq_mul_inv, mul_comm] using hscale
  have hupper : certificate.upperProbability.Contains
      ((1 + Real.sqrt (1 - (y : ℝ))) / 2) := by
    have hadd := RationalEnclosure.contains_add
      (RationalEnclosure.contains_point (1 : ℚ)) hsqrt
    have hscale := RationalEnclosure.contains_scale (1 / 2 : ℚ) hadd
    simpa [upperProbability, sqrtEnclosure, div_eq_mul_inv, mul_comm] using hscale
  have hlogLower := certificate.logLowerProbability.sound terms
    hparts.2.1 hlower
  have hlogUpper := certificate.logUpperProbability.sound terms
    hparts.2.2 hupper
  have hlogDiff := RationalEnclosure.contains_sub hlogUpper hlogLower
  have hquot := RationalEnclosure.contains_div hprimeParts.2 hlogDiff hsqrt
  have hscaled := RationalEnclosure.contains_scale (1 / 4 : ℚ) hquot
  let z := Real.sqrt (1 - (y : ℝ))
  have hzPos : 0 < z := Real.sqrt_pos.2 (by exact_mod_cast sub_pos.mpr hy.2)
  have hzLt : z < 1 := by
    have harg : (1 - (y : ℝ)) ∈ Ioo (0 : ℝ) 1 := by
      have hargRat : (1 - y : ℚ) ∈ Ioo 0 1 := by
        constructor <;> linarith [hy.1, hy.2]
      constructor
      · exact_mod_cast hargRat.1
      · exact_mod_cast hargRat.2
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
        lrCertificateQPrime (y : ℝ) := by
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

end LRQPointCertificate
end CourtadeKumar
