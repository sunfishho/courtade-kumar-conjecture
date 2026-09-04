import InformationTheory.CourtadeKumar.ExactLogEnclosure

/-!
# Genuine logarithm witnesses for `curvature-main-001`

The ordinary model builder requests logarithms of the coordinate centers
and of two.  For its first production box these centers are `13/160`,
`3/32`, and `3/64`.  The range reductions below are exact; eight positive
logarithm-series terms and their proved geometric tail fit inside the
explicit rational output intervals.

This supplies four actual request constants and semantic theorem references.
It is not a certificate for either curvature target or for the whole box.
All finite checks are proved by kernel-checked `norm_num`; the logarithmic
semantics use the existing `LogRangeCertificate.sound` theorem.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace RootRatioPrimitiveNumericalPilot

open RationalEnclosure

def sCenter : ℚ := 13 / 160
def kCenter : ℚ := 3 / 32
def chiCenter : ℚ := 3 / 64

theorem sCenter_eq_box_midpoint : sCenter = ((1 / 16 : ℚ) + 1 / 10) / 2 := by
  norm_num [sCenter]

theorem kCenter_eq_box_midpoint : kCenter = ((1 / 16 : ℚ) + 1 / 8) / 2 := by
  norm_num [kCenter]

theorem chiCenter_eq_box_midpoint : chiCenter = ((1 / 32 : ℚ) + 1 / 16) / 2 := by
  norm_num [chiCenter]

def logTerms : ℕ := 8

def logSRange : LogRangeCertificate := ⟨-4, 13 / 10⟩
def logKRange : LogRangeCertificate := ⟨-4, 3 / 2⟩
def logChiRange : LogRangeCertificate := ⟨-5, 3 / 2⟩
def logTwoRange : LogRangeCertificate := ⟨1, 1⟩

def logSEnclosure : RationalEnclosure :=
  ⟨-2510225 / 1000000, -2510224 / 1000000⟩

def logKEnclosure : RationalEnclosure :=
  ⟨-2367124 / 1000000, -2367123 / 1000000⟩

def logChiEnclosure : RationalEnclosure :=
  ⟨-3060271 / 1000000, -3060270 / 1000000⟩

def logTwoOutput : RationalEnclosure :=
  ⟨693147 / 1000000, 693148 / 1000000⟩

/-- The real function never occurs in the finite checker.  Its two jobs
are authenticating the exact range reduction and checking inclusion of
the proved series enclosure in the literal rational output. -/
def logWitnessCheck (input : ℚ) (certificate : LogRangeCertificate)
    (output : RationalEnclosure) : Bool :=
  certificate.check input &&
    decide (output.lower ≤ (certificate.enclosure logTerms).lower ∧
      (certificate.enclosure logTerms).upper ≤ output.upper)

theorem logWitnessCheck_sound {input : ℚ}
    {certificate : LogRangeCertificate} {output : RationalEnclosure}
    (hcheck : logWitnessCheck input certificate output = true) :
    output.Contains (Real.log (input : ℝ)) := by
  have hparts : certificate.check input = true ∧
      decide (output.lower ≤ (certificate.enclosure logTerms).lower ∧
        (certificate.enclosure logTerms).upper ≤ output.upper) = true := by
    simpa [logWitnessCheck] using hcheck
  have hsubset : output.lower ≤ (certificate.enclosure logTerms).lower ∧
      (certificate.enclosure logTerms).upper ≤ output.upper := by
    simpa using hparts.2
  have hlog := certificate.sound logTerms hparts.1
  constructor
  · have hlo : (output.lower : ℝ) ≤
        ((certificate.enclosure logTerms).lower : ℝ) := by
      exact_mod_cast hsubset.1
    exact hlo.trans hlog.1
  · have hhi : ((certificate.enclosure logTerms).upper : ℝ) ≤
        (output.upper : ℝ) := by
      exact_mod_cast hsubset.2
    exact hlog.2.trans hhi

theorem log_s_check : logWitnessCheck sCenter logSRange logSEnclosure = true := by
  norm_num [logWitnessCheck, sCenter, logSRange, logSEnclosure, logTerms,
    LogRangeCertificate.check, LogRangeCertificate.enclosure,
    logScaledMantissaEnclosure, logTwoEnclosure, logMantissaEnclosure,
    halfLogRatioEnclosure, logRatioCoordinate, atanhPartial, atanhTail,
    Finset.sum_range_succ, scale, mul, add, point, center, radius]

theorem log_k_check : logWitnessCheck kCenter logKRange logKEnclosure = true := by
  norm_num [logWitnessCheck, kCenter, logKRange, logKEnclosure, logTerms,
    LogRangeCertificate.check, LogRangeCertificate.enclosure,
    logScaledMantissaEnclosure, logTwoEnclosure, logMantissaEnclosure,
    halfLogRatioEnclosure, logRatioCoordinate, atanhPartial, atanhTail,
    Finset.sum_range_succ, scale, mul, add, point, center, radius]

theorem log_chi_check :
    logWitnessCheck chiCenter logChiRange logChiEnclosure = true := by
  norm_num [logWitnessCheck, chiCenter, logChiRange, logChiEnclosure, logTerms,
    LogRangeCertificate.check, LogRangeCertificate.enclosure,
    logScaledMantissaEnclosure, logTwoEnclosure, logMantissaEnclosure,
    halfLogRatioEnclosure, logRatioCoordinate, atanhPartial, atanhTail,
    Finset.sum_range_succ, scale, mul, add, point, center, radius]

theorem log_two_check : logWitnessCheck 2 logTwoRange logTwoOutput = true := by
  norm_num [logWitnessCheck, logTwoRange, logTwoOutput, logTerms,
    LogRangeCertificate.check, LogRangeCertificate.enclosure,
    logScaledMantissaEnclosure, logTwoEnclosure, logMantissaEnclosure,
    halfLogRatioEnclosure, logRatioCoordinate, atanhPartial, atanhTail,
    Finset.sum_range_succ, scale, mul, add, point, center, radius]

theorem log_s_contains : logSEnclosure.Contains (Real.log (sCenter : ℝ)) :=
  logWitnessCheck_sound log_s_check

theorem log_k_contains : logKEnclosure.Contains (Real.log (kCenter : ℝ)) :=
  logWitnessCheck_sound log_k_check

theorem log_chi_contains : logChiEnclosure.Contains (Real.log (chiCenter : ℝ)) :=
  logWitnessCheck_sound log_chi_check

theorem log_two_contains : logTwoOutput.Contains (Real.log 2) := by
  simpa using logWitnessCheck_sound log_two_check

end RootRatioPrimitiveNumericalPilot
end CourtadeKumar
