import InformationTheory.CourtadeKumar.LRCertificateQ
import InformationTheory.CourtadeKumar.ExactLogEnclosure
import InformationTheory.CourtadeKumar.ExactSqrtEnclosure

/-!
# Executable endpoint enclosures for the LR entropy scalar

The external generator supplies only range-reduction and square-root data.
Lean checks those data, reconstructs the binary-entropy expression using exact
rational interval arithmetic, and proves that the resulting interval contains
the actual `lrCertificateQ` value.
-/

open Set

namespace CourtadeKumar

/-- Untrusted auxiliary data for evaluating `Q` at one rational point. -/
structure LRQPointCertificate where
  sqrtOneSub : RationalEnclosure.SqrtCertificate
  logLowerProbability : RationalEnclosure.LogIntervalCertificate
  logUpperProbability : RationalEnclosure.LogIntervalCertificate

namespace LRQPointCertificate

def sqrtInput (y : ℚ) : RationalEnclosure :=
  RationalEnclosure.point (1 - y)

def sqrtEnclosure (certificate : LRQPointCertificate) : RationalEnclosure :=
  certificate.sqrtOneSub.enclosure

def lowerProbability (certificate : LRQPointCertificate) : RationalEnclosure :=
  RationalEnclosure.scale (1 / 2)
    (RationalEnclosure.sub (RationalEnclosure.point 1)
      certificate.sqrtEnclosure)

def upperProbability (certificate : LRQPointCertificate) : RationalEnclosure :=
  RationalEnclosure.scale (1 / 2)
    (RationalEnclosure.add (RationalEnclosure.point 1)
      certificate.sqrtEnclosure)

/-- Executable checker for all non-algebraic data in a point evaluation. -/
def check (y : ℚ) (certificate : LRQPointCertificate) : Bool :=
  certificate.sqrtOneSub.check (sqrtInput y) &&
    certificate.logLowerProbability.check certificate.lowerProbability &&
    certificate.logUpperProbability.check certificate.upperProbability

/-- The exact interval expression `-p log p -(1-p) log(1-p)`. -/
def enclosure (terms : ℕ) (certificate : LRQPointCertificate) :
    RationalEnclosure :=
  RationalEnclosure.neg (RationalEnclosure.add
    (RationalEnclosure.mul certificate.lowerProbability
      (certificate.logLowerProbability.enclosure terms))
    (RationalEnclosure.mul certificate.upperProbability
      (certificate.logUpperProbability.enclosure terms)))

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

end LRQPointCertificate

/-- Endpoint certificates for an entire rational interval in `0 < y < 1`. -/
structure LRQIntervalCertificate where
  lower : LRQPointCertificate
  upper : LRQPointCertificate

namespace LRQIntervalCertificate

def check (input : RationalEnclosure)
    (certificate : LRQIntervalCertificate) : Bool :=
  decide ((0 : ℚ) < input.lower ∧ input.lower ≤ input.upper ∧ input.upper < 1) &&
    certificate.lower.check input.lower && certificate.upper.check input.upper

def enclosure (terms : ℕ) (certificate : LRQIntervalCertificate) :
    RationalEnclosure :=
  ⟨(certificate.lower.enclosure terms).lower,
    (certificate.upper.enclosure terms).upper⟩

theorem sound (terms : ℕ) {input : RationalEnclosure}
    {certificate : LRQIntervalCertificate}
    (hcheck : certificate.check input = true)
    {y : ℝ} (hy : input.Contains y) :
    (certificate.enclosure terms).Contains (lrCertificateQ y) := by
  have hraw :
      (decide ((0 : ℚ) < input.lower ∧ input.lower ≤ input.upper ∧
          input.upper < 1) = true ∧
        certificate.lower.check input.lower = true) ∧
      certificate.upper.check input.upper = true := by
    simpa [check] using hcheck
  have hdomain :
      (0 : ℚ) < input.lower ∧ input.lower ≤ input.upper ∧
        input.upper < 1 := by
    simpa using hraw.1.1
  have hlower := certificate.lower.sound terms hraw.1.2
  have hupper := certificate.upper.sound terms hraw.2
  have hlowerMem : (input.lower : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact_mod_cast hdomain.1
    · exact_mod_cast hdomain.2.1.trans_lt hdomain.2.2
  have hupperMem : (input.upper : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact_mod_cast hdomain.1.trans_le hdomain.2.1
    · exact_mod_cast hdomain.2.2
  have hyMem : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨hlowerMem.1.trans_le hy.1, hy.2.trans_lt hupperMem.2⟩
  have hmonoLower :
      lrCertificateQ (input.lower : ℝ) ≤ lrCertificateQ y :=
    lrCertificateQ_strictMonoOn.monotoneOn hlowerMem hyMem hy.1
  have hmonoUpper :
      lrCertificateQ y ≤ lrCertificateQ (input.upper : ℝ) :=
    lrCertificateQ_strictMonoOn.monotoneOn hyMem hupperMem hy.2
  exact ⟨hlower.1.trans hmonoLower, hmonoUpper.trans hupper.2⟩

end LRQIntervalCertificate
end CourtadeKumar
