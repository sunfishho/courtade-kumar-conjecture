import AgentRootRatioPrimitiveNumericalPilot
import InformationTheory.CourtadeKumar.LRCertificateQPointSound

/-!
# `Q` and square-root witnesses for `curvature-main-001`

The first ordinary production box has center `(13/160, 3/32, 3/64)`.
This file supplies the requested `Q(13/160)` constant and all three initial
square-root constants of the ordinary formula.  Every square-root interval
is authenticated by rational square inequalities; the `Q` witness uses
the existing entropy point-certificate soundness theorem.

The `Q` output is the exact rational interval expression returned by the
verified evaluator with eight logarithm terms.  Its endpoints are not
replaced by floating approximations.  The same authenticated point data
also provides a `Q'` enclosure at no additional transcendental check.

These are concrete primitive witnesses, not a complete box certificate.
All finite checks use kernel-checked `norm_num`.
-/

set_option autoImplicit false

namespace CourtadeKumar
namespace RootRatioQNumericalPilot

open RationalEnclosure
open RootRatioPrimitiveNumericalPilot

def eCenter : ℚ := 39 / 5120
def yCenter : ℚ := 117 / 327680

theorem eCenter_eq : eCenter = sCenter * kCenter := by
  norm_num [eCenter, sCenter, kCenter]

theorem yCenter_eq : yCenter = eCenter * chiCenter := by
  norm_num [yCenter, eCenter, chiCenter]

def sqrtVCenter : ℚ := 325184 / 327563
def sqrtQhatECenter : ℚ := 5081 / 5120
def sqrtQhatYCenter : ℚ := 327563 / 327680

theorem sqrtVCenter_eq : sqrtVCenter = (1 - eCenter) / (1 - yCenter) := by
  norm_num [sqrtVCenter, eCenter, yCenter]

theorem sqrtQhatECenter_eq : sqrtQhatECenter = 1 - eCenter := by
  norm_num [sqrtQhatECenter, eCenter]

theorem sqrtQhatYCenter_eq : sqrtQhatYCenter = 1 - yCenter := by
  norm_num [sqrtQhatYCenter, yCenter]

def sqrtVCertificate : SqrtCertificate :=
  ⟨996362 / 1000000, 996363 / 1000000⟩

def sqrtQhatECertificate : SqrtCertificate :=
  ⟨996184 / 1000000, 996185 / 1000000⟩

def sqrtQhatYCertificate : SqrtCertificate :=
  ⟨999821 / 1000000, 999822 / 1000000⟩

theorem sqrt_v_check : sqrtVCertificate.check (point sqrtVCenter) = true := by
  norm_num [sqrtVCertificate, sqrtVCenter, SqrtCertificate.check, point]

theorem sqrt_qhat_e_check :
    sqrtQhatECertificate.check (point sqrtQhatECenter) = true := by
  norm_num [sqrtQhatECertificate, sqrtQhatECenter, SqrtCertificate.check, point]

theorem sqrt_qhat_y_check :
    sqrtQhatYCertificate.check (point sqrtQhatYCenter) = true := by
  norm_num [sqrtQhatYCertificate, sqrtQhatYCenter, SqrtCertificate.check, point]

theorem sqrt_v_contains :
    sqrtVCertificate.enclosure.Contains (Real.sqrt (sqrtVCenter : ℝ)) :=
  SqrtCertificate.sound sqrt_v_check (contains_point sqrtVCenter)

theorem sqrt_qhat_e_contains :
    sqrtQhatECertificate.enclosure.Contains (Real.sqrt (sqrtQhatECenter : ℝ)) :=
  SqrtCertificate.sound sqrt_qhat_e_check (contains_point sqrtQhatECenter)

theorem sqrt_qhat_y_contains :
    sqrtQhatYCertificate.enclosure.Contains (Real.sqrt (sqrtQhatYCenter : ℝ)) :=
  SqrtCertificate.sound sqrt_qhat_y_check (contains_point sqrtQhatYCenter)

/-- The interval encloses `sqrt (1 - 13/160)`.  The four logarithm range
reductions correspond exactly to the two endpoints of each probability
interval `(1 - sqrt)/2` and `(1 + sqrt)/2`. -/
def qSPointCertificate : LRQPointCertificate where
  sqrtOneSub := ⟨958514 / 1000000, 958515 / 1000000⟩
  logLowerProbability :=
    { lower := ⟨-6, 8297 / 6250⟩
      upper := ⟨-6, 20743 / 15625⟩ }
  logUpperProbability :=
    { lower := ⟨-1, 979257 / 500000⟩
      upper := ⟨-1, 391703 / 200000⟩ }

theorem q_s_check : qSPointCertificate.check sCenter = true := by
  norm_num [qSPointCertificate, sCenter, LRQPointCertificate.check,
    LRQPointCertificate.sqrtInput, LRQPointCertificate.sqrtEnclosure,
    LRQPointCertificate.lowerProbability, LRQPointCertificate.upperProbability,
    SqrtCertificate.check, SqrtCertificate.enclosure,
    LogIntervalCertificate.check, LogRangeCertificate.check,
    scale, mul, sub, add, neg, point, center, radius]

def qSEnclosure : RationalEnclosure :=
  qSPointCertificate.enclosure logTerms

theorem q_s_contains : qSEnclosure.Contains (lrCertificateQ (sCenter : ℝ)) :=
  LRQPointCertificate.sound logTerms q_s_check

/-- Reusing the same point certificate for `Q'` requires only positivity
of the already checked square-root lower endpoint. -/
theorem q_s_prime_check : qSPointCertificate.primeCheck sCenter = true := by
  simp only [LRQPointCertificate.primeCheck, q_s_check, Bool.true_and]
  norm_num [qSPointCertificate, LRQPointCertificate.sqrtEnclosure,
    SqrtCertificate.enclosure]

def qPrimeSEnclosure : RationalEnclosure :=
  qSPointCertificate.primeEnclosure logTerms

theorem q_prime_s_contains :
    qPrimeSEnclosure.Contains (lrCertificateQPrime (sCenter : ℝ)) :=
  LRQPointCertificate.prime_sound logTerms
    (by norm_num [sCenter] : sCenter ∈ Set.Ioo (0 : ℚ) 1) q_s_prime_check

end RootRatioQNumericalPilot
end CourtadeKumar
