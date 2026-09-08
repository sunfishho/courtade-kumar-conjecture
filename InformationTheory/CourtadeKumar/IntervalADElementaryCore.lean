import InformationTheory.CourtadeKumar.IntervalADArithmeticCore
import InformationTheory.CourtadeKumar.ExactLogEnclosureCore
import InformationTheory.CourtadeKumar.ExactSqrtEnclosureCore

/-!
# Executable elementary functions for interval AD

This module assembles exact-rational logarithm and positive-square-root nodes.
Their real-valued soundness theorems remain in `IntervalADElementary`.
-/

namespace CourtadeKumar
namespace IntervalAD

def log (terms : ℕ) (certificate : RationalEnclosure.LogIntervalCertificate)
    (a : IntervalAD) : IntervalAD :=
  unary (certificate.enclosure terms)
    (RationalEnclosure.invPositive a.value) a

/-- The square-root AD checker additionally requires a strictly positive
lower root bound so the derivative `1/(2√x)` is finite. -/
def sqrtCheck (input : RationalEnclosure)
    (certificate : RationalEnclosure.SqrtCertificate) : Bool :=
  certificate.check input && decide (0 < certificate.lower)

def sqrt (certificate : RationalEnclosure.SqrtCertificate)
    (a : IntervalAD) : IntervalAD :=
  let output := certificate.enclosure
  let twiceOutput := RationalEnclosure.scale 2 output
  unary output (RationalEnclosure.invPositive twiceOutput) a

end IntervalAD
end CourtadeKumar
