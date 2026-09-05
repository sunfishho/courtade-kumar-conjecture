import InformationTheory.CourtadeKumar.ExactLogEnclosureCore
import InformationTheory.CourtadeKumar.ExactSqrtEnclosureCore

/-!
# Executable point-enclosure core for the LR entropy scalar

This module contains the data and exact rational computations for one
`Q/Q'` point certificate.  Semantic containment theorems remain in
`LRCertificateQEnclosure`, allowing generated arithmetic shards to import
the executable layer without importing the analytic definition of `Q`.
-/

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

/-- The derivative evaluator additionally checks that the square-root
interval stays strictly away from zero, as required by interval division. -/
def primeCheck (y : ℚ) (certificate : LRQPointCertificate) : Bool :=
  certificate.check y && decide ((0 : ℚ) < certificate.sqrtEnclosure.lower)

def primeEnclosure (terms : ℕ) (certificate : LRQPointCertificate) :
    RationalEnclosure :=
  RationalEnclosure.scale (1 / 4)
    (RationalEnclosure.div
      (RationalEnclosure.sub
        (certificate.logUpperProbability.enclosure terms)
        (certificate.logLowerProbability.enclosure terms))
      certificate.sqrtEnclosure)

end LRQPointCertificate
end CourtadeKumar
