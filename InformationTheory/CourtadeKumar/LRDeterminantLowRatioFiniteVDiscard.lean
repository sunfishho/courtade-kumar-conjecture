import InformationTheory.CourtadeKumar.LRDeterminantLowRatioFiniteVConcreteOracle
import InformationTheory.CourtadeKumar.LRHighShapeVAutoCertificate

/-!
# Endpoint-safe discards for the finite low-ratio direct-`V` chart

The direct-`V` subdivision lives in correlated coordinates `(s,K,h)`, while
the physical and positive-`J` relevance predicates live in raw coordinates
`(s,k,chi)`.  This module checks every discard on `rawHull box` and
transports its soundness back through `k = s*K`, `chi = h^2`.

Only a compact tag is stored in a generated tree.  A nonpositive-`J` tag
deterministically regenerates its untrusted interval payload and checks it
again.  Its arithmetic check deliberately follows only the dependency graph
of `J = B*x-D`: the coordinate and `A/B/D` payloads plus the algebraic `x`
node.  It therefore avoids both the open-chart wrapper and the endpoint-
singular `Q(chi*e)` and `omega(chi*e)` payloads, so boxes touching `h = 0` or
`h = 1` can be discarded whenever the checked interval proves `J ≤ 0`.
-/

namespace CourtadeKumar
namespace LRLowRatioFiniteVDiscard

/-- Compact, serializable reasons for exclusion from the positive-`J`
finite-`V` domain. -/
inductive DiscardData where
  | physical (reason : LRPhysicalDiscardData)
  | jNonpositive
  deriving DecidableEq, Repr

/-- Descriptive public alias for use by generated finite-`V` trees. -/
abbrev FiniteVDiscardData := DiscardData

/-- The complete untrusted payload needed for `J = B*x-D`: a coordinate
certificate for `v` and the three logarithmic `A/B/D` certificates.  No
high-shape `G`, `Q`, or `omega` field is carried. -/
structure JCertificate where
  coordinate : LRHighShapeCoordinateCertificate
  ab : LRHighShapeABCertificate

namespace JCertificate

/-- The `A/B/D` checker already validates the coordinate payload. -/
def check (box : CertificateBox) (certificate : JCertificate) : Bool :=
  certificate.ab.check box certificate.coordinate

/-- Minimal interval extension of `J = B*x-D`. -/
def jAD (terms : ℕ) (box : CertificateBox)
    (certificate : JCertificate) : IntervalAD :=
  let ab := certificate.ab.evaluate terms box certificate.coordinate
  IntervalAD.sub
    (IntervalAD.mul ab.b (lrCertificateXAD box)) ab.d

/-- Direct endpoint-safe soundness of the minimal `J` graph. -/
theorem jAD_value_sound (terms : ℕ)
    {box : CertificateBox} {point : CertificatePoint}
    {certificate : JCertificate}
    (hpoint : box.Contains point)
    (hcheck : certificate.check box = true) :
    (certificate.jAD terms box).value.Contains
      (lrCertificateJ point) := by
  have hab := certificate.ab.sound terms hpoint (by
    simpa [check] using hcheck)
  have hx := lrCertificateXAD_sound hpoint
  have hj := IntervalAD.contains_sub
    (IntervalAD.contains_mul hab.2.1 hx) hab.2.2
  simpa [jAD, lrCertificateJ] using hj.1

end JCertificate

/-- Deterministic untrusted payload used only for a nonpositive-`J` check. -/
def jCertificate (sqrtFuel logFuel : ℕ) (box : CertificateBox) :
    JCertificate :=
  let raw := LRLowRatioFiniteVConcreteOracle.rawHull box
  let coordinate := LRHighShapeCoordinateCertificate.auto sqrtFuel raw
  { coordinate := coordinate
    ab := LRHighShapeABCertificate.auto logFuel raw coordinate }

/-- Endpoint-safe chart-lifted discard checker.  Physical reasons reuse the
existing raw checker.  The `J` reason checks only the arithmetic payload and
an upper enclosure `J ≤ 0`; no full direct-`V` certificate is constructed or
checked. -/
def discardCheck (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : DiscardData → Bool
  | .physical reason =>
      LRLowRatioFiniteVMeanValue.chartBoxCheck box &&
        lrPhysicalDiscardCheck
          (LRLowRatioFiniteVConcreteOracle.rawHull box) reason
  | .jNonpositive =>
      let certificate := jCertificate sqrtFuel logFuel box
      LRLowRatioFiniteVMeanValue.chartBoxCheck box &&
        (certificate.check
          (LRLowRatioFiniteVConcreteOracle.rawHull box) &&
        decide ((certificate.jAD terms
          (LRLowRatioFiniteVConcreteOracle.rawHull box)).value.upper ≤ 0))

/-- Every accepted compact discard excludes all relevant decoded points.
This is exactly the `discardSound` contract required by
`LRLowRatioFiniteVMeanValue.CheckedTree`. -/
theorem discardCheck_sound (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (data : DiscardData)
    (hcheck : discardCheck terms sqrtFuel logFuel box data = true) :
    ∀ coordinate, box.Contains coordinate →
      ¬ LRHighShapeVRelevant
        (lrDeterminantKChartDecode coordinate) := by
  intro coordinate hcoordinate hRelevant
  rcases hRelevant with ⟨hphysical, hJ⟩
  cases data with
  | physical reason =>
      have hparts :
          LRLowRatioFiniteVMeanValue.chartBoxCheck box = true ∧
          lrPhysicalDiscardCheck
            (LRLowRatioFiniteVConcreteOracle.rawHull box) reason = true := by
        simpa [discardCheck] using hcheck
      have hraw :=
        LRLowRatioFiniteVConcreteOracle.rawHull_contains_decode_of_chartBoxCheck
          hparts.1 hcoordinate
      exact lrPhysicalDiscardCheck_sound
        (LRLowRatioFiniteVConcreteOracle.rawHull box) reason hparts.2
        (lrDeterminantKChartDecode coordinate) hraw hphysical
  | jNonpositive =>
      have hparts :
          LRLowRatioFiniteVMeanValue.chartBoxCheck box = true ∧
          (jCertificate sqrtFuel logFuel box).check
            (LRLowRatioFiniteVConcreteOracle.rawHull box) = true ∧
          ((jCertificate sqrtFuel logFuel box).jAD terms
            (LRLowRatioFiniteVConcreteOracle.rawHull box)).value.upper ≤ 0 := by
        simpa [discardCheck] using hcheck
      have hraw :=
        LRLowRatioFiniteVConcreteOracle.rawHull_contains_decode_of_chartBoxCheck
          hparts.1 hcoordinate
      have henclose :=
        (jCertificate sqrtFuel logFuel box).jAD_value_sound terms
          hraw hparts.2.1
      have hupper :
          ((((jCertificate sqrtFuel logFuel box).jAD terms
            (LRLowRatioFiniteVConcreteOracle.rawHull box)).value.upper : ℚ) :
              ℝ) ≤ 0 := by
        exact_mod_cast hparts.2.2
      linarith [henclose.2]

/-- Try every verified discard reason in the same order as the existing
high-shape generator.  Returning `none` is failure, never authority. -/
def autoDiscard (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) : Option DiscardData :=
  if discardCheck terms sqrtFuel logFuel box
      (.physical .eAtLeastOne) then
    some (.physical .eAtLeastOne)
  else if discardCheck terms sqrtFuel logFuel box
      (.physical .xBelowHighShape) then
    some (.physical .xBelowHighShape)
  else if discardCheck terms sqrtFuel logFuel box
      (.physical .vBelowThird) then
    some (.physical .vBelowThird)
  else if discardCheck terms sqrtFuel logFuel box .jNonpositive then
    some .jNonpositive
  else
    none

/-- An automatically proposed discard is accepted only because its ordinary
kernel-reducible checker returned `true`. -/
theorem autoDiscard_check_of_eq (terms sqrtFuel logFuel : ℕ)
    (box : CertificateBox) (data : DiscardData)
    (hauto : autoDiscard terms sqrtFuel logFuel box = some data) :
    discardCheck terms sqrtFuel logFuel box data = true := by
  unfold autoDiscard at hauto
  split at hauto <;> rename_i he
  · cases hauto
    exact he
  split at hauto <;> rename_i hx
  · cases hauto
    exact hx
  split at hauto <;> rename_i hv
  · cases hauto
    exact hv
  split at hauto <;> rename_i hJ
  · cases hauto
    exact hJ
  · simp at hauto

end LRLowRatioFiniteVDiscard
end CourtadeKumar
