import InformationTheory.CourtadeKumar.LRSmallSWideLogSemanticCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogSharedSliceCore

/-!
# Factored validity for the rounded small-s certificate replay

The analytic soundness theorem consumes `WideCertificateValid` and
`WideLogData.Valid`, but most of their fields are shared by many leaves.  This
module splits those records at their actual dependency boundaries:

* one global logarithm fact;
* facts depending only on the `(s, k)` slice;
* facts depending only on the `chi` slice;
* the two genuinely leaf-local certificate checks;
* cached validity/positivity of an endpoint and the two leaf-specific endpoint
  coverage inequalities.

The assembly theorems below are purely propositional.  In particular, they do
not run a certificate checker and do not use VM/native evaluation.
-/

namespace CourtadeKumar
namespace LRSmallSWideLogFactoredValidity

open LRSmallSBridgeCoreCertificate
open LRSmallSWideLog
open LRSmallSWideLogSharedSliceCore

/-! ## Certificate validity -/

/-- The only certificate check independent of the box. -/
structure GlobalFacts
    (logTwo : RationalEnclosure.LogIntervalCertificate) : Prop where
  logTwo : logTwo.check (IntervalAD.const 2).value = true

/-- All validity facts determined by the four `(s, k)` endpoints. -/
structure SKFacts (slice : SKSlice)
    (logOuter logK logDArg : RationalEnclosure.LogIntervalCertificate) : Prop where
  domain : (0 : ℚ) ≤ slice.sLo ∧ slice.sHi ≤ 1 / 16384 ∧
    1 / 4 ≤ slice.kLo ∧ slice.kHi ≤ 4
  kPositive : (0 : ℚ) < slice.kAD.value.lower
  logOuter : logOuter.check slice.outerAD.value = true
  logK : logK.check slice.kAD.value = true
  logDArg : logDArg.check slice.dArgAD.value = true

/-- All validity facts determined by the two `chi` endpoints. -/
structure ChiFacts (slice : ChiSlice)
    (logChi : RationalEnclosure.LogIntervalCertificate) : Prop where
  domain : (0 : ℚ) ≤ slice.lo ∧ slice.hi ≤ 1
  onePlusPositive : (0 : ℚ) < slice.onePlusAD.value.lower
  logChi : (if slice.lo = 0 then
    if slice.hi = 0 then true
    else decide (slice.hi ≤ 1 / 4) &&
      logChi.check (IntervalAD.const slice.hi).value
    else logChi.check slice.chiAD.value) = true

/-- The two checks that really depend on the complete leaf certificate. -/
structure LeafFacts (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate) : Prop where
  coordinate : certificate.coordinate.check box = true
  logOnePlusV : certificate.logOnePlusV.check
    (IntervalAD.add (IntervalAD.const 1)
      (certificate.coordinate.vAD box)).value = true

/-- The complete shared identity of a leaf, excluding its coordinate and
`logOnePlusV` payloads.  Binding this record once is cheaper and more robust
than asking every generated leaf to transport seven fields independently. -/
structure SharedKey where
  sk : SKSlice
  chi : ChiSlice
  logTwo : RationalEnclosure.LogIntervalCertificate
  logOuter : RationalEnclosure.LogIntervalCertificate
  logK : RationalEnclosure.LogIntervalCertificate
  logChi : RationalEnclosure.LogIntervalCertificate
  logDArg : RationalEnclosure.LogIntervalCertificate

def SharedKey.ofLeaf (box : CertificateBox)
    (certificate : LRSmallSBridgeCoreCertificate) : SharedKey :=
  { sk := SKSlice.ofBox box
    chi := ChiSlice.ofBox box
    logTwo := certificate.logTwo
    logOuter := certificate.logOuter
    logK := certificate.logK
    logChi := certificate.logChi
    logDArg := certificate.logDArg }

def SharedKey.ofCaches (sk : SKSlice) (chi : ChiSlice)
    (logTwo logOuter logK logChi logDArg :
      RationalEnclosure.LogIntervalCertificate) : SharedKey :=
  { sk := sk
    chi := chi
    logTwo := logTwo
    logOuter := logOuter
    logK := logK
    logChi := logChi
    logDArg := logDArg }

/-- Assemble the original certificate-validity record from dependency-factored
facts.  The slice equalities are the only transports required at a leaf. -/
theorem wideCertificateValid_of_facts
    {box : CertificateBox}
    {certificate : LRSmallSBridgeCoreCertificate}
    {sk : SKSlice} {chi : ChiSlice}
    (hsk : SKSlice.ofBox box = sk)
    (hchi : ChiSlice.ofBox box = chi)
    (global : GlobalFacts certificate.logTwo)
    (skFacts : SKFacts sk certificate.logOuter certificate.logK
      certificate.logDArg)
    (chiFacts : ChiFacts chi certificate.logChi)
    (leaf : LeafFacts box certificate) :
    WideCertificateValid box certificate := by
  subst sk
  subst chi
  refine
    { coordinate := leaf.coordinate
      domain := ?_
      kPositive := ?_
      onePlusChiPositive := ?_
      logTwo := global.logTwo
      logOuter := ?_
      logK := ?_
      logChi := ?_
      logOnePlusV := leaf.logOnePlusV
      logDArg := ?_ }
  · exact ⟨skFacts.domain.1, skFacts.domain.2.1,
      skFacts.domain.2.2.1, skFacts.domain.2.2.2,
      chiFacts.domain.1, chiFacts.domain.2⟩
  · simpa only [kAD_eq_slice] using skFacts.kPositive
  · simpa only [onePlusChiAD_eq_slice] using chiFacts.onePlusPositive
  · simpa only [outerAD_eq_slice] using skFacts.logOuter
  · simpa only [kAD_eq_slice] using skFacts.logK
  · simpa only [chiAD_eq_slice] using chiFacts.logChi
  · simpa only [dArgAD_eq_slice] using skFacts.logDArg

/-- Production-facing assembly API.  Cache facts determine all implicit cache
parameters before the final `binding` argument is elaborated, so a generated
leaf normally closes that single equality with `rfl`. -/
theorem wideCertificateValid_of_cached
    {box : CertificateBox}
    {certificate : LRSmallSBridgeCoreCertificate}
    {sk : SKSlice} {chi : ChiSlice}
    {logTwo logOuter logK logChi logDArg :
      RationalEnclosure.LogIntervalCertificate}
    (global : GlobalFacts logTwo)
    (skFacts : SKFacts sk logOuter logK logDArg)
    (chiFacts : ChiFacts chi logChi)
    (leaf : LeafFacts box certificate)
    (binding : SharedKey.ofLeaf box certificate =
      SharedKey.ofCaches sk chi logTwo logOuter logK logChi logDArg) :
    WideCertificateValid box certificate := by
  have hsk : SKSlice.ofBox box = sk :=
    congrArg SharedKey.sk binding
  have hchi : ChiSlice.ofBox box = chi :=
    congrArg SharedKey.chi binding
  have hglobal : GlobalFacts certificate.logTwo := by
    rw [show certificate.logTwo = logTwo from
      congrArg SharedKey.logTwo binding]
    exact global
  have hskFacts : SKFacts sk certificate.logOuter certificate.logK
      certificate.logDArg := by
    rw [show certificate.logOuter = logOuter from
      congrArg SharedKey.logOuter binding]
    rw [show certificate.logK = logK from
      congrArg SharedKey.logK binding]
    rw [show certificate.logDArg = logDArg from
      congrArg SharedKey.logDArg binding]
    exact skFacts
  have hchiFacts : ChiFacts chi certificate.logChi := by
    rw [show certificate.logChi = logChi from
      congrArg SharedKey.logChi binding]
    exact chiFacts
  exact wideCertificateValid_of_facts hsk hchi hglobal hskFacts hchiFacts leaf

/-! ## Endpoint-log validity -/

/-- Cached endpoint validity together with the positivity needed when the
endpoint is selected as the lower logarithm endpoint. -/
structure PositiveEndpointFacts (terms : ℕ) (cache : EndpointCache) : Prop where
  valid : cache.Valid terms
  positive : (0 : ℚ) < cache.input

/-- The only two inner-log obligations that still depend on the current leaf
box and its chosen pair of cached endpoints. -/
structure CoverageFacts (a : IntervalAD) (data : WideLogData) : Prop where
  lower : data.lower.input ≤ a.value.lower
  upper : a.value.upper ≤ data.upper.input

/-- A deliberately shallow, kernel-reduced check for the two leaf-specific
coverage inequalities.  This uses ordinary `decide`; it has no native or VM
evaluation path. -/
def coverageCheck (a : IntervalAD) (data : WideLogData) : Bool :=
  decide (data.lower.input ≤ a.value.lower ∧
    a.value.upper ≤ data.upper.input)

theorem coverageFacts_of_check {a : IntervalAD} {data : WideLogData}
    (hcheck : coverageCheck a data = true) : CoverageFacts a data := by
  have hbounds : data.lower.input ≤ a.value.lower ∧
      a.value.upper ≤ data.upper.input := by
    exact of_decide_eq_true hcheck
  exact ⟨hbounds.1, hbounds.2⟩

/-- Assemble `WideLogData.Valid` without rechecking either endpoint. -/
theorem wideLogDataValid_of_facts
    {terms : ℕ} {a : IntervalAD} {data : WideLogData}
    (lower : PositiveEndpointFacts terms data.lower)
    (upper : data.upper.Valid terms)
    (coverage : CoverageFacts a data) :
    data.Valid terms a :=
  { lower := lower.valid
    upper := upper
    lowerPositive := lower.positive
    lowerCovers := coverage.lower
    upperCovers := coverage.upper }

/-- Short generated-leaf API: endpoint proofs are reused, and only the scalar
coverage Boolean is reduced at the leaf. -/
theorem wideLogDataValid_of_cachedCheck
    {terms : ℕ} {a : IntervalAD} {data : WideLogData}
    (lower : PositiveEndpointFacts terms data.lower)
    (upper : data.upper.Valid terms)
    (hcheck : coverageCheck a data = true) :
    data.Valid terms a :=
  wideLogDataValid_of_facts lower upper (coverageFacts_of_check hcheck)

end LRSmallSWideLogFactoredValidity
end CourtadeKumar
