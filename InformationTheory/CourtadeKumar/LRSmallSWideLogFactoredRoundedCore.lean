import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedValueInputs
import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredValidityCore

/-!
# Dependency-factored rounded primitive inputs

`CoversExact` has seven fields, but only one rounded primitive is genuinely
leaf-local. This module packages the other six at their true cache boundaries
and performs every certificate/slice transport in one generic theorem.

Rounded data and proof facts are deliberately separate. `lowerCheck` therefore
projects only through small data structures and never unfolds a proof-bearing
cache record or a large exact node.
-/

namespace CourtadeKumar
namespace LRSmallSWideLogFactoredRounded

open LRSmallSBridgeCoreCertificate
open LRSmallSWideLog
open LRSmallSWideLogRoundedValue
open LRSmallSWideLogSharedSliceCore
open LRSmallSWideLogFactoredValidity
open LRUpperKDyadicOuterRounding

@[simp] theorem intervalAD_log_value (terms : ℕ)
    (certificate : RationalEnclosure.LogIntervalCertificate)
    (a : IntervalAD) :
    (IntervalAD.log terms certificate a).value =
      certificate.enclosure terms := by
  rfl

@[simp] theorem wideLog_value (data : WideLogData) (a : IntervalAD) :
    (wideLog data a).value = data.output := by
  rfl

/-- Kernel-only bridge used when generating each shared rounded cache fact. -/
theorem covers_of_outerEnclosure_eq
    (bits : ℕ) {input exactValue : RationalEnclosure}
    (binding : input = outerEnclosure bits exactValue) :
    LRUpperKMidpointCoarsening.Covers input exactValue := by
  rw [binding]
  exact outerEnclosure_covers bits exactValue

/-- Rounded `log 2`, shared by every leaf. -/
structure GlobalRoundedFacts (terms : ℕ)
    (logTwo : RationalEnclosure.LogIntervalCertificate)
    (input : RationalEnclosure) : Prop where
  covers : LRUpperKMidpointCoarsening.Covers input
    (logTwo.enclosure terms)

/-- The three small rounded inputs carried by an `(s,k)` cache. -/
structure SKRoundedInputs where
  logOuter : RationalEnclosure
  logK : RationalEnclosure
  logDArg : RationalEnclosure

/-- Covers facts for the three `(s,k)`-cache logarithm certificates. Their
values are certificate enclosures and hence do not depend on AD derivatives. -/
structure SKRoundedFacts (terms : ℕ)
    (logOuter logK logDArg : RationalEnclosure.LogIntervalCertificate)
    (inputs : SKRoundedInputs) : Prop where
  coversLogOuter : LRUpperKMidpointCoarsening.Covers inputs.logOuter
    (logOuter.enclosure terms)
  coversLogK : LRUpperKMidpointCoarsening.Covers inputs.logK
    (logK.enclosure terms)
  coversLogDArg : LRUpperKMidpointCoarsening.Covers inputs.logDArg
    (logDArg.enclosure terms)

/-- Rounded `qChi`, the only shared primitive whose value still depends on an
interval slice rather than just on a log certificate. -/
structure ChiRoundedFacts (terms : ℕ) (slice : ChiSlice)
    (logChi : RationalEnclosure.LogIntervalCertificate)
    (inputQChi : RationalEnclosure) : Prop where
  coversQChi : LRUpperKMidpointCoarsening.Covers inputQChi
    (slice.qChiAD terms logChi).value

/-- The rounded inner logarithm depends only on its two endpoint caches. -/
structure InnerPairRoundedFacts (data : WideLogData)
    (inputLogInner : RationalEnclosure) : Prop where
  coversLogInner : LRUpperKMidpointCoarsening.Covers inputLogInner data.output

/-- The sole leaf-local rounded primitive. -/
structure LeafRoundedFacts (terms : ℕ)
    (logOnePlusV : RationalEnclosure.LogIntervalCertificate)
    (inputLogOnePlusV : RationalEnclosure) : Prop where
  coversLogOnePlusV : LRUpperKMidpointCoarsening.Covers inputLogOnePlusV
    (logOnePlusV.enclosure terms)

/-- Assemble seven small scalar inputs using data only. -/
def inputsOfCaches
    (globalLogTwo : RationalEnclosure)
    (sk : SKRoundedInputs)
    (chiQChi innerLog logOnePlusV : RationalEnclosure) : Inputs :=
  { logTwo := globalLogTwo
    logInner := innerLog
    logOuter := sk.logOuter
    logK := sk.logK
    logOnePlusV := logOnePlusV
    logDArg := sk.logDArg
    qChi := chiQChi }

/-- Assemble `CoversExact` from opaque cached proof facts. A leaf supplies one
shared-key binding; every semantic transport is centralized here. -/
theorem coversExact_of_cached
    {terms : ℕ} {box : CertificateBox}
    {certificate : LRSmallSBridgeCoreCertificate}
    {sk : SKSlice} {chi : ChiSlice} {innerLog : WideLogData}
    {logTwo logOuter logK logDArg logChi :
      RationalEnclosure.LogIntervalCertificate}
    {globalInput : RationalEnclosure} {skInputs : SKRoundedInputs}
    {chiInput innerInput leafInput : RationalEnclosure}
    (globalFacts : GlobalRoundedFacts terms logTwo globalInput)
    (skFacts : SKRoundedFacts terms logOuter logK logDArg skInputs)
    (chiFacts : ChiRoundedFacts terms chi logChi chiInput)
    (innerFacts : InnerPairRoundedFacts innerLog innerInput)
    (leafFacts : LeafRoundedFacts terms certificate.logOnePlusV leafInput)
    (binding : SharedKey.ofLeaf box certificate =
      SharedKey.ofCaches sk chi logTwo logOuter logK logChi logDArg) :
    CoversExact terms box certificate innerLog
      (inputsOfCaches globalInput skInputs chiInput innerInput leafInput) := by
  have hchi : ChiSlice.ofBox box = chi :=
    congrArg SharedKey.chi binding
  have hLogTwo : certificate.logTwo = logTwo :=
    congrArg SharedKey.logTwo binding
  have hLogOuter : certificate.logOuter = logOuter :=
    congrArg SharedKey.logOuter binding
  have hLogK : certificate.logK = logK :=
    congrArg SharedKey.logK binding
  have hLogChi : certificate.logChi = logChi :=
    congrArg SharedKey.logChi binding
  have hLogDArg : certificate.logDArg = logDArg :=
    congrArg SharedKey.logDArg binding
  refine
    { logTwo := ?_
      logInner := ?_
      logOuter := ?_
      logK := ?_
      logOnePlusV := ?_
      logDArg := ?_
      qChi := ?_ }
  · simpa only [intervalAD_log_value, hLogTwo] using globalFacts.covers
  · simpa only [wideLog_value] using innerFacts.coversLogInner
  · simpa only [intervalAD_log_value, hLogOuter] using
      skFacts.coversLogOuter
  · simpa only [intervalAD_log_value, hLogK] using skFacts.coversLogK
  · simpa only [intervalAD_log_value] using leafFacts.coversLogOnePlusV
  · simpa only [intervalAD_log_value, hLogDArg] using
      skFacts.coversLogDArg
  · change LRUpperKMidpointCoarsening.Covers chiInput
      (qChiAD terms box certificate).value
    rw [qChiAD_eq_of_slice_eq hchi, hLogChi]
    exact chiFacts.coversQChi

end LRSmallSWideLogFactoredRounded
end CourtadeKumar
