import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore

namespace CourtadeKumar
namespace LRSmallSWideLogRoundedScalarV2

open LRSmallSBridgeCoreCertificate
open LRSmallSWideLog
open LRSmallSWideLogRounded
open LRSmallSWideLogRoundedValue
open LRSmallSWideLogSharedSliceCore
open LRSmallSWideLogFactoredValidity
open LRSmallSWideLogFactoredRounded
open LRUpperKDyadicOuterRounding

noncomputable def globalLogTwoCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := 1, mantissa := (1) }, upper := { exponent := 1, mantissa := (1) } }

set_option maxRecDepth 1000000 in
private theorem globalLogTwo_valid :
    globalLogTwoCertificate.check (IntervalAD.const 2).value = true := by
  rfl'

theorem globalValidityFacts :
    GlobalFacts globalLogTwoCertificate :=
  { logTwo := globalLogTwo_valid }

noncomputable def globalInput : RationalEnclosure :=
  { lower := (11629079/16777216), upper := (11629081/16777216) }

set_option maxRecDepth 1000000 in
private theorem globalInput_eq :
    globalInput = outerEnclosure 24
      (globalLogTwoCertificate.enclosure 8) := by
  rfl'

theorem globalRoundedFacts : GlobalRoundedFacts 8
    globalLogTwoCertificate globalInput :=
  { covers := covers_of_outerEnclosure_eq 24 globalInput_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
