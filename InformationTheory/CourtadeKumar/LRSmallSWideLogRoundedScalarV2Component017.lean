import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch1

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
open LRSmallSWideLogRoundedFlatTopology

private noncomputable def leaf686Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (0), chiHi := (1/32) }

private noncomputable def leaf686Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777251/16777216) }, vSqrt := { lower := (65531/65536), upper := (4194320/4194287) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (16744415/8388608) }, upper := { exponent := 0, mantissa := (273/256) } }, logOuter := sk59LogOuterCertificate, logK := sk59LogKCertificate, logChi := chi29LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388607/8388574) } }, logDArg := sk59LogDArgCertificate }

private noncomputable def leaf686InnerLog : WideLogData :=
  innerPair0Data

set_option maxRecDepth 1000000 in
private theorem leaf686LocalValidity :
    LeafFacts leaf686Box leaf686Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf686Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194320/4194287) }) = true
      norm_num [leaf686Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf686CertificateValid :
    WideCertificateValid leaf686Box leaf686Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk59ValidityFacts chi29ValidityFacts
    leaf686LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf686CoverageChecked :
    coverageCheck (innerAD leaf686Box) leaf686InnerLog = true := by
  rfl'

private theorem leaf686InnerLogValid :
    leaf686InnerLog.Valid 8 (innerAD leaf686Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint1PositiveFacts.valid leaf686CoverageChecked

private noncomputable def leaf686InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629147/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf686InputLogOnePlusV_eq :
    leaf686InputLogOnePlusV = outerEnclosure 24
      (leaf686Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf686RoundedFacts : LeafRoundedFacts 8
    leaf686Certificate.logOnePlusV leaf686InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf686InputLogOnePlusV_eq }

private noncomputable def leaf686Inputs : Inputs :=
  inputsOfCaches globalInput sk59RoundedInputs
    chi29InputQChi innerPair0Input
    leaf686InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf686LowerChecked :
    lowerCheck 24 leaf686Box leaf686Inputs = true := by
  rfl'

private theorem leaf686CoversExact : CoversExact 8
    leaf686Box leaf686Certificate leaf686InnerLog leaf686Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk59RoundedFacts chi29RoundedFacts
    innerPair0RoundedFacts leaf686RoundedFacts (by rfl)

private theorem leaf686FlatSound : Sound leaf686Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf686CertificateValid
    leaf686InnerLogValid leaf686CoversExact leaf686LowerChecked

private noncomputable def leaf687Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (0), chiHi := (1/32) }

private noncomputable def leaf687Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (16777253/16777216) }, vSqrt := { lower := (65531/65536), upper := (2097160/2097143) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := -1, mantissa := (16744413/8388608) }, upper := { exponent := 0, mantissa := (137/128) } }, logOuter := sk60LogOuterCertificate, logK := sk60LogKCertificate, logChi := chi29LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4194303/4194286) } }, logDArg := sk60LogDArgCertificate }

private noncomputable def leaf687InnerLog : WideLogData :=
  innerPair0Data

set_option maxRecDepth 1000000 in
private theorem leaf687LocalValidity :
    LeafFacts leaf687Box leaf687Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf687Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2097160/2097143) }) = true
      norm_num [leaf687Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf687CertificateValid :
    WideCertificateValid leaf687Box leaf687Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk60ValidityFacts chi29ValidityFacts
    leaf687LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf687CoverageChecked :
    coverageCheck (innerAD leaf687Box) leaf687InnerLog = true := by
  rfl'

private theorem leaf687InnerLogValid :
    leaf687InnerLog.Valid 8 (innerAD leaf687Box) :=
  wideLogDataValid_of_cachedCheck endpoint0PositiveFacts
    endpoint1PositiveFacts.valid leaf687CoverageChecked

private noncomputable def leaf687InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629149/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf687InputLogOnePlusV_eq :
    leaf687InputLogOnePlusV = outerEnclosure 24
      (leaf687Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf687RoundedFacts : LeafRoundedFacts 8
    leaf687Certificate.logOnePlusV leaf687InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf687InputLogOnePlusV_eq }

private noncomputable def leaf687Inputs : Inputs :=
  inputsOfCaches globalInput sk60RoundedInputs
    chi29InputQChi innerPair0Input
    leaf687InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf687LowerChecked :
    lowerCheck 24 leaf687Box leaf687Inputs = true := by
  rfl'

private theorem leaf687CoversExact : CoversExact 8
    leaf687Box leaf687Certificate leaf687InnerLog leaf687Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk60RoundedFacts chi29RoundedFacts
    innerPair0RoundedFacts leaf687RoundedFacts (by rfl)

private theorem leaf687FlatSound : Sound leaf687Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf687CertificateValid
    leaf687InnerLogValid leaf687CoversExact leaf687LowerChecked

private noncomputable def leaf688Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (1/32), chiHi := (5/128) }

private noncomputable def leaf688Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108907/67108864) }, vSqrt := { lower := (65531/65536), upper := (16777280/16777131) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (71270103/67108864) }, upper := { exponent := 0, mantissa := (1109/1024) } }, logOuter := sk59LogOuterCertificate, logK := sk59LogKCertificate, logChi := chi38LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554411/33554262) } }, logDArg := sk59LogDArgCertificate }

private noncomputable def leaf688InnerLog : WideLogData :=
  innerPair9Data

set_option maxRecDepth 1000000 in
private theorem leaf688LocalValidity :
    LeafFacts leaf688Box leaf688Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf688Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777280/16777131) }) = true
      norm_num [leaf688Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf688CertificateValid :
    WideCertificateValid leaf688Box leaf688Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk59ValidityFacts chi38ValidityFacts
    leaf688LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf688CoverageChecked :
    coverageCheck (innerAD leaf688Box) leaf688InnerLog = true := by
  rfl'

private theorem leaf688InnerLogValid :
    leaf688InnerLog.Valid 8 (innerAD leaf688Box) :=
  wideLogDataValid_of_cachedCheck endpoint3PositiveFacts
    endpoint1PositiveFacts.valid leaf688CoverageChecked

private noncomputable def leaf688InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629155/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf688InputLogOnePlusV_eq :
    leaf688InputLogOnePlusV = outerEnclosure 24
      (leaf688Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf688RoundedFacts : LeafRoundedFacts 8
    leaf688Certificate.logOnePlusV leaf688InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf688InputLogOnePlusV_eq }

private noncomputable def leaf688Inputs : Inputs :=
  inputsOfCaches globalInput sk59RoundedInputs
    chi38InputQChi innerPair9Input
    leaf688InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf688LowerChecked :
    lowerCheck 24 leaf688Box leaf688Inputs = true := by
  rfl'

private theorem leaf688CoversExact : CoversExact 8
    leaf688Box leaf688Certificate leaf688InnerLog leaf688Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk59RoundedFacts chi38RoundedFacts
    innerPair9RoundedFacts leaf688RoundedFacts (by rfl)

private theorem leaf688FlatSound : Sound leaf688Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf688CertificateValid
    leaf688InnerLogValid leaf688CoversExact leaf688LowerChecked

private noncomputable def leaf689Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf689Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108909/67108864) }, vSqrt := { lower := (65531/65536), upper := (8388640/8388557) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (72318613/67108864) }, upper := { exponent := 0, mantissa := (563/512) } }, logOuter := sk59LogOuterCertificate, logK := sk59LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777197/16777114) } }, logDArg := sk59LogDArgCertificate }

private noncomputable def leaf689InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf689LocalValidity :
    LeafFacts leaf689Box leaf689Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf689Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388640/8388557) }) = true
      norm_num [leaf689Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf689CertificateValid :
    WideCertificateValid leaf689Box leaf689Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk59ValidityFacts chi39ValidityFacts
    leaf689LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf689CoverageChecked :
    coverageCheck (innerAD leaf689Box) leaf689InnerLog = true := by
  rfl'

private theorem leaf689InnerLogValid :
    leaf689InnerLog.Valid 8 (innerAD leaf689Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf689CoverageChecked

private noncomputable def leaf689InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907291/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf689InputLogOnePlusV_eq :
    leaf689InputLogOnePlusV = outerEnclosure 24
      (leaf689Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf689RoundedFacts : LeafRoundedFacts 8
    leaf689Certificate.logOnePlusV leaf689InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf689InputLogOnePlusV_eq }

private noncomputable def leaf689Inputs : Inputs :=
  inputsOfCaches globalInput sk59RoundedInputs
    chi39InputQChi innerPair5Input
    leaf689InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf689LowerChecked :
    lowerCheck 24 leaf689Box leaf689Inputs = true := by
  rfl'

private theorem leaf689CoversExact : CoversExact 8
    leaf689Box leaf689Certificate leaf689InnerLog leaf689Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk59RoundedFacts chi39RoundedFacts
    innerPair5RoundedFacts leaf689RoundedFacts (by rfl)

private theorem leaf689FlatSound : Sound leaf689Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf689CertificateValid
    leaf689InnerLogValid leaf689CoversExact leaf689LowerChecked

private noncomputable def leaf690Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (3/64), chiHi := (1/16) }

private noncomputable def leaf690Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108937/67108864) }, vSqrt := { lower := (65531/65536), upper := (4194312/4194271) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (73367097/67108864) }, upper := { exponent := 0, mantissa := (289/256) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi31LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388583/8388542) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf690InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf690LocalValidity :
    LeafFacts leaf690Box leaf690Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf690Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194312/4194271) }) = true
      norm_num [leaf690Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf690CertificateValid :
    WideCertificateValid leaf690Box leaf690Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi31ValidityFacts
    leaf690LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf690CoverageChecked :
    coverageCheck (innerAD leaf690Box) leaf690InnerLog = true := by
  rfl'

private theorem leaf690InnerLogValid :
    leaf690InnerLog.Valid 8 (innerAD leaf690Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf690CoverageChecked

private noncomputable def leaf690InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629163/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf690InputLogOnePlusV_eq :
    leaf690InputLogOnePlusV = outerEnclosure 24
      (leaf690Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf690RoundedFacts : LeafRoundedFacts 8
    leaf690Certificate.logOnePlusV leaf690InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf690InputLogOnePlusV_eq }

private noncomputable def leaf690Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi31InputQChi innerPair6Input
    leaf690InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf690LowerChecked :
    lowerCheck 24 leaf690Box leaf690Inputs = true := by
  rfl'

private theorem leaf690CoversExact : CoversExact 8
    leaf690Box leaf690Certificate leaf690InnerLog leaf690Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi31RoundedFacts
    innerPair6RoundedFacts leaf690RoundedFacts (by rfl)

private theorem leaf690FlatSound : Sound leaf690Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf690CertificateValid
    leaf690InnerLogValid leaf690CoversExact leaf690LowerChecked

private noncomputable def leaf691Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (3/64), chiHi := (1/16) }

private noncomputable def leaf691Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108939/67108864) }, vSqrt := { lower := (65531/65536), upper := (699052/699045) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (73563691/67108864) }, upper := { exponent := 0, mantissa := (145/128) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi31LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (1398097/1398090) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf691InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf691LocalValidity :
    LeafFacts leaf691Box leaf691Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf691Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (699052/699045) }) = true
      norm_num [leaf691Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf691CertificateValid :
    WideCertificateValid leaf691Box leaf691Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi31ValidityFacts
    leaf691LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf691CoverageChecked :
    coverageCheck (innerAD leaf691Box) leaf691InnerLog = true := by
  rfl'

private theorem leaf691InnerLogValid :
    leaf691InnerLog.Valid 8 (innerAD leaf691Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf691CoverageChecked

private noncomputable def leaf691InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629165/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf691InputLogOnePlusV_eq :
    leaf691InputLogOnePlusV = outerEnclosure 24
      (leaf691Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf691RoundedFacts : LeafRoundedFacts 8
    leaf691Certificate.logOnePlusV leaf691InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf691InputLogOnePlusV_eq }

private noncomputable def leaf691Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi31InputQChi innerPair6Input
    leaf691InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf691LowerChecked :
    lowerCheck 24 leaf691Box leaf691Inputs = true := by
  rfl'

private theorem leaf691CoversExact : CoversExact 8
    leaf691Box leaf691Certificate leaf691InnerLog leaf691Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi31RoundedFacts
    innerPair6RoundedFacts leaf691RoundedFacts (by rfl)

private theorem leaf691FlatSound : Sound leaf691Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf691CertificateValid
    leaf691InnerLogValid leaf691CoversExact leaf691LowerChecked

private noncomputable def leaf692Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (1/32), chiHi := (5/128) }

private noncomputable def leaf692Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108909/67108864) }, vSqrt := { lower := (65531/65536), upper := (8388640/8388563) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (71532229/67108864) }, upper := { exponent := 0, mantissa := (557/512) } }, logOuter := sk60LogOuterCertificate, logK := sk60LogKCertificate, logChi := chi38LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777203/16777126) } }, logDArg := sk60LogDArgCertificate }

private noncomputable def leaf692InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf692LocalValidity :
    LeafFacts leaf692Box leaf692Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf692Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388640/8388563) }) = true
      norm_num [leaf692Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf692CertificateValid :
    WideCertificateValid leaf692Box leaf692Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk60ValidityFacts chi38ValidityFacts
    leaf692LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf692CoverageChecked :
    coverageCheck (innerAD leaf692Box) leaf692InnerLog = true := by
  rfl'

private theorem leaf692InnerLogValid :
    leaf692InnerLog.Valid 8 (innerAD leaf692Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf692CoverageChecked

private noncomputable def leaf692InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814579/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf692InputLogOnePlusV_eq :
    leaf692InputLogOnePlusV = outerEnclosure 24
      (leaf692Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf692RoundedFacts : LeafRoundedFacts 8
    leaf692Certificate.logOnePlusV leaf692InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf692InputLogOnePlusV_eq }

private noncomputable def leaf692Inputs : Inputs :=
  inputsOfCaches globalInput sk60RoundedInputs
    chi38InputQChi innerPair5Input
    leaf692InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf692LowerChecked :
    lowerCheck 24 leaf692Box leaf692Inputs = true := by
  rfl'

private theorem leaf692CoversExact : CoversExact 8
    leaf692Box leaf692Certificate leaf692InnerLog leaf692Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk60RoundedFacts chi38RoundedFacts
    innerPair5RoundedFacts leaf692RoundedFacts (by rfl)

private theorem leaf692FlatSound : Sound leaf692Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf692CertificateValid
    leaf692InnerLogValid leaf692CoversExact leaf692LowerChecked

private noncomputable def leaf693Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (5/128), chiHi := (3/64) }

private noncomputable def leaf693Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108911/67108864) }, vSqrt := { lower := (65531/65536), upper := (4194320/4194277) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (72646271/67108864) }, upper := { exponent := 0, mantissa := (283/256) } }, logOuter := sk60LogOuterCertificate, logK := sk60LogKCertificate, logChi := chi39LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388597/8388554) } }, logDArg := sk60LogDArgCertificate }

private noncomputable def leaf693InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf693LocalValidity :
    LeafFacts leaf693Box leaf693Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf693Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194320/4194277) }) = true
      norm_num [leaf693Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf693CertificateValid :
    WideCertificateValid leaf693Box leaf693Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk60ValidityFacts chi39ValidityFacts
    leaf693LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf693CoverageChecked :
    coverageCheck (innerAD leaf693Box) leaf693InnerLog = true := by
  rfl'

private theorem leaf693InnerLogValid :
    leaf693InnerLog.Valid 8 (innerAD leaf693Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf693CoverageChecked

private noncomputable def leaf693InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629167/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf693InputLogOnePlusV_eq :
    leaf693InputLogOnePlusV = outerEnclosure 24
      (leaf693Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf693RoundedFacts : LeafRoundedFacts 8
    leaf693Certificate.logOnePlusV leaf693InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf693InputLogOnePlusV_eq }

private noncomputable def leaf693Inputs : Inputs :=
  inputsOfCaches globalInput sk60RoundedInputs
    chi39InputQChi innerPair5Input
    leaf693InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf693LowerChecked :
    lowerCheck 24 leaf693Box leaf693Inputs = true := by
  rfl'

private theorem leaf693CoversExact : CoversExact 8
    leaf693Box leaf693Certificate leaf693InnerLog leaf693Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk60RoundedFacts chi39RoundedFacts
    innerPair5RoundedFacts leaf693RoundedFacts (by rfl)

private theorem leaf693FlatSound : Sound leaf693Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf693CertificateValid
    leaf693InnerLogValid leaf693CoversExact leaf693LowerChecked

private noncomputable def leaf694Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf694Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217811/134217728) }, vSqrt := { lower := (65531/65536), upper := (11184832/11184729) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (147553407/134217728) }, upper := { exponent := 0, mantissa := (2293/2048) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (22369561/22369458) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf694InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf694LocalValidity :
    LeafFacts leaf694Box leaf694Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf694Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (11184832/11184729) }) = true
      norm_num [leaf694Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf694CertificateValid :
    WideCertificateValid leaf694Box leaf694Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi96ValidityFacts
    leaf694LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf694CoverageChecked :
    coverageCheck (innerAD leaf694Box) leaf694InnerLog = true := by
  rfl'

private theorem leaf694InnerLogValid :
    leaf694InnerLog.Valid 8 (innerAD leaf694Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf694CoverageChecked

private noncomputable def leaf694InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814579/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf694InputLogOnePlusV_eq :
    leaf694InputLogOnePlusV = outerEnclosure 24
      (leaf694Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf694RoundedFacts : LeafRoundedFacts 8
    leaf694Certificate.logOnePlusV leaf694InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf694InputLogOnePlusV_eq }

private noncomputable def leaf694Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi96InputQChi innerPair5Input
    leaf694InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf694LowerChecked :
    lowerCheck 24 leaf694Box leaf694Inputs = true := by
  rfl'

private theorem leaf694CoversExact : CoversExact 8
    leaf694Box leaf694Certificate leaf694InnerLog leaf694Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi96RoundedFacts
    innerPair5RoundedFacts leaf694RoundedFacts (by rfl)

private theorem leaf694FlatSound : Sound leaf694Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf694CertificateValid
    leaf694InnerLogValid leaf694CoversExact leaf694LowerChecked

private noncomputable def leaf695Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (3/64), chiHi := (7/128) }

private noncomputable def leaf695Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217813/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388624/8388545) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (147946597/134217728) }, upper := { exponent := 0, mantissa := (575/512) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi96LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777169/16777090) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf695InnerLog : WideLogData :=
  innerPair5Data

set_option maxRecDepth 1000000 in
private theorem leaf695LocalValidity :
    LeafFacts leaf695Box leaf695Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf695Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388624/8388545) }) = true
      norm_num [leaf695Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf695CertificateValid :
    WideCertificateValid leaf695Box leaf695Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi96ValidityFacts
    leaf695LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf695CoverageChecked :
    coverageCheck (innerAD leaf695Box) leaf695InnerLog = true := by
  rfl'

private theorem leaf695InnerLogValid :
    leaf695InnerLog.Valid 8 (innerAD leaf695Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint1PositiveFacts.valid leaf695CoverageChecked

private noncomputable def leaf695InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453645/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf695InputLogOnePlusV_eq :
    leaf695InputLogOnePlusV = outerEnclosure 24
      (leaf695Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf695RoundedFacts : LeafRoundedFacts 8
    leaf695Certificate.logOnePlusV leaf695InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf695InputLogOnePlusV_eq }

private noncomputable def leaf695Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi96InputQChi innerPair5Input
    leaf695InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf695LowerChecked :
    lowerCheck 24 leaf695Box leaf695Inputs = true := by
  rfl'

private theorem leaf695CoversExact : CoversExact 8
    leaf695Box leaf695Certificate leaf695InnerLog leaf695Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi96RoundedFacts
    innerPair5RoundedFacts leaf695RoundedFacts (by rfl)

private theorem leaf695FlatSound : Sound leaf695Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf695CertificateValid
    leaf695InnerLogValid leaf695CoversExact leaf695LowerChecked

private noncomputable def leaf696Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf696Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217813/134217728) }, vSqrt := { lower := (65531/65536), upper := (4194312/4194269) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (149781493/134217728) }, upper := { exponent := 0, mantissa := (291/256) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388581/8388538) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf696InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf696LocalValidity :
    LeafFacts leaf696Box leaf696Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf696Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194312/4194269) }) = true
      norm_num [leaf696Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf696CertificateValid :
    WideCertificateValid leaf696Box leaf696Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi97ValidityFacts
    leaf696LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf696CoverageChecked :
    coverageCheck (innerAD leaf696Box) leaf696InnerLog = true := by
  rfl'

private theorem leaf696InnerLogValid :
    leaf696InnerLog.Valid 8 (innerAD leaf696Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf696CoverageChecked

private noncomputable def leaf696InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629167/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf696InputLogOnePlusV_eq :
    leaf696InputLogOnePlusV = outerEnclosure 24
      (leaf696Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf696RoundedFacts : LeafRoundedFacts 8
    leaf696Certificate.logOnePlusV leaf696InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf696InputLogOnePlusV_eq }

private noncomputable def leaf696Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi97InputQChi innerPair6Input
    leaf696InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf696LowerChecked :
    lowerCheck 24 leaf696Box leaf696Inputs = true := by
  rfl'

private theorem leaf696CoversExact : CoversExact 8
    leaf696Box leaf696Certificate leaf696InnerLog leaf696Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi97RoundedFacts
    innerPair6RoundedFacts leaf696RoundedFacts (by rfl)

private theorem leaf696FlatSound : Sound leaf696Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf696CertificateValid
    leaf696InnerLogValid leaf696CoversExact leaf696LowerChecked

private noncomputable def leaf697Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (7/128), chiHi := (1/16) }

private noncomputable def leaf697Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217815/134217728) }, vSqrt := { lower := (65531/65536), upper := (1048578/1048567) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (150240215/134217728) }, upper := { exponent := 0, mantissa := (73/64) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi97LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (2097145/2097134) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf697InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf697LocalValidity :
    LeafFacts leaf697Box leaf697Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf697Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (1048578/1048567) }) = true
      norm_num [leaf697Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf697CertificateValid :
    WideCertificateValid leaf697Box leaf697Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi97ValidityFacts
    leaf697LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf697CoverageChecked :
    coverageCheck (innerAD leaf697Box) leaf697InnerLog = true := by
  rfl'

private theorem leaf697InnerLogValid :
    leaf697InnerLog.Valid 8 (innerAD leaf697Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf697CoverageChecked

private noncomputable def leaf697InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629169/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf697InputLogOnePlusV_eq :
    leaf697InputLogOnePlusV = outerEnclosure 24
      (leaf697Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf697RoundedFacts : LeafRoundedFacts 8
    leaf697Certificate.logOnePlusV leaf697InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf697InputLogOnePlusV_eq }

private noncomputable def leaf697Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi97InputQChi innerPair6Input
    leaf697InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf697LowerChecked :
    lowerCheck 24 leaf697Box leaf697Inputs = true := by
  rfl'

private theorem leaf697CoversExact : CoversExact 8
    leaf697Box leaf697Certificate leaf697InnerLog leaf697Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi97RoundedFacts
    innerPair6RoundedFacts leaf697RoundedFacts (by rfl)

private theorem leaf697FlatSound : Sound leaf697Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf697CertificateValid
    leaf697InnerLogValid leaf697CoversExact leaf697LowerChecked

private noncomputable def leaf698Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (1/16), chiHi := (5/64) }

private noncomputable def leaf698Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108939/67108864) }, vSqrt := { lower := (65531/65536), upper := (16777248/16777051) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (75464119/67108864) }, upper := { exponent := 0, mantissa := (1189/1024) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi32LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554299/33554102) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf698InnerLog : WideLogData :=
  innerPair6Data

set_option maxRecDepth 1000000 in
private theorem leaf698LocalValidity :
    LeafFacts leaf698Box leaf698Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf698Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777248/16777051) }) = true
      norm_num [leaf698Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf698CertificateValid :
    WideCertificateValid leaf698Box leaf698Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi32ValidityFacts
    leaf698LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf698CoverageChecked :
    coverageCheck (innerAD leaf698Box) leaf698InnerLog = true := by
  rfl'

private theorem leaf698InnerLogValid :
    leaf698InnerLog.Valid 8 (innerAD leaf698Box) :=
  wideLogDataValid_of_cachedCheck endpoint2PositiveFacts
    endpoint4PositiveFacts.valid leaf698CoverageChecked

private noncomputable def leaf698InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629179/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf698InputLogOnePlusV_eq :
    leaf698InputLogOnePlusV = outerEnclosure 24
      (leaf698Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf698RoundedFacts : LeafRoundedFacts 8
    leaf698Certificate.logOnePlusV leaf698InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf698InputLogOnePlusV_eq }

private noncomputable def leaf698Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi32InputQChi innerPair6Input
    leaf698InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf698LowerChecked :
    lowerCheck 24 leaf698Box leaf698Inputs = true := by
  rfl'

private theorem leaf698CoversExact : CoversExact 8
    leaf698Box leaf698Certificate leaf698InnerLog leaf698Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi32RoundedFacts
    innerPair6RoundedFacts leaf698RoundedFacts (by rfl)

private theorem leaf698FlatSound : Sound leaf698Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf698CertificateValid
    leaf698InnerLogValid leaf698CoversExact leaf698LowerChecked

private noncomputable def leaf699Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (1/16), chiHi := (5/64) }

private noncomputable def leaf699Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108941/67108864) }, vSqrt := { lower := (65531/65536), upper := (8388624/8388523) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (75726245/67108864) }, upper := { exponent := 0, mantissa := (597/512) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi32LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777147/16777046) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf699InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf699LocalValidity :
    LeafFacts leaf699Box leaf699Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf699Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388624/8388523) }) = true
      norm_num [leaf699Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf699CertificateValid :
    WideCertificateValid leaf699Box leaf699Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi32ValidityFacts
    leaf699LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf699CoverageChecked :
    coverageCheck (innerAD leaf699Box) leaf699InnerLog = true := by
  rfl'

private theorem leaf699InnerLogValid :
    leaf699InnerLog.Valid 8 (innerAD leaf699Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf699CoverageChecked

private noncomputable def leaf699InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814591/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf699InputLogOnePlusV_eq :
    leaf699InputLogOnePlusV = outerEnclosure 24
      (leaf699Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf699RoundedFacts : LeafRoundedFacts 8
    leaf699Certificate.logOnePlusV leaf699InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf699InputLogOnePlusV_eq }

private noncomputable def leaf699Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi32InputQChi innerPair2Input
    leaf699InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf699LowerChecked :
    lowerCheck 24 leaf699Box leaf699Inputs = true := by
  rfl'

private theorem leaf699CoversExact : CoversExact 8
    leaf699Box leaf699Certificate leaf699InnerLog leaf699Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi32RoundedFacts
    innerPair2RoundedFacts leaf699RoundedFacts (by rfl)

private theorem leaf699FlatSound : Sound leaf699Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf699CertificateValid
    leaf699InnerLogValid leaf699CoversExact leaf699LowerChecked

private noncomputable def leaf700Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (5/64), chiHi := (3/32) }

private noncomputable def leaf700Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108941/67108864) }, vSqrt := { lower := (65531/65536), upper := (8388624/8388509) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (77561141/67108864) }, upper := { exponent := 0, mantissa := (611/512) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi33LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777133/16777018) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf700InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf700LocalValidity :
    LeafFacts leaf700Box leaf700Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf700Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388624/8388509) }) = true
      norm_num [leaf700Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf700CertificateValid :
    WideCertificateValid leaf700Box leaf700Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi33ValidityFacts
    leaf700LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf700CoverageChecked :
    coverageCheck (innerAD leaf700Box) leaf700InnerLog = true := by
  rfl'

private theorem leaf700InnerLogValid :
    leaf700InnerLog.Valid 8 (innerAD leaf700Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf700CoverageChecked

private noncomputable def leaf700InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907299/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf700InputLogOnePlusV_eq :
    leaf700InputLogOnePlusV = outerEnclosure 24
      (leaf700Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf700RoundedFacts : LeafRoundedFacts 8
    leaf700Certificate.logOnePlusV leaf700InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf700InputLogOnePlusV_eq }

private noncomputable def leaf700Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi33InputQChi innerPair3Input
    leaf700InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf700LowerChecked :
    lowerCheck 24 leaf700Box leaf700Inputs = true := by
  rfl'

private theorem leaf700CoversExact : CoversExact 8
    leaf700Box leaf700Certificate leaf700InnerLog leaf700Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi33RoundedFacts
    innerPair3RoundedFacts leaf700RoundedFacts (by rfl)

private theorem leaf700FlatSound : Sound leaf700Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf700CertificateValid
    leaf700InnerLogValid leaf700CoversExact leaf700LowerChecked

private noncomputable def leaf701Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (5/64), chiHi := (3/32) }

private noncomputable def leaf701Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108943/67108864) }, vSqrt := { lower := (65531/65536), upper := (4194312/4194253) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (77888799/67108864) }, upper := { exponent := 0, mantissa := (307/256) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi33LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388565/8388506) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf701InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf701LocalValidity :
    LeafFacts leaf701Box leaf701Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf701Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194312/4194253) }) = true
      norm_num [leaf701Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf701CertificateValid :
    WideCertificateValid leaf701Box leaf701Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi33ValidityFacts
    leaf701LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf701CoverageChecked :
    coverageCheck (innerAD leaf701Box) leaf701InnerLog = true := by
  rfl'

private theorem leaf701InnerLogValid :
    leaf701InnerLog.Valid 8 (innerAD leaf701Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf701CoverageChecked

private noncomputable def leaf701InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629199/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf701InputLogOnePlusV_eq :
    leaf701InputLogOnePlusV = outerEnclosure 24
      (leaf701Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf701RoundedFacts : LeafRoundedFacts 8
    leaf701Certificate.logOnePlusV leaf701InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf701InputLogOnePlusV_eq }

private noncomputable def leaf701Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi33InputQChi innerPair3Input
    leaf701InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf701LowerChecked :
    lowerCheck 24 leaf701Box leaf701Inputs = true := by
  rfl'

private theorem leaf701CoversExact : CoversExact 8
    leaf701Box leaf701Certificate leaf701InnerLog leaf701Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi33RoundedFacts
    innerPair3RoundedFacts leaf701RoundedFacts (by rfl)

private theorem leaf701FlatSound : Sound leaf701Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf701CertificateValid
    leaf701InnerLogValid leaf701CoversExact leaf701LowerChecked

private noncomputable def leaf702Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (1/16), chiHi := (5/64) }

private noncomputable def leaf702Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108943/67108864) }, vSqrt := { lower := (65531/65536), upper := (5592416/5592347) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (75988371/67108864) }, upper := { exponent := 0, mantissa := (1199/1024) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi32LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11184763/11184694) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf702InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf702LocalValidity :
    LeafFacts leaf702Box leaf702Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf702Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5592416/5592347) }) = true
      norm_num [leaf702Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf702CertificateValid :
    WideCertificateValid leaf702Box leaf702Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi32ValidityFacts
    leaf702LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf702CoverageChecked :
    coverageCheck (innerAD leaf702Box) leaf702InnerLog = true := by
  rfl'

private theorem leaf702InnerLogValid :
    leaf702InnerLog.Valid 8 (innerAD leaf702Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf702CoverageChecked

private noncomputable def leaf702InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (90853/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf702InputLogOnePlusV_eq :
    leaf702InputLogOnePlusV = outerEnclosure 24
      (leaf702Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf702RoundedFacts : LeafRoundedFacts 8
    leaf702Certificate.logOnePlusV leaf702InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf702InputLogOnePlusV_eq }

private noncomputable def leaf702Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi32InputQChi innerPair2Input
    leaf702InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf702LowerChecked :
    lowerCheck 24 leaf702Box leaf702Inputs = true := by
  rfl'

private theorem leaf702CoversExact : CoversExact 8
    leaf702Box leaf702Certificate leaf702InnerLog leaf702Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi32RoundedFacts
    innerPair2RoundedFacts leaf702RoundedFacts (by rfl)

private theorem leaf702FlatSound : Sound leaf702Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf702CertificateValid
    leaf702InnerLogValid leaf702CoversExact leaf702LowerChecked

private noncomputable def leaf703Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (1/16), chiHi := (5/64) }

private noncomputable def leaf703Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108945/67108864) }, vSqrt := { lower := (65531/65536), upper := (4194312/4194259) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (76250497/67108864) }, upper := { exponent := 0, mantissa := (301/256) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi32LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388571/8388518) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf703InnerLog : WideLogData :=
  innerPair2Data

set_option maxRecDepth 1000000 in
private theorem leaf703LocalValidity :
    LeafFacts leaf703Box leaf703Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf703Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194312/4194259) }) = true
      norm_num [leaf703Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf703CertificateValid :
    WideCertificateValid leaf703Box leaf703Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi32ValidityFacts
    leaf703LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf703CoverageChecked :
    coverageCheck (innerAD leaf703Box) leaf703InnerLog = true := by
  rfl'

private theorem leaf703InnerLogValid :
    leaf703InnerLog.Valid 8 (innerAD leaf703Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint4PositiveFacts.valid leaf703CoverageChecked

private noncomputable def leaf703InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629187/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf703InputLogOnePlusV_eq :
    leaf703InputLogOnePlusV = outerEnclosure 24
      (leaf703Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf703RoundedFacts : LeafRoundedFacts 8
    leaf703Certificate.logOnePlusV leaf703InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf703InputLogOnePlusV_eq }

private noncomputable def leaf703Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi32InputQChi innerPair2Input
    leaf703InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf703LowerChecked :
    lowerCheck 24 leaf703Box leaf703Inputs = true := by
  rfl'

private theorem leaf703CoversExact : CoversExact 8
    leaf703Box leaf703Certificate leaf703InnerLog leaf703Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi32RoundedFacts
    innerPair2RoundedFacts leaf703RoundedFacts (by rfl)

private theorem leaf703FlatSound : Sound leaf703Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf703CertificateValid
    leaf703InnerLogValid leaf703CoversExact leaf703LowerChecked

private noncomputable def leaf704Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (5/64), chiHi := (3/32) }

private noncomputable def leaf704Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108945/67108864) }, vSqrt := { lower := (65531/65536), upper := (8388624/8388503) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (78216457/67108864) }, upper := { exponent := 0, mantissa := (617/512) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi33LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777127/16777006) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf704InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf704LocalValidity :
    LeafFacts leaf704Box leaf704Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf704Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388624/8388503) }) = true
      norm_num [leaf704Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf704CertificateValid :
    WideCertificateValid leaf704Box leaf704Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi33ValidityFacts
    leaf704LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf704CoverageChecked :
    coverageCheck (innerAD leaf704Box) leaf704InnerLog = true := by
  rfl'

private theorem leaf704InnerLogValid :
    leaf704InnerLog.Valid 8 (innerAD leaf704Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf704CoverageChecked

private noncomputable def leaf704InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814601/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf704InputLogOnePlusV_eq :
    leaf704InputLogOnePlusV = outerEnclosure 24
      (leaf704Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf704RoundedFacts : LeafRoundedFacts 8
    leaf704Certificate.logOnePlusV leaf704InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf704InputLogOnePlusV_eq }

private noncomputable def leaf704Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi33InputQChi innerPair3Input
    leaf704InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf704LowerChecked :
    lowerCheck 24 leaf704Box leaf704Inputs = true := by
  rfl'

private theorem leaf704CoversExact : CoversExact 8
    leaf704Box leaf704Certificate leaf704InnerLog leaf704Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi33RoundedFacts
    innerPair3RoundedFacts leaf704RoundedFacts (by rfl)

private theorem leaf704FlatSound : Sound leaf704Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf704CertificateValid
    leaf704InnerLogValid leaf704CoversExact leaf704LowerChecked

private noncomputable def leaf705Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (5/64), chiHi := (3/32) }

private noncomputable def leaf705Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108947/67108864) }, vSqrt := { lower := (65531/65536), upper := (2097156/2097125) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (78544115/67108864) }, upper := { exponent := 0, mantissa := (155/128) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi33LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4194281/4194250) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf705InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf705LocalValidity :
    LeafFacts leaf705Box leaf705Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf705Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2097156/2097125) }) = true
      norm_num [leaf705Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf705CertificateValid :
    WideCertificateValid leaf705Box leaf705Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi33ValidityFacts
    leaf705LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf705CoverageChecked :
    coverageCheck (innerAD leaf705Box) leaf705InnerLog = true := by
  rfl'

private theorem leaf705InnerLogValid :
    leaf705InnerLog.Valid 8 (innerAD leaf705Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf705CoverageChecked

private noncomputable def leaf705InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629205/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf705InputLogOnePlusV_eq :
    leaf705InputLogOnePlusV = outerEnclosure 24
      (leaf705Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf705RoundedFacts : LeafRoundedFacts 8
    leaf705Certificate.logOnePlusV leaf705InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf705InputLogOnePlusV_eq }

private noncomputable def leaf705Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi33InputQChi innerPair3Input
    leaf705InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf705LowerChecked :
    lowerCheck 24 leaf705Box leaf705Inputs = true := by
  rfl'

private theorem leaf705CoversExact : CoversExact 8
    leaf705Box leaf705Certificate leaf705InnerLog leaf705Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi33RoundedFacts
    innerPair3RoundedFacts leaf705RoundedFacts (by rfl)

private theorem leaf705FlatSound : Sound leaf705Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf705CertificateValid
    leaf705InnerLogValid leaf705CoversExact leaf705LowerChecked

private noncomputable def leaf706Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (3/32), chiHi := (7/64) }

private noncomputable def leaf706Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108943/67108864) }, vSqrt := { lower := (65531/65536), upper := (16777248/16776985) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (79658163/67108864) }, upper := { exponent := 0, mantissa := (1255/1024) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi36LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554233/33553970) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf706InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf706LocalValidity :
    LeafFacts leaf706Box leaf706Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf706Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777248/16776985) }) = true
      norm_num [leaf706Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf706CertificateValid :
    WideCertificateValid leaf706Box leaf706Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi36ValidityFacts
    leaf706LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf706CoverageChecked :
    coverageCheck (innerAD leaf706Box) leaf706InnerLog = true := by
  rfl'

private theorem leaf706InnerLogValid :
    leaf706InnerLog.Valid 8 (innerAD leaf706Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf706CoverageChecked

private noncomputable def leaf706InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907303/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf706InputLogOnePlusV_eq :
    leaf706InputLogOnePlusV = outerEnclosure 24
      (leaf706Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf706RoundedFacts : LeafRoundedFacts 8
    leaf706Certificate.logOnePlusV leaf706InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf706InputLogOnePlusV_eq }

private noncomputable def leaf706Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi36InputQChi innerPair3Input
    leaf706InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf706LowerChecked :
    lowerCheck 24 leaf706Box leaf706Inputs = true := by
  rfl'

private theorem leaf706CoversExact : CoversExact 8
    leaf706Box leaf706Certificate leaf706InnerLog leaf706Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi36RoundedFacts
    innerPair3RoundedFacts leaf706RoundedFacts (by rfl)

private theorem leaf706FlatSound : Sound leaf706Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf706CertificateValid
    leaf706InnerLogValid leaf706CoversExact leaf706LowerChecked

private noncomputable def leaf707Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (3/32), chiHi := (7/64) }

private noncomputable def leaf707Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108945/67108864) }, vSqrt := { lower := (65531/65536), upper := (2796208/2796163) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (80051353/67108864) }, upper := { exponent := 0, mantissa := (631/512) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi36LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (5592371/5592326) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf707InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf707LocalValidity :
    LeafFacts leaf707Box leaf707Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf707Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2796208/2796163) }) = true
      norm_num [leaf707Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf707CertificateValid :
    WideCertificateValid leaf707Box leaf707Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi36ValidityFacts
    leaf707LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf707CoverageChecked :
    coverageCheck (innerAD leaf707Box) leaf707InnerLog = true := by
  rfl'

private theorem leaf707InnerLogValid :
    leaf707InnerLog.Valid 8 (innerAD leaf707Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf707CoverageChecked

private noncomputable def leaf707InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (363413/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf707InputLogOnePlusV_eq :
    leaf707InputLogOnePlusV = outerEnclosure 24
      (leaf707Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf707RoundedFacts : LeafRoundedFacts 8
    leaf707Certificate.logOnePlusV leaf707InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf707InputLogOnePlusV_eq }

private noncomputable def leaf707Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi36InputQChi innerPair12Input
    leaf707InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf707LowerChecked :
    lowerCheck 24 leaf707Box leaf707Inputs = true := by
  rfl'

private theorem leaf707CoversExact : CoversExact 8
    leaf707Box leaf707Certificate leaf707InnerLog leaf707Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi36RoundedFacts
    innerPair12RoundedFacts leaf707RoundedFacts (by rfl)

private theorem leaf707FlatSound : Sound leaf707Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf707CertificateValid
    leaf707InnerLogValid leaf707CoversExact leaf707LowerChecked

private noncomputable def leaf708Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (7/64), chiHi := (1/8) }

private noncomputable def leaf708Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108945/67108864) }, vSqrt := { lower := (65531/65536), upper := (2097156/2097119) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (81755185/67108864) }, upper := { exponent := 0, mantissa := (161/128) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi37LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4194275/4194238) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf708InnerLog : WideLogData :=
  innerPair126Data

set_option maxRecDepth 1000000 in
private theorem leaf708LocalValidity :
    LeafFacts leaf708Box leaf708Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf708Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2097156/2097119) }) = true
      norm_num [leaf708Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf708CertificateValid :
    WideCertificateValid leaf708Box leaf708Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi37ValidityFacts
    leaf708LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf708CoverageChecked :
    coverageCheck (innerAD leaf708Box) leaf708InnerLog = true := by
  rfl'

private theorem leaf708InnerLogValid :
    leaf708InnerLog.Valid 8 (innerAD leaf708Box) :=
  wideLogDataValid_of_cachedCheck endpoint26PositiveFacts
    endpoint100PositiveFacts.valid leaf708CoverageChecked

private noncomputable def leaf708InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf708InputLogOnePlusV_eq :
    leaf708InputLogOnePlusV = outerEnclosure 24
      (leaf708Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf708RoundedFacts : LeafRoundedFacts 8
    leaf708Certificate.logOnePlusV leaf708InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf708InputLogOnePlusV_eq }

private noncomputable def leaf708Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi37InputQChi innerPair126Input
    leaf708InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf708LowerChecked :
    lowerCheck 24 leaf708Box leaf708Inputs = true := by
  rfl'

private theorem leaf708CoversExact : CoversExact 8
    leaf708Box leaf708Certificate leaf708InnerLog leaf708Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi37RoundedFacts
    innerPair126RoundedFacts leaf708RoundedFacts (by rfl)

private theorem leaf708FlatSound : Sound leaf708Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf708CertificateValid
    leaf708InnerLogValid leaf708CoversExact leaf708LowerChecked

private noncomputable def leaf709Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (7/64), chiHi := (1/8) }

private noncomputable def leaf709Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108947/67108864) }, vSqrt := { lower := (65531/65536), upper := (1048578/1048559) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (82213907/67108864) }, upper := { exponent := 0, mantissa := (81/64) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi37LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (2097137/2097118) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf709InnerLog : WideLogData :=
  innerPair128Data

set_option maxRecDepth 1000000 in
private theorem leaf709LocalValidity :
    LeafFacts leaf709Box leaf709Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf709Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (1048578/1048559) }) = true
      norm_num [leaf709Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf709CertificateValid :
    WideCertificateValid leaf709Box leaf709Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi37ValidityFacts
    leaf709LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf709CoverageChecked :
    coverageCheck (innerAD leaf709Box) leaf709InnerLog = true := by
  rfl'

private theorem leaf709InnerLogValid :
    leaf709InnerLog.Valid 8 (innerAD leaf709Box) :=
  wideLogDataValid_of_cachedCheck endpoint27PositiveFacts
    endpoint100PositiveFacts.valid leaf709CoverageChecked

private noncomputable def leaf709InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf709InputLogOnePlusV_eq :
    leaf709InputLogOnePlusV = outerEnclosure 24
      (leaf709Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf709RoundedFacts : LeafRoundedFacts 8
    leaf709Certificate.logOnePlusV leaf709InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf709InputLogOnePlusV_eq }

private noncomputable def leaf709Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi37InputQChi innerPair128Input
    leaf709InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf709LowerChecked :
    lowerCheck 24 leaf709Box leaf709Inputs = true := by
  rfl'

private theorem leaf709CoversExact : CoversExact 8
    leaf709Box leaf709Certificate leaf709InnerLog leaf709Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi37RoundedFacts
    innerPair128RoundedFacts leaf709RoundedFacts (by rfl)

private theorem leaf709FlatSound : Sound leaf709Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf709CertificateValid
    leaf709InnerLogValid leaf709CoversExact leaf709LowerChecked

private noncomputable def leaf710Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (3/32), chiHi := (7/64) }

private noncomputable def leaf710Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108947/67108864) }, vSqrt := { lower := (65531/65536), upper := (16777248/16776971) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (80444543/67108864) }, upper := { exponent := 0, mantissa := (1269/1024) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi36LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554219/33553942) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf710InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf710LocalValidity :
    LeafFacts leaf710Box leaf710Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf710Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777248/16776971) }) = true
      norm_num [leaf710Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf710CertificateValid :
    WideCertificateValid leaf710Box leaf710Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi36ValidityFacts
    leaf710LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf710CoverageChecked :
    coverageCheck (innerAD leaf710Box) leaf710InnerLog = true := by
  rfl'

private theorem leaf710InnerLogValid :
    leaf710InnerLog.Valid 8 (innerAD leaf710Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf710CoverageChecked

private noncomputable def leaf710InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629219/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf710InputLogOnePlusV_eq :
    leaf710InputLogOnePlusV = outerEnclosure 24
      (leaf710Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf710RoundedFacts : LeafRoundedFacts 8
    leaf710Certificate.logOnePlusV leaf710InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf710InputLogOnePlusV_eq }

private noncomputable def leaf710Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi36InputQChi innerPair12Input
    leaf710InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf710LowerChecked :
    lowerCheck 24 leaf710Box leaf710Inputs = true := by
  rfl'

private theorem leaf710CoversExact : CoversExact 8
    leaf710Box leaf710Certificate leaf710InnerLog leaf710Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi36RoundedFacts
    innerPair12RoundedFacts leaf710RoundedFacts (by rfl)

private theorem leaf710FlatSound : Sound leaf710Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf710CertificateValid
    leaf710InnerLogValid leaf710CoversExact leaf710LowerChecked

private noncomputable def leaf711Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (3/32), chiHi := (7/64) }

private noncomputable def leaf711Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108949/67108864) }, vSqrt := { lower := (65531/65536), upper := (4194312/4194241) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (80837733/67108864) }, upper := { exponent := 0, mantissa := (319/256) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi36LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388553/8388482) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf711InnerLog : WideLogData :=
  innerPair125Data

set_option maxRecDepth 1000000 in
private theorem leaf711LocalValidity :
    LeafFacts leaf711Box leaf711Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf711Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194312/4194241) }) = true
      norm_num [leaf711Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf711CertificateValid :
    WideCertificateValid leaf711Box leaf711Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi36ValidityFacts
    leaf711LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf711CoverageChecked :
    coverageCheck (innerAD leaf711Box) leaf711InnerLog = true := by
  rfl'

private theorem leaf711InnerLogValid :
    leaf711InnerLog.Valid 8 (innerAD leaf711Box) :=
  wideLogDataValid_of_cachedCheck endpoint26PositiveFacts
    endpoint33PositiveFacts.valid leaf711CoverageChecked

private noncomputable def leaf711InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf711InputLogOnePlusV_eq :
    leaf711InputLogOnePlusV = outerEnclosure 24
      (leaf711Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf711RoundedFacts : LeafRoundedFacts 8
    leaf711Certificate.logOnePlusV leaf711InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf711InputLogOnePlusV_eq }

private noncomputable def leaf711Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi36InputQChi innerPair125Input
    leaf711InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf711LowerChecked :
    lowerCheck 24 leaf711Box leaf711Inputs = true := by
  rfl'

private theorem leaf711CoversExact : CoversExact 8
    leaf711Box leaf711Certificate leaf711InnerLog leaf711Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi36RoundedFacts
    innerPair125RoundedFacts leaf711RoundedFacts (by rfl)

private theorem leaf711FlatSound : Sound leaf711Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf711CertificateValid
    leaf711InnerLogValid leaf711CoversExact leaf711LowerChecked

private noncomputable def leaf712Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf712Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217827/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554496/33553907) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (165378095/134217728) }, upper := { exponent := 0, mantissa := (2573/2048) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108403/67107814) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf712InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf712LocalValidity :
    LeafFacts leaf712Box leaf712Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf712Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554496/33553907) }) = true
      norm_num [leaf712Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf712CertificateValid :
    WideCertificateValid leaf712Box leaf712Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi98ValidityFacts
    leaf712LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf712CoverageChecked :
    coverageCheck (innerAD leaf712Box) leaf712InnerLog = true := by
  rfl'

private theorem leaf712InnerLogValid :
    leaf712InnerLog.Valid 8 (innerAD leaf712Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf712CoverageChecked

private noncomputable def leaf712InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907307/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf712InputLogOnePlusV_eq :
    leaf712InputLogOnePlusV = outerEnclosure 24
      (leaf712Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf712RoundedFacts : LeafRoundedFacts 8
    leaf712Certificate.logOnePlusV leaf712InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf712InputLogOnePlusV_eq }

private noncomputable def leaf712Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi98InputQChi innerPair13Input
    leaf712InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf712LowerChecked :
    lowerCheck 24 leaf712Box leaf712Inputs = true := by
  rfl'

private theorem leaf712CoversExact : CoversExact 8
    leaf712Box leaf712Certificate leaf712InnerLog leaf712Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi98RoundedFacts
    innerPair13RoundedFacts leaf712RoundedFacts (by rfl)

private theorem leaf712FlatSound : Sound leaf712Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf712CertificateValid
    leaf712InnerLogValid leaf712CoversExact leaf712LowerChecked

private noncomputable def leaf713Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf713Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217829/134217728) }, vSqrt := { lower := (65531/65536), upper := (699052/699039) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (167606181/134217728) }, upper := { exponent := 0, mantissa := (163/128) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (1398091/1398078) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf713InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf713LocalValidity :
    LeafFacts leaf713Box leaf713Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf713Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (699052/699039) }) = true
      norm_num [leaf713Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf713CertificateValid :
    WideCertificateValid leaf713Box leaf713Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi99ValidityFacts
    leaf713LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf713CoverageChecked :
    coverageCheck (innerAD leaf713Box) leaf713InnerLog = true := by
  rfl'

private theorem leaf713InnerLogValid :
    leaf713InnerLog.Valid 8 (innerAD leaf713Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf713CoverageChecked

private noncomputable def leaf713InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf713InputLogOnePlusV_eq :
    leaf713InputLogOnePlusV = outerEnclosure 24
      (leaf713Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf713RoundedFacts : LeafRoundedFacts 8
    leaf713Certificate.logOnePlusV leaf713InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf713InputLogOnePlusV_eq }

private noncomputable def leaf713Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi99InputQChi innerPair13Input
    leaf713InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf713LowerChecked :
    lowerCheck 24 leaf713Box leaf713Inputs = true := by
  rfl'

private theorem leaf713CoversExact : CoversExact 8
    leaf713Box leaf713Certificate leaf713InnerLog leaf713Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi99RoundedFacts
    innerPair13RoundedFacts leaf713RoundedFacts (by rfl)

private theorem leaf713FlatSound : Sound leaf713Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf713CertificateValid
    leaf713InnerLogValid leaf713CoversExact leaf713LowerChecked

private noncomputable def leaf714Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf714Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217829/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388624/8388473) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (166295541/134217728) }, upper := { exponent := 0, mantissa := (647/512) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777097/16776946) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf714InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf714LocalValidity :
    LeafFacts leaf714Box leaf714Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf714Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388624/8388473) }) = true
      norm_num [leaf714Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf714CertificateValid :
    WideCertificateValid leaf714Box leaf714Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi98ValidityFacts
    leaf714LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf714CoverageChecked :
    coverageCheck (innerAD leaf714Box) leaf714InnerLog = true := by
  rfl'

private theorem leaf714InnerLogValid :
    leaf714InnerLog.Valid 8 (innerAD leaf714Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf714CoverageChecked

private noncomputable def leaf714InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf714InputLogOnePlusV_eq :
    leaf714InputLogOnePlusV = outerEnclosure 24
      (leaf714Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf714RoundedFacts : LeafRoundedFacts 8
    leaf714Certificate.logOnePlusV leaf714InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf714InputLogOnePlusV_eq }

private noncomputable def leaf714Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi98InputQChi innerPair13Input
    leaf714InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf714LowerChecked :
    lowerCheck 24 leaf714Box leaf714Inputs = true := by
  rfl'

private theorem leaf714CoversExact : CoversExact 8
    leaf714Box leaf714Certificate leaf714InnerLog leaf714Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi98RoundedFacts
    innerPair13RoundedFacts leaf714RoundedFacts (by rfl)

private theorem leaf714FlatSound : Sound leaf714Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf714CertificateValid
    leaf714InnerLogValid leaf714CoversExact leaf714LowerChecked

private noncomputable def leaf715Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf715Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217831/134217728) }, vSqrt := { lower := (65531/65536), upper := (524289/524279) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (168589159/134217728) }, upper := { exponent := 0, mantissa := (41/32) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (524284/524279) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf715InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf715LocalValidity :
    LeafFacts leaf715Box leaf715Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf715Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (524289/524279) }) = true
      norm_num [leaf715Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf715CertificateValid :
    WideCertificateValid leaf715Box leaf715Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi99ValidityFacts
    leaf715LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf715CoverageChecked :
    coverageCheck (innerAD leaf715Box) leaf715InnerLog = true := by
  rfl'

private theorem leaf715InnerLogValid :
    leaf715InnerLog.Valid 8 (innerAD leaf715Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf715CoverageChecked

private noncomputable def leaf715InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf715InputLogOnePlusV_eq :
    leaf715InputLogOnePlusV = outerEnclosure 24
      (leaf715Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf715RoundedFacts : LeafRoundedFacts 8
    leaf715Certificate.logOnePlusV leaf715InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf715InputLogOnePlusV_eq }

private noncomputable def leaf715Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi99InputQChi innerPair16Input
    leaf715InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf715LowerChecked :
    lowerCheck 24 leaf715Box leaf715Inputs = true := by
  rfl'

private theorem leaf715CoversExact : CoversExact 8
    leaf715Box leaf715Certificate leaf715InnerLog leaf715Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi99RoundedFacts
    innerPair16RoundedFacts leaf715RoundedFacts (by rfl)

private theorem leaf715FlatSound : Sound leaf715Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf715CertificateValid
    leaf715InnerLogValid leaf715CoversExact leaf715LowerChecked

private noncomputable def component17Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (0), chiHi := (1/32) }

set_option maxRecDepth 1000000 in
private theorem component17Node0_sound : Sound component17Node0Box :=
  sound_of_literal_split component17Node0Box leaf686Box leaf687Box
    .k (17/8) (by rfl) (by rfl)
    leaf686FlatSound leaf687FlatSound

private noncomputable def component17Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component17Node1_sound : Sound component17Node1Box :=
  sound_of_literal_split component17Node1Box leaf688Box leaf689Box
    .chi (5/128) (by rfl) (by rfl)
    leaf688FlatSound leaf689FlatSound

private noncomputable def component17Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component17Node2_sound : Sound component17Node2Box :=
  sound_of_literal_split component17Node2Box leaf690Box leaf691Box
    .k (33/16) (by rfl) (by rfl)
    leaf690FlatSound leaf691FlatSound

private noncomputable def component17Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component17Node3_sound : Sound component17Node3Box :=
  sound_of_literal_split component17Node3Box component17Node1Box component17Node2Box
    .chi (3/64) (by rfl) (by rfl)
    component17Node1_sound component17Node2_sound

private noncomputable def component17Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (1/32), chiHi := (3/64) }

set_option maxRecDepth 1000000 in
private theorem component17Node4_sound : Sound component17Node4Box :=
  sound_of_literal_split component17Node4Box leaf692Box leaf693Box
    .chi (5/128) (by rfl) (by rfl)
    leaf692FlatSound leaf693FlatSound

private noncomputable def component17Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (3/64), chiHi := (7/128) }

set_option maxRecDepth 1000000 in
private theorem component17Node5_sound : Sound component17Node5Box :=
  sound_of_literal_split component17Node5Box leaf694Box leaf695Box
    .k (35/16) (by rfl) (by rfl)
    leaf694FlatSound leaf695FlatSound

private noncomputable def component17Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (7/128), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component17Node6_sound : Sound component17Node6Box :=
  sound_of_literal_split component17Node6Box leaf696Box leaf697Box
    .k (35/16) (by rfl) (by rfl)
    leaf696FlatSound leaf697FlatSound

private noncomputable def component17Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (3/64), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component17Node7_sound : Sound component17Node7Box :=
  sound_of_literal_split component17Node7Box component17Node5Box component17Node6Box
    .chi (7/128) (by rfl) (by rfl)
    component17Node5_sound component17Node6_sound

private noncomputable def component17Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component17Node8_sound : Sound component17Node8Box :=
  sound_of_literal_split component17Node8Box component17Node4Box component17Node7Box
    .chi (3/64) (by rfl) (by rfl)
    component17Node4_sound component17Node7_sound

private noncomputable def component17Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (1/32), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component17Node9_sound : Sound component17Node9Box :=
  sound_of_literal_split component17Node9Box component17Node3Box component17Node8Box
    .k (17/8) (by rfl) (by rfl)
    component17Node3_sound component17Node8_sound

private noncomputable def component17Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (0), chiHi := (1/16) }

set_option maxRecDepth 1000000 in
private theorem component17Node10_sound : Sound component17Node10Box :=
  sound_of_literal_split component17Node10Box component17Node0Box component17Node9Box
    .chi (1/32) (by rfl) (by rfl)
    component17Node0_sound component17Node9_sound

private noncomputable def component17Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component17Node11_sound : Sound component17Node11Box :=
  sound_of_literal_split component17Node11Box leaf698Box leaf699Box
    .k (33/16) (by rfl) (by rfl)
    leaf698FlatSound leaf699FlatSound

private noncomputable def component17Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component17Node12_sound : Sound component17Node12Box :=
  sound_of_literal_split component17Node12Box leaf700Box leaf701Box
    .k (33/16) (by rfl) (by rfl)
    leaf700FlatSound leaf701FlatSound

private noncomputable def component17Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component17Node13_sound : Sound component17Node13Box :=
  sound_of_literal_split component17Node13Box component17Node11Box component17Node12Box
    .chi (5/64) (by rfl) (by rfl)
    component17Node11_sound component17Node12_sound

private noncomputable def component17Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component17Node14_sound : Sound component17Node14Box :=
  sound_of_literal_split component17Node14Box leaf702Box leaf703Box
    .k (35/16) (by rfl) (by rfl)
    leaf702FlatSound leaf703FlatSound

private noncomputable def component17Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component17Node15_sound : Sound component17Node15Box :=
  sound_of_literal_split component17Node15Box leaf704Box leaf705Box
    .k (35/16) (by rfl) (by rfl)
    leaf704FlatSound leaf705FlatSound

private noncomputable def component17Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component17Node16_sound : Sound component17Node16Box :=
  sound_of_literal_split component17Node16Box component17Node14Box component17Node15Box
    .chi (5/64) (by rfl) (by rfl)
    component17Node14_sound component17Node15_sound

private noncomputable def component17Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component17Node17_sound : Sound component17Node17Box :=
  sound_of_literal_split component17Node17Box component17Node13Box component17Node16Box
    .k (17/8) (by rfl) (by rfl)
    component17Node13_sound component17Node16_sound

private noncomputable def component17Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component17Node18_sound : Sound component17Node18Box :=
  sound_of_literal_split component17Node18Box leaf706Box leaf707Box
    .k (33/16) (by rfl) (by rfl)
    leaf706FlatSound leaf707FlatSound

private noncomputable def component17Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component17Node19_sound : Sound component17Node19Box :=
  sound_of_literal_split component17Node19Box leaf708Box leaf709Box
    .k (33/16) (by rfl) (by rfl)
    leaf708FlatSound leaf709FlatSound

private noncomputable def component17Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component17Node20_sound : Sound component17Node20Box :=
  sound_of_literal_split component17Node20Box component17Node18Box component17Node19Box
    .chi (7/64) (by rfl) (by rfl)
    component17Node18_sound component17Node19_sound

private noncomputable def component17Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component17Node21_sound : Sound component17Node21Box :=
  sound_of_literal_split component17Node21Box leaf710Box leaf711Box
    .k (35/16) (by rfl) (by rfl)
    leaf710FlatSound leaf711FlatSound

private noncomputable def component17Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component17Node22_sound : Sound component17Node22Box :=
  sound_of_literal_split component17Node22Box leaf712Box leaf713Box
    .chi (15/128) (by rfl) (by rfl)
    leaf712FlatSound leaf713FlatSound

private noncomputable def component17Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component17Node23_sound : Sound component17Node23Box :=
  sound_of_literal_split component17Node23Box leaf714Box leaf715Box
    .chi (15/128) (by rfl) (by rfl)
    leaf714FlatSound leaf715FlatSound

private noncomputable def component17Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component17Node24_sound : Sound component17Node24Box :=
  sound_of_literal_split component17Node24Box component17Node22Box component17Node23Box
    .k (35/16) (by rfl) (by rfl)
    component17Node22_sound component17Node23_sound

private noncomputable def component17Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component17Node25_sound : Sound component17Node25Box :=
  sound_of_literal_split component17Node25Box component17Node21Box component17Node24Box
    .chi (7/64) (by rfl) (by rfl)
    component17Node21_sound component17Node24_sound

private noncomputable def component17Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component17Node26_sound : Sound component17Node26Box :=
  sound_of_literal_split component17Node26Box component17Node20Box component17Node25Box
    .k (17/8) (by rfl) (by rfl)
    component17Node20_sound component17Node25_sound

private noncomputable def component17Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component17Node27_sound : Sound component17Node27Box :=
  sound_of_literal_split component17Node27Box component17Node17Box component17Node26Box
    .chi (3/32) (by rfl) (by rfl)
    component17Node17_sound component17Node26_sound

noncomputable def component17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (0), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
theorem component17_sound : Sound component17Box :=
  sound_of_literal_split component17Box component17Node10Box component17Node27Box
    .chi (1/16) (by rfl) (by rfl)
    component17Node10_sound component17Node27_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
