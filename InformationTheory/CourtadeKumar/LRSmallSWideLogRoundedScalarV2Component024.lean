import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
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

private noncomputable def leaf1000Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (1/16), chiHi := (9/128) }

private noncomputable def leaf1000Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217835/134217728) }, vSqrt := { lower := (32765/32768), upper := (33554496/33554027) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (157252119/134217728) }, upper := { exponent := 0, mantissa := (2453/2048) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi125LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108523/67108054) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf1000InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1000LocalValidity :
    LeafFacts leaf1000Box leaf1000Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1000Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554496/33554027) }) = true
      norm_num [leaf1000Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1000CertificateValid :
    WideCertificateValid leaf1000Box leaf1000Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi125ValidityFacts
    leaf1000LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1000CoverageChecked :
    coverageCheck (innerAD leaf1000Box) leaf1000InnerLog = true := by
  rfl'

private theorem leaf1000InnerLogValid :
    leaf1000InnerLog.Valid 8 (innerAD leaf1000Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1000CoverageChecked

private noncomputable def leaf1000InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814599/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1000InputLogOnePlusV_eq :
    leaf1000InputLogOnePlusV = outerEnclosure 24
      (leaf1000Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1000RoundedFacts : LeafRoundedFacts 8
    leaf1000Certificate.logOnePlusV leaf1000InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1000InputLogOnePlusV_eq }

private noncomputable def leaf1000Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi125InputQChi innerPair3Input
    leaf1000InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1000LowerChecked :
    lowerCheck 24 leaf1000Box leaf1000Inputs = true := by
  rfl'

private theorem leaf1000CoversExact : CoversExact 8
    leaf1000Box leaf1000Certificate leaf1000InnerLog leaf1000Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi125RoundedFacts
    innerPair3RoundedFacts leaf1000RoundedFacts (by rfl)

private theorem leaf1000FlatSound : Sound leaf1000Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1000CertificateValid
    leaf1000InnerLogValid leaf1000CoversExact leaf1000LowerChecked

private noncomputable def leaf1001Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (1/16), chiHi := (9/128) }

private noncomputable def leaf1001Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217837/134217728) }, vSqrt := { lower := (32765/32768), upper := (16777248/16777009) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (157776373/134217728) }, upper := { exponent := 0, mantissa := (1231/1024) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi125LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554257/33554018) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf1001InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1001LocalValidity :
    LeafFacts leaf1001Box leaf1001Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1001Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777248/16777009) }) = true
      norm_num [leaf1001Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1001CertificateValid :
    WideCertificateValid leaf1001Box leaf1001Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi125ValidityFacts
    leaf1001LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1001CoverageChecked :
    coverageCheck (innerAD leaf1001Box) leaf1001InnerLog = true := by
  rfl'

private theorem leaf1001InnerLogValid :
    leaf1001InnerLog.Valid 8 (innerAD leaf1001Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1001CoverageChecked

private noncomputable def leaf1001InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726825/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1001InputLogOnePlusV_eq :
    leaf1001InputLogOnePlusV = outerEnclosure 24
      (leaf1001Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1001RoundedFacts : LeafRoundedFacts 8
    leaf1001Certificate.logOnePlusV leaf1001InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1001InputLogOnePlusV_eq }

private noncomputable def leaf1001Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi125InputQChi innerPair3Input
    leaf1001InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1001LowerChecked :
    lowerCheck 24 leaf1001Box leaf1001Inputs = true := by
  rfl'

private theorem leaf1001CoversExact : CoversExact 8
    leaf1001Box leaf1001Certificate leaf1001InnerLog leaf1001Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi125RoundedFacts
    innerPair3RoundedFacts leaf1001RoundedFacts (by rfl)

private theorem leaf1001FlatSound : Sound leaf1001Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1001CertificateValid
    leaf1001InnerLogValid leaf1001CoversExact leaf1001LowerChecked

private noncomputable def leaf1002Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (9/128), chiHi := (5/64) }

private noncomputable def leaf1002Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217837/134217728) }, vSqrt := { lower := (32765/32768), upper := (16777248/16776991) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (160135525/134217728) }, upper := { exponent := 0, mantissa := (1249/1024) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi126LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554239/33553982) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf1002InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1002LocalValidity :
    LeafFacts leaf1002Box leaf1002Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1002Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777248/16776991) }) = true
      norm_num [leaf1002Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1002CertificateValid :
    WideCertificateValid leaf1002Box leaf1002Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi126ValidityFacts
    leaf1002LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1002CoverageChecked :
    coverageCheck (innerAD leaf1002Box) leaf1002InnerLog = true := by
  rfl'

private theorem leaf1002InnerLogValid :
    leaf1002InnerLog.Valid 8 (innerAD leaf1002Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1002CoverageChecked

private noncomputable def leaf1002InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1002InputLogOnePlusV_eq :
    leaf1002InputLogOnePlusV = outerEnclosure 24
      (leaf1002Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1002RoundedFacts : LeafRoundedFacts 8
    leaf1002Certificate.logOnePlusV leaf1002InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1002InputLogOnePlusV_eq }

private noncomputable def leaf1002Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi126InputQChi innerPair12Input
    leaf1002InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1002LowerChecked :
    lowerCheck 24 leaf1002Box leaf1002Inputs = true := by
  rfl'

private theorem leaf1002CoversExact : CoversExact 8
    leaf1002Box leaf1002Certificate leaf1002InnerLog leaf1002Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi126RoundedFacts
    innerPair12RoundedFacts leaf1002RoundedFacts (by rfl)

private theorem leaf1002FlatSound : Sound leaf1002Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1002CertificateValid
    leaf1002InnerLogValid leaf1002CoversExact leaf1002LowerChecked

private noncomputable def leaf1003Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (9/128), chiHi := (5/64) }

private noncomputable def leaf1003Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217839/134217728) }, vSqrt := { lower := (32765/32768), upper := (8388624/8388493) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (160725311/134217728) }, upper := { exponent := 0, mantissa := (627/512) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi126LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777117/16776986) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf1003InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1003LocalValidity :
    LeafFacts leaf1003Box leaf1003Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1003Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388624/8388493) }) = true
      norm_num [leaf1003Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1003CertificateValid :
    WideCertificateValid leaf1003Box leaf1003Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi126ValidityFacts
    leaf1003LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1003CoverageChecked :
    coverageCheck (innerAD leaf1003Box) leaf1003InnerLog = true := by
  rfl'

private theorem leaf1003InnerLogValid :
    leaf1003InnerLog.Valid 8 (innerAD leaf1003Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1003CoverageChecked

private noncomputable def leaf1003InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907303/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1003InputLogOnePlusV_eq :
    leaf1003InputLogOnePlusV = outerEnclosure 24
      (leaf1003Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1003RoundedFacts : LeafRoundedFacts 8
    leaf1003Certificate.logOnePlusV leaf1003InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1003InputLogOnePlusV_eq }

private noncomputable def leaf1003Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi126InputQChi innerPair12Input
    leaf1003InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1003LowerChecked :
    lowerCheck 24 leaf1003Box leaf1003Inputs = true := by
  rfl'

private theorem leaf1003CoversExact : CoversExact 8
    leaf1003Box leaf1003Certificate leaf1003InnerLog leaf1003Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi126RoundedFacts
    innerPair12RoundedFacts leaf1003RoundedFacts (by rfl)

private theorem leaf1003FlatSound : Sound leaf1003Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1003CertificateValid
    leaf1003InnerLogValid leaf1003CoversExact leaf1003LowerChecked

private noncomputable def leaf1004Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (5/64), chiHi := (11/128) }

private noncomputable def leaf1004Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217839/134217728) }, vSqrt := { lower := (32765/32768), upper := (33554496/33553937) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (163018931/134217728) }, upper := { exponent := 0, mantissa := (2543/2048) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi103LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108433/67107874) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf1004InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1004LocalValidity :
    LeafFacts leaf1004Box leaf1004Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1004Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554496/33553937) }) = true
      norm_num [leaf1004Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1004CertificateValid :
    WideCertificateValid leaf1004Box leaf1004Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi103ValidityFacts
    leaf1004LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1004CoverageChecked :
    coverageCheck (innerAD leaf1004Box) leaf1004InnerLog = true := by
  rfl'

private theorem leaf1004InnerLogValid :
    leaf1004InnerLog.Valid 8 (innerAD leaf1004Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1004CoverageChecked

private noncomputable def leaf1004InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907305/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1004InputLogOnePlusV_eq :
    leaf1004InputLogOnePlusV = outerEnclosure 24
      (leaf1004Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1004RoundedFacts : LeafRoundedFacts 8
    leaf1004Certificate.logOnePlusV leaf1004InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1004InputLogOnePlusV_eq }

private noncomputable def leaf1004Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi103InputQChi innerPair12Input
    leaf1004InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1004LowerChecked :
    lowerCheck 24 leaf1004Box leaf1004Inputs = true := by
  rfl'

private theorem leaf1004CoversExact : CoversExact 8
    leaf1004Box leaf1004Certificate leaf1004InnerLog leaf1004Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi103RoundedFacts
    innerPair12RoundedFacts leaf1004RoundedFacts (by rfl)

private theorem leaf1004FlatSound : Sound leaf1004Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1004CertificateValid
    leaf1004InnerLogValid leaf1004CoversExact leaf1004LowerChecked

private noncomputable def leaf1005Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (11/128), chiHi := (3/32) }

private noncomputable def leaf1005Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217841/134217728) }, vSqrt := { lower := (32765/32768), upper := (8388624/8388473) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (165902337/134217728) }, upper := { exponent := 0, mantissa := (647/512) } }, logOuter := sk95LogOuterCertificate, logK := sk95LogKCertificate, logChi := chi104LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777097/16776946) } }, logDArg := sk95LogDArgCertificate }

private noncomputable def leaf1005InnerLog : WideLogData :=
  innerPair402Data

set_option maxRecDepth 1000000 in
private theorem leaf1005LocalValidity :
    LeafFacts leaf1005Box leaf1005Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1005Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388624/8388473) }) = true
      norm_num [leaf1005Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1005CertificateValid :
    WideCertificateValid leaf1005Box leaf1005Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk95ValidityFacts chi104ValidityFacts
    leaf1005LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1005CoverageChecked :
    coverageCheck (innerAD leaf1005Box) leaf1005InnerLog = true := by
  rfl'

private theorem leaf1005InnerLogValid :
    leaf1005InnerLog.Valid 8 (innerAD leaf1005Box) :=
  wideLogDataValid_of_cachedCheck endpoint116PositiveFacts
    endpoint100PositiveFacts.valid leaf1005CoverageChecked

private noncomputable def leaf1005InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1005InputLogOnePlusV_eq :
    leaf1005InputLogOnePlusV = outerEnclosure 24
      (leaf1005Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1005RoundedFacts : LeafRoundedFacts 8
    leaf1005Certificate.logOnePlusV leaf1005InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1005InputLogOnePlusV_eq }

private noncomputable def leaf1005Inputs : Inputs :=
  inputsOfCaches globalInput sk95RoundedInputs
    chi104InputQChi innerPair402Input
    leaf1005InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1005LowerChecked :
    lowerCheck 24 leaf1005Box leaf1005Inputs = true := by
  rfl'

private theorem leaf1005CoversExact : CoversExact 8
    leaf1005Box leaf1005Certificate leaf1005InnerLog leaf1005Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk95RoundedFacts chi104RoundedFacts
    innerPair402RoundedFacts leaf1005RoundedFacts (by rfl)

private theorem leaf1005FlatSound : Sound leaf1005Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1005CertificateValid
    leaf1005InnerLogValid leaf1005CoversExact leaf1005LowerChecked

private noncomputable def leaf1006Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (5/64), chiHi := (11/128) }

private noncomputable def leaf1006Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217841/134217728) }, vSqrt := { lower := (32765/32768), upper := (5592416/5592321) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (163674249/134217728) }, upper := { exponent := 0, mantissa := (1277/1024) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi103LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (11184737/11184642) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf1006InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1006LocalValidity :
    LeafFacts leaf1006Box leaf1006Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1006Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (5592416/5592321) }) = true
      norm_num [leaf1006Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1006CertificateValid :
    WideCertificateValid leaf1006Box leaf1006Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi103ValidityFacts
    leaf1006LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1006CoverageChecked :
    coverageCheck (innerAD leaf1006Box) leaf1006InnerLog = true := by
  rfl'

private theorem leaf1006InnerLogValid :
    leaf1006InnerLog.Valid 8 (innerAD leaf1006Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1006CoverageChecked

private noncomputable def leaf1006InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1006InputLogOnePlusV_eq :
    leaf1006InputLogOnePlusV = outerEnclosure 24
      (leaf1006Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1006RoundedFacts : LeafRoundedFacts 8
    leaf1006Certificate.logOnePlusV leaf1006InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1006InputLogOnePlusV_eq }

private noncomputable def leaf1006Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi103InputQChi innerPair12Input
    leaf1006InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1006LowerChecked :
    lowerCheck 24 leaf1006Box leaf1006Inputs = true := by
  rfl'

private theorem leaf1006CoversExact : CoversExact 8
    leaf1006Box leaf1006Certificate leaf1006InnerLog leaf1006Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi103RoundedFacts
    innerPair12RoundedFacts leaf1006RoundedFacts (by rfl)

private theorem leaf1006FlatSound : Sound leaf1006Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1006CertificateValid
    leaf1006InnerLogValid leaf1006CoversExact leaf1006LowerChecked

private noncomputable def leaf1007Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (11/128), chiHi := (3/32) }

private noncomputable def leaf1007Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217843/134217728) }, vSqrt := { lower := (32765/32768), upper := (4194312/4194235) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (166623187/134217728) }, upper := { exponent := 0, mantissa := (325/256) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi104LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388547/8388470) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf1007InnerLog : WideLogData :=
  innerPair404Data

set_option maxRecDepth 1000000 in
private theorem leaf1007LocalValidity :
    LeafFacts leaf1007Box leaf1007Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1007Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194312/4194235) }) = true
      norm_num [leaf1007Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1007CertificateValid :
    WideCertificateValid leaf1007Box leaf1007Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi104ValidityFacts
    leaf1007LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1007CoverageChecked :
    coverageCheck (innerAD leaf1007Box) leaf1007InnerLog = true := by
  rfl'

private theorem leaf1007InnerLogValid :
    leaf1007InnerLog.Valid 8 (innerAD leaf1007Box) :=
  wideLogDataValid_of_cachedCheck endpoint117PositiveFacts
    endpoint118PositiveFacts.valid leaf1007CoverageChecked

private noncomputable def leaf1007InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1007InputLogOnePlusV_eq :
    leaf1007InputLogOnePlusV = outerEnclosure 24
      (leaf1007Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1007RoundedFacts : LeafRoundedFacts 8
    leaf1007Certificate.logOnePlusV leaf1007InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1007InputLogOnePlusV_eq }

private noncomputable def leaf1007Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi104InputQChi innerPair404Input
    leaf1007InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1007LowerChecked :
    lowerCheck 24 leaf1007Box leaf1007Inputs = true := by
  rfl'

private theorem leaf1007CoversExact : CoversExact 8
    leaf1007Box leaf1007Certificate leaf1007InnerLog leaf1007Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi104RoundedFacts
    innerPair404RoundedFacts leaf1007RoundedFacts (by rfl)

private theorem leaf1007FlatSound : Sound leaf1007Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1007CertificateValid
    leaf1007InnerLogValid leaf1007CoversExact leaf1007LowerChecked

private noncomputable def leaf1008Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (1/16), chiHi := (9/128) }

private noncomputable def leaf1008Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217839/134217728) }, vSqrt := { lower := (32765/32768), upper := (33554496/33554009) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (158300627/134217728) }, upper := { exponent := 0, mantissa := (2471/2048) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi125LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108505/67108018) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf1008InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1008LocalValidity :
    LeafFacts leaf1008Box leaf1008Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1008Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554496/33554009) }) = true
      norm_num [leaf1008Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1008CertificateValid :
    WideCertificateValid leaf1008Box leaf1008Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi125ValidityFacts
    leaf1008LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1008CoverageChecked :
    coverageCheck (innerAD leaf1008Box) leaf1008InnerLog = true := by
  rfl'

private theorem leaf1008InnerLogValid :
    leaf1008InnerLog.Valid 8 (innerAD leaf1008Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1008CoverageChecked

private noncomputable def leaf1008InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814601/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1008InputLogOnePlusV_eq :
    leaf1008InputLogOnePlusV = outerEnclosure 24
      (leaf1008Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1008RoundedFacts : LeafRoundedFacts 8
    leaf1008Certificate.logOnePlusV leaf1008InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1008InputLogOnePlusV_eq }

private noncomputable def leaf1008Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi125InputQChi innerPair3Input
    leaf1008InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1008LowerChecked :
    lowerCheck 24 leaf1008Box leaf1008Inputs = true := by
  rfl'

private theorem leaf1008CoversExact : CoversExact 8
    leaf1008Box leaf1008Certificate leaf1008InnerLog leaf1008Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi125RoundedFacts
    innerPair3RoundedFacts leaf1008RoundedFacts (by rfl)

private theorem leaf1008FlatSound : Sound leaf1008Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1008CertificateValid
    leaf1008InnerLogValid leaf1008CoversExact leaf1008LowerChecked

private noncomputable def leaf1009Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (1/16), chiHi := (9/128) }

private noncomputable def leaf1009Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217841/134217728) }, vSqrt := { lower := (65529/65536), upper := (2097156/2097125) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (158824881/134217728) }, upper := { exponent := 0, mantissa := (155/128) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi125LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4194281/4194250) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf1009InnerLog : WideLogData :=
  innerPair3Data

set_option maxRecDepth 1000000 in
private theorem leaf1009LocalValidity :
    LeafFacts leaf1009Box leaf1009Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1009Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2097156/2097125) }) = true
      norm_num [leaf1009Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1009CertificateValid :
    WideCertificateValid leaf1009Box leaf1009Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi125ValidityFacts
    leaf1009LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1009CoverageChecked :
    coverageCheck (innerAD leaf1009Box) leaf1009InnerLog = true := by
  rfl'

private theorem leaf1009InnerLogValid :
    leaf1009InnerLog.Valid 8 (innerAD leaf1009Box) :=
  wideLogDataValid_of_cachedCheck endpoint1PositiveFacts
    endpoint5PositiveFacts.valid leaf1009CoverageChecked

private noncomputable def leaf1009InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629205/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1009InputLogOnePlusV_eq :
    leaf1009InputLogOnePlusV = outerEnclosure 24
      (leaf1009Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1009RoundedFacts : LeafRoundedFacts 8
    leaf1009Certificate.logOnePlusV leaf1009InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1009InputLogOnePlusV_eq }

private noncomputable def leaf1009Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi125InputQChi innerPair3Input
    leaf1009InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1009LowerChecked :
    lowerCheck 24 leaf1009Box leaf1009Inputs = true := by
  rfl'

private theorem leaf1009CoversExact : CoversExact 8
    leaf1009Box leaf1009Certificate leaf1009InnerLog leaf1009Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi125RoundedFacts
    innerPair3RoundedFacts leaf1009RoundedFacts (by rfl)

private theorem leaf1009FlatSound : Sound leaf1009Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1009CertificateValid
    leaf1009InnerLogValid leaf1009CoversExact leaf1009LowerChecked

private noncomputable def leaf1010Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (9/128), chiHi := (5/64) }

private noncomputable def leaf1010Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217841/134217728) }, vSqrt := { lower := (32765/32768), upper := (5592416/5592327) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (161315097/134217728) }, upper := { exponent := 0, mantissa := (1259/1024) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi126LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (11184743/11184654) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf1010InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1010LocalValidity :
    LeafFacts leaf1010Box leaf1010Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1010Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (5592416/5592327) }) = true
      norm_num [leaf1010Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1010CertificateValid :
    WideCertificateValid leaf1010Box leaf1010Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi126ValidityFacts
    leaf1010LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1010CoverageChecked :
    coverageCheck (innerAD leaf1010Box) leaf1010InnerLog = true := by
  rfl'

private theorem leaf1010InnerLogValid :
    leaf1010InnerLog.Valid 8 (innerAD leaf1010Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1010CoverageChecked

private noncomputable def leaf1010InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814607/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1010InputLogOnePlusV_eq :
    leaf1010InputLogOnePlusV = outerEnclosure 24
      (leaf1010Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1010RoundedFacts : LeafRoundedFacts 8
    leaf1010Certificate.logOnePlusV leaf1010InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1010InputLogOnePlusV_eq }

private noncomputable def leaf1010Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi126InputQChi innerPair12Input
    leaf1010InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1010LowerChecked :
    lowerCheck 24 leaf1010Box leaf1010Inputs = true := by
  rfl'

private theorem leaf1010CoversExact : CoversExact 8
    leaf1010Box leaf1010Certificate leaf1010InnerLog leaf1010Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi126RoundedFacts
    innerPair12RoundedFacts leaf1010RoundedFacts (by rfl)

private theorem leaf1010FlatSound : Sound leaf1010Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1010CertificateValid
    leaf1010InnerLogValid leaf1010CoversExact leaf1010LowerChecked

private noncomputable def leaf1011Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (9/128), chiHi := (5/64) }

private noncomputable def leaf1011Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217843/134217728) }, vSqrt := { lower := (65529/65536), upper := (1048578/1048561) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (161904883/134217728) }, upper := { exponent := 0, mantissa := (79/64) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi126LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2097139/2097122) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf1011InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1011LocalValidity :
    LeafFacts leaf1011Box leaf1011Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1011Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1048578/1048561) }) = true
      norm_num [leaf1011Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1011CertificateValid :
    WideCertificateValid leaf1011Box leaf1011Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi126ValidityFacts
    leaf1011LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1011CoverageChecked :
    coverageCheck (innerAD leaf1011Box) leaf1011InnerLog = true := by
  rfl'

private theorem leaf1011InnerLogValid :
    leaf1011InnerLog.Valid 8 (innerAD leaf1011Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1011CoverageChecked

private noncomputable def leaf1011InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1011InputLogOnePlusV_eq :
    leaf1011InputLogOnePlusV = outerEnclosure 24
      (leaf1011Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1011RoundedFacts : LeafRoundedFacts 8
    leaf1011Certificate.logOnePlusV leaf1011InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1011InputLogOnePlusV_eq }

private noncomputable def leaf1011Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi126InputQChi innerPair12Input
    leaf1011InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1011LowerChecked :
    lowerCheck 24 leaf1011Box leaf1011Inputs = true := by
  rfl'

private theorem leaf1011CoversExact : CoversExact 8
    leaf1011Box leaf1011Certificate leaf1011InnerLog leaf1011Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi126RoundedFacts
    innerPair12RoundedFacts leaf1011RoundedFacts (by rfl)

private theorem leaf1011FlatSound : Sound leaf1011Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1011CertificateValid
    leaf1011InnerLogValid leaf1011CoversExact leaf1011LowerChecked

private noncomputable def leaf1012Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (5/64), chiHi := (11/128) }

private noncomputable def leaf1012Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217843/134217728) }, vSqrt := { lower := (32765/32768), upper := (33554496/33553915) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (164329567/134217728) }, upper := { exponent := 0, mantissa := (2565/2048) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi103LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108411/67107830) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf1012InnerLog : WideLogData :=
  innerPair128Data

set_option maxRecDepth 1000000 in
private theorem leaf1012LocalValidity :
    LeafFacts leaf1012Box leaf1012Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1012Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554496/33553915) }) = true
      norm_num [leaf1012Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1012CertificateValid :
    WideCertificateValid leaf1012Box leaf1012Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi103ValidityFacts
    leaf1012LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1012CoverageChecked :
    coverageCheck (innerAD leaf1012Box) leaf1012InnerLog = true := by
  rfl'

private theorem leaf1012InnerLogValid :
    leaf1012InnerLog.Valid 8 (innerAD leaf1012Box) :=
  wideLogDataValid_of_cachedCheck endpoint27PositiveFacts
    endpoint100PositiveFacts.valid leaf1012CoverageChecked

private noncomputable def leaf1012InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814613/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1012InputLogOnePlusV_eq :
    leaf1012InputLogOnePlusV = outerEnclosure 24
      (leaf1012Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1012RoundedFacts : LeafRoundedFacts 8
    leaf1012Certificate.logOnePlusV leaf1012InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1012InputLogOnePlusV_eq }

private noncomputable def leaf1012Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi103InputQChi innerPair128Input
    leaf1012InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1012LowerChecked :
    lowerCheck 24 leaf1012Box leaf1012Inputs = true := by
  rfl'

private theorem leaf1012CoversExact : CoversExact 8
    leaf1012Box leaf1012Certificate leaf1012InnerLog leaf1012Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi103RoundedFacts
    innerPair128RoundedFacts leaf1012RoundedFacts (by rfl)

private theorem leaf1012FlatSound : Sound leaf1012Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1012CertificateValid
    leaf1012InnerLogValid leaf1012CoversExact leaf1012LowerChecked

private noncomputable def leaf1013Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1013Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435593/268435456) }, vSqrt := { lower := (65529/65536), upper := (4194312/4194241) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (330002633/268435456) }, upper := { exponent := 0, mantissa := (319/256) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388553/8388482) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf1013InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1013LocalValidity :
    LeafFacts leaf1013Box leaf1013Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1013Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194312/4194241) }) = true
      norm_num [leaf1013Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1013CertificateValid :
    WideCertificateValid leaf1013Box leaf1013Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi127ValidityFacts
    leaf1013LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1013CoverageChecked :
    coverageCheck (innerAD leaf1013Box) leaf1013InnerLog = true := by
  rfl'

private theorem leaf1013InnerLogValid :
    leaf1013InnerLog.Valid 8 (innerAD leaf1013Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1013CoverageChecked

private noncomputable def leaf1013InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1013InputLogOnePlusV_eq :
    leaf1013InputLogOnePlusV = outerEnclosure 24
      (leaf1013Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1013RoundedFacts : LeafRoundedFacts 8
    leaf1013Certificate.logOnePlusV leaf1013InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1013InputLogOnePlusV_eq }

private noncomputable def leaf1013Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi127InputQChi innerPair12Input
    leaf1013InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1013LowerChecked :
    lowerCheck 24 leaf1013Box leaf1013Inputs = true := by
  rfl'

private theorem leaf1013CoversExact : CoversExact 8
    leaf1013Box leaf1013Certificate leaf1013InnerLog leaf1013Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi127RoundedFacts
    innerPair12RoundedFacts leaf1013RoundedFacts (by rfl)

private theorem leaf1013FlatSound : Sound leaf1013Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1013CertificateValid
    leaf1013InnerLogValid leaf1013CoversExact leaf1013LowerChecked

private noncomputable def leaf1014Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1014Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435595/268435456) }, vSqrt := { lower := (65529/65536), upper := (2097156/2097119) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (333082635/268435456) }, upper := { exponent := 0, mantissa := (161/128) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4194275/4194238) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf1014InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1014LocalValidity :
    LeafFacts leaf1014Box leaf1014Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1014Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2097156/2097119) }) = true
      norm_num [leaf1014Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1014CertificateValid :
    WideCertificateValid leaf1014Box leaf1014Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi128ValidityFacts
    leaf1014LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1014CoverageChecked :
    coverageCheck (innerAD leaf1014Box) leaf1014InnerLog = true := by
  rfl'

private theorem leaf1014InnerLogValid :
    leaf1014InnerLog.Valid 8 (innerAD leaf1014Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1014CoverageChecked

private noncomputable def leaf1014InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1014InputLogOnePlusV_eq :
    leaf1014InputLogOnePlusV = outerEnclosure 24
      (leaf1014Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1014RoundedFacts : LeafRoundedFacts 8
    leaf1014Certificate.logOnePlusV leaf1014InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1014InputLogOnePlusV_eq }

private noncomputable def leaf1014Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi128InputQChi innerPair13Input
    leaf1014InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1014LowerChecked :
    lowerCheck 24 leaf1014Box leaf1014Inputs = true := by
  rfl'

private theorem leaf1014CoversExact : CoversExact 8
    leaf1014Box leaf1014Certificate leaf1014InnerLog leaf1014Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi128RoundedFacts
    innerPair13RoundedFacts leaf1014RoundedFacts (by rfl)

private theorem leaf1014FlatSound : Sound leaf1014Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1014CertificateValid
    leaf1014InnerLogValid leaf1014CoversExact leaf1014LowerChecked

private noncomputable def leaf1015Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1015Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435595/268435456) }, vSqrt := { lower := (32765/32768), upper := (22369664/22369261) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (334720935/268435456) }, upper := { exponent := 0, mantissa := (5177/4096) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (44738925/44738522) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf1015InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1015LocalValidity :
    LeafFacts leaf1015Box leaf1015Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1015Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22369664/22369261) }) = true
      norm_num [leaf1015Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1015CertificateValid :
    WideCertificateValid leaf1015Box leaf1015Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi129ValidityFacts
    leaf1015LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1015CoverageChecked :
    coverageCheck (innerAD leaf1015Box) leaf1015InnerLog = true := by
  rfl'

private theorem leaf1015InnerLogValid :
    leaf1015InnerLog.Valid 8 (innerAD leaf1015Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1015CoverageChecked

private noncomputable def leaf1015InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1015InputLogOnePlusV_eq :
    leaf1015InputLogOnePlusV = outerEnclosure 24
      (leaf1015Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1015RoundedFacts : LeafRoundedFacts 8
    leaf1015Certificate.logOnePlusV leaf1015InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1015InputLogOnePlusV_eq }

private noncomputable def leaf1015Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi129InputQChi innerPair13Input
    leaf1015InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1015LowerChecked :
    lowerCheck 24 leaf1015Box leaf1015Inputs = true := by
  rfl'

private theorem leaf1015CoversExact : CoversExact 8
    leaf1015Box leaf1015Certificate leaf1015InnerLog leaf1015Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi129RoundedFacts
    innerPair13RoundedFacts leaf1015RoundedFacts (by rfl)

private theorem leaf1015FlatSound : Sound leaf1015Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1015CertificateValid
    leaf1015InnerLogValid leaf1015CoversExact leaf1015LowerChecked

private noncomputable def leaf1016Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1016Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435597/268435456) }, vSqrt := { lower := (32765/32768), upper := (8388624/8388467) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (337735405/268435456) }, upper := { exponent := 0, mantissa := (653/512) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777091/16776934) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf1016InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1016LocalValidity :
    LeafFacts leaf1016Box leaf1016Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1016Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388624/8388467) }) = true
      norm_num [leaf1016Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1016CertificateValid :
    WideCertificateValid leaf1016Box leaf1016Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi130ValidityFacts
    leaf1016LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1016CoverageChecked :
    coverageCheck (innerAD leaf1016Box) leaf1016InnerLog = true := by
  rfl'

private theorem leaf1016InnerLogValid :
    leaf1016InnerLog.Valid 8 (innerAD leaf1016Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1016CoverageChecked

private noncomputable def leaf1016InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814619/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1016InputLogOnePlusV_eq :
    leaf1016InputLogOnePlusV = outerEnclosure 24
      (leaf1016Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1016RoundedFacts : LeafRoundedFacts 8
    leaf1016Certificate.logOnePlusV leaf1016InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1016InputLogOnePlusV_eq }

private noncomputable def leaf1016Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi130InputQChi innerPair16Input
    leaf1016InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1016LowerChecked :
    lowerCheck 24 leaf1016Box leaf1016Inputs = true := by
  rfl'

private theorem leaf1016CoversExact : CoversExact 8
    leaf1016Box leaf1016Certificate leaf1016InnerLog leaf1016Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi130RoundedFacts
    innerPair16RoundedFacts leaf1016RoundedFacts (by rfl)

private theorem leaf1016FlatSound : Sound leaf1016Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1016CertificateValid
    leaf1016InnerLogValid leaf1016CoversExact leaf1016LowerChecked

private noncomputable def leaf1017Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1017Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435597/268435456) }, vSqrt := { lower := (65529/65536), upper := (4194312/4194235) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (336162637/268435456) }, upper := { exponent := 0, mantissa := (325/256) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388547/8388470) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf1017InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1017LocalValidity :
    LeafFacts leaf1017Box leaf1017Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1017Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194312/4194235) }) = true
      norm_num [leaf1017Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1017CertificateValid :
    WideCertificateValid leaf1017Box leaf1017Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi129ValidityFacts
    leaf1017LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1017CoverageChecked :
    coverageCheck (innerAD leaf1017Box) leaf1017InnerLog = true := by
  rfl'

private theorem leaf1017InnerLogValid :
    leaf1017InnerLog.Valid 8 (innerAD leaf1017Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1017CoverageChecked

private noncomputable def leaf1017InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1017InputLogOnePlusV_eq :
    leaf1017InputLogOnePlusV = outerEnclosure 24
      (leaf1017Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1017RoundedFacts : LeafRoundedFacts 8
    leaf1017Certificate.logOnePlusV leaf1017InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1017InputLogOnePlusV_eq }

private noncomputable def leaf1017Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi129InputQChi innerPair16Input
    leaf1017InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1017LowerChecked :
    lowerCheck 24 leaf1017Box leaf1017Inputs = true := by
  rfl'

private theorem leaf1017CoversExact : CoversExact 8
    leaf1017Box leaf1017Certificate leaf1017InnerLog leaf1017Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi129RoundedFacts
    innerPair16RoundedFacts leaf1017RoundedFacts (by rfl)

private theorem leaf1017FlatSound : Sound leaf1017Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1017CertificateValid
    leaf1017InnerLogValid leaf1017CoversExact leaf1017LowerChecked

private noncomputable def leaf1018Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1018Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435599/268435456) }, vSqrt := { lower := (65529/65536), upper := (524289/524279) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (339242639/268435456) }, upper := { exponent := 0, mantissa := (41/32) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (524284/524279) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf1018InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1018LocalValidity :
    LeafFacts leaf1018Box leaf1018Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1018Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (524289/524279) }) = true
      norm_num [leaf1018Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1018CertificateValid :
    WideCertificateValid leaf1018Box leaf1018Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi130ValidityFacts
    leaf1018LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1018CoverageChecked :
    coverageCheck (innerAD leaf1018Box) leaf1018InnerLog = true := by
  rfl'

private theorem leaf1018InnerLogValid :
    leaf1018InnerLog.Valid 8 (innerAD leaf1018Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1018CoverageChecked

private noncomputable def leaf1018InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1018InputLogOnePlusV_eq :
    leaf1018InputLogOnePlusV = outerEnclosure 24
      (leaf1018Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1018RoundedFacts : LeafRoundedFacts 8
    leaf1018Certificate.logOnePlusV leaf1018InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1018InputLogOnePlusV_eq }

private noncomputable def leaf1018Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi130InputQChi innerPair16Input
    leaf1018InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1018LowerChecked :
    lowerCheck 24 leaf1018Box leaf1018Inputs = true := by
  rfl'

private theorem leaf1018CoversExact : CoversExact 8
    leaf1018Box leaf1018Certificate leaf1018InnerLog leaf1018Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi130RoundedFacts
    innerPair16RoundedFacts leaf1018RoundedFacts (by rfl)

private theorem leaf1018FlatSound : Sound leaf1018Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1018CertificateValid
    leaf1018InnerLogValid leaf1018CoversExact leaf1018LowerChecked

private noncomputable def leaf1019Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (3/32), chiHi := (13/128) }

private noncomputable def leaf1019Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435659/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107707) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (337604279/268435456) }, upper := { exponent := 0, mantissa := (5253/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi105LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216635/134215414) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1019InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1019LocalValidity :
    LeafFacts leaf1019Box leaf1019Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1019Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107707) }) = true
      norm_num [leaf1019Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1019CertificateValid :
    WideCertificateValid leaf1019Box leaf1019Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi105ValidityFacts
    leaf1019LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1019CoverageChecked :
    coverageCheck (innerAD leaf1019Box) leaf1019InnerLog = true := by
  rfl'

private theorem leaf1019InnerLogValid :
    leaf1019InnerLog.Valid 8 (innerAD leaf1019Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1019CoverageChecked

private noncomputable def leaf1019InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1019InputLogOnePlusV_eq :
    leaf1019InputLogOnePlusV = outerEnclosure 24
      (leaf1019Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1019RoundedFacts : LeafRoundedFacts 8
    leaf1019Certificate.logOnePlusV leaf1019InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1019InputLogOnePlusV_eq }

private noncomputable def leaf1019Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi105InputQChi innerPair16Input
    leaf1019InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1019LowerChecked :
    lowerCheck 24 leaf1019Box leaf1019Inputs = true := by
  rfl'

private theorem leaf1019CoversExact : CoversExact 8
    leaf1019Box leaf1019Certificate leaf1019InnerLog leaf1019Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi105RoundedFacts
    innerPair16RoundedFacts leaf1019RoundedFacts (by rfl)

private theorem leaf1019FlatSound : Sound leaf1019Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1019CertificateValid
    leaf1019InnerLogValid leaf1019CoversExact leaf1019LowerChecked

private noncomputable def leaf1020Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (3/32), chiHi := (13/128) }

private noncomputable def leaf1020Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435661/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553847) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (338390661/268435456) }, upper := { exponent := 0, mantissa := (2633/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi105LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108311/67107694) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1020InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1020LocalValidity :
    LeafFacts leaf1020Box leaf1020Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1020Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553847) }) = true
      norm_num [leaf1020Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1020CertificateValid :
    WideCertificateValid leaf1020Box leaf1020Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi105ValidityFacts
    leaf1020LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1020CoverageChecked :
    coverageCheck (innerAD leaf1020Box) leaf1020InnerLog = true := by
  rfl'

private theorem leaf1020InnerLogValid :
    leaf1020InnerLog.Valid 8 (innerAD leaf1020Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1020CoverageChecked

private noncomputable def leaf1020InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1020InputLogOnePlusV_eq :
    leaf1020InputLogOnePlusV = outerEnclosure 24
      (leaf1020Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1020RoundedFacts : LeafRoundedFacts 8
    leaf1020Certificate.logOnePlusV leaf1020InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1020InputLogOnePlusV_eq }

private noncomputable def leaf1020Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi105InputQChi innerPair16Input
    leaf1020InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1020LowerChecked :
    lowerCheck 24 leaf1020Box leaf1020Inputs = true := by
  rfl'

private theorem leaf1020CoversExact : CoversExact 8
    leaf1020Box leaf1020Certificate leaf1020InnerLog leaf1020Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi105RoundedFacts
    innerPair16RoundedFacts leaf1020RoundedFacts (by rfl)

private theorem leaf1020FlatSound : Sound leaf1020Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1020CertificateValid
    leaf1020InnerLogValid leaf1020CoversExact leaf1020LowerChecked

private noncomputable def leaf1021Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf1021Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435661/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553809) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (343371093/268435456) }, upper := { exponent := 0, mantissa := (2671/2048) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108273/67107618) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1021InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1021LocalValidity :
    LeafFacts leaf1021Box leaf1021Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1021Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553809) }) = true
      norm_num [leaf1021Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1021CertificateValid :
    WideCertificateValid leaf1021Box leaf1021Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi106ValidityFacts
    leaf1021LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1021CoverageChecked :
    coverageCheck (innerAD leaf1021Box) leaf1021InnerLog = true := by
  rfl'

private theorem leaf1021InnerLogValid :
    leaf1021InnerLog.Valid 8 (innerAD leaf1021Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1021CoverageChecked

private noncomputable def leaf1021InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1021InputLogOnePlusV_eq :
    leaf1021InputLogOnePlusV = outerEnclosure 24
      (leaf1021Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1021RoundedFacts : LeafRoundedFacts 8
    leaf1021Certificate.logOnePlusV leaf1021InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1021InputLogOnePlusV_eq }

private noncomputable def leaf1021Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi106InputQChi innerPair16Input
    leaf1021InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1021LowerChecked :
    lowerCheck 24 leaf1021Box leaf1021Inputs = true := by
  rfl'

private theorem leaf1021CoversExact : CoversExact 8
    leaf1021Box leaf1021Certificate leaf1021InnerLog leaf1021Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi106RoundedFacts
    innerPair16RoundedFacts leaf1021RoundedFacts (by rfl)

private theorem leaf1021FlatSound : Sound leaf1021Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1021CertificateValid
    leaf1021InnerLogValid leaf1021CoversExact leaf1021LowerChecked

private noncomputable def leaf1022Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf1022Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435663/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776901) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (344223007/268435456) }, upper := { exponent := 0, mantissa := (1339/1024) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554133/33553802) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1022InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1022LocalValidity :
    LeafFacts leaf1022Box leaf1022Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1022Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776901) }) = true
      norm_num [leaf1022Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1022CertificateValid :
    WideCertificateValid leaf1022Box leaf1022Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi106ValidityFacts
    leaf1022LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1022CoverageChecked :
    coverageCheck (innerAD leaf1022Box) leaf1022InnerLog = true := by
  rfl'

private theorem leaf1022InnerLogValid :
    leaf1022InnerLog.Valid 8 (innerAD leaf1022Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1022CoverageChecked

private noncomputable def leaf1022InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814623/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1022InputLogOnePlusV_eq :
    leaf1022InputLogOnePlusV = outerEnclosure 24
      (leaf1022Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1022RoundedFacts : LeafRoundedFacts 8
    leaf1022Certificate.logOnePlusV leaf1022InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1022InputLogOnePlusV_eq }

private noncomputable def leaf1022Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi106InputQChi innerPair16Input
    leaf1022InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1022LowerChecked :
    lowerCheck 24 leaf1022Box leaf1022Inputs = true := by
  rfl'

private theorem leaf1022CoversExact : CoversExact 8
    leaf1022Box leaf1022Certificate leaf1022InnerLog leaf1022Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi106RoundedFacts
    innerPair16RoundedFacts leaf1022RoundedFacts (by rfl)

private theorem leaf1022FlatSound : Sound leaf1022Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1022CertificateValid
    leaf1022InnerLogValid leaf1022CoversExact leaf1022LowerChecked

private noncomputable def leaf1023Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1023Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435597/268435456) }, vSqrt := { lower := (32765/32768), upper := (11184832/11184619) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (339177109/268435456) }, upper := { exponent := 0, mantissa := (2623/2048) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22369451/22369238) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf1023InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1023LocalValidity :
    LeafFacts leaf1023Box leaf1023Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1023Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11184832/11184619) }) = true
      norm_num [leaf1023Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1023CertificateValid :
    WideCertificateValid leaf1023Box leaf1023Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi131ValidityFacts
    leaf1023LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1023CoverageChecked :
    coverageCheck (innerAD leaf1023Box) leaf1023InnerLog = true := by
  rfl'

private theorem leaf1023InnerLogValid :
    leaf1023InnerLog.Valid 8 (innerAD leaf1023Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1023CoverageChecked

private noncomputable def leaf1023InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1023InputLogOnePlusV_eq :
    leaf1023InputLogOnePlusV = outerEnclosure 24
      (leaf1023Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1023RoundedFacts : LeafRoundedFacts 8
    leaf1023Certificate.logOnePlusV leaf1023InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1023InputLogOnePlusV_eq }

private noncomputable def leaf1023Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi131InputQChi innerPair16Input
    leaf1023InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1023LowerChecked :
    lowerCheck 24 leaf1023Box leaf1023Inputs = true := by
  rfl'

private theorem leaf1023CoversExact : CoversExact 8
    leaf1023Box leaf1023Certificate leaf1023InnerLog leaf1023Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi131RoundedFacts
    innerPair16RoundedFacts leaf1023RoundedFacts (by rfl)

private theorem leaf1023FlatSound : Sound leaf1023Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1023CertificateValid
    leaf1023InnerLogValid leaf1023CoversExact leaf1023LowerChecked

private noncomputable def leaf1024Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1024Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435599/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777248/16776917) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (342126047/268435456) }, upper := { exponent := 0, mantissa := (1323/1024) } }, logOuter := sk96LogOuterCertificate, logK := sk96LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554165/33553834) } }, logDArg := sk96LogDArgCertificate }

private noncomputable def leaf1024InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1024LocalValidity :
    LeafFacts leaf1024Box leaf1024Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1024Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777248/16776917) }) = true
      norm_num [leaf1024Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1024CertificateValid :
    WideCertificateValid leaf1024Box leaf1024Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk96ValidityFacts chi132ValidityFacts
    leaf1024LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1024CoverageChecked :
    coverageCheck (innerAD leaf1024Box) leaf1024InnerLog = true := by
  rfl'

private theorem leaf1024InnerLogValid :
    leaf1024InnerLog.Valid 8 (innerAD leaf1024Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1024CoverageChecked

private noncomputable def leaf1024InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814623/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1024InputLogOnePlusV_eq :
    leaf1024InputLogOnePlusV = outerEnclosure 24
      (leaf1024Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1024RoundedFacts : LeafRoundedFacts 8
    leaf1024Certificate.logOnePlusV leaf1024InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1024InputLogOnePlusV_eq }

private noncomputable def leaf1024Inputs : Inputs :=
  inputsOfCaches globalInput sk96RoundedInputs
    chi132InputQChi innerPair16Input
    leaf1024InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1024LowerChecked :
    lowerCheck 24 leaf1024Box leaf1024Inputs = true := by
  rfl'

private theorem leaf1024CoversExact : CoversExact 8
    leaf1024Box leaf1024Certificate leaf1024InnerLog leaf1024Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk96RoundedFacts chi132RoundedFacts
    innerPair16RoundedFacts leaf1024RoundedFacts (by rfl)

private theorem leaf1024FlatSound : Sound leaf1024Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1024CertificateValid
    leaf1024InnerLogValid leaf1024CoversExact leaf1024LowerChecked

private noncomputable def leaf1025Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf1025Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435665/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553795) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (345074921/268435456) }, upper := { exponent := 0, mantissa := (2685/2048) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108259/67107590) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1025InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1025LocalValidity :
    LeafFacts leaf1025Box leaf1025Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1025Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553795) }) = true
      norm_num [leaf1025Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1025CertificateValid :
    WideCertificateValid leaf1025Box leaf1025Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi106ValidityFacts
    leaf1025LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1025CoverageChecked :
    coverageCheck (innerAD leaf1025Box) leaf1025InnerLog = true := by
  rfl'

private theorem leaf1025InnerLogValid :
    leaf1025InnerLog.Valid 8 (innerAD leaf1025Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1025CoverageChecked

private noncomputable def leaf1025InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf1025InputLogOnePlusV_eq :
    leaf1025InputLogOnePlusV = outerEnclosure 24
      (leaf1025Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1025RoundedFacts : LeafRoundedFacts 8
    leaf1025Certificate.logOnePlusV leaf1025InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1025InputLogOnePlusV_eq }

private noncomputable def leaf1025Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi106InputQChi innerPair16Input
    leaf1025InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1025LowerChecked :
    lowerCheck 24 leaf1025Box leaf1025Inputs = true := by
  rfl'

private theorem leaf1025CoversExact : CoversExact 8
    leaf1025Box leaf1025Certificate leaf1025InnerLog leaf1025Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi106RoundedFacts
    innerPair16RoundedFacts leaf1025RoundedFacts (by rfl)

private theorem leaf1025FlatSound : Sound leaf1025Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1025CertificateValid
    leaf1025InnerLogValid leaf1025CoversExact leaf1025LowerChecked

private noncomputable def leaf1026Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf1026Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435667/268435456) }, vSqrt := { lower := (32765/32768), upper := (8388616/8388447) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (345926835/268435456) }, upper := { exponent := 0, mantissa := (673/512) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (16777063/16776894) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1026InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1026LocalValidity :
    LeafFacts leaf1026Box leaf1026Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1026Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (8388616/8388447) }) = true
      norm_num [leaf1026Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1026CertificateValid :
    WideCertificateValid leaf1026Box leaf1026Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi106ValidityFacts
    leaf1026LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1026CoverageChecked :
    coverageCheck (innerAD leaf1026Box) leaf1026InnerLog = true := by
  rfl'

private theorem leaf1026InnerLogValid :
    leaf1026InnerLog.Valid 8 (innerAD leaf1026Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1026CoverageChecked

private noncomputable def leaf1026InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1026InputLogOnePlusV_eq :
    leaf1026InputLogOnePlusV = outerEnclosure 24
      (leaf1026Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1026RoundedFacts : LeafRoundedFacts 8
    leaf1026Certificate.logOnePlusV leaf1026InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1026InputLogOnePlusV_eq }

private noncomputable def leaf1026Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi106InputQChi innerPair17Input
    leaf1026InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1026LowerChecked :
    lowerCheck 24 leaf1026Box leaf1026Inputs = true := by
  rfl'

private theorem leaf1026CoversExact : CoversExact 8
    leaf1026Box leaf1026Certificate leaf1026InnerLog leaf1026Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi106RoundedFacts
    innerPair17RoundedFacts leaf1026RoundedFacts (by rfl)

private theorem leaf1026FlatSound : Sound leaf1026Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1026CertificateValid
    leaf1026InnerLogValid leaf1026CoversExact leaf1026LowerChecked

private noncomputable def leaf1027Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1027Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435663/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107529) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (349137907/268435456) }, upper := { exponent := 0, mantissa := (5431/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216457/134215058) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1027InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1027LocalValidity :
    LeafFacts leaf1027Box leaf1027Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1027Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107529) }) = true
      norm_num [leaf1027Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1027CertificateValid :
    WideCertificateValid leaf1027Box leaf1027Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi98ValidityFacts
    leaf1027LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1027CoverageChecked :
    coverageCheck (innerAD leaf1027Box) leaf1027InnerLog = true := by
  rfl'

private theorem leaf1027InnerLogValid :
    leaf1027InnerLog.Valid 8 (innerAD leaf1027Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1027CoverageChecked

private noncomputable def leaf1027InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453657/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1027InputLogOnePlusV_eq :
    leaf1027InputLogOnePlusV = outerEnclosure 24
      (leaf1027Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1027RoundedFacts : LeafRoundedFacts 8
    leaf1027Certificate.logOnePlusV leaf1027InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1027InputLogOnePlusV_eq }

private noncomputable def leaf1027Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi98InputQChi innerPair17Input
    leaf1027InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1027LowerChecked :
    lowerCheck 24 leaf1027Box leaf1027Inputs = true := by
  rfl'

private theorem leaf1027CoversExact : CoversExact 8
    leaf1027Box leaf1027Certificate leaf1027InnerLog leaf1027Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi98RoundedFacts
    innerPair17RoundedFacts leaf1027RoundedFacts (by rfl)

private theorem leaf1027FlatSound : Sound leaf1027Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1027CertificateValid
    leaf1027InnerLogValid leaf1027CoversExact leaf1027LowerChecked

private noncomputable def leaf1028Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1028Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435665/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553757) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (350055353/268435456) }, upper := { exponent := 0, mantissa := (2723/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108221/67107514) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1028InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1028LocalValidity :
    LeafFacts leaf1028Box leaf1028Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1028Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553757) }) = true
      norm_num [leaf1028Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1028CertificateValid :
    WideCertificateValid leaf1028Box leaf1028Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi98ValidityFacts
    leaf1028LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1028CoverageChecked :
    coverageCheck (innerAD leaf1028Box) leaf1028InnerLog = true := by
  rfl'

private theorem leaf1028InnerLogValid :
    leaf1028InnerLog.Valid 8 (innerAD leaf1028Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1028CoverageChecked

private noncomputable def leaf1028InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1028InputLogOnePlusV_eq :
    leaf1028InputLogOnePlusV = outerEnclosure 24
      (leaf1028Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1028RoundedFacts : LeafRoundedFacts 8
    leaf1028Certificate.logOnePlusV leaf1028InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1028InputLogOnePlusV_eq }

private noncomputable def leaf1028Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi98InputQChi innerPair17Input
    leaf1028InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1028LowerChecked :
    lowerCheck 24 leaf1028Box leaf1028Inputs = true := by
  rfl'

private theorem leaf1028CoversExact : CoversExact 8
    leaf1028Box leaf1028Certificate leaf1028InnerLog leaf1028Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi98RoundedFacts
    innerPair17RoundedFacts leaf1028RoundedFacts (by rfl)

private theorem leaf1028FlatSound : Sound leaf1028Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1028CertificateValid
    leaf1028InnerLogValid leaf1028CoversExact leaf1028LowerChecked

private noncomputable def leaf1029Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf1029Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435665/268435456) }, vSqrt := { lower := (32765/32768), upper := (4194308/4194215) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (354904721/268435456) }, upper := { exponent := 0, mantissa := (345/256) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388523/8388430) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1029InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1029LocalValidity :
    LeafFacts leaf1029Box leaf1029Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1029Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194308/4194215) }) = true
      norm_num [leaf1029Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1029CertificateValid :
    WideCertificateValid leaf1029Box leaf1029Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi99ValidityFacts
    leaf1029LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1029CoverageChecked :
    coverageCheck (innerAD leaf1029Box) leaf1029InnerLog = true := by
  rfl'

private theorem leaf1029InnerLogValid :
    leaf1029InnerLog.Valid 8 (innerAD leaf1029Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1029CoverageChecked

private noncomputable def leaf1029InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1029InputLogOnePlusV_eq :
    leaf1029InputLogOnePlusV = outerEnclosure 24
      (leaf1029Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1029RoundedFacts : LeafRoundedFacts 8
    leaf1029Certificate.logOnePlusV leaf1029InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1029InputLogOnePlusV_eq }

private noncomputable def leaf1029Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi99InputQChi innerPair21Input
    leaf1029InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1029LowerChecked :
    lowerCheck 24 leaf1029Box leaf1029Inputs = true := by
  rfl'

private theorem leaf1029CoversExact : CoversExact 8
    leaf1029Box leaf1029Certificate leaf1029InnerLog leaf1029Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi99RoundedFacts
    innerPair21RoundedFacts leaf1029RoundedFacts (by rfl)

private theorem leaf1029FlatSound : Sound leaf1029Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1029CertificateValid
    leaf1029InnerLogValid leaf1029CoversExact leaf1029LowerChecked

private noncomputable def leaf1030Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf1030Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435667/268435456) }, vSqrt := { lower := (32765/32768), upper := (2097154/2097107) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (355887699/268435456) }, upper := { exponent := 0, mantissa := (173/128) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4194261/4194214) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1030InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1030LocalValidity :
    LeafFacts leaf1030Box leaf1030Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1030Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2097154/2097107) }) = true
      norm_num [leaf1030Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1030CertificateValid :
    WideCertificateValid leaf1030Box leaf1030Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi99ValidityFacts
    leaf1030LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1030CoverageChecked :
    coverageCheck (innerAD leaf1030Box) leaf1030InnerLog = true := by
  rfl'

private theorem leaf1030InnerLogValid :
    leaf1030InnerLog.Valid 8 (innerAD leaf1030Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1030CoverageChecked

private noncomputable def leaf1030InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1030InputLogOnePlusV_eq :
    leaf1030InputLogOnePlusV = outerEnclosure 24
      (leaf1030Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1030RoundedFacts : LeafRoundedFacts 8
    leaf1030Certificate.logOnePlusV leaf1030InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1030InputLogOnePlusV_eq }

private noncomputable def leaf1030Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi99InputQChi innerPair21Input
    leaf1030InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1030LowerChecked :
    lowerCheck 24 leaf1030Box leaf1030Inputs = true := by
  rfl'

private theorem leaf1030CoversExact : CoversExact 8
    leaf1030Box leaf1030Certificate leaf1030InnerLog leaf1030Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi99RoundedFacts
    innerPair21RoundedFacts leaf1030RoundedFacts (by rfl)

private theorem leaf1030FlatSound : Sound leaf1030Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1030CertificateValid
    leaf1030InnerLogValid leaf1030CoversExact leaf1030LowerChecked

private noncomputable def leaf1031Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1031Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435667/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107499) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (350972799/268435456) }, upper := { exponent := 0, mantissa := (5461/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216427/134214998) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1031InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1031LocalValidity :
    LeafFacts leaf1031Box leaf1031Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1031Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107499) }) = true
      norm_num [leaf1031Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1031CertificateValid :
    WideCertificateValid leaf1031Box leaf1031Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi98ValidityFacts
    leaf1031LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1031CoverageChecked :
    coverageCheck (innerAD leaf1031Box) leaf1031InnerLog = true := by
  rfl'

private theorem leaf1031InnerLogValid :
    leaf1031InnerLog.Valid 8 (innerAD leaf1031Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1031CoverageChecked

private noncomputable def leaf1031InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1031InputLogOnePlusV_eq :
    leaf1031InputLogOnePlusV = outerEnclosure 24
      (leaf1031Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1031RoundedFacts : LeafRoundedFacts 8
    leaf1031Certificate.logOnePlusV leaf1031InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1031InputLogOnePlusV_eq }

private noncomputable def leaf1031Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi98InputQChi innerPair17Input
    leaf1031InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1031LowerChecked :
    lowerCheck 24 leaf1031Box leaf1031Inputs = true := by
  rfl'

private theorem leaf1031CoversExact : CoversExact 8
    leaf1031Box leaf1031Certificate leaf1031InnerLog leaf1031Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi98RoundedFacts
    innerPair17RoundedFacts leaf1031RoundedFacts (by rfl)

private theorem leaf1031FlatSound : Sound leaf1031Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1031CertificateValid
    leaf1031InnerLogValid leaf1031CoversExact leaf1031LowerChecked

private noncomputable def leaf1032Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1032Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435669/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776871) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (351890245/268435456) }, upper := { exponent := 0, mantissa := (1369/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554103/33553742) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1032InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1032LocalValidity :
    LeafFacts leaf1032Box leaf1032Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1032Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776871) }) = true
      norm_num [leaf1032Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1032CertificateValid :
    WideCertificateValid leaf1032Box leaf1032Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi98ValidityFacts
    leaf1032LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1032CoverageChecked :
    coverageCheck (innerAD leaf1032Box) leaf1032InnerLog = true := by
  rfl'

private theorem leaf1032InnerLogValid :
    leaf1032InnerLog.Valid 8 (innerAD leaf1032Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1032CoverageChecked

private noncomputable def leaf1032InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1032InputLogOnePlusV_eq :
    leaf1032InputLogOnePlusV = outerEnclosure 24
      (leaf1032Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1032RoundedFacts : LeafRoundedFacts 8
    leaf1032Certificate.logOnePlusV leaf1032InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1032InputLogOnePlusV_eq }

private noncomputable def leaf1032Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi98InputQChi innerPair17Input
    leaf1032InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1032LowerChecked :
    lowerCheck 24 leaf1032Box leaf1032Inputs = true := by
  rfl'

private theorem leaf1032CoversExact : CoversExact 8
    leaf1032Box leaf1032Certificate leaf1032InnerLog leaf1032Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi98RoundedFacts
    innerPair17RoundedFacts leaf1032RoundedFacts (by rfl)

private theorem leaf1032FlatSound : Sound leaf1032Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1032CertificateValid
    leaf1032InnerLogValid leaf1032CoversExact leaf1032LowerChecked

private noncomputable def leaf1033Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf1033Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435669/268435456) }, vSqrt := { lower := (32765/32768), upper := (4194308/4194213) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (356870677/268435456) }, upper := { exponent := 0, mantissa := (347/256) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388521/8388426) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1033InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1033LocalValidity :
    LeafFacts leaf1033Box leaf1033Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1033Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194308/4194213) }) = true
      norm_num [leaf1033Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1033CertificateValid :
    WideCertificateValid leaf1033Box leaf1033Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi99ValidityFacts
    leaf1033LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1033CoverageChecked :
    coverageCheck (innerAD leaf1033Box) leaf1033InnerLog = true := by
  rfl'

private theorem leaf1033InnerLogValid :
    leaf1033InnerLog.Valid 8 (innerAD leaf1033Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1033CoverageChecked

private noncomputable def leaf1033InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1033InputLogOnePlusV_eq :
    leaf1033InputLogOnePlusV = outerEnclosure 24
      (leaf1033Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1033RoundedFacts : LeafRoundedFacts 8
    leaf1033Certificate.logOnePlusV leaf1033InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1033InputLogOnePlusV_eq }

private noncomputable def leaf1033Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi99InputQChi innerPair21Input
    leaf1033InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1033LowerChecked :
    lowerCheck 24 leaf1033Box leaf1033Inputs = true := by
  rfl'

private theorem leaf1033CoversExact : CoversExact 8
    leaf1033Box leaf1033Certificate leaf1033InnerLog leaf1033Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi99RoundedFacts
    innerPair21RoundedFacts leaf1033RoundedFacts (by rfl)

private theorem leaf1033FlatSound : Sound leaf1033Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1033CertificateValid
    leaf1033InnerLogValid leaf1033CoversExact leaf1033LowerChecked

private noncomputable def leaf1034Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf1034Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435671/268435456) }, vSqrt := { lower := (32765/32768), upper := (1048577/1048553) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (357853655/268435456) }, upper := { exponent := 0, mantissa := (87/64) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1048565/1048553) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1034InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1034LocalValidity :
    LeafFacts leaf1034Box leaf1034Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1034Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1048577/1048553) }) = true
      norm_num [leaf1034Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1034CertificateValid :
    WideCertificateValid leaf1034Box leaf1034Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi99ValidityFacts
    leaf1034LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1034CoverageChecked :
    coverageCheck (innerAD leaf1034Box) leaf1034InnerLog = true := by
  rfl'

private theorem leaf1034InnerLogValid :
    leaf1034InnerLog.Valid 8 (innerAD leaf1034Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1034CoverageChecked

private noncomputable def leaf1034InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1034InputLogOnePlusV_eq :
    leaf1034InputLogOnePlusV = outerEnclosure 24
      (leaf1034Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1034RoundedFacts : LeafRoundedFacts 8
    leaf1034Certificate.logOnePlusV leaf1034InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1034InputLogOnePlusV_eq }

private noncomputable def leaf1034Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi99InputQChi innerPair21Input
    leaf1034InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1034LowerChecked :
    lowerCheck 24 leaf1034Box leaf1034Inputs = true := by
  rfl'

private theorem leaf1034CoversExact : CoversExact 8
    leaf1034Box leaf1034Certificate leaf1034InnerLog leaf1034Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi99RoundedFacts
    innerPair21RoundedFacts leaf1034RoundedFacts (by rfl)

private theorem leaf1034FlatSound : Sound leaf1034Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1034CertificateValid
    leaf1034InnerLogValid leaf1034CoversExact leaf1034LowerChecked

private noncomputable def leaf1035Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1035Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435599/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108992/67107689) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (340749875/268435456) }, upper := { exponent := 0, mantissa := (5271/4096) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216681/134215378) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf1035InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1035LocalValidity :
    LeafFacts leaf1035Box leaf1035Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1035Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108992/67107689) }) = true
      norm_num [leaf1035Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1035CertificateValid :
    WideCertificateValid leaf1035Box leaf1035Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi131ValidityFacts
    leaf1035LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1035CoverageChecked :
    coverageCheck (innerAD leaf1035Box) leaf1035InnerLog = true := by
  rfl'

private theorem leaf1035InnerLogValid :
    leaf1035InnerLog.Valid 8 (innerAD leaf1035Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1035CoverageChecked

private noncomputable def leaf1035InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1035InputLogOnePlusV_eq :
    leaf1035InputLogOnePlusV = outerEnclosure 24
      (leaf1035Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1035RoundedFacts : LeafRoundedFacts 8
    leaf1035Certificate.logOnePlusV leaf1035InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1035InputLogOnePlusV_eq }

private noncomputable def leaf1035Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi131InputQChi innerPair16Input
    leaf1035InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1035LowerChecked :
    lowerCheck 24 leaf1035Box leaf1035Inputs = true := by
  rfl'

private theorem leaf1035CoversExact : CoversExact 8
    leaf1035Box leaf1035Certificate leaf1035InnerLog leaf1035Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi131RoundedFacts
    innerPair16RoundedFacts leaf1035RoundedFacts (by rfl)

private theorem leaf1035FlatSound : Sound leaf1035Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1035CertificateValid
    leaf1035InnerLogValid leaf1035CoversExact leaf1035LowerChecked

private noncomputable def leaf1036Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1036Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435601/268435456) }, vSqrt := { lower := (32765/32768), upper := (11184832/11184607) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (343764345/268435456) }, upper := { exponent := 0, mantissa := (2659/2048) } }, logOuter := sk97LogOuterCertificate, logK := sk97LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22369439/22369214) } }, logDArg := sk97LogDArgCertificate }

private noncomputable def leaf1036InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1036LocalValidity :
    LeafFacts leaf1036Box leaf1036Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1036Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11184832/11184607) }) = true
      norm_num [leaf1036Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1036CertificateValid :
    WideCertificateValid leaf1036Box leaf1036Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk97ValidityFacts chi132ValidityFacts
    leaf1036LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1036CoverageChecked :
    coverageCheck (innerAD leaf1036Box) leaf1036InnerLog = true := by
  rfl'

private theorem leaf1036InnerLogValid :
    leaf1036InnerLog.Valid 8 (innerAD leaf1036Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1036CoverageChecked

private noncomputable def leaf1036InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1036InputLogOnePlusV_eq :
    leaf1036InputLogOnePlusV = outerEnclosure 24
      (leaf1036Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1036RoundedFacts : LeafRoundedFacts 8
    leaf1036Certificate.logOnePlusV leaf1036InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1036InputLogOnePlusV_eq }

private noncomputable def leaf1036Inputs : Inputs :=
  inputsOfCaches globalInput sk97RoundedInputs
    chi132InputQChi innerPair16Input
    leaf1036InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1036LowerChecked :
    lowerCheck 24 leaf1036Box leaf1036Inputs = true := by
  rfl'

private theorem leaf1036CoversExact : CoversExact 8
    leaf1036Box leaf1036Certificate leaf1036InnerLog leaf1036Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk97RoundedFacts chi132RoundedFacts
    innerPair16RoundedFacts leaf1036RoundedFacts (by rfl)

private theorem leaf1036FlatSound : Sound leaf1036Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1036CertificateValid
    leaf1036InnerLogValid leaf1036CoversExact leaf1036LowerChecked

private noncomputable def leaf1037Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf1037Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435669/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553781) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (346778749/268435456) }, upper := { exponent := 0, mantissa := (2699/2048) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108245/67107562) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1037InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1037LocalValidity :
    LeafFacts leaf1037Box leaf1037Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1037Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553781) }) = true
      norm_num [leaf1037Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1037CertificateValid :
    WideCertificateValid leaf1037Box leaf1037Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi106ValidityFacts
    leaf1037LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1037CoverageChecked :
    coverageCheck (innerAD leaf1037Box) leaf1037InnerLog = true := by
  rfl'

private theorem leaf1037InnerLogValid :
    leaf1037InnerLog.Valid 8 (innerAD leaf1037Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1037CoverageChecked

private noncomputable def leaf1037InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1037InputLogOnePlusV_eq :
    leaf1037InputLogOnePlusV = outerEnclosure 24
      (leaf1037Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1037RoundedFacts : LeafRoundedFacts 8
    leaf1037Certificate.logOnePlusV leaf1037InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1037InputLogOnePlusV_eq }

private noncomputable def leaf1037Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi106InputQChi innerPair17Input
    leaf1037InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1037LowerChecked :
    lowerCheck 24 leaf1037Box leaf1037Inputs = true := by
  rfl'

private theorem leaf1037CoversExact : CoversExact 8
    leaf1037Box leaf1037Certificate leaf1037InnerLog leaf1037Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi106RoundedFacts
    innerPair17RoundedFacts leaf1037RoundedFacts (by rfl)

private theorem leaf1037FlatSound : Sound leaf1037Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1037CertificateValid
    leaf1037InnerLogValid leaf1037CoversExact leaf1037LowerChecked

private noncomputable def leaf1038Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf1038Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435671/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776887) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (347630663/268435456) }, upper := { exponent := 0, mantissa := (1353/1024) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33554119/33553774) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf1038InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1038LocalValidity :
    LeafFacts leaf1038Box leaf1038Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1038Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776887) }) = true
      norm_num [leaf1038Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1038CertificateValid :
    WideCertificateValid leaf1038Box leaf1038Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi106ValidityFacts
    leaf1038LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1038CoverageChecked :
    coverageCheck (innerAD leaf1038Box) leaf1038InnerLog = true := by
  rfl'

private theorem leaf1038InnerLogValid :
    leaf1038InnerLog.Valid 8 (innerAD leaf1038Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1038CoverageChecked

private noncomputable def leaf1038InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1038InputLogOnePlusV_eq :
    leaf1038InputLogOnePlusV = outerEnclosure 24
      (leaf1038Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1038RoundedFacts : LeafRoundedFacts 8
    leaf1038Certificate.logOnePlusV leaf1038InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1038InputLogOnePlusV_eq }

private noncomputable def leaf1038Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi106InputQChi innerPair17Input
    leaf1038InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1038LowerChecked :
    lowerCheck 24 leaf1038Box leaf1038Inputs = true := by
  rfl'

private theorem leaf1038CoversExact : CoversExact 8
    leaf1038Box leaf1038Certificate leaf1038InnerLog leaf1038Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi106RoundedFacts
    innerPair17RoundedFacts leaf1038RoundedFacts (by rfl)

private theorem leaf1038FlatSound : Sound leaf1038Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1038CertificateValid
    leaf1038InnerLogValid leaf1038CoversExact leaf1038LowerChecked

private noncomputable def leaf1039Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1039Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435601/268435456) }, vSqrt := { lower := (65529/65536), upper := (4194312/4194229) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (342322641/268435456) }, upper := { exponent := 0, mantissa := (331/256) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388541/8388458) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf1039InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1039LocalValidity :
    LeafFacts leaf1039Box leaf1039Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1039Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194312/4194229) }) = true
      norm_num [leaf1039Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1039CertificateValid :
    WideCertificateValid leaf1039Box leaf1039Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi131ValidityFacts
    leaf1039LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1039CoverageChecked :
    coverageCheck (innerAD leaf1039Box) leaf1039InnerLog = true := by
  rfl'

private theorem leaf1039InnerLogValid :
    leaf1039InnerLog.Valid 8 (innerAD leaf1039Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1039CoverageChecked

private noncomputable def leaf1039InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1039InputLogOnePlusV_eq :
    leaf1039InputLogOnePlusV = outerEnclosure 24
      (leaf1039Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1039RoundedFacts : LeafRoundedFacts 8
    leaf1039Certificate.logOnePlusV leaf1039InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1039InputLogOnePlusV_eq }

private noncomputable def leaf1039Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi131InputQChi innerPair16Input
    leaf1039InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1039LowerChecked :
    lowerCheck 24 leaf1039Box leaf1039Inputs = true := by
  rfl'

private theorem leaf1039CoversExact : CoversExact 8
    leaf1039Box leaf1039Certificate leaf1039InnerLog leaf1039Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi131RoundedFacts
    innerPair16RoundedFacts leaf1039RoundedFacts (by rfl)

private theorem leaf1039FlatSound : Sound leaf1039Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1039CertificateValid
    leaf1039InnerLogValid leaf1039CoversExact leaf1039LowerChecked

private noncomputable def leaf1040Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1040Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435603/268435456) }, vSqrt := { lower := (65529/65536), upper := (2097156/2097113) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (345402643/268435456) }, upper := { exponent := 0, mantissa := (167/128) } }, logOuter := sk98LogOuterCertificate, logK := sk98LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4194269/4194226) } }, logDArg := sk98LogDArgCertificate }

private noncomputable def leaf1040InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1040LocalValidity :
    LeafFacts leaf1040Box leaf1040Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1040Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2097156/2097113) }) = true
      norm_num [leaf1040Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1040CertificateValid :
    WideCertificateValid leaf1040Box leaf1040Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk98ValidityFacts chi132ValidityFacts
    leaf1040LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1040CoverageChecked :
    coverageCheck (innerAD leaf1040Box) leaf1040InnerLog = true := by
  rfl'

private theorem leaf1040InnerLogValid :
    leaf1040InnerLog.Valid 8 (innerAD leaf1040Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1040CoverageChecked

private noncomputable def leaf1040InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1040InputLogOnePlusV_eq :
    leaf1040InputLogOnePlusV = outerEnclosure 24
      (leaf1040Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1040RoundedFacts : LeafRoundedFacts 8
    leaf1040Certificate.logOnePlusV leaf1040InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1040InputLogOnePlusV_eq }

private noncomputable def leaf1040Inputs : Inputs :=
  inputsOfCaches globalInput sk98RoundedInputs
    chi132InputQChi innerPair16Input
    leaf1040InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1040LowerChecked :
    lowerCheck 24 leaf1040Box leaf1040Inputs = true := by
  rfl'

private theorem leaf1040CoversExact : CoversExact 8
    leaf1040Box leaf1040Certificate leaf1040InnerLog leaf1040Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk98RoundedFacts chi132RoundedFacts
    innerPair16RoundedFacts leaf1040RoundedFacts (by rfl)

private theorem leaf1040FlatSound : Sound leaf1040Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1040CertificateValid
    leaf1040InnerLogValid leaf1040CoversExact leaf1040LowerChecked

private noncomputable def leaf1041Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf1041Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435673/268435456) }, vSqrt := { lower := (32765/32768), upper := (1973792/1973751) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (348482577/268435456) }, upper := { exponent := 0, mantissa := (2713/2048) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (3947543/3947502) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf1041InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1041LocalValidity :
    LeafFacts leaf1041Box leaf1041Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1041Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1973792/1973751) }) = true
      norm_num [leaf1041Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1041CertificateValid :
    WideCertificateValid leaf1041Box leaf1041Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi106ValidityFacts
    leaf1041LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1041CoverageChecked :
    coverageCheck (innerAD leaf1041Box) leaf1041InnerLog = true := by
  rfl'

private theorem leaf1041InnerLogValid :
    leaf1041InnerLog.Valid 8 (innerAD leaf1041Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1041CoverageChecked

private noncomputable def leaf1041InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1041InputLogOnePlusV_eq :
    leaf1041InputLogOnePlusV = outerEnclosure 24
      (leaf1041Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1041RoundedFacts : LeafRoundedFacts 8
    leaf1041Certificate.logOnePlusV leaf1041InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1041InputLogOnePlusV_eq }

private noncomputable def leaf1041Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi106InputQChi innerPair17Input
    leaf1041InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1041LowerChecked :
    lowerCheck 24 leaf1041Box leaf1041Inputs = true := by
  rfl'

private theorem leaf1041CoversExact : CoversExact 8
    leaf1041Box leaf1041Certificate leaf1041InnerLog leaf1041Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi106RoundedFacts
    innerPair17RoundedFacts leaf1041RoundedFacts (by rfl)

private theorem leaf1041FlatSound : Sound leaf1041Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1041CertificateValid
    leaf1041InnerLogValid leaf1041CoversExact leaf1041LowerChecked

private noncomputable def leaf1042Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (13/128), chiHi := (7/64) }

private noncomputable def leaf1042Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435675/268435456) }, vSqrt := { lower := (65529/65536), upper := (1048577/1048555) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (349334491/268435456) }, upper := { exponent := 0, mantissa := (85/64) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi106LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1048566/1048555) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf1042InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1042LocalValidity :
    LeafFacts leaf1042Box leaf1042Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1042Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1048577/1048555) }) = true
      norm_num [leaf1042Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1042CertificateValid :
    WideCertificateValid leaf1042Box leaf1042Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi106ValidityFacts
    leaf1042LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1042CoverageChecked :
    coverageCheck (innerAD leaf1042Box) leaf1042InnerLog = true := by
  rfl'

private theorem leaf1042InnerLogValid :
    leaf1042InnerLog.Valid 8 (innerAD leaf1042Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1042CoverageChecked

private noncomputable def leaf1042InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1042InputLogOnePlusV_eq :
    leaf1042InputLogOnePlusV = outerEnclosure 24
      (leaf1042Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1042RoundedFacts : LeafRoundedFacts 8
    leaf1042Certificate.logOnePlusV leaf1042InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1042InputLogOnePlusV_eq }

private noncomputable def leaf1042Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi106InputQChi innerPair17Input
    leaf1042InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1042LowerChecked :
    lowerCheck 24 leaf1042Box leaf1042Inputs = true := by
  rfl'

private theorem leaf1042CoversExact : CoversExact 8
    leaf1042Box leaf1042Certificate leaf1042InnerLog leaf1042Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi106RoundedFacts
    innerPair17RoundedFacts leaf1042RoundedFacts (by rfl)

private theorem leaf1042FlatSound : Sound leaf1042Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1042CertificateValid
    leaf1042InnerLogValid leaf1042CoversExact leaf1042LowerChecked

private noncomputable def leaf1043Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1043Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435671/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107469) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (352807691/268435456) }, upper := { exponent := 0, mantissa := (5491/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216397/134214938) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1043InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1043LocalValidity :
    LeafFacts leaf1043Box leaf1043Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1043Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107469) }) = true
      norm_num [leaf1043Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1043CertificateValid :
    WideCertificateValid leaf1043Box leaf1043Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi98ValidityFacts
    leaf1043LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1043CoverageChecked :
    coverageCheck (innerAD leaf1043Box) leaf1043InnerLog = true := by
  rfl'

private theorem leaf1043InnerLogValid :
    leaf1043InnerLog.Valid 8 (innerAD leaf1043Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1043CoverageChecked

private noncomputable def leaf1043InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1043InputLogOnePlusV_eq :
    leaf1043InputLogOnePlusV = outerEnclosure 24
      (leaf1043Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1043RoundedFacts : LeafRoundedFacts 8
    leaf1043Certificate.logOnePlusV leaf1043InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1043InputLogOnePlusV_eq }

private noncomputable def leaf1043Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi98InputQChi innerPair21Input
    leaf1043InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1043LowerChecked :
    lowerCheck 24 leaf1043Box leaf1043Inputs = true := by
  rfl'

private theorem leaf1043CoversExact : CoversExact 8
    leaf1043Box leaf1043Certificate leaf1043InnerLog leaf1043Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi98RoundedFacts
    innerPair21RoundedFacts leaf1043RoundedFacts (by rfl)

private theorem leaf1043FlatSound : Sound leaf1043Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1043CertificateValid
    leaf1043InnerLogValid leaf1043CoversExact leaf1043LowerChecked

private noncomputable def leaf1044Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1044Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435673/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553727) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (353725137/268435456) }, upper := { exponent := 0, mantissa := (2753/2048) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67108191/67107454) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf1044InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1044LocalValidity :
    LeafFacts leaf1044Box leaf1044Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1044Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553727) }) = true
      norm_num [leaf1044Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1044CertificateValid :
    WideCertificateValid leaf1044Box leaf1044Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi98ValidityFacts
    leaf1044LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1044CoverageChecked :
    coverageCheck (innerAD leaf1044Box) leaf1044InnerLog = true := by
  rfl'

private theorem leaf1044InnerLogValid :
    leaf1044InnerLog.Valid 8 (innerAD leaf1044Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1044CoverageChecked

private noncomputable def leaf1044InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1044InputLogOnePlusV_eq :
    leaf1044InputLogOnePlusV = outerEnclosure 24
      (leaf1044Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1044RoundedFacts : LeafRoundedFacts 8
    leaf1044Certificate.logOnePlusV leaf1044InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1044InputLogOnePlusV_eq }

private noncomputable def leaf1044Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi98InputQChi innerPair21Input
    leaf1044InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1044LowerChecked :
    lowerCheck 24 leaf1044Box leaf1044Inputs = true := by
  rfl'

private theorem leaf1044CoversExact : CoversExact 8
    leaf1044Box leaf1044Certificate leaf1044InnerLog leaf1044Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi98RoundedFacts
    innerPair21RoundedFacts leaf1044RoundedFacts (by rfl)

private theorem leaf1044FlatSound : Sound leaf1044Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1044CertificateValid
    leaf1044InnerLogValid leaf1044CoversExact leaf1044LowerChecked

private noncomputable def leaf1045Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf1045Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435673/268435456) }, vSqrt := { lower := (32765/32768), upper := (4194308/4194211) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (358836633/268435456) }, upper := { exponent := 0, mantissa := (349/256) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388519/8388422) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1045InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1045LocalValidity :
    LeafFacts leaf1045Box leaf1045Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1045Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194308/4194211) }) = true
      norm_num [leaf1045Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1045CertificateValid :
    WideCertificateValid leaf1045Box leaf1045Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi99ValidityFacts
    leaf1045LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1045CoverageChecked :
    coverageCheck (innerAD leaf1045Box) leaf1045InnerLog = true := by
  rfl'

private theorem leaf1045InnerLogValid :
    leaf1045InnerLog.Valid 8 (innerAD leaf1045Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1045CoverageChecked

private noncomputable def leaf1045InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629275/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1045InputLogOnePlusV_eq :
    leaf1045InputLogOnePlusV = outerEnclosure 24
      (leaf1045Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1045RoundedFacts : LeafRoundedFacts 8
    leaf1045Certificate.logOnePlusV leaf1045InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1045InputLogOnePlusV_eq }

private noncomputable def leaf1045Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi99InputQChi innerPair21Input
    leaf1045InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1045LowerChecked :
    lowerCheck 24 leaf1045Box leaf1045Inputs = true := by
  rfl'

private theorem leaf1045CoversExact : CoversExact 8
    leaf1045Box leaf1045Certificate leaf1045InnerLog leaf1045Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi99RoundedFacts
    innerPair21RoundedFacts leaf1045RoundedFacts (by rfl)

private theorem leaf1045FlatSound : Sound leaf1045Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1045CertificateValid
    leaf1045InnerLogValid leaf1045CoversExact leaf1045LowerChecked

private noncomputable def leaf1046Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf1046Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435675/268435456) }, vSqrt := { lower := (32765/32768), upper := (2097154/2097105) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (359819611/268435456) }, upper := { exponent := 0, mantissa := (175/128) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4194259/4194210) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf1046InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1046LocalValidity :
    LeafFacts leaf1046Box leaf1046Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1046Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2097154/2097105) }) = true
      norm_num [leaf1046Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1046CertificateValid :
    WideCertificateValid leaf1046Box leaf1046Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi99ValidityFacts
    leaf1046LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1046CoverageChecked :
    coverageCheck (innerAD leaf1046Box) leaf1046InnerLog = true := by
  rfl'

private theorem leaf1046InnerLogValid :
    leaf1046InnerLog.Valid 8 (innerAD leaf1046Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1046CoverageChecked

private noncomputable def leaf1046InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1046InputLogOnePlusV_eq :
    leaf1046InputLogOnePlusV = outerEnclosure 24
      (leaf1046Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1046RoundedFacts : LeafRoundedFacts 8
    leaf1046Certificate.logOnePlusV leaf1046InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1046InputLogOnePlusV_eq }

private noncomputable def leaf1046Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi99InputQChi innerPair21Input
    leaf1046InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1046LowerChecked :
    lowerCheck 24 leaf1046Box leaf1046Inputs = true := by
  rfl'

private theorem leaf1046CoversExact : CoversExact 8
    leaf1046Box leaf1046Certificate leaf1046InnerLog leaf1046Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi99RoundedFacts
    innerPair21RoundedFacts leaf1046RoundedFacts (by rfl)

private theorem leaf1046FlatSound : Sound leaf1046Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1046CertificateValid
    leaf1046InnerLogValid leaf1046CoversExact leaf1046LowerChecked

private noncomputable def leaf1047Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1047Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435675/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67107439) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (354642583/268435456) }, upper := { exponent := 0, mantissa := (5521/4096) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134216367/134214878) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf1047InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1047LocalValidity :
    LeafFacts leaf1047Box leaf1047Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1047Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67107439) }) = true
      norm_num [leaf1047Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1047CertificateValid :
    WideCertificateValid leaf1047Box leaf1047Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi98ValidityFacts
    leaf1047LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1047CoverageChecked :
    coverageCheck (innerAD leaf1047Box) leaf1047InnerLog = true := by
  rfl'

private theorem leaf1047InnerLogValid :
    leaf1047InnerLog.Valid 8 (innerAD leaf1047Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1047CoverageChecked

private noncomputable def leaf1047InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1047InputLogOnePlusV_eq :
    leaf1047InputLogOnePlusV = outerEnclosure 24
      (leaf1047Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1047RoundedFacts : LeafRoundedFacts 8
    leaf1047Certificate.logOnePlusV leaf1047InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1047InputLogOnePlusV_eq }

private noncomputable def leaf1047Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi98InputQChi innerPair21Input
    leaf1047InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1047LowerChecked :
    lowerCheck 24 leaf1047Box leaf1047Inputs = true := by
  rfl'

private theorem leaf1047CoversExact : CoversExact 8
    leaf1047Box leaf1047Certificate leaf1047InnerLog leaf1047Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi98RoundedFacts
    innerPair21RoundedFacts leaf1047RoundedFacts (by rfl)

private theorem leaf1047FlatSound : Sound leaf1047Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1047CertificateValid
    leaf1047InnerLogValid leaf1047CoversExact leaf1047LowerChecked

private noncomputable def leaf1048Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1048Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435677/268435456) }, vSqrt := { lower := (65529/65536), upper := (2097154/2097107) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (355560029/268435456) }, upper := { exponent := 0, mantissa := (173/128) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4194261/4194214) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf1048InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1048LocalValidity :
    LeafFacts leaf1048Box leaf1048Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1048Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2097154/2097107) }) = true
      norm_num [leaf1048Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1048CertificateValid :
    WideCertificateValid leaf1048Box leaf1048Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi98ValidityFacts
    leaf1048LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1048CoverageChecked :
    coverageCheck (innerAD leaf1048Box) leaf1048InnerLog = true := by
  rfl'

private theorem leaf1048InnerLogValid :
    leaf1048InnerLog.Valid 8 (innerAD leaf1048Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1048CoverageChecked

private noncomputable def leaf1048InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1048InputLogOnePlusV_eq :
    leaf1048InputLogOnePlusV = outerEnclosure 24
      (leaf1048Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1048RoundedFacts : LeafRoundedFacts 8
    leaf1048Certificate.logOnePlusV leaf1048InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1048InputLogOnePlusV_eq }

private noncomputable def leaf1048Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi98InputQChi innerPair21Input
    leaf1048InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1048LowerChecked :
    lowerCheck 24 leaf1048Box leaf1048Inputs = true := by
  rfl'

private theorem leaf1048CoversExact : CoversExact 8
    leaf1048Box leaf1048Certificate leaf1048InnerLog leaf1048Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi98RoundedFacts
    innerPair21RoundedFacts leaf1048RoundedFacts (by rfl)

private theorem leaf1048FlatSound : Sound leaf1048Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1048CertificateValid
    leaf1048InnerLogValid leaf1048CoversExact leaf1048LowerChecked

private noncomputable def leaf1049Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf1049Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435677/268435456) }, vSqrt := { lower := (32765/32768), upper := (4194308/4194209) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (360802589/268435456) }, upper := { exponent := 0, mantissa := (351/256) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388517/8388418) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf1049InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1049LocalValidity :
    LeafFacts leaf1049Box leaf1049Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1049Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194308/4194209) }) = true
      norm_num [leaf1049Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1049CertificateValid :
    WideCertificateValid leaf1049Box leaf1049Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi99ValidityFacts
    leaf1049LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1049CoverageChecked :
    coverageCheck (innerAD leaf1049Box) leaf1049InnerLog = true := by
  rfl'

private theorem leaf1049InnerLogValid :
    leaf1049InnerLog.Valid 8 (innerAD leaf1049Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1049CoverageChecked

private noncomputable def leaf1049InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1049InputLogOnePlusV_eq :
    leaf1049InputLogOnePlusV = outerEnclosure 24
      (leaf1049Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1049RoundedFacts : LeafRoundedFacts 8
    leaf1049Certificate.logOnePlusV leaf1049InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1049InputLogOnePlusV_eq }

private noncomputable def leaf1049Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi99InputQChi innerPair21Input
    leaf1049InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1049LowerChecked :
    lowerCheck 24 leaf1049Box leaf1049Inputs = true := by
  rfl'

private theorem leaf1049CoversExact : CoversExact 8
    leaf1049Box leaf1049Certificate leaf1049InnerLog leaf1049Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi99RoundedFacts
    innerPair21RoundedFacts leaf1049RoundedFacts (by rfl)

private theorem leaf1049FlatSound : Sound leaf1049Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1049CertificateValid
    leaf1049InnerLogValid leaf1049CoversExact leaf1049LowerChecked

private noncomputable def leaf1050Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (15/128), chiHi := (1/8) }

private noncomputable def leaf1050Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435679/268435456) }, vSqrt := { lower := (65529/65536), upper := (1048577/1048552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (361785567/268435456) }, upper := { exponent := 0, mantissa := (11/8) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi99LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2097129/2097104) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf1050InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1050LocalValidity :
    LeafFacts leaf1050Box leaf1050Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1050Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1048577/1048552) }) = true
      norm_num [leaf1050Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1050CertificateValid :
    WideCertificateValid leaf1050Box leaf1050Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi99ValidityFacts
    leaf1050LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1050CoverageChecked :
    coverageCheck (innerAD leaf1050Box) leaf1050InnerLog = true := by
  rfl'

private theorem leaf1050InnerLogValid :
    leaf1050InnerLog.Valid 8 (innerAD leaf1050Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1050CoverageChecked

private noncomputable def leaf1050InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1050InputLogOnePlusV_eq :
    leaf1050InputLogOnePlusV = outerEnclosure 24
      (leaf1050Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1050RoundedFacts : LeafRoundedFacts 8
    leaf1050Certificate.logOnePlusV leaf1050InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1050InputLogOnePlusV_eq }

private noncomputable def leaf1050Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi99InputQChi innerPair21Input
    leaf1050InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1050LowerChecked :
    lowerCheck 24 leaf1050Box leaf1050Inputs = true := by
  rfl'

private theorem leaf1050CoversExact : CoversExact 8
    leaf1050Box leaf1050Certificate leaf1050InnerLog leaf1050Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi99RoundedFacts
    innerPair21RoundedFacts leaf1050RoundedFacts (by rfl)

private theorem leaf1050FlatSound : Sound leaf1050Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1050CertificateValid
    leaf1050InnerLogValid leaf1050CoversExact leaf1050LowerChecked

private noncomputable def component24Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component24Node0_sound : Sound component24Node0Box :=
  sound_of_literal_split component24Node0Box leaf1000Box leaf1001Box
    .k (45/16) (by rfl) (by rfl)
    leaf1000FlatSound leaf1001FlatSound

private noncomputable def component24Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component24Node1_sound : Sound component24Node1Box :=
  sound_of_literal_split component24Node1Box leaf1002Box leaf1003Box
    .k (45/16) (by rfl) (by rfl)
    leaf1002FlatSound leaf1003FlatSound

private noncomputable def component24Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component24Node2_sound : Sound component24Node2Box :=
  sound_of_literal_split component24Node2Box component24Node0Box component24Node1Box
    .chi (9/128) (by rfl) (by rfl)
    component24Node0_sound component24Node1_sound

private noncomputable def component24Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component24Node3_sound : Sound component24Node3Box :=
  sound_of_literal_split component24Node3Box leaf1004Box leaf1005Box
    .chi (11/128) (by rfl) (by rfl)
    leaf1004FlatSound leaf1005FlatSound

private noncomputable def component24Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component24Node4_sound : Sound component24Node4Box :=
  sound_of_literal_split component24Node4Box leaf1006Box leaf1007Box
    .chi (11/128) (by rfl) (by rfl)
    leaf1006FlatSound leaf1007FlatSound

private noncomputable def component24Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component24Node5_sound : Sound component24Node5Box :=
  sound_of_literal_split component24Node5Box component24Node3Box component24Node4Box
    .k (45/16) (by rfl) (by rfl)
    component24Node3_sound component24Node4_sound

private noncomputable def component24Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component24Node6_sound : Sound component24Node6Box :=
  sound_of_literal_split component24Node6Box component24Node2Box component24Node5Box
    .chi (5/64) (by rfl) (by rfl)
    component24Node2_sound component24Node5_sound

private noncomputable def component24Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component24Node7_sound : Sound component24Node7Box :=
  sound_of_literal_split component24Node7Box leaf1008Box leaf1009Box
    .k (47/16) (by rfl) (by rfl)
    leaf1008FlatSound leaf1009FlatSound

private noncomputable def component24Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component24Node8_sound : Sound component24Node8Box :=
  sound_of_literal_split component24Node8Box leaf1010Box leaf1011Box
    .k (47/16) (by rfl) (by rfl)
    leaf1010FlatSound leaf1011FlatSound

private noncomputable def component24Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component24Node9_sound : Sound component24Node9Box :=
  sound_of_literal_split component24Node9Box component24Node7Box component24Node8Box
    .chi (9/128) (by rfl) (by rfl)
    component24Node7_sound component24Node8_sound

private noncomputable def component24Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component24Node10_sound : Sound component24Node10Box :=
  sound_of_literal_split component24Node10Box leaf1013Box leaf1014Box
    .chi (21/256) (by rfl) (by rfl)
    leaf1013FlatSound leaf1014FlatSound

private noncomputable def component24Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component24Node11_sound : Sound component24Node11Box :=
  sound_of_literal_split component24Node11Box leaf1012Box component24Node10Box
    .k (47/16) (by rfl) (by rfl)
    leaf1012FlatSound component24Node10_sound

private noncomputable def component24Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component24Node12_sound : Sound component24Node12Box :=
  sound_of_literal_split component24Node12Box leaf1015Box leaf1016Box
    .chi (23/256) (by rfl) (by rfl)
    leaf1015FlatSound leaf1016FlatSound

private noncomputable def component24Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component24Node13_sound : Sound component24Node13Box :=
  sound_of_literal_split component24Node13Box leaf1017Box leaf1018Box
    .chi (23/256) (by rfl) (by rfl)
    leaf1017FlatSound leaf1018FlatSound

private noncomputable def component24Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component24Node14_sound : Sound component24Node14Box :=
  sound_of_literal_split component24Node14Box component24Node12Box component24Node13Box
    .k (47/16) (by rfl) (by rfl)
    component24Node12_sound component24Node13_sound

private noncomputable def component24Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component24Node15_sound : Sound component24Node15Box :=
  sound_of_literal_split component24Node15Box component24Node11Box component24Node14Box
    .chi (11/128) (by rfl) (by rfl)
    component24Node11_sound component24Node14_sound

private noncomputable def component24Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component24Node16_sound : Sound component24Node16Box :=
  sound_of_literal_split component24Node16Box component24Node9Box component24Node15Box
    .chi (5/64) (by rfl) (by rfl)
    component24Node9_sound component24Node15_sound

private noncomputable def component24Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component24Node17_sound : Sound component24Node17Box :=
  sound_of_literal_split component24Node17Box component24Node6Box component24Node16Box
    .k (23/8) (by rfl) (by rfl)
    component24Node6_sound component24Node16_sound

private noncomputable def component24Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component24Node18_sound : Sound component24Node18Box :=
  sound_of_literal_split component24Node18Box leaf1019Box leaf1020Box
    .k (89/32) (by rfl) (by rfl)
    leaf1019FlatSound leaf1020FlatSound

private noncomputable def component24Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component24Node19_sound : Sound component24Node19Box :=
  sound_of_literal_split component24Node19Box leaf1021Box leaf1022Box
    .k (89/32) (by rfl) (by rfl)
    leaf1021FlatSound leaf1022FlatSound

private noncomputable def component24Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component24Node20_sound : Sound component24Node20Box :=
  sound_of_literal_split component24Node20Box component24Node18Box component24Node19Box
    .chi (13/128) (by rfl) (by rfl)
    component24Node18_sound component24Node19_sound

private noncomputable def component24Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component24Node21_sound : Sound component24Node21Box :=
  sound_of_literal_split component24Node21Box leaf1023Box leaf1024Box
    .chi (25/256) (by rfl) (by rfl)
    leaf1023FlatSound leaf1024FlatSound

private noncomputable def component24Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component24Node22_sound : Sound component24Node22Box :=
  sound_of_literal_split component24Node22Box leaf1025Box leaf1026Box
    .k (91/32) (by rfl) (by rfl)
    leaf1025FlatSound leaf1026FlatSound

private noncomputable def component24Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component24Node23_sound : Sound component24Node23Box :=
  sound_of_literal_split component24Node23Box component24Node21Box component24Node22Box
    .chi (13/128) (by rfl) (by rfl)
    component24Node21_sound component24Node22_sound

private noncomputable def component24Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component24Node24_sound : Sound component24Node24Box :=
  sound_of_literal_split component24Node24Box component24Node20Box component24Node23Box
    .k (45/16) (by rfl) (by rfl)
    component24Node20_sound component24Node23_sound

private noncomputable def component24Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component24Node25_sound : Sound component24Node25Box :=
  sound_of_literal_split component24Node25Box leaf1027Box leaf1028Box
    .k (89/32) (by rfl) (by rfl)
    leaf1027FlatSound leaf1028FlatSound

private noncomputable def component24Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component24Node26_sound : Sound component24Node26Box :=
  sound_of_literal_split component24Node26Box leaf1029Box leaf1030Box
    .k (89/32) (by rfl) (by rfl)
    leaf1029FlatSound leaf1030FlatSound

private noncomputable def component24Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component24Node27_sound : Sound component24Node27Box :=
  sound_of_literal_split component24Node27Box component24Node25Box component24Node26Box
    .chi (15/128) (by rfl) (by rfl)
    component24Node25_sound component24Node26_sound

private noncomputable def component24Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component24Node28_sound : Sound component24Node28Box :=
  sound_of_literal_split component24Node28Box leaf1031Box leaf1032Box
    .k (91/32) (by rfl) (by rfl)
    leaf1031FlatSound leaf1032FlatSound

private noncomputable def component24Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component24Node29_sound : Sound component24Node29Box :=
  sound_of_literal_split component24Node29Box leaf1033Box leaf1034Box
    .k (91/32) (by rfl) (by rfl)
    leaf1033FlatSound leaf1034FlatSound

private noncomputable def component24Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component24Node30_sound : Sound component24Node30Box :=
  sound_of_literal_split component24Node30Box component24Node28Box component24Node29Box
    .chi (15/128) (by rfl) (by rfl)
    component24Node28_sound component24Node29_sound

private noncomputable def component24Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component24Node31_sound : Sound component24Node31Box :=
  sound_of_literal_split component24Node31Box component24Node27Box component24Node30Box
    .k (45/16) (by rfl) (by rfl)
    component24Node27_sound component24Node30_sound

private noncomputable def component24Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component24Node32_sound : Sound component24Node32Box :=
  sound_of_literal_split component24Node32Box component24Node24Box component24Node31Box
    .chi (7/64) (by rfl) (by rfl)
    component24Node24_sound component24Node31_sound

private noncomputable def component24Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component24Node33_sound : Sound component24Node33Box :=
  sound_of_literal_split component24Node33Box leaf1035Box leaf1036Box
    .chi (25/256) (by rfl) (by rfl)
    leaf1035FlatSound leaf1036FlatSound

private noncomputable def component24Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component24Node34_sound : Sound component24Node34Box :=
  sound_of_literal_split component24Node34Box leaf1037Box leaf1038Box
    .k (93/32) (by rfl) (by rfl)
    leaf1037FlatSound leaf1038FlatSound

private noncomputable def component24Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component24Node35_sound : Sound component24Node35Box :=
  sound_of_literal_split component24Node35Box component24Node33Box component24Node34Box
    .chi (13/128) (by rfl) (by rfl)
    component24Node33_sound component24Node34_sound

private noncomputable def component24Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component24Node36_sound : Sound component24Node36Box :=
  sound_of_literal_split component24Node36Box leaf1039Box leaf1040Box
    .chi (25/256) (by rfl) (by rfl)
    leaf1039FlatSound leaf1040FlatSound

private noncomputable def component24Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component24Node37_sound : Sound component24Node37Box :=
  sound_of_literal_split component24Node37Box leaf1041Box leaf1042Box
    .k (95/32) (by rfl) (by rfl)
    leaf1041FlatSound leaf1042FlatSound

private noncomputable def component24Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component24Node38_sound : Sound component24Node38Box :=
  sound_of_literal_split component24Node38Box component24Node36Box component24Node37Box
    .chi (13/128) (by rfl) (by rfl)
    component24Node36_sound component24Node37_sound

private noncomputable def component24Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component24Node39_sound : Sound component24Node39Box :=
  sound_of_literal_split component24Node39Box component24Node35Box component24Node38Box
    .k (47/16) (by rfl) (by rfl)
    component24Node35_sound component24Node38_sound

private noncomputable def component24Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component24Node40_sound : Sound component24Node40Box :=
  sound_of_literal_split component24Node40Box leaf1043Box leaf1044Box
    .k (93/32) (by rfl) (by rfl)
    leaf1043FlatSound leaf1044FlatSound

private noncomputable def component24Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component24Node41_sound : Sound component24Node41Box :=
  sound_of_literal_split component24Node41Box leaf1045Box leaf1046Box
    .k (93/32) (by rfl) (by rfl)
    leaf1045FlatSound leaf1046FlatSound

private noncomputable def component24Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component24Node42_sound : Sound component24Node42Box :=
  sound_of_literal_split component24Node42Box component24Node40Box component24Node41Box
    .chi (15/128) (by rfl) (by rfl)
    component24Node40_sound component24Node41_sound

private noncomputable def component24Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component24Node43_sound : Sound component24Node43Box :=
  sound_of_literal_split component24Node43Box leaf1047Box leaf1048Box
    .k (95/32) (by rfl) (by rfl)
    leaf1047FlatSound leaf1048FlatSound

private noncomputable def component24Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component24Node44_sound : Sound component24Node44Box :=
  sound_of_literal_split component24Node44Box leaf1049Box leaf1050Box
    .k (95/32) (by rfl) (by rfl)
    leaf1049FlatSound leaf1050FlatSound

private noncomputable def component24Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component24Node45_sound : Sound component24Node45Box :=
  sound_of_literal_split component24Node45Box component24Node43Box component24Node44Box
    .chi (15/128) (by rfl) (by rfl)
    component24Node43_sound component24Node44_sound

private noncomputable def component24Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component24Node46_sound : Sound component24Node46Box :=
  sound_of_literal_split component24Node46Box component24Node42Box component24Node45Box
    .k (47/16) (by rfl) (by rfl)
    component24Node42_sound component24Node45_sound

private noncomputable def component24Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component24Node47_sound : Sound component24Node47Box :=
  sound_of_literal_split component24Node47Box component24Node39Box component24Node46Box
    .chi (7/64) (by rfl) (by rfl)
    component24Node39_sound component24Node46_sound

private noncomputable def component24Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component24Node48_sound : Sound component24Node48Box :=
  sound_of_literal_split component24Node48Box component24Node32Box component24Node47Box
    .k (23/8) (by rfl) (by rfl)
    component24Node32_sound component24Node47_sound

noncomputable def component24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (1/16), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
theorem component24_sound : Sound component24Box :=
  sound_of_literal_split component24Box component24Node17Box component24Node48Box
    .chi (3/32) (by rfl) (by rfl)
    component24Node17_sound component24Node48_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
