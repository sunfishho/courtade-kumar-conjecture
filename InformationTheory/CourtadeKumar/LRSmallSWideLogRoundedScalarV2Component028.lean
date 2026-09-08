import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
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

private noncomputable def leaf1181Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1181Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435667/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717403136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (394223919/268435456) }, upper := { exponent := 0, mantissa := (6121/4096) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435896831/137434806272) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf1181InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1181LocalValidity :
    LeafFacts leaf1181Box leaf1181Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1181Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717403136) }) = true
      norm_num [leaf1181Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1181CertificateValid :
    WideCertificateValid leaf1181Box leaf1181Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi115ValidityFacts
    leaf1181LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1181CoverageChecked :
    coverageCheck (innerAD leaf1181Box) leaf1181InnerLog = true := by
  rfl'

private theorem leaf1181InnerLogValid :
    leaf1181InnerLog.Valid 8 (innerAD leaf1181Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1181CoverageChecked

private noncomputable def leaf1181InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814607/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1181InputLogOnePlusV_eq :
    leaf1181InputLogOnePlusV = outerEnclosure 24
      (leaf1181Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1181RoundedFacts : LeafRoundedFacts 8
    leaf1181Certificate.logOnePlusV leaf1181InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1181InputLogOnePlusV_eq }

private noncomputable def leaf1181Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi115InputQChi innerPair34Input
    leaf1181InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1181LowerChecked :
    lowerCheck 24 leaf1181Box leaf1181Inputs = true := by
  rfl'

private theorem leaf1181CoversExact : CoversExact 8
    leaf1181Box leaf1181Certificate leaf1181InnerLog leaf1181Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi115RoundedFacts
    innerPair34RoundedFacts leaf1181RoundedFacts (by rfl)

private theorem leaf1181FlatSound : Sound leaf1181Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1181CertificateValid
    leaf1181InnerLogValid leaf1181CoversExact leaf1181LowerChecked

private noncomputable def leaf1182Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1182Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435669/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717320192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (399466477/268435456) }, upper := { exponent := 0, mantissa := (3101/2048) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435813887/137434640384) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf1182InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1182LocalValidity :
    LeafFacts leaf1182Box leaf1182Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1182Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717320192) }) = true
      norm_num [leaf1182Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1182CertificateValid :
    WideCertificateValid leaf1182Box leaf1182Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi116ValidityFacts
    leaf1182LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1182CoverageChecked :
    coverageCheck (innerAD leaf1182Box) leaf1182InnerLog = true := by
  rfl'

private theorem leaf1182InnerLogValid :
    leaf1182InnerLog.Valid 8 (innerAD leaf1182Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1182CoverageChecked

private noncomputable def leaf1182InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453653/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1182InputLogOnePlusV_eq :
    leaf1182InputLogOnePlusV = outerEnclosure 24
      (leaf1182Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1182RoundedFacts : LeafRoundedFacts 8
    leaf1182Certificate.logOnePlusV leaf1182InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1182InputLogOnePlusV_eq }

private noncomputable def leaf1182Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi116InputQChi innerPair35Input
    leaf1182InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1182LowerChecked :
    lowerCheck 24 leaf1182Box leaf1182Inputs = true := by
  rfl'

private theorem leaf1182CoversExact : CoversExact 8
    leaf1182Box leaf1182Certificate leaf1182InnerLog leaf1182Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi116RoundedFacts
    innerPair35RoundedFacts leaf1182RoundedFacts (by rfl)

private theorem leaf1182FlatSound : Sound leaf1182Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1182CertificateValid
    leaf1182InnerLogValid leaf1182CoversExact leaf1182LowerChecked

private noncomputable def leaf1183Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1183Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435669/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905792512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (395796685/268435456) }, upper := { exponent := 0, mantissa := (3073/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811957077/45811585024) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf1183InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1183LocalValidity :
    LeafFacts leaf1183Box leaf1183Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1183Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905792512) }) = true
      norm_num [leaf1183Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1183CertificateValid :
    WideCertificateValid leaf1183Box leaf1183Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi115ValidityFacts
    leaf1183LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1183CoverageChecked :
    coverageCheck (innerAD leaf1183Box) leaf1183InnerLog = true := by
  rfl'

private theorem leaf1183InnerLogValid :
    leaf1183InnerLog.Valid 8 (innerAD leaf1183Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1183CoverageChecked

private noncomputable def leaf1183InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1183InputLogOnePlusV_eq :
    leaf1183InputLogOnePlusV = outerEnclosure 24
      (leaf1183Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1183RoundedFacts : LeafRoundedFacts 8
    leaf1183Certificate.logOnePlusV leaf1183InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1183InputLogOnePlusV_eq }

private noncomputable def leaf1183Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi115InputQChi innerPair35Input
    leaf1183InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1183LowerChecked :
    lowerCheck 24 leaf1183Box leaf1183Inputs = true := by
  rfl'

private theorem leaf1183CoversExact : CoversExact 8
    leaf1183Box leaf1183Certificate leaf1183InnerLog leaf1183Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi115RoundedFacts
    innerPair35RoundedFacts leaf1183RoundedFacts (by rfl)

private theorem leaf1183FlatSound : Sound leaf1183Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1183CertificateValid
    leaf1183InnerLogValid leaf1183CoversExact leaf1183LowerChecked

private noncomputable def leaf1184Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1184Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435671/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717293568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (401104775/268435456) }, upper := { exponent := 0, mantissa := (1557/1024) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435787263/137434587136) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf1184InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1184LocalValidity :
    LeafFacts leaf1184Box leaf1184Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1184Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717293568) }) = true
      norm_num [leaf1184Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1184CertificateValid :
    WideCertificateValid leaf1184Box leaf1184Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi116ValidityFacts
    leaf1184LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1184CoverageChecked :
    coverageCheck (innerAD leaf1184Box) leaf1184InnerLog = true := by
  rfl'

private theorem leaf1184InnerLogValid :
    leaf1184InnerLog.Valid 8 (innerAD leaf1184Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1184CoverageChecked

private noncomputable def leaf1184InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1184InputLogOnePlusV_eq :
    leaf1184InputLogOnePlusV = outerEnclosure 24
      (leaf1184Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1184RoundedFacts : LeafRoundedFacts 8
    leaf1184Certificate.logOnePlusV leaf1184InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1184InputLogOnePlusV_eq }

private noncomputable def leaf1184Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi116InputQChi innerPair35Input
    leaf1184InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1184LowerChecked :
    lowerCheck 24 leaf1184Box leaf1184Inputs = true := by
  rfl'

private theorem leaf1184CoversExact : CoversExact 8
    leaf1184Box leaf1184Certificate leaf1184InnerLog leaf1184Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi116RoundedFacts
    innerPair35RoundedFacts leaf1184RoundedFacts (by rfl)

private theorem leaf1184FlatSound : Sound leaf1184Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1184CertificateValid
    leaf1184InnerLogValid leaf1184CoversExact leaf1184LowerChecked

private noncomputable def leaf1185Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1185Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435671/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717237248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (404709035/268435456) }, upper := { exponent := 0, mantissa := (6283/4096) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435730943/137434474496) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf1185InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1185LocalValidity :
    LeafFacts leaf1185Box leaf1185Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1185Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717237248) }) = true
      norm_num [leaf1185Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1185CertificateValid :
    WideCertificateValid leaf1185Box leaf1185Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi117ValidityFacts
    leaf1185LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1185CoverageChecked :
    coverageCheck (innerAD leaf1185Box) leaf1185InnerLog = true := by
  rfl'

private theorem leaf1185InnerLogValid :
    leaf1185InnerLog.Valid 8 (innerAD leaf1185Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1185CoverageChecked

private noncomputable def leaf1185InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1185InputLogOnePlusV_eq :
    leaf1185InputLogOnePlusV = outerEnclosure 24
      (leaf1185Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1185RoundedFacts : LeafRoundedFacts 8
    leaf1185Certificate.logOnePlusV leaf1185InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1185InputLogOnePlusV_eq }

private noncomputable def leaf1185Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi117InputQChi innerPair40Input
    leaf1185InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1185LowerChecked :
    lowerCheck 24 leaf1185Box leaf1185Inputs = true := by
  rfl'

private theorem leaf1185CoversExact : CoversExact 8
    leaf1185Box leaf1185Certificate leaf1185InnerLog leaf1185Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi117RoundedFacts
    innerPair40RoundedFacts leaf1185RoundedFacts (by rfl)

private theorem leaf1185FlatSound : Sound leaf1185Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1185CertificateValid
    leaf1185InnerLogValid leaf1185CoversExact leaf1185LowerChecked

private noncomputable def leaf1186Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1186Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435673/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717154304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (409951593/268435456) }, upper := { exponent := 0, mantissa := (1591/1024) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435647999/137434308608) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf1186InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1186LocalValidity :
    LeafFacts leaf1186Box leaf1186Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1186Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717154304) }) = true
      norm_num [leaf1186Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1186CertificateValid :
    WideCertificateValid leaf1186Box leaf1186Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi118ValidityFacts
    leaf1186LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1186CoverageChecked :
    coverageCheck (innerAD leaf1186Box) leaf1186InnerLog = true := by
  rfl'

private theorem leaf1186InnerLogValid :
    leaf1186InnerLog.Valid 8 (innerAD leaf1186Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1186CoverageChecked

private noncomputable def leaf1186InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1186InputLogOnePlusV_eq :
    leaf1186InputLogOnePlusV = outerEnclosure 24
      (leaf1186Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1186RoundedFacts : LeafRoundedFacts 8
    leaf1186Certificate.logOnePlusV leaf1186InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1186InputLogOnePlusV_eq }

private noncomputable def leaf1186Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi118InputQChi innerPair40Input
    leaf1186InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1186LowerChecked :
    lowerCheck 24 leaf1186Box leaf1186Inputs = true := by
  rfl'

private theorem leaf1186CoversExact : CoversExact 8
    leaf1186Box leaf1186Certificate leaf1186InnerLog leaf1186Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi118RoundedFacts
    innerPair40RoundedFacts leaf1186RoundedFacts (by rfl)

private theorem leaf1186FlatSound : Sound leaf1186Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1186CertificateValid
    leaf1186InnerLogValid leaf1186CoversExact leaf1186LowerChecked

private noncomputable def leaf1187Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1187Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435673/268435456) }, vSqrt := { lower := (32765/32768), upper := (808452867/808437760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (406412865/268435456) }, upper := { exponent := 0, mantissa := (3155/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1616890627/1616875520) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf1187InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1187LocalValidity :
    LeafFacts leaf1187Box leaf1187Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1187Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (808452867/808437760) }) = true
      norm_num [leaf1187Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1187CertificateValid :
    WideCertificateValid leaf1187Box leaf1187Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi117ValidityFacts
    leaf1187LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1187CoverageChecked :
    coverageCheck (innerAD leaf1187Box) leaf1187InnerLog = true := by
  rfl'

private theorem leaf1187InnerLogValid :
    leaf1187InnerLog.Valid 8 (innerAD leaf1187Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1187CoverageChecked

private noncomputable def leaf1187InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1187InputLogOnePlusV_eq :
    leaf1187InputLogOnePlusV = outerEnclosure 24
      (leaf1187Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1187RoundedFacts : LeafRoundedFacts 8
    leaf1187Certificate.logOnePlusV leaf1187InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1187InputLogOnePlusV_eq }

private noncomputable def leaf1187Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi117InputQChi innerPair40Input
    leaf1187InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1187LowerChecked :
    lowerCheck 24 leaf1187Box leaf1187Inputs = true := by
  rfl'

private theorem leaf1187CoversExact : CoversExact 8
    leaf1187Box leaf1187Certificate leaf1187InnerLog leaf1187Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi117RoundedFacts
    innerPair40RoundedFacts leaf1187RoundedFacts (by rfl)

private theorem leaf1187FlatSound : Sound leaf1187Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1187CertificateValid
    leaf1187InnerLogValid leaf1187CoversExact leaf1187LowerChecked

private noncomputable def leaf1188Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1188Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435675/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905708544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (411720955/268435456) }, upper := { exponent := 0, mantissa := (799/512) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811873109/45811417088) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf1188InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1188LocalValidity :
    LeafFacts leaf1188Box leaf1188Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1188Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905708544) }) = true
      norm_num [leaf1188Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1188CertificateValid :
    WideCertificateValid leaf1188Box leaf1188Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi118ValidityFacts
    leaf1188LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1188CoverageChecked :
    coverageCheck (innerAD leaf1188Box) leaf1188InnerLog = true := by
  rfl'

private theorem leaf1188InnerLogValid :
    leaf1188InnerLog.Valid 8 (innerAD leaf1188Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1188CoverageChecked

private noncomputable def leaf1188InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf1188InputLogOnePlusV_eq :
    leaf1188InputLogOnePlusV = outerEnclosure 24
      (leaf1188Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1188RoundedFacts : LeafRoundedFacts 8
    leaf1188Certificate.logOnePlusV leaf1188InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1188InputLogOnePlusV_eq }

private noncomputable def leaf1188Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi118InputQChi innerPair40Input
    leaf1188InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1188LowerChecked :
    lowerCheck 24 leaf1188Box leaf1188Inputs = true := by
  rfl'

private theorem leaf1188CoversExact : CoversExact 8
    leaf1188Box leaf1188Certificate leaf1188InnerLog leaf1188Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi118RoundedFacts
    innerPair40RoundedFacts leaf1188RoundedFacts (by rfl)

private theorem leaf1188FlatSound : Sound leaf1188Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1188CertificateValid
    leaf1188InnerLogValid leaf1188CoversExact leaf1188LowerChecked

private noncomputable def leaf1189Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1189Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435671/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717351936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (397369451/268435456) }, upper := { exponent := 0, mantissa := (6171/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435845631/137434703872) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf1189InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1189LocalValidity :
    LeafFacts leaf1189Box leaf1189Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1189Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717351936) }) = true
      norm_num [leaf1189Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1189CertificateValid :
    WideCertificateValid leaf1189Box leaf1189Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi115ValidityFacts
    leaf1189LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1189CoverageChecked :
    coverageCheck (innerAD leaf1189Box) leaf1189InnerLog = true := by
  rfl'

private theorem leaf1189InnerLogValid :
    leaf1189InnerLog.Valid 8 (innerAD leaf1189Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1189CoverageChecked

private noncomputable def leaf1189InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907305/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1189InputLogOnePlusV_eq :
    leaf1189InputLogOnePlusV = outerEnclosure 24
      (leaf1189Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1189RoundedFacts : LeafRoundedFacts 8
    leaf1189Certificate.logOnePlusV leaf1189InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1189InputLogOnePlusV_eq }

private noncomputable def leaf1189Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi115InputQChi innerPair35Input
    leaf1189InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1189LowerChecked :
    lowerCheck 24 leaf1189Box leaf1189Inputs = true := by
  rfl'

private theorem leaf1189CoversExact : CoversExact 8
    leaf1189Box leaf1189Certificate leaf1189InnerLog leaf1189Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi115RoundedFacts
    innerPair35RoundedFacts leaf1189RoundedFacts (by rfl)

private theorem leaf1189FlatSound : Sound leaf1189Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1189CertificateValid
    leaf1189InnerLogValid leaf1189CoversExact leaf1189LowerChecked

private noncomputable def leaf1190Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1190Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435673/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905755648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (402743073/268435456) }, upper := { exponent := 0, mantissa := (3127/2048) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811920213/45811511296) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf1190InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1190LocalValidity :
    LeafFacts leaf1190Box leaf1190Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1190Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905755648) }) = true
      norm_num [leaf1190Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1190CertificateValid :
    WideCertificateValid leaf1190Box leaf1190Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi116ValidityFacts
    leaf1190LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1190CoverageChecked :
    coverageCheck (innerAD leaf1190Box) leaf1190InnerLog = true := by
  rfl'

private theorem leaf1190InnerLogValid :
    leaf1190InnerLog.Valid 8 (innerAD leaf1190Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1190CoverageChecked

private noncomputable def leaf1190InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814615/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1190InputLogOnePlusV_eq :
    leaf1190InputLogOnePlusV = outerEnclosure 24
      (leaf1190Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1190RoundedFacts : LeafRoundedFacts 8
    leaf1190Certificate.logOnePlusV leaf1190InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1190InputLogOnePlusV_eq }

private noncomputable def leaf1190Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi116InputQChi innerPair40Input
    leaf1190InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1190LowerChecked :
    lowerCheck 24 leaf1190Box leaf1190Inputs = true := by
  rfl'

private theorem leaf1190CoversExact : CoversExact 8
    leaf1190Box leaf1190Certificate leaf1190InnerLog leaf1190Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi116RoundedFacts
    innerPair40RoundedFacts leaf1190RoundedFacts (by rfl)

private theorem leaf1190FlatSound : Sound leaf1190Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1190CertificateValid
    leaf1190InnerLogValid leaf1190CoversExact leaf1190LowerChecked

private noncomputable def leaf1191Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1191Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435673/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717326336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (398942217/268435456) }, upper := { exponent := 0, mantissa := (1549/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435820031/137434652672) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf1191InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1191LocalValidity :
    LeafFacts leaf1191Box leaf1191Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1191Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717326336) }) = true
      norm_num [leaf1191Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1191CertificateValid :
    WideCertificateValid leaf1191Box leaf1191Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi115ValidityFacts
    leaf1191LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1191CoverageChecked :
    coverageCheck (innerAD leaf1191Box) leaf1191InnerLog = true := by
  rfl'

private theorem leaf1191InnerLogValid :
    leaf1191InnerLog.Valid 8 (innerAD leaf1191Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1191CoverageChecked

private noncomputable def leaf1191InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1191InputLogOnePlusV_eq :
    leaf1191InputLogOnePlusV = outerEnclosure 24
      (leaf1191Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1191RoundedFacts : LeafRoundedFacts 8
    leaf1191Certificate.logOnePlusV leaf1191InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1191InputLogOnePlusV_eq }

private noncomputable def leaf1191Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi115InputQChi innerPair35Input
    leaf1191InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1191LowerChecked :
    lowerCheck 24 leaf1191Box leaf1191Inputs = true := by
  rfl'

private theorem leaf1191CoversExact : CoversExact 8
    leaf1191Box leaf1191Certificate leaf1191InnerLog leaf1191Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi115RoundedFacts
    innerPair35RoundedFacts leaf1191RoundedFacts (by rfl)

private theorem leaf1191FlatSound : Sound leaf1191Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1191CertificateValid
    leaf1191InnerLogValid leaf1191CoversExact leaf1191LowerChecked

private noncomputable def leaf1192Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1192Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435675/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743448064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (404381371/268435456) }, upper := { exponent := 0, mantissa := (785/512) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487146803/27486896128) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf1192InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1192LocalValidity :
    LeafFacts leaf1192Box leaf1192Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1192Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743448064) }) = true
      norm_num [leaf1192Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1192CertificateValid :
    WideCertificateValid leaf1192Box leaf1192Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi116ValidityFacts
    leaf1192LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1192CoverageChecked :
    coverageCheck (innerAD leaf1192Box) leaf1192InnerLog = true := by
  rfl'

private theorem leaf1192InnerLogValid :
    leaf1192InnerLog.Valid 8 (innerAD leaf1192Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1192CoverageChecked

private noncomputable def leaf1192InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1192InputLogOnePlusV_eq :
    leaf1192InputLogOnePlusV = outerEnclosure 24
      (leaf1192Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1192RoundedFacts : LeafRoundedFacts 8
    leaf1192Certificate.logOnePlusV leaf1192InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1192InputLogOnePlusV_eq }

private noncomputable def leaf1192Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi116InputQChi innerPair40Input
    leaf1192InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1192LowerChecked :
    lowerCheck 24 leaf1192Box leaf1192Inputs = true := by
  rfl'

private theorem leaf1192CoversExact : CoversExact 8
    leaf1192Box leaf1192Certificate leaf1192InnerLog leaf1192Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi116RoundedFacts
    innerPair40RoundedFacts leaf1192RoundedFacts (by rfl)

private theorem leaf1192FlatSound : Sound leaf1192Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1192CertificateValid
    leaf1192InnerLogValid leaf1192CoversExact leaf1192LowerChecked

private noncomputable def leaf1193Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1193Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435675/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717181952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (408116695/268435456) }, upper := { exponent := 0, mantissa := (6337/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435675647/137434363904) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf1193InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1193LocalValidity :
    LeafFacts leaf1193Box leaf1193Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1193Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717181952) }) = true
      norm_num [leaf1193Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1193CertificateValid :
    WideCertificateValid leaf1193Box leaf1193Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi117ValidityFacts
    leaf1193LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1193CoverageChecked :
    coverageCheck (innerAD leaf1193Box) leaf1193InnerLog = true := by
  rfl'

private theorem leaf1193InnerLogValid :
    leaf1193InnerLog.Valid 8 (innerAD leaf1193Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1193CoverageChecked

private noncomputable def leaf1193InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1193InputLogOnePlusV_eq :
    leaf1193InputLogOnePlusV = outerEnclosure 24
      (leaf1193Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1193RoundedFacts : LeafRoundedFacts 8
    leaf1193Certificate.logOnePlusV leaf1193InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1193InputLogOnePlusV_eq }

private noncomputable def leaf1193Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi117InputQChi innerPair40Input
    leaf1193InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1193LowerChecked :
    lowerCheck 24 leaf1193Box leaf1193Inputs = true := by
  rfl'

private theorem leaf1193CoversExact : CoversExact 8
    leaf1193Box leaf1193Certificate leaf1193InnerLog leaf1193Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi117RoundedFacts
    innerPair40RoundedFacts leaf1193RoundedFacts (by rfl)

private theorem leaf1193FlatSound : Sound leaf1193Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1193CertificateValid
    leaf1193InnerLogValid leaf1193CoversExact leaf1193LowerChecked

private noncomputable def leaf1194Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1194Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435677/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743419392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (413490317/268435456) }, upper := { exponent := 0, mantissa := (1605/1024) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487118131/27486838784) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf1194InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf1194LocalValidity :
    LeafFacts leaf1194Box leaf1194Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1194Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743419392) }) = true
      norm_num [leaf1194Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1194CertificateValid :
    WideCertificateValid leaf1194Box leaf1194Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi118ValidityFacts
    leaf1194LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1194CoverageChecked :
    coverageCheck (innerAD leaf1194Box) leaf1194InnerLog = true := by
  rfl'

private theorem leaf1194InnerLogValid :
    leaf1194InnerLog.Valid 8 (innerAD leaf1194Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf1194CoverageChecked

private noncomputable def leaf1194InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1194InputLogOnePlusV_eq :
    leaf1194InputLogOnePlusV = outerEnclosure 24
      (leaf1194Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1194RoundedFacts : LeafRoundedFacts 8
    leaf1194Certificate.logOnePlusV leaf1194InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1194InputLogOnePlusV_eq }

private noncomputable def leaf1194Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi118InputQChi innerPair41Input
    leaf1194InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1194LowerChecked :
    lowerCheck 24 leaf1194Box leaf1194Inputs = true := by
  rfl'

private theorem leaf1194CoversExact : CoversExact 8
    leaf1194Box leaf1194Certificate leaf1194InnerLog leaf1194Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi118RoundedFacts
    innerPair41RoundedFacts leaf1194RoundedFacts (by rfl)

private theorem leaf1194FlatSound : Sound leaf1194Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1194CertificateValid
    leaf1194InnerLogValid leaf1194CoversExact leaf1194LowerChecked

private noncomputable def leaf1195Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1195Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435677/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717154304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (409820525/268435456) }, upper := { exponent := 0, mantissa := (1591/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435647999/137434308608) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf1195InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1195LocalValidity :
    LeafFacts leaf1195Box leaf1195Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1195Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717154304) }) = true
      norm_num [leaf1195Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1195CertificateValid :
    WideCertificateValid leaf1195Box leaf1195Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi117ValidityFacts
    leaf1195LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1195CoverageChecked :
    coverageCheck (innerAD leaf1195Box) leaf1195InnerLog = true := by
  rfl'

private theorem leaf1195InnerLogValid :
    leaf1195InnerLog.Valid 8 (innerAD leaf1195Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1195CoverageChecked

private noncomputable def leaf1195InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1195InputLogOnePlusV_eq :
    leaf1195InputLogOnePlusV = outerEnclosure 24
      (leaf1195Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1195RoundedFacts : LeafRoundedFacts 8
    leaf1195Certificate.logOnePlusV leaf1195InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1195InputLogOnePlusV_eq }

private noncomputable def leaf1195Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi117InputQChi innerPair40Input
    leaf1195InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1195LowerChecked :
    lowerCheck 24 leaf1195Box leaf1195Inputs = true := by
  rfl'

private theorem leaf1195CoversExact : CoversExact 8
    leaf1195Box leaf1195Certificate leaf1195InnerLog leaf1195Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi117RoundedFacts
    innerPair40RoundedFacts leaf1195RoundedFacts (by rfl)

private theorem leaf1195FlatSound : Sound leaf1195Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1195CertificateValid
    leaf1195InnerLogValid leaf1195CoversExact leaf1195LowerChecked

private noncomputable def leaf1196Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1196Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435679/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717068288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (415259679/268435456) }, upper := { exponent := 0, mantissa := (403/256) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435561983/137434136576) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf1196InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf1196LocalValidity :
    LeafFacts leaf1196Box leaf1196Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1196Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717068288) }) = true
      norm_num [leaf1196Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1196CertificateValid :
    WideCertificateValid leaf1196Box leaf1196Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi118ValidityFacts
    leaf1196LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1196CoverageChecked :
    coverageCheck (innerAD leaf1196Box) leaf1196InnerLog = true := by
  rfl'

private theorem leaf1196InnerLogValid :
    leaf1196InnerLog.Valid 8 (innerAD leaf1196Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf1196CoverageChecked

private noncomputable def leaf1196InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1196InputLogOnePlusV_eq :
    leaf1196InputLogOnePlusV = outerEnclosure 24
      (leaf1196Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1196RoundedFacts : LeafRoundedFacts 8
    leaf1196Certificate.logOnePlusV leaf1196InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1196InputLogOnePlusV_eq }

private noncomputable def leaf1196Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi118InputQChi innerPair41Input
    leaf1196InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1196LowerChecked :
    lowerCheck 24 leaf1196Box leaf1196Inputs = true := by
  rfl'

private theorem leaf1196CoversExact : CoversExact 8
    leaf1196Box leaf1196Certificate leaf1196InnerLog leaf1196Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi118RoundedFacts
    innerPair41RoundedFacts leaf1196RoundedFacts (by rfl)

private theorem leaf1196FlatSound : Sound leaf1196Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1196CertificateValid
    leaf1196InnerLogValid leaf1196CoversExact leaf1196LowerChecked

private noncomputable def leaf1197Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1197Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435675/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743414272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (415194151/268435456) }, upper := { exponent := 0, mantissa := (6445/4096) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487113011/27486828544) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf1197InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf1197LocalValidity :
    LeafFacts leaf1197Box leaf1197Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1197Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743414272) }) = true
      norm_num [leaf1197Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1197CertificateValid :
    WideCertificateValid leaf1197Box leaf1197Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi119ValidityFacts
    leaf1197LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1197CoverageChecked :
    coverageCheck (innerAD leaf1197Box) leaf1197InnerLog = true := by
  rfl'

private theorem leaf1197InnerLogValid :
    leaf1197InnerLog.Valid 8 (innerAD leaf1197Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf1197CoverageChecked

private noncomputable def leaf1197InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1197InputLogOnePlusV_eq :
    leaf1197InputLogOnePlusV = outerEnclosure 24
      (leaf1197Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1197RoundedFacts : LeafRoundedFacts 8
    leaf1197Certificate.logOnePlusV leaf1197InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1197InputLogOnePlusV_eq }

private noncomputable def leaf1197Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi119InputQChi innerPair41Input
    leaf1197InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1197LowerChecked :
    lowerCheck 24 leaf1197Box leaf1197Inputs = true := by
  rfl'

private theorem leaf1197CoversExact : CoversExact 8
    leaf1197Box leaf1197Certificate leaf1197InnerLog leaf1197Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi119RoundedFacts
    innerPair41RoundedFacts leaf1197RoundedFacts (by rfl)

private theorem leaf1197FlatSound : Sound leaf1197Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1197CertificateValid
    leaf1197InnerLogValid leaf1197CoversExact leaf1197LowerChecked

private noncomputable def leaf1198Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1198Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435677/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716988416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (420436709/268435456) }, upper := { exponent := 0, mantissa := (3263/2048) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435482111/137433976832) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf1198InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1198LocalValidity :
    LeafFacts leaf1198Box leaf1198Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1198Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716988416) }) = true
      norm_num [leaf1198Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1198CertificateValid :
    WideCertificateValid leaf1198Box leaf1198Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi120ValidityFacts
    leaf1198LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1198CoverageChecked :
    coverageCheck (innerAD leaf1198Box) leaf1198InnerLog = true := by
  rfl'

private theorem leaf1198InnerLogValid :
    leaf1198InnerLog.Valid 8 (innerAD leaf1198Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1198CoverageChecked

private noncomputable def leaf1198InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726829/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1198InputLogOnePlusV_eq :
    leaf1198InputLogOnePlusV = outerEnclosure 24
      (leaf1198Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1198RoundedFacts : LeafRoundedFacts 8
    leaf1198Certificate.logOnePlusV leaf1198InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1198InputLogOnePlusV_eq }

private noncomputable def leaf1198Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi120InputQChi innerPair50Input
    leaf1198InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1198LowerChecked :
    lowerCheck 24 leaf1198Box leaf1198Inputs = true := by
  rfl'

private theorem leaf1198CoversExact : CoversExact 8
    leaf1198Box leaf1198Certificate leaf1198InnerLog leaf1198Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi120RoundedFacts
    innerPair50RoundedFacts leaf1198RoundedFacts (by rfl)

private theorem leaf1198FlatSound : Sound leaf1198Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1198CertificateValid
    leaf1198InnerLogValid leaf1198CoversExact leaf1198LowerChecked

private noncomputable def leaf1199Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1199Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435677/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717041664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (417029045/268435456) }, upper := { exponent := 0, mantissa := (3237/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435535359/137434083328) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf1199InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf1199LocalValidity :
    LeafFacts leaf1199Box leaf1199Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1199Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717041664) }) = true
      norm_num [leaf1199Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1199CertificateValid :
    WideCertificateValid leaf1199Box leaf1199Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi119ValidityFacts
    leaf1199LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1199CoverageChecked :
    coverageCheck (innerAD leaf1199Box) leaf1199InnerLog = true := by
  rfl'

private theorem leaf1199InnerLogValid :
    leaf1199InnerLog.Valid 8 (innerAD leaf1199Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf1199CoverageChecked

private noncomputable def leaf1199InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1199InputLogOnePlusV_eq :
    leaf1199InputLogOnePlusV = outerEnclosure 24
      (leaf1199Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1199RoundedFacts : LeafRoundedFacts 8
    leaf1199Certificate.logOnePlusV leaf1199InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1199InputLogOnePlusV_eq }

private noncomputable def leaf1199Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi119InputQChi innerPair41Input
    leaf1199InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1199LowerChecked :
    lowerCheck 24 leaf1199Box leaf1199Inputs = true := by
  rfl'

private theorem leaf1199CoversExact : CoversExact 8
    leaf1199Box leaf1199Certificate leaf1199InnerLog leaf1199Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi119RoundedFacts
    innerPair41RoundedFacts leaf1199RoundedFacts (by rfl)

private theorem leaf1199FlatSound : Sound leaf1199Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1199CertificateValid
    leaf1199InnerLogValid leaf1199CoversExact leaf1199LowerChecked

private noncomputable def leaf1200Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1200Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435679/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716957696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (422337135/268435456) }, upper := { exponent := 0, mantissa := (1639/1024) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435451391/137433915392) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf1200InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1200LocalValidity :
    LeafFacts leaf1200Box leaf1200Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1200Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716957696) }) = true
      norm_num [leaf1200Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1200CertificateValid :
    WideCertificateValid leaf1200Box leaf1200Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi120ValidityFacts
    leaf1200LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1200CoverageChecked :
    coverageCheck (innerAD leaf1200Box) leaf1200InnerLog = true := by
  rfl'

private theorem leaf1200InnerLogValid :
    leaf1200InnerLog.Valid 8 (innerAD leaf1200Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1200CoverageChecked

private noncomputable def leaf1200InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1200InputLogOnePlusV_eq :
    leaf1200InputLogOnePlusV = outerEnclosure 24
      (leaf1200Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1200RoundedFacts : LeafRoundedFacts 8
    leaf1200Certificate.logOnePlusV leaf1200InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1200InputLogOnePlusV_eq }

private noncomputable def leaf1200Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi120InputQChi innerPair50Input
    leaf1200InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1200LowerChecked :
    lowerCheck 24 leaf1200Box leaf1200Inputs = true := by
  rfl'

private theorem leaf1200CoversExact : CoversExact 8
    leaf1200Box leaf1200Certificate leaf1200InnerLog leaf1200Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi120RoundedFacts
    innerPair50RoundedFacts leaf1200RoundedFacts (by rfl)

private theorem leaf1200FlatSound : Sound leaf1200Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1200CertificateValid
    leaf1200InnerLogValid leaf1200CoversExact leaf1200LowerChecked

private noncomputable def leaf1201Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1201Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435679/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716905472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (425679267/268435456) }, upper := { exponent := 0, mantissa := (6607/4096) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435399167/137433810944) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf1201InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1201LocalValidity :
    LeafFacts leaf1201Box leaf1201Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1201Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716905472) }) = true
      norm_num [leaf1201Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1201CertificateValid :
    WideCertificateValid leaf1201Box leaf1201Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi121ValidityFacts
    leaf1201LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1201CoverageChecked :
    coverageCheck (innerAD leaf1201Box) leaf1201InnerLog = true := by
  rfl'

private theorem leaf1201InnerLogValid :
    leaf1201InnerLog.Valid 8 (innerAD leaf1201Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1201CoverageChecked

private noncomputable def leaf1201InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629275/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1201InputLogOnePlusV_eq :
    leaf1201InputLogOnePlusV = outerEnclosure 24
      (leaf1201Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1201RoundedFacts : LeafRoundedFacts 8
    leaf1201Certificate.logOnePlusV leaf1201InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1201InputLogOnePlusV_eq }

private noncomputable def leaf1201Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi121InputQChi innerPair50Input
    leaf1201InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1201LowerChecked :
    lowerCheck 24 leaf1201Box leaf1201Inputs = true := by
  rfl'

private theorem leaf1201CoversExact : CoversExact 8
    leaf1201Box leaf1201Certificate leaf1201InnerLog leaf1201Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi121RoundedFacts
    innerPair50RoundedFacts leaf1201RoundedFacts (by rfl)

private theorem leaf1201FlatSound : Sound leaf1201Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1201CertificateValid
    leaf1201InnerLogValid leaf1201CoversExact leaf1201LowerChecked

private noncomputable def leaf1202Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1202Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435681/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716822528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (430921825/268435456) }, upper := { exponent := 0, mantissa := (209/128) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435316223/137433645056) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf1202InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf1202LocalValidity :
    LeafFacts leaf1202Box leaf1202Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1202Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716822528) }) = true
      norm_num [leaf1202Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1202CertificateValid :
    WideCertificateValid leaf1202Box leaf1202Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi122ValidityFacts
    leaf1202LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1202CoverageChecked :
    coverageCheck (innerAD leaf1202Box) leaf1202InnerLog = true := by
  rfl'

private theorem leaf1202InnerLogValid :
    leaf1202InnerLog.Valid 8 (innerAD leaf1202Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf1202CoverageChecked

private noncomputable def leaf1202InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629285/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1202InputLogOnePlusV_eq :
    leaf1202InputLogOnePlusV = outerEnclosure 24
      (leaf1202Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1202RoundedFacts : LeafRoundedFacts 8
    leaf1202Certificate.logOnePlusV leaf1202InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1202InputLogOnePlusV_eq }

private noncomputable def leaf1202Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi122InputQChi innerPair51Input
    leaf1202InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1202LowerChecked :
    lowerCheck 24 leaf1202Box leaf1202Inputs = true := by
  rfl'

private theorem leaf1202CoversExact : CoversExact 8
    leaf1202Box leaf1202Certificate leaf1202InnerLog leaf1202Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi122RoundedFacts
    innerPair51RoundedFacts leaf1202RoundedFacts (by rfl)

private theorem leaf1202FlatSound : Sound leaf1202Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1202CertificateValid
    leaf1202InnerLogValid leaf1202CoversExact leaf1202LowerChecked

private noncomputable def leaf1203Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1203Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435681/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905624576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (427645225/268435456) }, upper := { exponent := 0, mantissa := (3319/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811789141/45811249152) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf1203InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1203LocalValidity :
    LeafFacts leaf1203Box leaf1203Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1203Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905624576) }) = true
      norm_num [leaf1203Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1203CertificateValid :
    WideCertificateValid leaf1203Box leaf1203Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi121ValidityFacts
    leaf1203LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1203CoverageChecked :
    coverageCheck (innerAD leaf1203Box) leaf1203InnerLog = true := by
  rfl'

private theorem leaf1203InnerLogValid :
    leaf1203InnerLog.Valid 8 (innerAD leaf1203Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1203CoverageChecked

private noncomputable def leaf1203InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814639/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1203InputLogOnePlusV_eq :
    leaf1203InputLogOnePlusV = outerEnclosure 24
      (leaf1203Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1203RoundedFacts : LeafRoundedFacts 8
    leaf1203Certificate.logOnePlusV leaf1203InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1203InputLogOnePlusV_eq }

private noncomputable def leaf1203Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi121InputQChi innerPair50Input
    leaf1203InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1203LowerChecked :
    lowerCheck 24 leaf1203Box leaf1203Inputs = true := by
  rfl'

private theorem leaf1203CoversExact : CoversExact 8
    leaf1203Box leaf1203Certificate leaf1203InnerLog leaf1203Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi121RoundedFacts
    innerPair50RoundedFacts leaf1203RoundedFacts (by rfl)

private theorem leaf1203FlatSound : Sound leaf1203Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1203CertificateValid
    leaf1203InnerLogValid leaf1203CoversExact leaf1203LowerChecked

private noncomputable def leaf1204Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1204Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435683/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743357952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (432953315/268435456) }, upper := { exponent := 0, mantissa := (105/64) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487056691/27486715904) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf1204InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf1204LocalValidity :
    LeafFacts leaf1204Box leaf1204Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1204Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743357952) }) = true
      norm_num [leaf1204Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1204CertificateValid :
    WideCertificateValid leaf1204Box leaf1204Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi122ValidityFacts
    leaf1204LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1204CoverageChecked :
    coverageCheck (innerAD leaf1204Box) leaf1204InnerLog = true := by
  rfl'

private theorem leaf1204InnerLogValid :
    leaf1204InnerLog.Valid 8 (innerAD leaf1204Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf1204CoverageChecked

private noncomputable def leaf1204InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1204InputLogOnePlusV_eq :
    leaf1204InputLogOnePlusV = outerEnclosure 24
      (leaf1204Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1204RoundedFacts : LeafRoundedFacts 8
    leaf1204Certificate.logOnePlusV leaf1204InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1204InputLogOnePlusV_eq }

private noncomputable def leaf1204Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi122InputQChi innerPair51Input
    leaf1204InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1204LowerChecked :
    lowerCheck 24 leaf1204Box leaf1204Inputs = true := by
  rfl'

private theorem leaf1204CoversExact : CoversExact 8
    leaf1204Box leaf1204Certificate leaf1204InnerLog leaf1204Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi122RoundedFacts
    innerPair51RoundedFacts leaf1204RoundedFacts (by rfl)

private theorem leaf1204FlatSound : Sound leaf1204Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1204CertificateValid
    leaf1204InnerLogValid leaf1204CoversExact leaf1204LowerChecked

private noncomputable def leaf1205Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1205Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435679/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905670656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (418863939/268435456) }, upper := { exponent := 0, mantissa := (6503/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811835221/45811341312) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf1205InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf1205LocalValidity :
    LeafFacts leaf1205Box leaf1205Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1205Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905670656) }) = true
      norm_num [leaf1205Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1205CertificateValid :
    WideCertificateValid leaf1205Box leaf1205Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi119ValidityFacts
    leaf1205LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1205CoverageChecked :
    coverageCheck (innerAD leaf1205Box) leaf1205InnerLog = true := by
  rfl'

private theorem leaf1205InnerLogValid :
    leaf1205InnerLog.Valid 8 (innerAD leaf1205Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf1205CoverageChecked

private noncomputable def leaf1205InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814631/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1205InputLogOnePlusV_eq :
    leaf1205InputLogOnePlusV = outerEnclosure 24
      (leaf1205Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1205RoundedFacts : LeafRoundedFacts 8
    leaf1205Certificate.logOnePlusV leaf1205InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1205InputLogOnePlusV_eq }

private noncomputable def leaf1205Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi119InputQChi innerPair41Input
    leaf1205InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1205LowerChecked :
    lowerCheck 24 leaf1205Box leaf1205Inputs = true := by
  rfl'

private theorem leaf1205CoversExact : CoversExact 8
    leaf1205Box leaf1205Certificate leaf1205InnerLog leaf1205Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi119RoundedFacts
    innerPair41RoundedFacts leaf1205RoundedFacts (by rfl)

private theorem leaf1205FlatSound : Sound leaf1205Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1205CertificateValid
    leaf1205InnerLogValid leaf1205CoversExact leaf1205LowerChecked

private noncomputable def leaf1206Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1206Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435681/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716926976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (424237561/268435456) }, upper := { exponent := 0, mantissa := (3293/2048) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435420671/137433853952) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf1206InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1206LocalValidity :
    LeafFacts leaf1206Box leaf1206Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1206Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716926976) }) = true
      norm_num [leaf1206Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1206CertificateValid :
    WideCertificateValid leaf1206Box leaf1206Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi120ValidityFacts
    leaf1206LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1206CoverageChecked :
    coverageCheck (innerAD leaf1206Box) leaf1206InnerLog = true := by
  rfl'

private theorem leaf1206InnerLogValid :
    leaf1206InnerLog.Valid 8 (innerAD leaf1206Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1206CoverageChecked

private noncomputable def leaf1206InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1206InputLogOnePlusV_eq :
    leaf1206InputLogOnePlusV = outerEnclosure 24
      (leaf1206Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1206RoundedFacts : LeafRoundedFacts 8
    leaf1206Certificate.logOnePlusV leaf1206InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1206InputLogOnePlusV_eq }

private noncomputable def leaf1206Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi120InputQChi innerPair50Input
    leaf1206InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1206LowerChecked :
    lowerCheck 24 leaf1206Box leaf1206Inputs = true := by
  rfl'

private theorem leaf1206CoversExact : CoversExact 8
    leaf1206Box leaf1206Certificate leaf1206InnerLog leaf1206Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi120RoundedFacts
    innerPair50RoundedFacts leaf1206RoundedFacts (by rfl)

private theorem leaf1206FlatSound : Sound leaf1206Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1206CertificateValid
    leaf1206InnerLogValid leaf1206CoversExact leaf1206LowerChecked

private noncomputable def leaf1207Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1207Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435681/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716982272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (420698833/268435456) }, upper := { exponent := 0, mantissa := (1633/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435475967/137433964544) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf1207InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1207LocalValidity :
    LeafFacts leaf1207Box leaf1207Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1207Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716982272) }) = true
      norm_num [leaf1207Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1207CertificateValid :
    WideCertificateValid leaf1207Box leaf1207Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi119ValidityFacts
    leaf1207LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1207CoverageChecked :
    coverageCheck (innerAD leaf1207Box) leaf1207InnerLog = true := by
  rfl'

private theorem leaf1207InnerLogValid :
    leaf1207InnerLog.Valid 8 (innerAD leaf1207Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1207CoverageChecked

private noncomputable def leaf1207InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1207InputLogOnePlusV_eq :
    leaf1207InputLogOnePlusV = outerEnclosure 24
      (leaf1207Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1207RoundedFacts : LeafRoundedFacts 8
    leaf1207Certificate.logOnePlusV leaf1207InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1207InputLogOnePlusV_eq }

private noncomputable def leaf1207Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi119InputQChi innerPair50Input
    leaf1207InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1207LowerChecked :
    lowerCheck 24 leaf1207Box leaf1207Inputs = true := by
  rfl'

private theorem leaf1207CoversExact : CoversExact 8
    leaf1207Box leaf1207Certificate leaf1207InnerLog leaf1207Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi119RoundedFacts
    innerPair50RoundedFacts leaf1207RoundedFacts (by rfl)

private theorem leaf1207FlatSound : Sound leaf1207Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1207CertificateValid
    leaf1207InnerLogValid leaf1207CoversExact leaf1207LowerChecked

private noncomputable def leaf1208Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1208Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435683/268435456) }, vSqrt := { lower := (32765/32768), upper := (4042264335/4042170368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (426137987/268435456) }, upper := { exponent := 0, mantissa := (827/512) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8084434703/8084340736) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf1208InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1208LocalValidity :
    LeafFacts leaf1208Box leaf1208Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1208Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4042264335/4042170368) }) = true
      norm_num [leaf1208Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1208CertificateValid :
    WideCertificateValid leaf1208Box leaf1208Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi120ValidityFacts
    leaf1208LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1208CoverageChecked :
    coverageCheck (innerAD leaf1208Box) leaf1208InnerLog = true := by
  rfl'

private theorem leaf1208InnerLogValid :
    leaf1208InnerLog.Valid 8 (innerAD leaf1208Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1208CoverageChecked

private noncomputable def leaf1208InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1208InputLogOnePlusV_eq :
    leaf1208InputLogOnePlusV = outerEnclosure 24
      (leaf1208Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1208RoundedFacts : LeafRoundedFacts 8
    leaf1208Certificate.logOnePlusV leaf1208InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1208InputLogOnePlusV_eq }

private noncomputable def leaf1208Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi120InputQChi innerPair50Input
    leaf1208InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1208LowerChecked :
    lowerCheck 24 leaf1208Box leaf1208Inputs = true := by
  rfl'

private theorem leaf1208CoversExact : CoversExact 8
    leaf1208Box leaf1208Certificate leaf1208InnerLog leaf1208Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi120RoundedFacts
    innerPair50RoundedFacts leaf1208RoundedFacts (by rfl)

private theorem leaf1208FlatSound : Sound leaf1208Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1208CertificateValid
    leaf1208InnerLogValid leaf1208CoversExact leaf1208LowerChecked

private noncomputable def leaf1209Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1209Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435683/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716841984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (429611183/268435456) }, upper := { exponent := 0, mantissa := (6669/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435335679/137433683968) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf1209InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf1209LocalValidity :
    LeafFacts leaf1209Box leaf1209Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1209Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716841984) }) = true
      norm_num [leaf1209Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1209CertificateValid :
    WideCertificateValid leaf1209Box leaf1209Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi121ValidityFacts
    leaf1209LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1209CoverageChecked :
    coverageCheck (innerAD leaf1209Box) leaf1209InnerLog = true := by
  rfl'

private theorem leaf1209InnerLogValid :
    leaf1209InnerLog.Valid 8 (innerAD leaf1209Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf1209CoverageChecked

private noncomputable def leaf1209InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1209InputLogOnePlusV_eq :
    leaf1209InputLogOnePlusV = outerEnclosure 24
      (leaf1209Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1209RoundedFacts : LeafRoundedFacts 8
    leaf1209Certificate.logOnePlusV leaf1209InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1209InputLogOnePlusV_eq }

private noncomputable def leaf1209Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi121InputQChi innerPair51Input
    leaf1209InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1209LowerChecked :
    lowerCheck 24 leaf1209Box leaf1209Inputs = true := by
  rfl'

private theorem leaf1209CoversExact : CoversExact 8
    leaf1209Box leaf1209Certificate leaf1209InnerLog leaf1209Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi121RoundedFacts
    innerPair51RoundedFacts leaf1209RoundedFacts (by rfl)

private theorem leaf1209FlatSound : Sound leaf1209Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1209CertificateValid
    leaf1209InnerLogValid leaf1209CoversExact leaf1209LowerChecked

private noncomputable def leaf1210Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1210Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435685/268435456) }, vSqrt := { lower := (32765/32768), upper := (1347421445/1347387392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (434984805/268435456) }, upper := { exponent := 0, mantissa := (211/128) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2694808837/2694774784) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf1210InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf1210LocalValidity :
    LeafFacts leaf1210Box leaf1210Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1210Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1347421445/1347387392) }) = true
      norm_num [leaf1210Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1210CertificateValid :
    WideCertificateValid leaf1210Box leaf1210Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi122ValidityFacts
    leaf1210LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1210CoverageChecked :
    coverageCheck (innerAD leaf1210Box) leaf1210InnerLog = true := by
  rfl'

private theorem leaf1210InnerLogValid :
    leaf1210InnerLog.Valid 8 (innerAD leaf1210Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf1210CoverageChecked

private noncomputable def leaf1210InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1210InputLogOnePlusV_eq :
    leaf1210InputLogOnePlusV = outerEnclosure 24
      (leaf1210Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1210RoundedFacts : LeafRoundedFacts 8
    leaf1210Certificate.logOnePlusV leaf1210InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1210InputLogOnePlusV_eq }

private noncomputable def leaf1210Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi122InputQChi innerPair51Input
    leaf1210InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1210LowerChecked :
    lowerCheck 24 leaf1210Box leaf1210Inputs = true := by
  rfl'

private theorem leaf1210CoversExact : CoversExact 8
    leaf1210Box leaf1210Certificate leaf1210InnerLog leaf1210Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi122RoundedFacts
    innerPair51RoundedFacts leaf1210RoundedFacts (by rfl)

private theorem leaf1210FlatSound : Sound leaf1210Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1210CertificateValid
    leaf1210InnerLogValid leaf1210CoversExact leaf1210LowerChecked

private noncomputable def leaf1211Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1211Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435685/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743362048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (431577141/268435456) }, upper := { exponent := 0, mantissa := (1675/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487060787/27486724096) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf1211InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf1211LocalValidity :
    LeafFacts leaf1211Box leaf1211Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1211Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743362048) }) = true
      norm_num [leaf1211Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1211CertificateValid :
    WideCertificateValid leaf1211Box leaf1211Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi121ValidityFacts
    leaf1211LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1211CoverageChecked :
    coverageCheck (innerAD leaf1211Box) leaf1211InnerLog = true := by
  rfl'

private theorem leaf1211InnerLogValid :
    leaf1211InnerLog.Valid 8 (innerAD leaf1211Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf1211CoverageChecked

private noncomputable def leaf1211InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1211InputLogOnePlusV_eq :
    leaf1211InputLogOnePlusV = outerEnclosure 24
      (leaf1211Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1211RoundedFacts : LeafRoundedFacts 8
    leaf1211Certificate.logOnePlusV leaf1211InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1211InputLogOnePlusV_eq }

private noncomputable def leaf1211Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi121InputQChi innerPair51Input
    leaf1211InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1211LowerChecked :
    lowerCheck 24 leaf1211Box leaf1211Inputs = true := by
  rfl'

private theorem leaf1211CoversExact : CoversExact 8
    leaf1211Box leaf1211Certificate leaf1211InnerLog leaf1211Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi121RoundedFacts
    innerPair51RoundedFacts leaf1211RoundedFacts (by rfl)

private theorem leaf1211FlatSound : Sound leaf1211Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1211CertificateValid
    leaf1211InnerLogValid leaf1211CoversExact leaf1211LowerChecked

private noncomputable def leaf1212Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1212Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435687/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716724224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (437016295/268435456) }, upper := { exponent := 0, mantissa := (53/32) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435217919/137433448448) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf1212InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1212LocalValidity :
    LeafFacts leaf1212Box leaf1212Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1212Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716724224) }) = true
      norm_num [leaf1212Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1212CertificateValid :
    WideCertificateValid leaf1212Box leaf1212Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi122ValidityFacts
    leaf1212LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1212CoverageChecked :
    coverageCheck (innerAD leaf1212Box) leaf1212InnerLog = true := by
  rfl'

private theorem leaf1212InnerLogValid :
    leaf1212InnerLog.Valid 8 (innerAD leaf1212Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1212CoverageChecked

private noncomputable def leaf1212InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1212InputLogOnePlusV_eq :
    leaf1212InputLogOnePlusV = outerEnclosure 24
      (leaf1212Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1212RoundedFacts : LeafRoundedFacts 8
    leaf1212Certificate.logOnePlusV leaf1212InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1212InputLogOnePlusV_eq }

private noncomputable def leaf1212Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi122InputQChi innerPair56Input
    leaf1212InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1212LowerChecked :
    lowerCheck 24 leaf1212Box leaf1212Inputs = true := by
  rfl'

private theorem leaf1212CoversExact : CoversExact 8
    leaf1212Box leaf1212Certificate leaf1212InnerLog leaf1212Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi122RoundedFacts
    innerPair56RoundedFacts leaf1212RoundedFacts (by rfl)

private theorem leaf1212FlatSound : Sound leaf1212Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1212CertificateValid
    leaf1212InnerLogValid leaf1212CoversExact leaf1212LowerChecked

private noncomputable def leaf1213Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1213Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435675/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905766912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (400514983/268435456) }, upper := { exponent := 0, mantissa := (6221/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811931477/45811533824) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf1213InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1213LocalValidity :
    LeafFacts leaf1213Box leaf1213Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1213Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905766912) }) = true
      norm_num [leaf1213Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1213CertificateValid :
    WideCertificateValid leaf1213Box leaf1213Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi115ValidityFacts
    leaf1213LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1213CoverageChecked :
    coverageCheck (innerAD leaf1213Box) leaf1213InnerLog = true := by
  rfl'

private theorem leaf1213InnerLogValid :
    leaf1213InnerLog.Valid 8 (innerAD leaf1213Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1213CoverageChecked

private noncomputable def leaf1213InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814613/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1213InputLogOnePlusV_eq :
    leaf1213InputLogOnePlusV = outerEnclosure 24
      (leaf1213Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1213RoundedFacts : LeafRoundedFacts 8
    leaf1213Certificate.logOnePlusV leaf1213InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1213InputLogOnePlusV_eq }

private noncomputable def leaf1213Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi115InputQChi innerPair35Input
    leaf1213InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1213LowerChecked :
    lowerCheck 24 leaf1213Box leaf1213Inputs = true := by
  rfl'

private theorem leaf1213CoversExact : CoversExact 8
    leaf1213Box leaf1213Certificate leaf1213InnerLog leaf1213Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi115RoundedFacts
    innerPair35RoundedFacts leaf1213RoundedFacts (by rfl)

private theorem leaf1213FlatSound : Sound leaf1213Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1213CertificateValid
    leaf1213InnerLogValid leaf1213CoversExact leaf1213LowerChecked

private noncomputable def leaf1214Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1214Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435677/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717213696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (406019669/268435456) }, upper := { exponent := 0, mantissa := (3153/2048) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435707391/137434427392) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf1214InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1214LocalValidity :
    LeafFacts leaf1214Box leaf1214Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1214Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717213696) }) = true
      norm_num [leaf1214Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1214CertificateValid :
    WideCertificateValid leaf1214Box leaf1214Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi116ValidityFacts
    leaf1214LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1214CoverageChecked :
    coverageCheck (innerAD leaf1214Box) leaf1214InnerLog = true := by
  rfl'

private theorem leaf1214InnerLogValid :
    leaf1214InnerLog.Valid 8 (innerAD leaf1214Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1214CoverageChecked

private noncomputable def leaf1214InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1214InputLogOnePlusV_eq :
    leaf1214InputLogOnePlusV = outerEnclosure 24
      (leaf1214Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1214RoundedFacts : LeafRoundedFacts 8
    leaf1214Certificate.logOnePlusV leaf1214InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1214InputLogOnePlusV_eq }

private noncomputable def leaf1214Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi116InputQChi innerPair40Input
    leaf1214InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1214LowerChecked :
    lowerCheck 24 leaf1214Box leaf1214Inputs = true := by
  rfl'

private theorem leaf1214CoversExact : CoversExact 8
    leaf1214Box leaf1214Certificate leaf1214InnerLog leaf1214Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi116RoundedFacts
    innerPair40RoundedFacts leaf1214RoundedFacts (by rfl)

private theorem leaf1214FlatSound : Sound leaf1214Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1214CertificateValid
    leaf1214InnerLogValid leaf1214CoversExact leaf1214LowerChecked

private noncomputable def leaf1215Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1215Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435677/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717275136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (402087749/268435456) }, upper := { exponent := 0, mantissa := (3123/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435768831/137434550272) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf1215InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1215LocalValidity :
    LeafFacts leaf1215Box leaf1215Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1215Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717275136) }) = true
      norm_num [leaf1215Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1215CertificateValid :
    WideCertificateValid leaf1215Box leaf1215Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi115ValidityFacts
    leaf1215LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1215CoverageChecked :
    coverageCheck (innerAD leaf1215Box) leaf1215InnerLog = true := by
  rfl'

private theorem leaf1215InnerLogValid :
    leaf1215InnerLog.Valid 8 (innerAD leaf1215Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1215CoverageChecked

private noncomputable def leaf1215InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1215InputLogOnePlusV_eq :
    leaf1215InputLogOnePlusV = outerEnclosure 24
      (leaf1215Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1215RoundedFacts : LeafRoundedFacts 8
    leaf1215Certificate.logOnePlusV leaf1215InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1215InputLogOnePlusV_eq }

private noncomputable def leaf1215Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi115InputQChi innerPair35Input
    leaf1215InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1215LowerChecked :
    lowerCheck 24 leaf1215Box leaf1215Inputs = true := by
  rfl'

private theorem leaf1215CoversExact : CoversExact 8
    leaf1215Box leaf1215Certificate leaf1215InnerLog leaf1215Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi115RoundedFacts
    innerPair35RoundedFacts leaf1215RoundedFacts (by rfl)

private theorem leaf1215FlatSound : Sound leaf1215Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1215CertificateValid
    leaf1215InnerLogValid leaf1215CoversExact leaf1215LowerChecked

private noncomputable def leaf1216Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1216Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435679/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905729024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (407657967/268435456) }, upper := { exponent := 0, mantissa := (1583/1024) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811893589/45811458048) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf1216InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1216LocalValidity :
    LeafFacts leaf1216Box leaf1216Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1216Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905729024) }) = true
      norm_num [leaf1216Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1216CertificateValid :
    WideCertificateValid leaf1216Box leaf1216Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi116ValidityFacts
    leaf1216LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1216CoverageChecked :
    coverageCheck (innerAD leaf1216Box) leaf1216InnerLog = true := by
  rfl'

private theorem leaf1216InnerLogValid :
    leaf1216InnerLog.Valid 8 (innerAD leaf1216Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1216CoverageChecked

private noncomputable def leaf1216InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1216InputLogOnePlusV_eq :
    leaf1216InputLogOnePlusV = outerEnclosure 24
      (leaf1216Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1216RoundedFacts : LeafRoundedFacts 8
    leaf1216Certificate.logOnePlusV leaf1216InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1216InputLogOnePlusV_eq }

private noncomputable def leaf1216Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi116InputQChi innerPair40Input
    leaf1216InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1216LowerChecked :
    lowerCheck 24 leaf1216Box leaf1216Inputs = true := by
  rfl'

private theorem leaf1216CoversExact : CoversExact 8
    leaf1216Box leaf1216Certificate leaf1216InnerLog leaf1216Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi116RoundedFacts
    innerPair40RoundedFacts leaf1216RoundedFacts (by rfl)

private theorem leaf1216FlatSound : Sound leaf1216Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1216CertificateValid
    leaf1216InnerLogValid leaf1216CoversExact leaf1216LowerChecked

private noncomputable def leaf1217Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1217Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435679/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717126656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (411524355/268435456) }, upper := { exponent := 0, mantissa := (6391/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435620351/137434253312) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf1217InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1217LocalValidity :
    LeafFacts leaf1217Box leaf1217Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1217Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717126656) }) = true
      norm_num [leaf1217Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1217CertificateValid :
    WideCertificateValid leaf1217Box leaf1217Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi117ValidityFacts
    leaf1217LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1217CoverageChecked :
    coverageCheck (innerAD leaf1217Box) leaf1217InnerLog = true := by
  rfl'

private theorem leaf1217InnerLogValid :
    leaf1217InnerLog.Valid 8 (innerAD leaf1217Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1217CoverageChecked

private noncomputable def leaf1217InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf1217InputLogOnePlusV_eq :
    leaf1217InputLogOnePlusV = outerEnclosure 24
      (leaf1217Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1217RoundedFacts : LeafRoundedFacts 8
    leaf1217Certificate.logOnePlusV leaf1217InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1217InputLogOnePlusV_eq }

private noncomputable def leaf1217Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi117InputQChi innerPair40Input
    leaf1217InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1217LowerChecked :
    lowerCheck 24 leaf1217Box leaf1217Inputs = true := by
  rfl'

private theorem leaf1217CoversExact : CoversExact 8
    leaf1217Box leaf1217Certificate leaf1217InnerLog leaf1217Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi117RoundedFacts
    innerPair40RoundedFacts leaf1217RoundedFacts (by rfl)

private theorem leaf1217FlatSound : Sound leaf1217Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1217CertificateValid
    leaf1217InnerLogValid leaf1217CoversExact leaf1217LowerChecked

private noncomputable def leaf1218Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1218Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435681/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905679872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (417029041/268435456) }, upper := { exponent := 0, mantissa := (1619/1024) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811844437/45811359744) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf1218InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf1218LocalValidity :
    LeafFacts leaf1218Box leaf1218Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1218Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905679872) }) = true
      norm_num [leaf1218Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1218CertificateValid :
    WideCertificateValid leaf1218Box leaf1218Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi118ValidityFacts
    leaf1218LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1218CoverageChecked :
    coverageCheck (innerAD leaf1218Box) leaf1218InnerLog = true := by
  rfl'

private theorem leaf1218InnerLogValid :
    leaf1218InnerLog.Valid 8 (innerAD leaf1218Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf1218CoverageChecked

private noncomputable def leaf1218InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1218InputLogOnePlusV_eq :
    leaf1218InputLogOnePlusV = outerEnclosure 24
      (leaf1218Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1218RoundedFacts : LeafRoundedFacts 8
    leaf1218Certificate.logOnePlusV leaf1218InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1218InputLogOnePlusV_eq }

private noncomputable def leaf1218Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi118InputQChi innerPair41Input
    leaf1218InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1218LowerChecked :
    lowerCheck 24 leaf1218Box leaf1218Inputs = true := by
  rfl'

private theorem leaf1218CoversExact : CoversExact 8
    leaf1218Box leaf1218Certificate leaf1218InnerLog leaf1218Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi118RoundedFacts
    innerPair41RoundedFacts leaf1218RoundedFacts (by rfl)

private theorem leaf1218FlatSound : Sound leaf1218Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1218CertificateValid
    leaf1218InnerLogValid leaf1218CoversExact leaf1218LowerChecked

private noncomputable def leaf1219Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1219Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435681/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717099008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (413228185/268435456) }, upper := { exponent := 0, mantissa := (3209/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435592703/137434198016) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf1219InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf1219LocalValidity :
    LeafFacts leaf1219Box leaf1219Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1219Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717099008) }) = true
      norm_num [leaf1219Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1219CertificateValid :
    WideCertificateValid leaf1219Box leaf1219Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi117ValidityFacts
    leaf1219LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1219CoverageChecked :
    coverageCheck (innerAD leaf1219Box) leaf1219InnerLog = true := by
  rfl'

private theorem leaf1219InnerLogValid :
    leaf1219InnerLog.Valid 8 (innerAD leaf1219Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf1219CoverageChecked

private noncomputable def leaf1219InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1219InputLogOnePlusV_eq :
    leaf1219InputLogOnePlusV = outerEnclosure 24
      (leaf1219Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1219RoundedFacts : LeafRoundedFacts 8
    leaf1219Certificate.logOnePlusV leaf1219InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1219InputLogOnePlusV_eq }

private noncomputable def leaf1219Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi117InputQChi innerPair41Input
    leaf1219InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1219LowerChecked :
    lowerCheck 24 leaf1219Box leaf1219Inputs = true := by
  rfl'

private theorem leaf1219CoversExact : CoversExact 8
    leaf1219Box leaf1219Certificate leaf1219InnerLog leaf1219Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi117RoundedFacts
    innerPair41RoundedFacts leaf1219RoundedFacts (by rfl)

private theorem leaf1219FlatSound : Sound leaf1219Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1219CertificateValid
    leaf1219InnerLogValid leaf1219CoversExact leaf1219LowerChecked

private noncomputable def leaf1220Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1220Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435683/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717010944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (418798403/268435456) }, upper := { exponent := 0, mantissa := (813/512) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435504639/137434021888) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf1220InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf1220LocalValidity :
    LeafFacts leaf1220Box leaf1220Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1220Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717010944) }) = true
      norm_num [leaf1220Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1220CertificateValid :
    WideCertificateValid leaf1220Box leaf1220Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi118ValidityFacts
    leaf1220LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1220CoverageChecked :
    coverageCheck (innerAD leaf1220Box) leaf1220InnerLog = true := by
  rfl'

private theorem leaf1220InnerLogValid :
    leaf1220InnerLog.Valid 8 (innerAD leaf1220Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf1220CoverageChecked

private noncomputable def leaf1220InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814631/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1220InputLogOnePlusV_eq :
    leaf1220InputLogOnePlusV = outerEnclosure 24
      (leaf1220Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1220RoundedFacts : LeafRoundedFacts 8
    leaf1220Certificate.logOnePlusV leaf1220InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1220InputLogOnePlusV_eq }

private noncomputable def leaf1220Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi118InputQChi innerPair41Input
    leaf1220InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1220LowerChecked :
    lowerCheck 24 leaf1220Box leaf1220Inputs = true := by
  rfl'

private theorem leaf1220CoversExact : CoversExact 8
    leaf1220Box leaf1220Certificate leaf1220InnerLog leaf1220Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi118RoundedFacts
    innerPair41RoundedFacts leaf1220RoundedFacts (by rfl)

private theorem leaf1220FlatSound : Sound leaf1220Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1220CertificateValid
    leaf1220InnerLogValid leaf1220CoversExact leaf1220LowerChecked

private noncomputable def leaf1221Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1221Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435679/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717249536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (403660515/268435456) }, upper := { exponent := 0, mantissa := (6271/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435743231/137434499072) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf1221InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1221LocalValidity :
    LeafFacts leaf1221Box leaf1221Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1221Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717249536) }) = true
      norm_num [leaf1221Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1221CertificateValid :
    WideCertificateValid leaf1221Box leaf1221Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi115ValidityFacts
    leaf1221LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1221CoverageChecked :
    coverageCheck (innerAD leaf1221Box) leaf1221InnerLog = true := by
  rfl'

private theorem leaf1221InnerLogValid :
    leaf1221InnerLog.Valid 8 (innerAD leaf1221Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1221CoverageChecked

private noncomputable def leaf1221InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1221InputLogOnePlusV_eq :
    leaf1221InputLogOnePlusV = outerEnclosure 24
      (leaf1221Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1221RoundedFacts : LeafRoundedFacts 8
    leaf1221Certificate.logOnePlusV leaf1221InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1221InputLogOnePlusV_eq }

private noncomputable def leaf1221Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi115InputQChi innerPair40Input
    leaf1221InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1221LowerChecked :
    lowerCheck 24 leaf1221Box leaf1221Inputs = true := by
  rfl'

private theorem leaf1221CoversExact : CoversExact 8
    leaf1221Box leaf1221Certificate leaf1221InnerLog leaf1221Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi115RoundedFacts
    innerPair40RoundedFacts leaf1221RoundedFacts (by rfl)

private theorem leaf1221FlatSound : Sound leaf1221Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1221CertificateValid
    leaf1221InnerLogValid leaf1221CoversExact leaf1221LowerChecked

private noncomputable def leaf1222Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1222Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435681/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717160448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (409296265/268435456) }, upper := { exponent := 0, mantissa := (3179/2048) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435654143/137434320896) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf1222InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1222LocalValidity :
    LeafFacts leaf1222Box leaf1222Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1222Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717160448) }) = true
      norm_num [leaf1222Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1222CertificateValid :
    WideCertificateValid leaf1222Box leaf1222Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi116ValidityFacts
    leaf1222LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1222CoverageChecked :
    coverageCheck (innerAD leaf1222Box) leaf1222InnerLog = true := by
  rfl'

private theorem leaf1222InnerLogValid :
    leaf1222InnerLog.Valid 8 (innerAD leaf1222Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1222CoverageChecked

private noncomputable def leaf1222InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629243/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1222InputLogOnePlusV_eq :
    leaf1222InputLogOnePlusV = outerEnclosure 24
      (leaf1222Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1222RoundedFacts : LeafRoundedFacts 8
    leaf1222Certificate.logOnePlusV leaf1222InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1222InputLogOnePlusV_eq }

private noncomputable def leaf1222Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi116InputQChi innerPair40Input
    leaf1222InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1222LowerChecked :
    lowerCheck 24 leaf1222Box leaf1222Inputs = true := by
  rfl'

private theorem leaf1222CoversExact : CoversExact 8
    leaf1222Box leaf1222Certificate leaf1222InnerLog leaf1222Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi116RoundedFacts
    innerPair40RoundedFacts leaf1222RoundedFacts (by rfl)

private theorem leaf1222FlatSound : Sound leaf1222Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1222CertificateValid
    leaf1222InnerLogValid leaf1222CoversExact leaf1222LowerChecked

private noncomputable def leaf1223Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1223Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435681/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905741312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (405233281/268435456) }, upper := { exponent := 0, mantissa := (787/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811905877/45811482624) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf1223InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1223LocalValidity :
    LeafFacts leaf1223Box leaf1223Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1223Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905741312) }) = true
      norm_num [leaf1223Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1223CertificateValid :
    WideCertificateValid leaf1223Box leaf1223Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi115ValidityFacts
    leaf1223LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1223CoverageChecked :
    coverageCheck (innerAD leaf1223Box) leaf1223InnerLog = true := by
  rfl'

private theorem leaf1223InnerLogValid :
    leaf1223InnerLog.Valid 8 (innerAD leaf1223Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1223CoverageChecked

private noncomputable def leaf1223InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1223InputLogOnePlusV_eq :
    leaf1223InputLogOnePlusV = outerEnclosure 24
      (leaf1223Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1223RoundedFacts : LeafRoundedFacts 8
    leaf1223Certificate.logOnePlusV leaf1223InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1223InputLogOnePlusV_eq }

private noncomputable def leaf1223Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi115InputQChi innerPair40Input
    leaf1223InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1223LowerChecked :
    lowerCheck 24 leaf1223Box leaf1223Inputs = true := by
  rfl'

private theorem leaf1223CoversExact : CoversExact 8
    leaf1223Box leaf1223Certificate leaf1223InnerLog leaf1223Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi115RoundedFacts
    innerPair40RoundedFacts leaf1223RoundedFacts (by rfl)

private theorem leaf1223FlatSound : Sound leaf1223Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1223CertificateValid
    leaf1223InnerLogValid leaf1223CoversExact leaf1223LowerChecked

private noncomputable def leaf1224Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1224Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435683/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717133824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (410934563/268435456) }, upper := { exponent := 0, mantissa := (399/256) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435627519/137434267648) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf1224InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1224LocalValidity :
    LeafFacts leaf1224Box leaf1224Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1224Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717133824) }) = true
      norm_num [leaf1224Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1224CertificateValid :
    WideCertificateValid leaf1224Box leaf1224Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi116ValidityFacts
    leaf1224LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1224CoverageChecked :
    coverageCheck (innerAD leaf1224Box) leaf1224InnerLog = true := by
  rfl'

private theorem leaf1224InnerLogValid :
    leaf1224InnerLog.Valid 8 (innerAD leaf1224Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1224CoverageChecked

private noncomputable def leaf1224InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1224InputLogOnePlusV_eq :
    leaf1224InputLogOnePlusV = outerEnclosure 24
      (leaf1224Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1224RoundedFacts : LeafRoundedFacts 8
    leaf1224Certificate.logOnePlusV leaf1224InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1224InputLogOnePlusV_eq }

private noncomputable def leaf1224Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi116InputQChi innerPair40Input
    leaf1224InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1224LowerChecked :
    lowerCheck 24 leaf1224Box leaf1224Inputs = true := by
  rfl'

private theorem leaf1224CoversExact : CoversExact 8
    leaf1224Box leaf1224Certificate leaf1224InnerLog leaf1224Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi116RoundedFacts
    innerPair40RoundedFacts leaf1224RoundedFacts (by rfl)

private theorem leaf1224FlatSound : Sound leaf1224Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1224CertificateValid
    leaf1224InnerLogValid leaf1224CoversExact leaf1224LowerChecked

private noncomputable def leaf1225Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1225Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435683/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743414272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (414932015/268435456) }, upper := { exponent := 0, mantissa := (6445/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487113011/27486828544) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf1225InnerLog : WideLogData :=
  innerPair87Data

set_option maxRecDepth 1000000 in
private theorem leaf1225LocalValidity :
    LeafFacts leaf1225Box leaf1225Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1225Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743414272) }) = true
      norm_num [leaf1225Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1225CertificateValid :
    WideCertificateValid leaf1225Box leaf1225Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi117ValidityFacts
    leaf1225LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1225CoverageChecked :
    coverageCheck (innerAD leaf1225Box) leaf1225InnerLog = true := by
  rfl'

private theorem leaf1225InnerLogValid :
    leaf1225InnerLog.Valid 8 (innerAD leaf1225Box) :=
  wideLogDataValid_of_cachedCheck endpoint19PositiveFacts
    endpoint47PositiveFacts.valid leaf1225CoverageChecked

private noncomputable def leaf1225InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1225InputLogOnePlusV_eq :
    leaf1225InputLogOnePlusV = outerEnclosure 24
      (leaf1225Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1225RoundedFacts : LeafRoundedFacts 8
    leaf1225Certificate.logOnePlusV leaf1225InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1225InputLogOnePlusV_eq }

private noncomputable def leaf1225Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi117InputQChi innerPair87Input
    leaf1225InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1225LowerChecked :
    lowerCheck 24 leaf1225Box leaf1225Inputs = true := by
  rfl'

private theorem leaf1225CoversExact : CoversExact 8
    leaf1225Box leaf1225Certificate leaf1225InnerLog leaf1225Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi117RoundedFacts
    innerPair87RoundedFacts leaf1225RoundedFacts (by rfl)

private theorem leaf1225FlatSound : Sound leaf1225Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1225CertificateValid
    leaf1225InnerLogValid leaf1225CoversExact leaf1225LowerChecked

private noncomputable def leaf1226Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1226Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435685/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716982272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (420567765/268435456) }, upper := { exponent := 0, mantissa := (1633/1024) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435475967/137433964544) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf1226InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1226LocalValidity :
    LeafFacts leaf1226Box leaf1226Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1226Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716982272) }) = true
      norm_num [leaf1226Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1226CertificateValid :
    WideCertificateValid leaf1226Box leaf1226Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi118ValidityFacts
    leaf1226LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1226CoverageChecked :
    coverageCheck (innerAD leaf1226Box) leaf1226InnerLog = true := by
  rfl'

private theorem leaf1226InnerLogValid :
    leaf1226InnerLog.Valid 8 (innerAD leaf1226Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1226CoverageChecked

private noncomputable def leaf1226InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1226InputLogOnePlusV_eq :
    leaf1226InputLogOnePlusV = outerEnclosure 24
      (leaf1226Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1226RoundedFacts : LeafRoundedFacts 8
    leaf1226Certificate.logOnePlusV leaf1226InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1226InputLogOnePlusV_eq }

private noncomputable def leaf1226Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi118InputQChi innerPair50Input
    leaf1226InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1226LowerChecked :
    lowerCheck 24 leaf1226Box leaf1226Inputs = true := by
  rfl'

private theorem leaf1226CoversExact : CoversExact 8
    leaf1226Box leaf1226Certificate leaf1226InnerLog leaf1226Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi118RoundedFacts
    innerPair50RoundedFacts leaf1226RoundedFacts (by rfl)

private theorem leaf1226FlatSound : Sound leaf1226Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1226CertificateValid
    leaf1226InnerLogValid leaf1226CoversExact leaf1226LowerChecked

private noncomputable def leaf1227Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1227Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435685/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717043712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (416635845/268435456) }, upper := { exponent := 0, mantissa := (809/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435537407/137434087424) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf1227InnerLog : WideLogData :=
  innerPair154Data

set_option maxRecDepth 1000000 in
private theorem leaf1227LocalValidity :
    LeafFacts leaf1227Box leaf1227Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1227Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717043712) }) = true
      norm_num [leaf1227Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1227CertificateValid :
    WideCertificateValid leaf1227Box leaf1227Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi117ValidityFacts
    leaf1227LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1227CoverageChecked :
    coverageCheck (innerAD leaf1227Box) leaf1227InnerLog = true := by
  rfl'

private theorem leaf1227InnerLogValid :
    leaf1227InnerLog.Valid 8 (innerAD leaf1227Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint44PositiveFacts.valid leaf1227CoverageChecked

private noncomputable def leaf1227InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1227InputLogOnePlusV_eq :
    leaf1227InputLogOnePlusV = outerEnclosure 24
      (leaf1227Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1227RoundedFacts : LeafRoundedFacts 8
    leaf1227Certificate.logOnePlusV leaf1227InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1227InputLogOnePlusV_eq }

private noncomputable def leaf1227Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi117InputQChi innerPair154Input
    leaf1227InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1227LowerChecked :
    lowerCheck 24 leaf1227Box leaf1227Inputs = true := by
  rfl'

private theorem leaf1227CoversExact : CoversExact 8
    leaf1227Box leaf1227Certificate leaf1227InnerLog leaf1227Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi117RoundedFacts
    innerPair154RoundedFacts leaf1227RoundedFacts (by rfl)

private theorem leaf1227FlatSound : Sound leaf1227Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1227CertificateValid
    leaf1227InnerLogValid leaf1227CoversExact leaf1227LowerChecked

private noncomputable def leaf1228Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1228Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435687/268435456) }, vSqrt := { lower := (32765/32768), upper := (4581232913/4581130240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (422337127/268435456) }, upper := { exponent := 0, mantissa := (205/128) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9162363153/9162260480) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf1228InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1228LocalValidity :
    LeafFacts leaf1228Box leaf1228Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1228Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4581232913/4581130240) }) = true
      norm_num [leaf1228Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1228CertificateValid :
    WideCertificateValid leaf1228Box leaf1228Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi118ValidityFacts
    leaf1228LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1228CoverageChecked :
    coverageCheck (innerAD leaf1228Box) leaf1228InnerLog = true := by
  rfl'

private theorem leaf1228InnerLogValid :
    leaf1228InnerLog.Valid 8 (innerAD leaf1228Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1228CoverageChecked

private noncomputable def leaf1228InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1228InputLogOnePlusV_eq :
    leaf1228InputLogOnePlusV = outerEnclosure 24
      (leaf1228Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1228RoundedFacts : LeafRoundedFacts 8
    leaf1228Certificate.logOnePlusV leaf1228InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1228InputLogOnePlusV_eq }

private noncomputable def leaf1228Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi118InputQChi innerPair50Input
    leaf1228InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1228LowerChecked :
    lowerCheck 24 leaf1228Box leaf1228Inputs = true := by
  rfl'

private theorem leaf1228CoversExact : CoversExact 8
    leaf1228Box leaf1228Certificate leaf1228InnerLog leaf1228Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi118RoundedFacts
    innerPair50RoundedFacts leaf1228RoundedFacts (by rfl)

private theorem leaf1228FlatSound : Sound leaf1228Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1228CertificateValid
    leaf1228InnerLogValid leaf1228CoversExact leaf1228LowerChecked

private noncomputable def leaf1229Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1229Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435683/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716952576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (422533727/268435456) }, upper := { exponent := 0, mantissa := (6561/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435446271/137433905152) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf1229InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1229LocalValidity :
    LeafFacts leaf1229Box leaf1229Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1229Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716952576) }) = true
      norm_num [leaf1229Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1229CertificateValid :
    WideCertificateValid leaf1229Box leaf1229Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi119ValidityFacts
    leaf1229LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1229CoverageChecked :
    coverageCheck (innerAD leaf1229Box) leaf1229InnerLog = true := by
  rfl'

private theorem leaf1229InnerLogValid :
    leaf1229InnerLog.Valid 8 (innerAD leaf1229Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1229CoverageChecked

private noncomputable def leaf1229InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1229InputLogOnePlusV_eq :
    leaf1229InputLogOnePlusV = outerEnclosure 24
      (leaf1229Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1229RoundedFacts : LeafRoundedFacts 8
    leaf1229Certificate.logOnePlusV leaf1229InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1229InputLogOnePlusV_eq }

private noncomputable def leaf1229Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi119InputQChi innerPair50Input
    leaf1229InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1229LowerChecked :
    lowerCheck 24 leaf1229Box leaf1229Inputs = true := by
  rfl'

private theorem leaf1229CoversExact : CoversExact 8
    leaf1229Box leaf1229Certificate leaf1229InnerLog leaf1229Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi119RoundedFacts
    innerPair50RoundedFacts leaf1229RoundedFacts (by rfl)

private theorem leaf1229FlatSound : Sound leaf1229Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1229CertificateValid
    leaf1229InnerLogValid leaf1229CoversExact leaf1229LowerChecked

private noncomputable def leaf1230Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1230Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435685/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716865536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (428038413/268435456) }, upper := { exponent := 0, mantissa := (3323/2048) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435359231/137433731072) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf1230InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1230LocalValidity :
    LeafFacts leaf1230Box leaf1230Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1230Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716865536) }) = true
      norm_num [leaf1230Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1230CertificateValid :
    WideCertificateValid leaf1230Box leaf1230Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi120ValidityFacts
    leaf1230LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1230CoverageChecked :
    coverageCheck (innerAD leaf1230Box) leaf1230InnerLog = true := by
  rfl'

private theorem leaf1230InnerLogValid :
    leaf1230InnerLog.Valid 8 (innerAD leaf1230Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1230CoverageChecked

private noncomputable def leaf1230InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1230InputLogOnePlusV_eq :
    leaf1230InputLogOnePlusV = outerEnclosure 24
      (leaf1230Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1230RoundedFacts : LeafRoundedFacts 8
    leaf1230Certificate.logOnePlusV leaf1230InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1230InputLogOnePlusV_eq }

private noncomputable def leaf1230Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi120InputQChi innerPair50Input
    leaf1230InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1230LowerChecked :
    lowerCheck 24 leaf1230Box leaf1230Inputs = true := by
  rfl'

private theorem leaf1230CoversExact : CoversExact 8
    leaf1230Box leaf1230Certificate leaf1230InnerLog leaf1230Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi120RoundedFacts
    innerPair50RoundedFacts leaf1230RoundedFacts (by rfl)

private theorem leaf1230FlatSound : Sound leaf1230Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1230CertificateValid
    leaf1230InnerLogValid leaf1230CoversExact leaf1230LowerChecked

private noncomputable def leaf1231Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1231Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435685/268435456) }, vSqrt := { lower := (32765/32768), upper := (4581232913/4581128192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (424368621/268435456) }, upper := { exponent := 0, mantissa := (3295/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9162361105/9162256384) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf1231InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1231LocalValidity :
    LeafFacts leaf1231Box leaf1231Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1231Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4581232913/4581128192) }) = true
      norm_num [leaf1231Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1231CertificateValid :
    WideCertificateValid leaf1231Box leaf1231Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi119ValidityFacts
    leaf1231LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1231CoverageChecked :
    coverageCheck (innerAD leaf1231Box) leaf1231InnerLog = true := by
  rfl'

private theorem leaf1231InnerLogValid :
    leaf1231InnerLog.Valid 8 (innerAD leaf1231Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1231CoverageChecked

private noncomputable def leaf1231InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1231InputLogOnePlusV_eq :
    leaf1231InputLogOnePlusV = outerEnclosure 24
      (leaf1231Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1231RoundedFacts : LeafRoundedFacts 8
    leaf1231Certificate.logOnePlusV leaf1231InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1231InputLogOnePlusV_eq }

private noncomputable def leaf1231Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi119InputQChi innerPair50Input
    leaf1231InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1231LowerChecked :
    lowerCheck 24 leaf1231Box leaf1231Inputs = true := by
  rfl'

private theorem leaf1231CoversExact : CoversExact 8
    leaf1231Box leaf1231Certificate leaf1231InnerLog leaf1231Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi119RoundedFacts
    innerPair50RoundedFacts leaf1231RoundedFacts (by rfl)

private theorem leaf1231FlatSound : Sound leaf1231Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1231CertificateValid
    leaf1231InnerLogValid leaf1231CoversExact leaf1231LowerChecked

private noncomputable def leaf1232Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1232Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435687/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716834816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (429938839/268435456) }, upper := { exponent := 0, mantissa := (1669/1024) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435328511/137433669632) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf1232InnerLog : WideLogData :=
  innerPair157Data

set_option maxRecDepth 1000000 in
private theorem leaf1232LocalValidity :
    LeafFacts leaf1232Box leaf1232Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1232Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716834816) }) = true
      norm_num [leaf1232Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1232CertificateValid :
    WideCertificateValid leaf1232Box leaf1232Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi120ValidityFacts
    leaf1232LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1232CoverageChecked :
    coverageCheck (innerAD leaf1232Box) leaf1232InnerLog = true := by
  rfl'

private theorem leaf1232InnerLogValid :
    leaf1232InnerLog.Valid 8 (innerAD leaf1232Box) :=
  wideLogDataValid_of_cachedCheck endpoint44PositiveFacts
    endpoint45PositiveFacts.valid leaf1232CoverageChecked

private noncomputable def leaf1232InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629283/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1232InputLogOnePlusV_eq :
    leaf1232InputLogOnePlusV = outerEnclosure 24
      (leaf1232Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1232RoundedFacts : LeafRoundedFacts 8
    leaf1232Certificate.logOnePlusV leaf1232InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1232InputLogOnePlusV_eq }

private noncomputable def leaf1232Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi120InputQChi innerPair157Input
    leaf1232InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1232LowerChecked :
    lowerCheck 24 leaf1232Box leaf1232Inputs = true := by
  rfl'

private theorem leaf1232CoversExact : CoversExact 8
    leaf1232Box leaf1232Certificate leaf1232InnerLog leaf1232Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi120RoundedFacts
    innerPair157RoundedFacts leaf1232RoundedFacts (by rfl)

private theorem leaf1232FlatSound : Sound leaf1232Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1232CertificateValid
    leaf1232InnerLogValid leaf1232CoversExact leaf1232LowerChecked

private noncomputable def leaf1233Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1233Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435687/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905592832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (433543099/268435456) }, upper := { exponent := 0, mantissa := (6731/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811757397/45811185664) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf1233InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf1233LocalValidity :
    LeafFacts leaf1233Box leaf1233Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1233Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905592832) }) = true
      norm_num [leaf1233Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1233CertificateValid :
    WideCertificateValid leaf1233Box leaf1233Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi121ValidityFacts
    leaf1233LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1233CoverageChecked :
    coverageCheck (innerAD leaf1233Box) leaf1233InnerLog = true := by
  rfl'

private theorem leaf1233InnerLogValid :
    leaf1233InnerLog.Valid 8 (innerAD leaf1233Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf1233CoverageChecked

private noncomputable def leaf1233InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814645/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1233InputLogOnePlusV_eq :
    leaf1233InputLogOnePlusV = outerEnclosure 24
      (leaf1233Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1233RoundedFacts : LeafRoundedFacts 8
    leaf1233Certificate.logOnePlusV leaf1233InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1233InputLogOnePlusV_eq }

private noncomputable def leaf1233Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi121InputQChi innerPair51Input
    leaf1233InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1233LowerChecked :
    lowerCheck 24 leaf1233Box leaf1233Inputs = true := by
  rfl'

private theorem leaf1233CoversExact : CoversExact 8
    leaf1233Box leaf1233Certificate leaf1233InnerLog leaf1233Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi121RoundedFacts
    innerPair51RoundedFacts leaf1233RoundedFacts (by rfl)

private theorem leaf1233FlatSound : Sound leaf1233Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1233CertificateValid
    leaf1233InnerLogValid leaf1233CoversExact leaf1233LowerChecked

private noncomputable def leaf1234Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1234Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435689/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716691456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (439047785/268435456) }, upper := { exponent := 0, mantissa := (213/128) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435185151/137433382912) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf1234InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1234LocalValidity :
    LeafFacts leaf1234Box leaf1234Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1234Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716691456) }) = true
      norm_num [leaf1234Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1234CertificateValid :
    WideCertificateValid leaf1234Box leaf1234Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi122ValidityFacts
    leaf1234LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1234CoverageChecked :
    coverageCheck (innerAD leaf1234Box) leaf1234InnerLog = true := by
  rfl'

private theorem leaf1234InnerLogValid :
    leaf1234InnerLog.Valid 8 (innerAD leaf1234Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1234CoverageChecked

private noncomputable def leaf1234InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1234InputLogOnePlusV_eq :
    leaf1234InputLogOnePlusV = outerEnclosure 24
      (leaf1234Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1234RoundedFacts : LeafRoundedFacts 8
    leaf1234Certificate.logOnePlusV leaf1234InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1234InputLogOnePlusV_eq }

private noncomputable def leaf1234Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi122InputQChi innerPair56Input
    leaf1234InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1234LowerChecked :
    lowerCheck 24 leaf1234Box leaf1234Inputs = true := by
  rfl'

private theorem leaf1234CoversExact : CoversExact 8
    leaf1234Box leaf1234Certificate leaf1234InnerLog leaf1234Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi122RoundedFacts
    innerPair56RoundedFacts leaf1234RoundedFacts (by rfl)

private theorem leaf1234FlatSound : Sound leaf1234Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1234CertificateValid
    leaf1234InnerLogValid leaf1234CoversExact leaf1234LowerChecked

private noncomputable def leaf1235Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1235Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435689/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716746752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (435509057/268435456) }, upper := { exponent := 0, mantissa := (3381/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435240447/137433493504) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf1235InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf1235LocalValidity :
    LeafFacts leaf1235Box leaf1235Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1235Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716746752) }) = true
      norm_num [leaf1235Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1235CertificateValid :
    WideCertificateValid leaf1235Box leaf1235Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi121ValidityFacts
    leaf1235LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1235CoverageChecked :
    coverageCheck (innerAD leaf1235Box) leaf1235InnerLog = true := by
  rfl'

private theorem leaf1235InnerLogValid :
    leaf1235InnerLog.Valid 8 (innerAD leaf1235Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf1235CoverageChecked

private noncomputable def leaf1235InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814647/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1235InputLogOnePlusV_eq :
    leaf1235InputLogOnePlusV = outerEnclosure 24
      (leaf1235Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1235RoundedFacts : LeafRoundedFacts 8
    leaf1235Certificate.logOnePlusV leaf1235InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1235InputLogOnePlusV_eq }

private noncomputable def leaf1235Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi121InputQChi innerPair51Input
    leaf1235InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1235LowerChecked :
    lowerCheck 24 leaf1235Box leaf1235Inputs = true := by
  rfl'

private theorem leaf1235CoversExact : CoversExact 8
    leaf1235Box leaf1235Certificate leaf1235InnerLog leaf1235Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi121RoundedFacts
    innerPair51RoundedFacts leaf1235RoundedFacts (by rfl)

private theorem leaf1235FlatSound : Sound leaf1235Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1235CertificateValid
    leaf1235InnerLogValid leaf1235CoversExact leaf1235LowerChecked

private noncomputable def leaf1236Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1236Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435691/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905552896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (441079275/268435456) }, upper := { exponent := 0, mantissa := (107/64) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811717461/45811105792) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf1236InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1236LocalValidity :
    LeafFacts leaf1236Box leaf1236Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1236Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905552896) }) = true
      norm_num [leaf1236Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1236CertificateValid :
    WideCertificateValid leaf1236Box leaf1236Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi122ValidityFacts
    leaf1236LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1236CoverageChecked :
    coverageCheck (innerAD leaf1236Box) leaf1236InnerLog = true := by
  rfl'

private theorem leaf1236InnerLogValid :
    leaf1236InnerLog.Valid 8 (innerAD leaf1236Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1236CoverageChecked

private noncomputable def leaf1236InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1236InputLogOnePlusV_eq :
    leaf1236InputLogOnePlusV = outerEnclosure 24
      (leaf1236Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1236RoundedFacts : LeafRoundedFacts 8
    leaf1236Certificate.logOnePlusV leaf1236InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1236InputLogOnePlusV_eq }

private noncomputable def leaf1236Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi122InputQChi innerPair56Input
    leaf1236InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1236LowerChecked :
    lowerCheck 24 leaf1236Box leaf1236Inputs = true := by
  rfl'

private theorem leaf1236CoversExact : CoversExact 8
    leaf1236Box leaf1236Certificate leaf1236InnerLog leaf1236Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi122RoundedFacts
    innerPair56RoundedFacts leaf1236RoundedFacts (by rfl)

private theorem leaf1236FlatSound : Sound leaf1236Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1236CertificateValid
    leaf1236InnerLogValid leaf1236CoversExact leaf1236LowerChecked

private noncomputable def leaf1237Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1237Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435687/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716893184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (426203515/268435456) }, upper := { exponent := 0, mantissa := (6619/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435386879/137433786368) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf1237InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1237LocalValidity :
    LeafFacts leaf1237Box leaf1237Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1237Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716893184) }) = true
      norm_num [leaf1237Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1237CertificateValid :
    WideCertificateValid leaf1237Box leaf1237Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi119ValidityFacts
    leaf1237LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1237CoverageChecked :
    coverageCheck (innerAD leaf1237Box) leaf1237InnerLog = true := by
  rfl'

private theorem leaf1237InnerLogValid :
    leaf1237InnerLog.Valid 8 (innerAD leaf1237Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1237CoverageChecked

private noncomputable def leaf1237InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1237InputLogOnePlusV_eq :
    leaf1237InputLogOnePlusV = outerEnclosure 24
      (leaf1237Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1237RoundedFacts : LeafRoundedFacts 8
    leaf1237Certificate.logOnePlusV leaf1237InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1237InputLogOnePlusV_eq }

private noncomputable def leaf1237Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi119InputQChi innerPair50Input
    leaf1237InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1237LowerChecked :
    lowerCheck 24 leaf1237Box leaf1237Inputs = true := by
  rfl'

private theorem leaf1237CoversExact : CoversExact 8
    leaf1237Box leaf1237Certificate leaf1237InnerLog leaf1237Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi119RoundedFacts
    innerPair50RoundedFacts leaf1237RoundedFacts (by rfl)

private theorem leaf1237FlatSound : Sound leaf1237Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1237CertificateValid
    leaf1237InnerLogValid leaf1237CoversExact leaf1237LowerChecked

private noncomputable def leaf1238Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1238Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435689/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716804096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (431839265/268435456) }, upper := { exponent := 0, mantissa := (3353/2048) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435297791/137433608192) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf1238InnerLog : WideLogData :=
  innerPair157Data

set_option maxRecDepth 1000000 in
private theorem leaf1238LocalValidity :
    LeafFacts leaf1238Box leaf1238Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1238Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716804096) }) = true
      norm_num [leaf1238Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1238CertificateValid :
    WideCertificateValid leaf1238Box leaf1238Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi120ValidityFacts
    leaf1238LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1238CoverageChecked :
    coverageCheck (innerAD leaf1238Box) leaf1238InnerLog = true := by
  rfl'

private theorem leaf1238InnerLogValid :
    leaf1238InnerLog.Valid 8 (innerAD leaf1238Box) :=
  wideLogDataValid_of_cachedCheck endpoint44PositiveFacts
    endpoint45PositiveFacts.valid leaf1238CoverageChecked

private noncomputable def leaf1238InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1238InputLogOnePlusV_eq :
    leaf1238InputLogOnePlusV = outerEnclosure 24
      (leaf1238Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1238RoundedFacts : LeafRoundedFacts 8
    leaf1238Certificate.logOnePlusV leaf1238InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1238InputLogOnePlusV_eq }

private noncomputable def leaf1238Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi120InputQChi innerPair157Input
    leaf1238InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1238LowerChecked :
    lowerCheck 24 leaf1238Box leaf1238Inputs = true := by
  rfl'

private theorem leaf1238CoversExact : CoversExact 8
    leaf1238Box leaf1238Certificate leaf1238InnerLog leaf1238Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi120RoundedFacts
    innerPair157RoundedFacts leaf1238RoundedFacts (by rfl)

private theorem leaf1238FlatSound : Sound leaf1238Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1238CertificateValid
    leaf1238InnerLogValid leaf1238CoversExact leaf1238LowerChecked

private noncomputable def leaf1239Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (7/32), chiHi := (29/128) }

private noncomputable def leaf1239Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435689/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716863488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (428038409/268435456) }, upper := { exponent := 0, mantissa := (831/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi119LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435357183/137433726976) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf1239InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1239LocalValidity :
    LeafFacts leaf1239Box leaf1239Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1239Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716863488) }) = true
      norm_num [leaf1239Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1239CertificateValid :
    WideCertificateValid leaf1239Box leaf1239Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi119ValidityFacts
    leaf1239LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1239CoverageChecked :
    coverageCheck (innerAD leaf1239Box) leaf1239InnerLog = true := by
  rfl'

private theorem leaf1239InnerLogValid :
    leaf1239InnerLog.Valid 8 (innerAD leaf1239Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1239CoverageChecked

private noncomputable def leaf1239InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (363415/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf1239InputLogOnePlusV_eq :
    leaf1239InputLogOnePlusV = outerEnclosure 24
      (leaf1239Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1239RoundedFacts : LeafRoundedFacts 8
    leaf1239Certificate.logOnePlusV leaf1239InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1239InputLogOnePlusV_eq }

private noncomputable def leaf1239Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi119InputQChi innerPair50Input
    leaf1239InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1239LowerChecked :
    lowerCheck 24 leaf1239Box leaf1239Inputs = true := by
  rfl'

private theorem leaf1239CoversExact : CoversExact 8
    leaf1239Box leaf1239Certificate leaf1239InnerLog leaf1239Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi119RoundedFacts
    innerPair50RoundedFacts leaf1239RoundedFacts (by rfl)

private theorem leaf1239FlatSound : Sound leaf1239Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1239CertificateValid
    leaf1239InnerLogValid leaf1239CoversExact leaf1239LowerChecked

private noncomputable def leaf1240Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (29/128), chiHi := (15/64) }

private noncomputable def leaf1240Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435691/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716773376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (433739691/268435456) }, upper := { exponent := 0, mantissa := (421/256) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi120LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435267071/137433546752) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf1240InnerLog : WideLogData :=
  innerPair167Data

set_option maxRecDepth 1000000 in
private theorem leaf1240LocalValidity :
    LeafFacts leaf1240Box leaf1240Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1240Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716773376) }) = true
      norm_num [leaf1240Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1240CertificateValid :
    WideCertificateValid leaf1240Box leaf1240Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi120ValidityFacts
    leaf1240LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1240CoverageChecked :
    coverageCheck (innerAD leaf1240Box) leaf1240InnerLog = true := by
  rfl'

private theorem leaf1240InnerLogValid :
    leaf1240InnerLog.Valid 8 (innerAD leaf1240Box) :=
  wideLogDataValid_of_cachedCheck endpoint46PositiveFacts
    endpoint48PositiveFacts.valid leaf1240CoverageChecked

private noncomputable def leaf1240InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1240InputLogOnePlusV_eq :
    leaf1240InputLogOnePlusV = outerEnclosure 24
      (leaf1240Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1240RoundedFacts : LeafRoundedFacts 8
    leaf1240Certificate.logOnePlusV leaf1240InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1240InputLogOnePlusV_eq }

private noncomputable def leaf1240Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi120InputQChi innerPair167Input
    leaf1240InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1240LowerChecked :
    lowerCheck 24 leaf1240Box leaf1240Inputs = true := by
  rfl'

private theorem leaf1240CoversExact : CoversExact 8
    leaf1240Box leaf1240Certificate leaf1240InnerLog leaf1240Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi120RoundedFacts
    innerPair167RoundedFacts leaf1240RoundedFacts (by rfl)

private theorem leaf1240FlatSound : Sound leaf1240Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1240CertificateValid
    leaf1240InnerLogValid leaf1240CoversExact leaf1240LowerChecked

private noncomputable def leaf1241Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1241Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435691/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716715008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (437475015/268435456) }, upper := { exponent := 0, mantissa := (6793/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435208703/137433430016) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf1241InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1241LocalValidity :
    LeafFacts leaf1241Box leaf1241Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1241Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716715008) }) = true
      norm_num [leaf1241Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1241CertificateValid :
    WideCertificateValid leaf1241Box leaf1241Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi121ValidityFacts
    leaf1241LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1241CoverageChecked :
    coverageCheck (innerAD leaf1241Box) leaf1241InnerLog = true := by
  rfl'

private theorem leaf1241InnerLogValid :
    leaf1241InnerLog.Valid 8 (innerAD leaf1241Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1241CoverageChecked

private noncomputable def leaf1241InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1241InputLogOnePlusV_eq :
    leaf1241InputLogOnePlusV = outerEnclosure 24
      (leaf1241Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1241RoundedFacts : LeafRoundedFacts 8
    leaf1241Certificate.logOnePlusV leaf1241InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1241InputLogOnePlusV_eq }

private noncomputable def leaf1241Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi121InputQChi innerPair56Input
    leaf1241InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1241LowerChecked :
    lowerCheck 24 leaf1241Box leaf1241Inputs = true := by
  rfl'

private theorem leaf1241CoversExact : CoversExact 8
    leaf1241Box leaf1241Certificate leaf1241InnerLog leaf1241Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi121RoundedFacts
    innerPair56RoundedFacts leaf1241RoundedFacts (by rfl)

private theorem leaf1241FlatSound : Sound leaf1241Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1241CertificateValid
    leaf1241InnerLogValid leaf1241CoversExact leaf1241LowerChecked

private noncomputable def leaf1242Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1242Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435693/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743325184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (443110765/268435456) }, upper := { exponent := 0, mantissa := (215/128) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487023923/27486650368) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf1242InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1242LocalValidity :
    LeafFacts leaf1242Box leaf1242Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1242Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743325184) }) = true
      norm_num [leaf1242Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1242CertificateValid :
    WideCertificateValid leaf1242Box leaf1242Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi122ValidityFacts
    leaf1242LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1242CoverageChecked :
    coverageCheck (innerAD leaf1242Box) leaf1242InnerLog = true := by
  rfl'

private theorem leaf1242InnerLogValid :
    leaf1242InnerLog.Valid 8 (innerAD leaf1242Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1242CoverageChecked

private noncomputable def leaf1242InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1242InputLogOnePlusV_eq :
    leaf1242InputLogOnePlusV = outerEnclosure 24
      (leaf1242Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1242RoundedFacts : LeafRoundedFacts 8
    leaf1242Certificate.logOnePlusV leaf1242InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1242InputLogOnePlusV_eq }

private noncomputable def leaf1242Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi122InputQChi innerPair56Input
    leaf1242InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1242LowerChecked :
    lowerCheck 24 leaf1242Box leaf1242Inputs = true := by
  rfl'

private theorem leaf1242CoversExact : CoversExact 8
    leaf1242Box leaf1242Certificate leaf1242InnerLog leaf1242Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi122RoundedFacts
    innerPair56RoundedFacts leaf1242RoundedFacts (by rfl)

private theorem leaf1242FlatSound : Sound leaf1242Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1242CertificateValid
    leaf1242InnerLogValid leaf1242CoversExact leaf1242LowerChecked

private noncomputable def leaf1243Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (15/64), chiHi := (31/128) }

private noncomputable def leaf1243Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435693/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905561088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (439440973/268435456) }, upper := { exponent := 0, mantissa := (853/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi121LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811725653/45811122176) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf1243InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1243LocalValidity :
    LeafFacts leaf1243Box leaf1243Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1243Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905561088) }) = true
      norm_num [leaf1243Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1243CertificateValid :
    WideCertificateValid leaf1243Box leaf1243Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi121ValidityFacts
    leaf1243LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1243CoverageChecked :
    coverageCheck (innerAD leaf1243Box) leaf1243InnerLog = true := by
  rfl'

private theorem leaf1243InnerLogValid :
    leaf1243InnerLog.Valid 8 (innerAD leaf1243Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1243CoverageChecked

private noncomputable def leaf1243InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1243InputLogOnePlusV_eq :
    leaf1243InputLogOnePlusV = outerEnclosure 24
      (leaf1243Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1243RoundedFacts : LeafRoundedFacts 8
    leaf1243Certificate.logOnePlusV leaf1243InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1243InputLogOnePlusV_eq }

private noncomputable def leaf1243Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi121InputQChi innerPair56Input
    leaf1243InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1243LowerChecked :
    lowerCheck 24 leaf1243Box leaf1243Inputs = true := by
  rfl'

private theorem leaf1243CoversExact : CoversExact 8
    leaf1243Box leaf1243Certificate leaf1243InnerLog leaf1243Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi121RoundedFacts
    innerPair56RoundedFacts leaf1243RoundedFacts (by rfl)

private theorem leaf1243FlatSound : Sound leaf1243Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1243CertificateValid
    leaf1243InnerLogValid leaf1243CoversExact leaf1243LowerChecked

private noncomputable def leaf1244Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (31/128), chiHi := (1/4) }

private noncomputable def leaf1244Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435695/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716593152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (445142255/268435456) }, upper := { exponent := 0, mantissa := (27/16) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi122LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435086847/137433186304) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf1244InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1244LocalValidity :
    LeafFacts leaf1244Box leaf1244Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1244Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716593152) }) = true
      norm_num [leaf1244Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1244CertificateValid :
    WideCertificateValid leaf1244Box leaf1244Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi122ValidityFacts
    leaf1244LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1244CoverageChecked :
    coverageCheck (innerAD leaf1244Box) leaf1244InnerLog = true := by
  rfl'

private theorem leaf1244InnerLogValid :
    leaf1244InnerLog.Valid 8 (innerAD leaf1244Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1244CoverageChecked

private noncomputable def leaf1244InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1244InputLogOnePlusV_eq :
    leaf1244InputLogOnePlusV = outerEnclosure 24
      (leaf1244Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1244RoundedFacts : LeafRoundedFacts 8
    leaf1244Certificate.logOnePlusV leaf1244InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1244InputLogOnePlusV_eq }

private noncomputable def leaf1244Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi122InputQChi innerPair56Input
    leaf1244InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1244LowerChecked :
    lowerCheck 24 leaf1244Box leaf1244Inputs = true := by
  rfl'

private theorem leaf1244CoversExact : CoversExact 8
    leaf1244Box leaf1244Certificate leaf1244InnerLog leaf1244Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi122RoundedFacts
    innerPair56RoundedFacts leaf1244RoundedFacts (by rfl)

private theorem leaf1244FlatSound : Sound leaf1244Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1244CertificateValid
    leaf1244InnerLogValid leaf1244CoversExact leaf1244LowerChecked

private noncomputable def component28Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node0_sound : Sound component28Node0Box :=
  sound_of_literal_split component28Node0Box leaf1181Box leaf1182Box
    .chi (25/128) (by rfl) (by rfl)
    leaf1181FlatSound leaf1182FlatSound

private noncomputable def component28Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node1_sound : Sound component28Node1Box :=
  sound_of_literal_split component28Node1Box leaf1183Box leaf1184Box
    .chi (25/128) (by rfl) (by rfl)
    leaf1183FlatSound leaf1184FlatSound

private noncomputable def component28Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node2_sound : Sound component28Node2Box :=
  sound_of_literal_split component28Node2Box component28Node0Box component28Node1Box
    .k (81/32) (by rfl) (by rfl)
    component28Node0_sound component28Node1_sound

private noncomputable def component28Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node3_sound : Sound component28Node3Box :=
  sound_of_literal_split component28Node3Box leaf1185Box leaf1186Box
    .chi (27/128) (by rfl) (by rfl)
    leaf1185FlatSound leaf1186FlatSound

private noncomputable def component28Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node4_sound : Sound component28Node4Box :=
  sound_of_literal_split component28Node4Box leaf1187Box leaf1188Box
    .chi (27/128) (by rfl) (by rfl)
    leaf1187FlatSound leaf1188FlatSound

private noncomputable def component28Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node5_sound : Sound component28Node5Box :=
  sound_of_literal_split component28Node5Box component28Node3Box component28Node4Box
    .k (81/32) (by rfl) (by rfl)
    component28Node3_sound component28Node4_sound

private noncomputable def component28Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node6_sound : Sound component28Node6Box :=
  sound_of_literal_split component28Node6Box component28Node2Box component28Node5Box
    .chi (13/64) (by rfl) (by rfl)
    component28Node2_sound component28Node5_sound

private noncomputable def component28Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node7_sound : Sound component28Node7Box :=
  sound_of_literal_split component28Node7Box leaf1189Box leaf1190Box
    .chi (25/128) (by rfl) (by rfl)
    leaf1189FlatSound leaf1190FlatSound

private noncomputable def component28Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node8_sound : Sound component28Node8Box :=
  sound_of_literal_split component28Node8Box leaf1191Box leaf1192Box
    .chi (25/128) (by rfl) (by rfl)
    leaf1191FlatSound leaf1192FlatSound

private noncomputable def component28Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node9_sound : Sound component28Node9Box :=
  sound_of_literal_split component28Node9Box component28Node7Box component28Node8Box
    .k (83/32) (by rfl) (by rfl)
    component28Node7_sound component28Node8_sound

private noncomputable def component28Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node10_sound : Sound component28Node10Box :=
  sound_of_literal_split component28Node10Box leaf1193Box leaf1194Box
    .chi (27/128) (by rfl) (by rfl)
    leaf1193FlatSound leaf1194FlatSound

private noncomputable def component28Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node11_sound : Sound component28Node11Box :=
  sound_of_literal_split component28Node11Box leaf1195Box leaf1196Box
    .chi (27/128) (by rfl) (by rfl)
    leaf1195FlatSound leaf1196FlatSound

private noncomputable def component28Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node12_sound : Sound component28Node12Box :=
  sound_of_literal_split component28Node12Box component28Node10Box component28Node11Box
    .k (83/32) (by rfl) (by rfl)
    component28Node10_sound component28Node11_sound

private noncomputable def component28Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node13_sound : Sound component28Node13Box :=
  sound_of_literal_split component28Node13Box component28Node9Box component28Node12Box
    .chi (13/64) (by rfl) (by rfl)
    component28Node9_sound component28Node12_sound

private noncomputable def component28Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node14_sound : Sound component28Node14Box :=
  sound_of_literal_split component28Node14Box component28Node6Box component28Node13Box
    .k (41/16) (by rfl) (by rfl)
    component28Node6_sound component28Node13_sound

private noncomputable def component28Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node15_sound : Sound component28Node15Box :=
  sound_of_literal_split component28Node15Box leaf1197Box leaf1198Box
    .chi (29/128) (by rfl) (by rfl)
    leaf1197FlatSound leaf1198FlatSound

private noncomputable def component28Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node16_sound : Sound component28Node16Box :=
  sound_of_literal_split component28Node16Box leaf1199Box leaf1200Box
    .chi (29/128) (by rfl) (by rfl)
    leaf1199FlatSound leaf1200FlatSound

private noncomputable def component28Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node17_sound : Sound component28Node17Box :=
  sound_of_literal_split component28Node17Box component28Node15Box component28Node16Box
    .k (81/32) (by rfl) (by rfl)
    component28Node15_sound component28Node16_sound

private noncomputable def component28Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node18_sound : Sound component28Node18Box :=
  sound_of_literal_split component28Node18Box leaf1201Box leaf1202Box
    .chi (31/128) (by rfl) (by rfl)
    leaf1201FlatSound leaf1202FlatSound

private noncomputable def component28Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node19_sound : Sound component28Node19Box :=
  sound_of_literal_split component28Node19Box leaf1203Box leaf1204Box
    .chi (31/128) (by rfl) (by rfl)
    leaf1203FlatSound leaf1204FlatSound

private noncomputable def component28Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node20_sound : Sound component28Node20Box :=
  sound_of_literal_split component28Node20Box component28Node18Box component28Node19Box
    .k (81/32) (by rfl) (by rfl)
    component28Node18_sound component28Node19_sound

private noncomputable def component28Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node21_sound : Sound component28Node21Box :=
  sound_of_literal_split component28Node21Box component28Node17Box component28Node20Box
    .chi (15/64) (by rfl) (by rfl)
    component28Node17_sound component28Node20_sound

private noncomputable def component28Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node22_sound : Sound component28Node22Box :=
  sound_of_literal_split component28Node22Box leaf1205Box leaf1206Box
    .chi (29/128) (by rfl) (by rfl)
    leaf1205FlatSound leaf1206FlatSound

private noncomputable def component28Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node23_sound : Sound component28Node23Box :=
  sound_of_literal_split component28Node23Box leaf1207Box leaf1208Box
    .chi (29/128) (by rfl) (by rfl)
    leaf1207FlatSound leaf1208FlatSound

private noncomputable def component28Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node24_sound : Sound component28Node24Box :=
  sound_of_literal_split component28Node24Box component28Node22Box component28Node23Box
    .k (83/32) (by rfl) (by rfl)
    component28Node22_sound component28Node23_sound

private noncomputable def component28Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node25_sound : Sound component28Node25Box :=
  sound_of_literal_split component28Node25Box leaf1209Box leaf1210Box
    .chi (31/128) (by rfl) (by rfl)
    leaf1209FlatSound leaf1210FlatSound

private noncomputable def component28Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node26_sound : Sound component28Node26Box :=
  sound_of_literal_split component28Node26Box leaf1211Box leaf1212Box
    .chi (31/128) (by rfl) (by rfl)
    leaf1211FlatSound leaf1212FlatSound

private noncomputable def component28Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node27_sound : Sound component28Node27Box :=
  sound_of_literal_split component28Node27Box component28Node25Box component28Node26Box
    .k (83/32) (by rfl) (by rfl)
    component28Node25_sound component28Node26_sound

private noncomputable def component28Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node28_sound : Sound component28Node28Box :=
  sound_of_literal_split component28Node28Box component28Node24Box component28Node27Box
    .chi (15/64) (by rfl) (by rfl)
    component28Node24_sound component28Node27_sound

private noncomputable def component28Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node29_sound : Sound component28Node29Box :=
  sound_of_literal_split component28Node29Box component28Node21Box component28Node28Box
    .k (41/16) (by rfl) (by rfl)
    component28Node21_sound component28Node28_sound

private noncomputable def component28Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node30_sound : Sound component28Node30Box :=
  sound_of_literal_split component28Node30Box component28Node14Box component28Node29Box
    .chi (7/32) (by rfl) (by rfl)
    component28Node14_sound component28Node29_sound

private noncomputable def component28Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node31_sound : Sound component28Node31Box :=
  sound_of_literal_split component28Node31Box leaf1213Box leaf1214Box
    .chi (25/128) (by rfl) (by rfl)
    leaf1213FlatSound leaf1214FlatSound

private noncomputable def component28Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node32_sound : Sound component28Node32Box :=
  sound_of_literal_split component28Node32Box leaf1215Box leaf1216Box
    .chi (25/128) (by rfl) (by rfl)
    leaf1215FlatSound leaf1216FlatSound

private noncomputable def component28Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node33_sound : Sound component28Node33Box :=
  sound_of_literal_split component28Node33Box component28Node31Box component28Node32Box
    .k (85/32) (by rfl) (by rfl)
    component28Node31_sound component28Node32_sound

private noncomputable def component28Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node34_sound : Sound component28Node34Box :=
  sound_of_literal_split component28Node34Box leaf1217Box leaf1218Box
    .chi (27/128) (by rfl) (by rfl)
    leaf1217FlatSound leaf1218FlatSound

private noncomputable def component28Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node35_sound : Sound component28Node35Box :=
  sound_of_literal_split component28Node35Box leaf1219Box leaf1220Box
    .chi (27/128) (by rfl) (by rfl)
    leaf1219FlatSound leaf1220FlatSound

private noncomputable def component28Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node36_sound : Sound component28Node36Box :=
  sound_of_literal_split component28Node36Box component28Node34Box component28Node35Box
    .k (85/32) (by rfl) (by rfl)
    component28Node34_sound component28Node35_sound

private noncomputable def component28Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node37_sound : Sound component28Node37Box :=
  sound_of_literal_split component28Node37Box component28Node33Box component28Node36Box
    .chi (13/64) (by rfl) (by rfl)
    component28Node33_sound component28Node36_sound

private noncomputable def component28Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node38_sound : Sound component28Node38Box :=
  sound_of_literal_split component28Node38Box leaf1221Box leaf1222Box
    .chi (25/128) (by rfl) (by rfl)
    leaf1221FlatSound leaf1222FlatSound

private noncomputable def component28Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node39_sound : Sound component28Node39Box :=
  sound_of_literal_split component28Node39Box leaf1223Box leaf1224Box
    .chi (25/128) (by rfl) (by rfl)
    leaf1223FlatSound leaf1224FlatSound

private noncomputable def component28Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node40_sound : Sound component28Node40Box :=
  sound_of_literal_split component28Node40Box component28Node38Box component28Node39Box
    .k (87/32) (by rfl) (by rfl)
    component28Node38_sound component28Node39_sound

private noncomputable def component28Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node41_sound : Sound component28Node41Box :=
  sound_of_literal_split component28Node41Box leaf1225Box leaf1226Box
    .chi (27/128) (by rfl) (by rfl)
    leaf1225FlatSound leaf1226FlatSound

private noncomputable def component28Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node42_sound : Sound component28Node42Box :=
  sound_of_literal_split component28Node42Box leaf1227Box leaf1228Box
    .chi (27/128) (by rfl) (by rfl)
    leaf1227FlatSound leaf1228FlatSound

private noncomputable def component28Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node43_sound : Sound component28Node43Box :=
  sound_of_literal_split component28Node43Box component28Node41Box component28Node42Box
    .k (87/32) (by rfl) (by rfl)
    component28Node41_sound component28Node42_sound

private noncomputable def component28Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node44_sound : Sound component28Node44Box :=
  sound_of_literal_split component28Node44Box component28Node40Box component28Node43Box
    .chi (13/64) (by rfl) (by rfl)
    component28Node40_sound component28Node43_sound

private noncomputable def component28Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component28Node45_sound : Sound component28Node45Box :=
  sound_of_literal_split component28Node45Box component28Node37Box component28Node44Box
    .k (43/16) (by rfl) (by rfl)
    component28Node37_sound component28Node44_sound

private noncomputable def component28Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node46_sound : Sound component28Node46Box :=
  sound_of_literal_split component28Node46Box leaf1229Box leaf1230Box
    .chi (29/128) (by rfl) (by rfl)
    leaf1229FlatSound leaf1230FlatSound

private noncomputable def component28Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node47_sound : Sound component28Node47Box :=
  sound_of_literal_split component28Node47Box leaf1231Box leaf1232Box
    .chi (29/128) (by rfl) (by rfl)
    leaf1231FlatSound leaf1232FlatSound

private noncomputable def component28Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node48_sound : Sound component28Node48Box :=
  sound_of_literal_split component28Node48Box component28Node46Box component28Node47Box
    .k (85/32) (by rfl) (by rfl)
    component28Node46_sound component28Node47_sound

private noncomputable def component28Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node49_sound : Sound component28Node49Box :=
  sound_of_literal_split component28Node49Box leaf1233Box leaf1234Box
    .chi (31/128) (by rfl) (by rfl)
    leaf1233FlatSound leaf1234FlatSound

private noncomputable def component28Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node50_sound : Sound component28Node50Box :=
  sound_of_literal_split component28Node50Box leaf1235Box leaf1236Box
    .chi (31/128) (by rfl) (by rfl)
    leaf1235FlatSound leaf1236FlatSound

private noncomputable def component28Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node51_sound : Sound component28Node51Box :=
  sound_of_literal_split component28Node51Box component28Node49Box component28Node50Box
    .k (85/32) (by rfl) (by rfl)
    component28Node49_sound component28Node50_sound

private noncomputable def component28Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node52_sound : Sound component28Node52Box :=
  sound_of_literal_split component28Node52Box component28Node48Box component28Node51Box
    .chi (15/64) (by rfl) (by rfl)
    component28Node48_sound component28Node51_sound

private noncomputable def component28Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node53_sound : Sound component28Node53Box :=
  sound_of_literal_split component28Node53Box leaf1237Box leaf1238Box
    .chi (29/128) (by rfl) (by rfl)
    leaf1237FlatSound leaf1238FlatSound

private noncomputable def component28Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node54_sound : Sound component28Node54Box :=
  sound_of_literal_split component28Node54Box leaf1239Box leaf1240Box
    .chi (29/128) (by rfl) (by rfl)
    leaf1239FlatSound leaf1240FlatSound

private noncomputable def component28Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component28Node55_sound : Sound component28Node55Box :=
  sound_of_literal_split component28Node55Box component28Node53Box component28Node54Box
    .k (87/32) (by rfl) (by rfl)
    component28Node53_sound component28Node54_sound

private noncomputable def component28Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node56_sound : Sound component28Node56Box :=
  sound_of_literal_split component28Node56Box leaf1241Box leaf1242Box
    .chi (31/128) (by rfl) (by rfl)
    leaf1241FlatSound leaf1242FlatSound

private noncomputable def component28Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node57_sound : Sound component28Node57Box :=
  sound_of_literal_split component28Node57Box leaf1243Box leaf1244Box
    .chi (31/128) (by rfl) (by rfl)
    leaf1243FlatSound leaf1244FlatSound

private noncomputable def component28Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node58_sound : Sound component28Node58Box :=
  sound_of_literal_split component28Node58Box component28Node56Box component28Node57Box
    .k (87/32) (by rfl) (by rfl)
    component28Node56_sound component28Node57_sound

private noncomputable def component28Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node59_sound : Sound component28Node59Box :=
  sound_of_literal_split component28Node59Box component28Node55Box component28Node58Box
    .chi (15/64) (by rfl) (by rfl)
    component28Node55_sound component28Node58_sound

private noncomputable def component28Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node60_sound : Sound component28Node60Box :=
  sound_of_literal_split component28Node60Box component28Node52Box component28Node59Box
    .k (43/16) (by rfl) (by rfl)
    component28Node52_sound component28Node59_sound

private noncomputable def component28Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component28Node61_sound : Sound component28Node61Box :=
  sound_of_literal_split component28Node61Box component28Node45Box component28Node60Box
    .chi (7/32) (by rfl) (by rfl)
    component28Node45_sound component28Node60_sound

noncomputable def component28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
theorem component28_sound : Sound component28Box :=
  sound_of_literal_split component28Box component28Node30Box component28Node61Box
    .k (21/8) (by rfl) (by rfl)
    component28Node30_sound component28Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
