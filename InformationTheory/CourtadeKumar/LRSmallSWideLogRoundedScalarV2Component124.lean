import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch9
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

private noncomputable def leaf6182Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf6182Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109003/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178618880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (142568823/134217728) }, upper := { exponent := 1, mantissa := (2245/2048) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357996543/34357237760) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6182InnerLog : WideLogData :=
  innerPair337Data

set_option maxRecDepth 1000000 in
private theorem leaf6182LocalValidity :
    LeafFacts leaf6182Box leaf6182Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6182Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178618880) }) = true
      norm_num [leaf6182Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6182CertificateValid :
    WideCertificateValid leaf6182Box leaf6182Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi82ValidityFacts
    leaf6182LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6182CoverageChecked :
    coverageCheck (innerAD leaf6182Box) leaf6182InnerLog = true := by
  rfl'

private theorem leaf6182InnerLogValid :
    leaf6182InnerLog.Valid 8 (innerAD leaf6182Box) :=
  wideLogDataValid_of_cachedCheck endpoint89PositiveFacts
    endpoint291PositiveFacts.valid leaf6182CoverageChecked

private noncomputable def leaf6182InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6182InputLogOnePlusV_eq :
    leaf6182InputLogOnePlusV = outerEnclosure 24
      (leaf6182Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6182RoundedFacts : LeafRoundedFacts 8
    leaf6182Certificate.logOnePlusV leaf6182InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6182InputLogOnePlusV_eq }

private noncomputable def leaf6182Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi82InputQChi innerPair337Input
    leaf6182InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6182LowerChecked :
    lowerCheck 24 leaf6182Box leaf6182Inputs = true := by
  rfl'

private theorem leaf6182CoversExact : CoversExact 8
    leaf6182Box leaf6182Certificate leaf6182InnerLog leaf6182Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi82RoundedFacts
    innerPair337RoundedFacts leaf6182RoundedFacts (by rfl)

private theorem leaf6182FlatSound : Sound leaf6182Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6182CertificateValid
    leaf6182InnerLogValid leaf6182CoversExact leaf6182LowerChecked

private noncomputable def leaf6183Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (33/64), chiHi := (17/32) }

private noncomputable def leaf6183Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109005/67108864) }, vSqrt := { lower := (65531/65536), upper := (5726459221/5726193664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (144927973/134217728) }, upper := { exponent := 1, mantissa := (1141/1024) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi83LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11452652885/11452387328) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6183InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf6183LocalValidity :
    LeafFacts leaf6183Box leaf6183Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6183Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5726459221/5726193664) }) = true
      norm_num [leaf6183Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6183CertificateValid :
    WideCertificateValid leaf6183Box leaf6183Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi83ValidityFacts
    leaf6183LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6183CoverageChecked :
    coverageCheck (innerAD leaf6183Box) leaf6183InnerLog = true := by
  rfl'

private theorem leaf6183InnerLogValid :
    leaf6183InnerLog.Valid 8 (innerAD leaf6183Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf6183CoverageChecked

private noncomputable def leaf6183InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814735/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6183InputLogOnePlusV_eq :
    leaf6183InputLogOnePlusV = outerEnclosure 24
      (leaf6183Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6183RoundedFacts : LeafRoundedFacts 8
    leaf6183Certificate.logOnePlusV leaf6183InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6183InputLogOnePlusV_eq }

private noncomputable def leaf6183Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi83InputQChi innerPair250Input
    leaf6183InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6183LowerChecked :
    lowerCheck 24 leaf6183Box leaf6183Inputs = true := by
  rfl'

private theorem leaf6183CoversExact : CoversExact 8
    leaf6183Box leaf6183Certificate leaf6183InnerLog leaf6183Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi83RoundedFacts
    innerPair250RoundedFacts leaf6183RoundedFacts (by rfl)

private theorem leaf6183FlatSound : Sound leaf6183Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6183CertificateValid
    leaf6183InnerLogValid leaf6183CoversExact leaf6183LowerChecked

private noncomputable def leaf6184Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf6184Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109005/67108864) }, vSqrt := { lower := (65531/65536), upper := (2454196809/2454083584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (144665845/134217728) }, upper := { exponent := 1, mantissa := (1139/1024) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4908280393/4908167168) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6184InnerLog : WideLogData :=
  innerPair616Data

set_option maxRecDepth 1000000 in
private theorem leaf6184LocalValidity :
    LeafFacts leaf6184Box leaf6184Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6184Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2454196809/2454083584) }) = true
      norm_num [leaf6184Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6184CertificateValid :
    WideCertificateValid leaf6184Box leaf6184Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi82ValidityFacts
    leaf6184LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6184CoverageChecked :
    coverageCheck (innerAD leaf6184Box) leaf6184InnerLog = true := by
  rfl'

private theorem leaf6184InnerLogValid :
    leaf6184InnerLog.Valid 8 (innerAD leaf6184Box) :=
  wideLogDataValid_of_cachedCheck endpoint341PositiveFacts
    endpoint379PositiveFacts.valid leaf6184CoverageChecked

private noncomputable def leaf6184InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907367/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6184InputLogOnePlusV_eq :
    leaf6184InputLogOnePlusV = outerEnclosure 24
      (leaf6184Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6184RoundedFacts : LeafRoundedFacts 8
    leaf6184Certificate.logOnePlusV leaf6184InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6184InputLogOnePlusV_eq }

private noncomputable def leaf6184Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi82InputQChi innerPair616Input
    leaf6184InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6184LowerChecked :
    lowerCheck 24 leaf6184Box leaf6184Inputs = true := by
  rfl'

private theorem leaf6184CoversExact : CoversExact 8
    leaf6184Box leaf6184Certificate leaf6184InnerLog leaf6184Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi82RoundedFacts
    innerPair616RoundedFacts leaf6184RoundedFacts (by rfl)

private theorem leaf6184FlatSound : Sound leaf6184Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6184CertificateValid
    leaf6184InnerLogValid leaf6184CoversExact leaf6184LowerChecked

private noncomputable def leaf6185Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (33/64), chiHi := (17/32) }

private noncomputable def leaf6185Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109007/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178546176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (147090527/134217728) }, upper := { exponent := 1, mantissa := (579/512) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi83LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357923839/34357092352) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6185InnerLog : WideLogData :=
  innerPair261Data

set_option maxRecDepth 1000000 in
private theorem leaf6185LocalValidity :
    LeafFacts leaf6185Box leaf6185Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6185Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178546176) }) = true
      norm_num [leaf6185Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6185CertificateValid :
    WideCertificateValid leaf6185Box leaf6185Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi83ValidityFacts
    leaf6185LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6185CoverageChecked :
    coverageCheck (innerAD leaf6185Box) leaf6185InnerLog = true := by
  rfl'

private theorem leaf6185InnerLogValid :
    leaf6185InnerLog.Valid 8 (innerAD leaf6185Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint292PositiveFacts.valid leaf6185CoverageChecked

private noncomputable def leaf6185InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629487/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6185InputLogOnePlusV_eq :
    leaf6185InputLogOnePlusV = outerEnclosure 24
      (leaf6185Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6185RoundedFacts : LeafRoundedFacts 8
    leaf6185Certificate.logOnePlusV leaf6185InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6185InputLogOnePlusV_eq }

private noncomputable def leaf6185Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi83InputQChi innerPair261Input
    leaf6185InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6185LowerChecked :
    lowerCheck 24 leaf6185Box leaf6185Inputs = true := by
  rfl'

private theorem leaf6185CoversExact : CoversExact 8
    leaf6185Box leaf6185Certificate leaf6185InnerLog leaf6185Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi83RoundedFacts
    innerPair261RoundedFacts leaf6185RoundedFacts (by rfl)

private theorem leaf6185FlatSound : Sound leaf6185Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6185CertificateValid
    leaf6185InnerLogValid leaf6185CoversExact leaf6185LowerChecked

private noncomputable def leaf6186Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (17/32), chiHi := (35/64) }

private noncomputable def leaf6186Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109007/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178543104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (147287123/134217728) }, upper := { exponent := 1, mantissa := (2319/2048) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi84LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357920767/34357086208) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6186InnerLog : WideLogData :=
  innerPair261Data

set_option maxRecDepth 1000000 in
private theorem leaf6186LocalValidity :
    LeafFacts leaf6186Box leaf6186Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6186Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178543104) }) = true
      norm_num [leaf6186Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6186CertificateValid :
    WideCertificateValid leaf6186Box leaf6186Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi84ValidityFacts
    leaf6186LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6186CoverageChecked :
    coverageCheck (innerAD leaf6186Box) leaf6186InnerLog = true := by
  rfl'

private theorem leaf6186InnerLogValid :
    leaf6186InnerLog.Valid 8 (innerAD leaf6186Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint292PositiveFacts.valid leaf6186CoverageChecked

private noncomputable def leaf6186InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (726843/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6186InputLogOnePlusV_eq :
    leaf6186InputLogOnePlusV = outerEnclosure 24
      (leaf6186Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6186RoundedFacts : LeafRoundedFacts 8
    leaf6186Certificate.logOnePlusV leaf6186InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6186InputLogOnePlusV_eq }

private noncomputable def leaf6186Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi84InputQChi innerPair261Input
    leaf6186InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6186LowerChecked :
    lowerCheck 24 leaf6186Box leaf6186Inputs = true := by
  rfl'

private theorem leaf6186CoversExact : CoversExact 8
    leaf6186Box leaf6186Certificate leaf6186InnerLog leaf6186Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi84RoundedFacts
    innerPair261RoundedFacts leaf6186RoundedFacts (by rfl)

private theorem leaf6186FlatSound : Sound leaf6186Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6186CertificateValid
    leaf6186InnerLogValid leaf6186CoversExact leaf6186LowerChecked

private noncomputable def leaf6187Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (35/64), chiHi := (9/16) }

private noncomputable def leaf6187Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109009/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178505216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (149646273/134217728) }, upper := { exponent := 1, mantissa := (589/512) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi85LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357882879/34357010432) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6187InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf6187LocalValidity :
    LeafFacts leaf6187Box leaf6187Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6187Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178505216) }) = true
      norm_num [leaf6187Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6187CertificateValid :
    WideCertificateValid leaf6187Box leaf6187Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi85ValidityFacts
    leaf6187LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6187CoverageChecked :
    coverageCheck (innerAD leaf6187Box) leaf6187InnerLog = true := by
  rfl'

private theorem leaf6187InnerLogValid :
    leaf6187InnerLog.Valid 8 (innerAD leaf6187Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf6187CoverageChecked

private noncomputable def leaf6187InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629507/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6187InputLogOnePlusV_eq :
    leaf6187InputLogOnePlusV = outerEnclosure 24
      (leaf6187Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6187RoundedFacts : LeafRoundedFacts 8
    leaf6187Certificate.logOnePlusV leaf6187InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6187InputLogOnePlusV_eq }

private noncomputable def leaf6187Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi85InputQChi innerPair257Input
    leaf6187InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6187LowerChecked :
    lowerCheck 24 leaf6187Box leaf6187Inputs = true := by
  rfl'

private theorem leaf6187CoversExact : CoversExact 8
    leaf6187Box leaf6187Certificate leaf6187InnerLog leaf6187Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi85RoundedFacts
    innerPair257RoundedFacts leaf6187RoundedFacts (by rfl)

private theorem leaf6187FlatSound : Sound leaf6187Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6187CertificateValid
    leaf6187InnerLogValid leaf6187CoversExact leaf6187LowerChecked

private noncomputable def leaf6188Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (17/32), chiHi := (35/64) }

private noncomputable def leaf6188Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109009/67108864) }, vSqrt := { lower := (65531/65536), upper := (5726459221/5726169088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (149515209/134217728) }, upper := { exponent := 1, mantissa := (1177/1024) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi84LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11452628309/11452338176) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6188InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf6188LocalValidity :
    LeafFacts leaf6188Box leaf6188Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6188Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5726459221/5726169088) }) = true
      norm_num [leaf6188Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6188CertificateValid :
    WideCertificateValid leaf6188Box leaf6188Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi84ValidityFacts
    leaf6188LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6188CoverageChecked :
    coverageCheck (innerAD leaf6188Box) leaf6188InnerLog = true := by
  rfl'

private theorem leaf6188InnerLogValid :
    leaf6188InnerLog.Valid 8 (innerAD leaf6188Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf6188CoverageChecked

private noncomputable def leaf6188InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814753/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6188InputLogOnePlusV_eq :
    leaf6188InputLogOnePlusV = outerEnclosure 24
      (leaf6188Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6188RoundedFacts : LeafRoundedFacts 8
    leaf6188Certificate.logOnePlusV leaf6188InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6188InputLogOnePlusV_eq }

private noncomputable def leaf6188Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi84InputQChi innerPair257Input
    leaf6188InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6188LowerChecked :
    lowerCheck 24 leaf6188Box leaf6188Inputs = true := by
  rfl'

private theorem leaf6188CoversExact : CoversExact 8
    leaf6188Box leaf6188Certificate leaf6188InnerLog leaf6188Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi84RoundedFacts
    innerPair257RoundedFacts leaf6188RoundedFacts (by rfl)

private theorem leaf6188FlatSound : Sound leaf6188Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6188CertificateValid
    leaf6188InnerLogValid leaf6188CoversExact leaf6188LowerChecked

private noncomputable def leaf6189Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (35/64), chiHi := (9/16) }

private noncomputable def leaf6189Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109011/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178468352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (151939891/134217728) }, upper := { exponent := 1, mantissa := (299/256) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi85LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357846015/34356936704) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6189InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6189LocalValidity :
    LeafFacts leaf6189Box leaf6189Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6189Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178468352) }) = true
      norm_num [leaf6189Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6189CertificateValid :
    WideCertificateValid leaf6189Box leaf6189Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi85ValidityFacts
    leaf6189LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6189CoverageChecked :
    coverageCheck (innerAD leaf6189Box) leaf6189InnerLog = true := by
  rfl'

private theorem leaf6189InnerLogValid :
    leaf6189InnerLog.Valid 8 (innerAD leaf6189Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6189CoverageChecked

private noncomputable def leaf6189InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629525/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6189InputLogOnePlusV_eq :
    leaf6189InputLogOnePlusV = outerEnclosure 24
      (leaf6189Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6189RoundedFacts : LeafRoundedFacts 8
    leaf6189Certificate.logOnePlusV leaf6189InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6189InputLogOnePlusV_eq }

private noncomputable def leaf6189Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi85InputQChi innerPair265Input
    leaf6189InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6189LowerChecked :
    lowerCheck 24 leaf6189Box leaf6189Inputs = true := by
  rfl'

private theorem leaf6189CoversExact : CoversExact 8
    leaf6189Box leaf6189Certificate leaf6189InnerLog leaf6189Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi85RoundedFacts
    innerPair265RoundedFacts leaf6189RoundedFacts (by rfl)

private theorem leaf6189FlatSound : Sound leaf6189Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6189CertificateValid
    leaf6189InnerLogValid leaf6189CoversExact leaf6189LowerChecked

private noncomputable def leaf6190Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf6190Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217947/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357136384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (293558567/268435456) }, upper := { exponent := 1, mantissa := (4589/4096) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68715858943/68714272768) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf6190InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf6190LocalValidity :
    LeafFacts leaf6190Box leaf6190Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6190Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357136384) }) = true
      norm_num [leaf6190Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6190CertificateValid :
    WideCertificateValid leaf6190Box leaf6190Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi82ValidityFacts
    leaf6190LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6190CoverageChecked :
    coverageCheck (innerAD leaf6190Box) leaf6190InnerLog = true := by
  rfl'

private theorem leaf6190InnerLogValid :
    leaf6190InnerLog.Valid 8 (innerAD leaf6190Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf6190CoverageChecked

private noncomputable def leaf6190InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907367/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6190InputLogOnePlusV_eq :
    leaf6190InputLogOnePlusV = outerEnclosure 24
      (leaf6190Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6190RoundedFacts : LeafRoundedFacts 8
    leaf6190Certificate.logOnePlusV leaf6190InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6190InputLogOnePlusV_eq }

private noncomputable def leaf6190Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi82InputQChi innerPair250Input
    leaf6190InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6190LowerChecked :
    lowerCheck 24 leaf6190Box leaf6190Inputs = true := by
  rfl'

private theorem leaf6190CoversExact : CoversExact 8
    leaf6190Box leaf6190Certificate leaf6190InnerLog leaf6190Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi82RoundedFacts
    innerPair250RoundedFacts leaf6190RoundedFacts (by rfl)

private theorem leaf6190FlatSound : Sound leaf6190Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6190CertificateValid
    leaf6190InnerLogValid leaf6190CoversExact leaf6190LowerChecked

private noncomputable def leaf6191Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf6191Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217949/134217728) }, vSqrt := { lower := (65531/65536), upper := (1108345889/1108293632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (295655589/268435456) }, upper := { exponent := 1, mantissa := (2311/2048) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (2216639521/2216587264) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf6191InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf6191LocalValidity :
    LeafFacts leaf6191Box leaf6191Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6191Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (1108345889/1108293632) }) = true
      norm_num [leaf6191Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6191CertificateValid :
    WideCertificateValid leaf6191Box leaf6191Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi82ValidityFacts
    leaf6191LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6191CoverageChecked :
    coverageCheck (innerAD leaf6191Box) leaf6191InnerLog = true := by
  rfl'

private theorem leaf6191InnerLogValid :
    leaf6191InnerLog.Valid 8 (innerAD leaf6191Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf6191CoverageChecked

private noncomputable def leaf6191InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907369/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6191InputLogOnePlusV_eq :
    leaf6191InputLogOnePlusV = outerEnclosure 24
      (leaf6191Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6191RoundedFacts : LeafRoundedFacts 8
    leaf6191Certificate.logOnePlusV leaf6191InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6191InputLogOnePlusV_eq }

private noncomputable def leaf6191Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi82InputQChi innerPair257Input
    leaf6191InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6191LowerChecked :
    lowerCheck 24 leaf6191Box leaf6191Inputs = true := by
  rfl'

private theorem leaf6191CoversExact : CoversExact 8
    leaf6191Box leaf6191Certificate leaf6191InnerLog leaf6191Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi82RoundedFacts
    innerPair257RoundedFacts leaf6191RoundedFacts (by rfl)

private theorem leaf6191FlatSound : Sound leaf6191Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6191CertificateValid
    leaf6191InnerLogValid leaf6191CoversExact leaf6191LowerChecked

private noncomputable def leaf6192Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (33/64), chiHi := (17/32) }

private noncomputable def leaf6192Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109009/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178511360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (149253081/134217728) }, upper := { exponent := 1, mantissa := (1175/1024) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi83LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357889023/34357022720) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6192InnerLog : WideLogData :=
  innerPair302Data

set_option maxRecDepth 1000000 in
private theorem leaf6192LocalValidity :
    LeafFacts leaf6192Box leaf6192Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6192Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178511360) }) = true
      norm_num [leaf6192Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6192CertificateValid :
    WideCertificateValid leaf6192Box leaf6192Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi83ValidityFacts
    leaf6192LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6192CoverageChecked :
    coverageCheck (innerAD leaf6192Box) leaf6192InnerLog = true := by
  rfl'

private theorem leaf6192InnerLogValid :
    leaf6192InnerLog.Valid 8 (innerAD leaf6192Box) :=
  wideLogDataValid_of_cachedCheck endpoint80PositiveFacts
    endpoint298PositiveFacts.valid leaf6192CoverageChecked

private noncomputable def leaf6192InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (181711/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf6192InputLogOnePlusV_eq :
    leaf6192InputLogOnePlusV = outerEnclosure 24
      (leaf6192Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6192RoundedFacts : LeafRoundedFacts 8
    leaf6192Certificate.logOnePlusV leaf6192InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6192InputLogOnePlusV_eq }

private noncomputable def leaf6192Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi83InputQChi innerPair302Input
    leaf6192InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6192LowerChecked :
    lowerCheck 24 leaf6192Box leaf6192Inputs = true := by
  rfl'

private theorem leaf6192CoversExact : CoversExact 8
    leaf6192Box leaf6192Certificate leaf6192InnerLog leaf6192Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi83RoundedFacts
    innerPair302RoundedFacts leaf6192RoundedFacts (by rfl)

private theorem leaf6192FlatSound : Sound leaf6192Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6192CertificateValid
    leaf6192InnerLogValid leaf6192CoversExact leaf6192LowerChecked

private noncomputable def leaf6193Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf6193Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217951/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34357068800) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (297752611/268435456) }, upper := { exponent := 1, mantissa := (4655/4096) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68715791359/68714137600) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf6193InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf6193LocalValidity :
    LeafFacts leaf6193Box leaf6193Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6193Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34357068800) }) = true
      norm_num [leaf6193Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6193CertificateValid :
    WideCertificateValid leaf6193Box leaf6193Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi82ValidityFacts
    leaf6193LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6193CoverageChecked :
    coverageCheck (innerAD leaf6193Box) leaf6193InnerLog = true := by
  rfl'

private theorem leaf6193InnerLogValid :
    leaf6193InnerLog.Valid 8 (innerAD leaf6193Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf6193CoverageChecked

private noncomputable def leaf6193InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629485/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6193InputLogOnePlusV_eq :
    leaf6193InputLogOnePlusV = outerEnclosure 24
      (leaf6193Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6193RoundedFacts : LeafRoundedFacts 8
    leaf6193Certificate.logOnePlusV leaf6193InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6193InputLogOnePlusV_eq }

private noncomputable def leaf6193Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi82InputQChi innerPair257Input
    leaf6193InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6193LowerChecked :
    lowerCheck 24 leaf6193Box leaf6193Inputs = true := by
  rfl'

private theorem leaf6193CoversExact : CoversExact 8
    leaf6193Box leaf6193Certificate leaf6193InnerLog leaf6193Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi82RoundedFacts
    innerPair257RoundedFacts leaf6193RoundedFacts (by rfl)

private theorem leaf6193FlatSound : Sound leaf6193Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6193CertificateValid
    leaf6193InnerLogValid leaf6193CoversExact leaf6193LowerChecked

private noncomputable def leaf6194Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf6194Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217953/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357035008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (299849633/268435456) }, upper := { exponent := 1, mantissa := (293/256) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715757567/68714070016) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf6194InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf6194LocalValidity :
    LeafFacts leaf6194Box leaf6194Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6194Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357035008) }) = true
      norm_num [leaf6194Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6194CertificateValid :
    WideCertificateValid leaf6194Box leaf6194Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi82ValidityFacts
    leaf6194LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6194CoverageChecked :
    coverageCheck (innerAD leaf6194Box) leaf6194InnerLog = true := by
  rfl'

private theorem leaf6194InnerLogValid :
    leaf6194InnerLog.Valid 8 (innerAD leaf6194Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf6194CoverageChecked

private noncomputable def leaf6194InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629493/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6194InputLogOnePlusV_eq :
    leaf6194InputLogOnePlusV = outerEnclosure 24
      (leaf6194Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6194RoundedFacts : LeafRoundedFacts 8
    leaf6194Certificate.logOnePlusV leaf6194InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6194InputLogOnePlusV_eq }

private noncomputable def leaf6194Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi82InputQChi innerPair257Input
    leaf6194InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6194LowerChecked :
    lowerCheck 24 leaf6194Box leaf6194Inputs = true := by
  rfl'

private theorem leaf6194CoversExact : CoversExact 8
    leaf6194Box leaf6194Certificate leaf6194InnerLog leaf6194Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi82RoundedFacts
    innerPair257RoundedFacts leaf6194RoundedFacts (by rfl)

private theorem leaf6194FlatSound : Sound leaf6194Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6194CertificateValid
    leaf6194InnerLogValid leaf6194CoversExact leaf6194LowerChecked

private noncomputable def leaf6195Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (33/64), chiHi := (17/32) }

private noncomputable def leaf6195Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217953/134217728) }, vSqrt := { lower := (65531/65536), upper := (34358722559/34356987904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (302864105/268435456) }, upper := { exponent := 1, mantissa := (2367/2048) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi83LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68715710463/68713975808) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf6195InnerLog : WideLogData :=
  innerPair264Data

set_option maxRecDepth 1000000 in
private theorem leaf6195LocalValidity :
    LeafFacts leaf6195Box leaf6195Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6195Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358722559/34356987904) }) = true
      norm_num [leaf6195Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6195CertificateValid :
    WideCertificateValid leaf6195Box leaf6195Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi83ValidityFacts
    leaf6195LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6195CoverageChecked :
    coverageCheck (innerAD leaf6195Box) leaf6195InnerLog = true := by
  rfl'

private theorem leaf6195InnerLogValid :
    leaf6195InnerLog.Valid 8 (innerAD leaf6195Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint76PositiveFacts.valid leaf6195CoverageChecked

private noncomputable def leaf6195InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (181711/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf6195InputLogOnePlusV_eq :
    leaf6195InputLogOnePlusV = outerEnclosure 24
      (leaf6195Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6195RoundedFacts : LeafRoundedFacts 8
    leaf6195Certificate.logOnePlusV leaf6195InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6195InputLogOnePlusV_eq }

private noncomputable def leaf6195Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi83InputQChi innerPair264Input
    leaf6195InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6195LowerChecked :
    lowerCheck 24 leaf6195Box leaf6195Inputs = true := by
  rfl'

private theorem leaf6195CoversExact : CoversExact 8
    leaf6195Box leaf6195Certificate leaf6195InnerLog leaf6195Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi83RoundedFacts
    innerPair264RoundedFacts leaf6195RoundedFacts (by rfl)

private theorem leaf6195FlatSound : Sound leaf6195Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6195CertificateValid
    leaf6195InnerLogValid leaf6195CoversExact leaf6195LowerChecked

private noncomputable def leaf6196Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (33/64), chiHi := (17/32) }

private noncomputable def leaf6196Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (134217955/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34356953088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (305026659/268435456) }, upper := { exponent := 1, mantissa := (149/128) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi83LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68715675647/68713906176) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf6196InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6196LocalValidity :
    LeafFacts leaf6196Box leaf6196Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6196Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34356953088) }) = true
      norm_num [leaf6196Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6196CertificateValid :
    WideCertificateValid leaf6196Box leaf6196Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi83ValidityFacts
    leaf6196LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6196CoverageChecked :
    coverageCheck (innerAD leaf6196Box) leaf6196InnerLog = true := by
  rfl'

private theorem leaf6196InnerLogValid :
    leaf6196InnerLog.Valid 8 (innerAD leaf6196Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6196CoverageChecked

private noncomputable def leaf6196InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629513/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6196InputLogOnePlusV_eq :
    leaf6196InputLogOnePlusV = outerEnclosure 24
      (leaf6196Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6196RoundedFacts : LeafRoundedFacts 8
    leaf6196Certificate.logOnePlusV leaf6196InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6196InputLogOnePlusV_eq }

private noncomputable def leaf6196Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi83InputQChi innerPair265Input
    leaf6196InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6196LowerChecked :
    lowerCheck 24 leaf6196Box leaf6196Inputs = true := by
  rfl'

private theorem leaf6196CoversExact : CoversExact 8
    leaf6196Box leaf6196Certificate leaf6196InnerLog leaf6196Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi83RoundedFacts
    innerPair265RoundedFacts leaf6196RoundedFacts (by rfl)

private theorem leaf6196FlatSound : Sound leaf6196Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6196CertificateValid
    leaf6196InnerLogValid leaf6196CoversExact leaf6196LowerChecked

private noncomputable def leaf6197Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (17/32), chiHi := (35/64) }

private noncomputable def leaf6197Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109011/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178471424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (151743295/134217728) }, upper := { exponent := 1, mantissa := (2389/2048) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi84LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357849087/34356942848) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6197InnerLog : WideLogData :=
  innerPair270Data

set_option maxRecDepth 1000000 in
private theorem leaf6197LocalValidity :
    LeafFacts leaf6197Box leaf6197Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6197Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178471424) }) = true
      norm_num [leaf6197Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6197CertificateValid :
    WideCertificateValid leaf6197Box leaf6197Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi84ValidityFacts
    leaf6197LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6197CoverageChecked :
    coverageCheck (innerAD leaf6197Box) leaf6197InnerLog = true := by
  rfl'

private theorem leaf6197InnerLogValid :
    leaf6197InnerLog.Valid 8 (innerAD leaf6197Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint297PositiveFacts.valid leaf6197CoverageChecked

private noncomputable def leaf6197InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629523/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6197InputLogOnePlusV_eq :
    leaf6197InputLogOnePlusV = outerEnclosure 24
      (leaf6197Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6197RoundedFacts : LeafRoundedFacts 8
    leaf6197Certificate.logOnePlusV leaf6197InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6197InputLogOnePlusV_eq }

private noncomputable def leaf6197Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi84InputQChi innerPair270Input
    leaf6197InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6197LowerChecked :
    lowerCheck 24 leaf6197Box leaf6197Inputs = true := by
  rfl'

private theorem leaf6197CoversExact : CoversExact 8
    leaf6197Box leaf6197Certificate leaf6197InnerLog leaf6197Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi84RoundedFacts
    innerPair270RoundedFacts leaf6197RoundedFacts (by rfl)

private theorem leaf6197FlatSound : Sound leaf6197Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6197CertificateValid
    leaf6197InnerLogValid leaf6197CoversExact leaf6197LowerChecked

private noncomputable def leaf6198Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (35/64), chiHi := (9/16) }

private noncomputable def leaf6198Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109013/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178431488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (154233509/134217728) }, upper := { exponent := 1, mantissa := (607/512) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi85LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357809151/34356862976) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6198InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6198LocalValidity :
    LeafFacts leaf6198Box leaf6198Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6198Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178431488) }) = true
      norm_num [leaf6198Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6198CertificateValid :
    WideCertificateValid leaf6198Box leaf6198Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi85ValidityFacts
    leaf6198LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6198CoverageChecked :
    coverageCheck (innerAD leaf6198Box) leaf6198InnerLog = true := by
  rfl'

private theorem leaf6198InnerLogValid :
    leaf6198InnerLog.Valid 8 (innerAD leaf6198Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6198CoverageChecked

private noncomputable def leaf6198InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629543/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6198InputLogOnePlusV_eq :
    leaf6198InputLogOnePlusV = outerEnclosure 24
      (leaf6198Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6198RoundedFacts : LeafRoundedFacts 8
    leaf6198Certificate.logOnePlusV leaf6198InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6198InputLogOnePlusV_eq }

private noncomputable def leaf6198Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi85InputQChi innerPair265Input
    leaf6198InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6198LowerChecked :
    lowerCheck 24 leaf6198Box leaf6198Inputs = true := by
  rfl'

private theorem leaf6198CoversExact : CoversExact 8
    leaf6198Box leaf6198Certificate leaf6198InnerLog leaf6198Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi85RoundedFacts
    innerPair265RoundedFacts leaf6198RoundedFacts (by rfl)

private theorem leaf6198FlatSound : Sound leaf6198Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6198CertificateValid
    leaf6198InnerLogValid leaf6198CoversExact leaf6198LowerChecked

private noncomputable def leaf6199Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (17/32), chiHi := (35/64) }

private noncomputable def leaf6199Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109013/67108864) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178435584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (153971381/134217728) }, upper := { exponent := 1, mantissa := (303/256) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi84LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357813247/34356871168) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6199InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6199LocalValidity :
    LeafFacts leaf6199Box leaf6199Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6199Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178435584) }) = true
      norm_num [leaf6199Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6199CertificateValid :
    WideCertificateValid leaf6199Box leaf6199Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi84ValidityFacts
    leaf6199LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6199CoverageChecked :
    coverageCheck (innerAD leaf6199Box) leaf6199InnerLog = true := by
  rfl'

private theorem leaf6199InnerLogValid :
    leaf6199InnerLog.Valid 8 (innerAD leaf6199Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6199CoverageChecked

private noncomputable def leaf6199InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629541/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6199InputLogOnePlusV_eq :
    leaf6199InputLogOnePlusV = outerEnclosure 24
      (leaf6199Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6199RoundedFacts : LeafRoundedFacts 8
    leaf6199Certificate.logOnePlusV leaf6199InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6199InputLogOnePlusV_eq }

private noncomputable def leaf6199Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi84InputQChi innerPair265Input
    leaf6199InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6199LowerChecked :
    lowerCheck 24 leaf6199Box leaf6199Inputs = true := by
  rfl'

private theorem leaf6199CoversExact : CoversExact 8
    leaf6199Box leaf6199Certificate leaf6199InnerLog leaf6199Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi84RoundedFacts
    innerPair265RoundedFacts leaf6199RoundedFacts (by rfl)

private theorem leaf6199FlatSound : Sound leaf6199Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6199CertificateValid
    leaf6199InnerLogValid leaf6199CoversExact leaf6199LowerChecked

private noncomputable def leaf6200Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (35/64), chiHi := (9/16) }

private noncomputable def leaf6200Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109015/67108864) }, vSqrt := { lower := (32765/32768), upper := (17179377663/17178394624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (156527127/134217728) }, upper := { exponent := 1, mantissa := (77/64) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi85LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (34357772287/34356789248) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6200InnerLog : WideLogData :=
  innerPair568Data

set_option maxRecDepth 1000000 in
private theorem leaf6200LocalValidity :
    LeafFacts leaf6200Box leaf6200Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6200Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (17179377663/17178394624) }) = true
      norm_num [leaf6200Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6200CertificateValid :
    WideCertificateValid leaf6200Box leaf6200Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi85ValidityFacts
    leaf6200LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6200CoverageChecked :
    coverageCheck (innerAD leaf6200Box) leaf6200InnerLog = true := by
  rfl'

private theorem leaf6200InnerLogValid :
    leaf6200InnerLog.Valid 8 (innerAD leaf6200Box) :=
  wideLogDataValid_of_cachedCheck endpoint296PositiveFacts
    endpoint305PositiveFacts.valid leaf6200CoverageChecked

private noncomputable def leaf6200InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629561/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6200InputLogOnePlusV_eq :
    leaf6200InputLogOnePlusV = outerEnclosure 24
      (leaf6200Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6200RoundedFacts : LeafRoundedFacts 8
    leaf6200Certificate.logOnePlusV leaf6200InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6200InputLogOnePlusV_eq }

private noncomputable def leaf6200Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi85InputQChi innerPair568Input
    leaf6200InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6200LowerChecked :
    lowerCheck 24 leaf6200Box leaf6200Inputs = true := by
  rfl'

private theorem leaf6200CoversExact : CoversExact 8
    leaf6200Box leaf6200Certificate leaf6200InnerLog leaf6200Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi85RoundedFacts
    innerPair568RoundedFacts leaf6200RoundedFacts (by rfl)

private theorem leaf6200FlatSound : Sound leaf6200Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6200CertificateValid
    leaf6200InnerLogValid leaf6200CoversExact leaf6200LowerChecked

private noncomputable def leaf6201Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (9/16), chiHi := (37/64) }

private noncomputable def leaf6201Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109011/67108864) }, vSqrt := { lower := (65531/65536), upper := (5726459221/5726155776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (152005423/134217728) }, upper := { exponent := 1, mantissa := (2393/2048) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi86LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11452614997/11452311552) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6201InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6201LocalValidity :
    LeafFacts leaf6201Box leaf6201Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6201Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5726459221/5726155776) }) = true
      norm_num [leaf6201Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6201CertificateValid :
    WideCertificateValid leaf6201Box leaf6201Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi86ValidityFacts
    leaf6201LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6201CoverageChecked :
    coverageCheck (innerAD leaf6201Box) leaf6201InnerLog = true := by
  rfl'

private theorem leaf6201InnerLogValid :
    leaf6201InnerLog.Valid 8 (innerAD leaf6201Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6201CoverageChecked

private noncomputable def leaf6201InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629525/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6201InputLogOnePlusV_eq :
    leaf6201InputLogOnePlusV = outerEnclosure 24
      (leaf6201Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6201RoundedFacts : LeafRoundedFacts 8
    leaf6201Certificate.logOnePlusV leaf6201InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6201InputLogOnePlusV_eq }

private noncomputable def leaf6201Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi86InputQChi innerPair265Input
    leaf6201InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6201LowerChecked :
    lowerCheck 24 leaf6201Box leaf6201Inputs = true := by
  rfl'

private theorem leaf6201CoversExact : CoversExact 8
    leaf6201Box leaf6201Certificate leaf6201InnerLog leaf6201Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi86RoundedFacts
    innerPair265RoundedFacts leaf6201RoundedFacts (by rfl)

private theorem leaf6201FlatSound : Sound leaf6201Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6201CertificateValid
    leaf6201InnerLogValid leaf6201CoversExact leaf6201LowerChecked

private noncomputable def leaf6202Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (37/64), chiHi := (19/32) }

private noncomputable def leaf6202Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109013/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178429440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (154364573/134217728) }, upper := { exponent := 1, mantissa := (1215/1024) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi87LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357807103/34356858880) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6202InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6202LocalValidity :
    LeafFacts leaf6202Box leaf6202Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6202Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178429440) }) = true
      norm_num [leaf6202Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6202CertificateValid :
    WideCertificateValid leaf6202Box leaf6202Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi87ValidityFacts
    leaf6202LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6202CoverageChecked :
    coverageCheck (innerAD leaf6202Box) leaf6202InnerLog = true := by
  rfl'

private theorem leaf6202InnerLogValid :
    leaf6202InnerLog.Valid 8 (innerAD leaf6202Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6202CoverageChecked

private noncomputable def leaf6202InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453693/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6202InputLogOnePlusV_eq :
    leaf6202InputLogOnePlusV = outerEnclosure 24
      (leaf6202Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6202RoundedFacts : LeafRoundedFacts 8
    leaf6202Certificate.logOnePlusV leaf6202InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6202InputLogOnePlusV_eq }

private noncomputable def leaf6202Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi87InputQChi innerPair265Input
    leaf6202InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6202LowerChecked :
    lowerCheck 24 leaf6202Box leaf6202Inputs = true := by
  rfl'

private theorem leaf6202CoversExact : CoversExact 8
    leaf6202Box leaf6202Certificate leaf6202InnerLog leaf6202Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi87RoundedFacts
    innerPair265RoundedFacts leaf6202RoundedFacts (by rfl)

private theorem leaf6202FlatSound : Sound leaf6202Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6202CertificateValid
    leaf6202InnerLogValid leaf6202CoversExact leaf6202LowerChecked

private noncomputable def leaf6203Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (9/16), chiHi := (37/64) }

private noncomputable def leaf6203Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109013/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178429440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (154364573/134217728) }, upper := { exponent := 1, mantissa := (1215/1024) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi86LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357807103/34356858880) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6203InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6203LocalValidity :
    LeafFacts leaf6203Box leaf6203Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6203Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178429440) }) = true
      norm_num [leaf6203Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6203CertificateValid :
    WideCertificateValid leaf6203Box leaf6203Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi86ValidityFacts
    leaf6203LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6203CoverageChecked :
    coverageCheck (innerAD leaf6203Box) leaf6203InnerLog = true := by
  rfl'

private theorem leaf6203InnerLogValid :
    leaf6203InnerLog.Valid 8 (innerAD leaf6203Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6203CoverageChecked

private noncomputable def leaf6203InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453693/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6203InputLogOnePlusV_eq :
    leaf6203InputLogOnePlusV = outerEnclosure 24
      (leaf6203Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6203RoundedFacts : LeafRoundedFacts 8
    leaf6203Certificate.logOnePlusV leaf6203InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6203InputLogOnePlusV_eq }

private noncomputable def leaf6203Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi86InputQChi innerPair265Input
    leaf6203InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6203LowerChecked :
    lowerCheck 24 leaf6203Box leaf6203Inputs = true := by
  rfl'

private theorem leaf6203CoversExact : CoversExact 8
    leaf6203Box leaf6203Certificate leaf6203InnerLog leaf6203Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi86RoundedFacts
    innerPair265RoundedFacts leaf6203RoundedFacts (by rfl)

private theorem leaf6203FlatSound : Sound leaf6203Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6203CertificateValid
    leaf6203InnerLogValid leaf6203CoversExact leaf6203LowerChecked

private noncomputable def leaf6204Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (37/64), chiHi := (19/32) }

private noncomputable def leaf6204Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109015/67108864) }, vSqrt := { lower := (65531/65536), upper := (5726459221/5726130176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (156789255/134217728) }, upper := { exponent := 1, mantissa := (617/512) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi87LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11452589397/11452260352) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6204InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf6204LocalValidity :
    LeafFacts leaf6204Box leaf6204Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6204Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5726459221/5726130176) }) = true
      norm_num [leaf6204Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6204CertificateValid :
    WideCertificateValid leaf6204Box leaf6204Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi87ValidityFacts
    leaf6204LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6204CoverageChecked :
    coverageCheck (innerAD leaf6204Box) leaf6204InnerLog = true := by
  rfl'

private theorem leaf6204InnerLogValid :
    leaf6204InnerLog.Valid 8 (innerAD leaf6204Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf6204CoverageChecked

private noncomputable def leaf6204InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629563/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6204InputLogOnePlusV_eq :
    leaf6204InputLogOnePlusV = outerEnclosure 24
      (leaf6204Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6204RoundedFacts : LeafRoundedFacts 8
    leaf6204Certificate.logOnePlusV leaf6204InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6204InputLogOnePlusV_eq }

private noncomputable def leaf6204Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi87InputQChi innerPair273Input
    leaf6204InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6204LowerChecked :
    lowerCheck 24 leaf6204Box leaf6204Inputs = true := by
  rfl'

private theorem leaf6204CoversExact : CoversExact 8
    leaf6204Box leaf6204Certificate leaf6204InnerLog leaf6204Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi87RoundedFacts
    innerPair273RoundedFacts leaf6204RoundedFacts (by rfl)

private theorem leaf6204FlatSound : Sound leaf6204Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6204CertificateValid
    leaf6204InnerLogValid leaf6204CoversExact leaf6204LowerChecked

private noncomputable def leaf6205Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (19/32), chiHi := (39/64) }

private noncomputable def leaf6205Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109015/67108864) }, vSqrt := { lower := (65531/65536), upper := (2454196809/2454055936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (156723723/134217728) }, upper := { exponent := 1, mantissa := (2467/2048) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi321LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4908252745/4908111872) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6205InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf6205LocalValidity :
    LeafFacts leaf6205Box leaf6205Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6205Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2454196809/2454055936) }) = true
      norm_num [leaf6205Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6205CertificateValid :
    WideCertificateValid leaf6205Box leaf6205Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi321ValidityFacts
    leaf6205LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6205CoverageChecked :
    coverageCheck (innerAD leaf6205Box) leaf6205InnerLog = true := by
  rfl'

private theorem leaf6205InnerLogValid :
    leaf6205InnerLog.Valid 8 (innerAD leaf6205Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf6205CoverageChecked

private noncomputable def leaf6205InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814781/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6205InputLogOnePlusV_eq :
    leaf6205InputLogOnePlusV = outerEnclosure 24
      (leaf6205Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6205RoundedFacts : LeafRoundedFacts 8
    leaf6205Certificate.logOnePlusV leaf6205InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6205InputLogOnePlusV_eq }

private noncomputable def leaf6205Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi321InputQChi innerPair273Input
    leaf6205InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6205LowerChecked :
    lowerCheck 24 leaf6205Box leaf6205Inputs = true := by
  rfl'

private theorem leaf6205CoversExact : CoversExact 8
    leaf6205Box leaf6205Certificate leaf6205InnerLog leaf6205Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi321RoundedFacts
    innerPair273RoundedFacts leaf6205RoundedFacts (by rfl)

private theorem leaf6205FlatSound : Sound leaf6205Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6205CertificateValid
    leaf6205InnerLogValid leaf6205CoversExact leaf6205LowerChecked

private noncomputable def leaf6206Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (39/64), chiHi := (5/8) }

private noncomputable def leaf6206Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109017/67108864) }, vSqrt := { lower := (65531/65536), upper := (5726459221/5726117888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (159082873/134217728) }, upper := { exponent := 1, mantissa := (313/256) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi322LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11452577109/11452235776) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6206InnerLog : WideLogData :=
  innerPair274Data

set_option maxRecDepth 1000000 in
private theorem leaf6206LocalValidity :
    LeafFacts leaf6206Box leaf6206Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6206Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5726459221/5726117888) }) = true
      norm_num [leaf6206Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6206CertificateValid :
    WideCertificateValid leaf6206Box leaf6206Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi322ValidityFacts
    leaf6206LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6206CoverageChecked :
    coverageCheck (innerAD leaf6206Box) leaf6206InnerLog = true := by
  rfl'

private theorem leaf6206InnerLogValid :
    leaf6206InnerLog.Valid 8 (innerAD leaf6206Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint79PositiveFacts.valid leaf6206CoverageChecked

private noncomputable def leaf6206InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629581/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6206InputLogOnePlusV_eq :
    leaf6206InputLogOnePlusV = outerEnclosure 24
      (leaf6206Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6206RoundedFacts : LeafRoundedFacts 8
    leaf6206Certificate.logOnePlusV leaf6206InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6206InputLogOnePlusV_eq }

private noncomputable def leaf6206Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi322InputQChi innerPair274Input
    leaf6206InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6206LowerChecked :
    lowerCheck 24 leaf6206Box leaf6206Inputs = true := by
  rfl'

private theorem leaf6206CoversExact : CoversExact 8
    leaf6206Box leaf6206Certificate leaf6206InnerLog leaf6206Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi322RoundedFacts
    innerPair274RoundedFacts leaf6206RoundedFacts (by rfl)

private theorem leaf6206FlatSound : Sound leaf6206Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6206CertificateValid
    leaf6206InnerLogValid leaf6206CoversExact leaf6206LowerChecked

private noncomputable def leaf6207Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (19/32), chiHi := (39/64) }

private noncomputable def leaf6207Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109017/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178351616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (159213937/134217728) }, upper := { exponent := 1, mantissa := (1253/1024) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi321LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357729279/34356703232) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6207InnerLog : WideLogData :=
  innerPair274Data

set_option maxRecDepth 1000000 in
private theorem leaf6207LocalValidity :
    LeafFacts leaf6207Box leaf6207Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6207Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178351616) }) = true
      norm_num [leaf6207Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6207CertificateValid :
    WideCertificateValid leaf6207Box leaf6207Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi321ValidityFacts
    leaf6207LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6207CoverageChecked :
    coverageCheck (innerAD leaf6207Box) leaf6207InnerLog = true := by
  rfl'

private theorem leaf6207InnerLogValid :
    leaf6207InnerLog.Valid 8 (innerAD leaf6207Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint79PositiveFacts.valid leaf6207CoverageChecked

private noncomputable def leaf6207InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814791/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6207InputLogOnePlusV_eq :
    leaf6207InputLogOnePlusV = outerEnclosure 24
      (leaf6207Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6207RoundedFacts : LeafRoundedFacts 8
    leaf6207Certificate.logOnePlusV leaf6207InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6207InputLogOnePlusV_eq }

private noncomputable def leaf6207Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi321InputQChi innerPair274Input
    leaf6207InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6207LowerChecked :
    lowerCheck 24 leaf6207Box leaf6207Inputs = true := by
  rfl'

private theorem leaf6207CoversExact : CoversExact 8
    leaf6207Box leaf6207Certificate leaf6207InnerLog leaf6207Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi321RoundedFacts
    innerPair274RoundedFacts leaf6207RoundedFacts (by rfl)

private theorem leaf6207FlatSound : Sound leaf6207Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6207CertificateValid
    leaf6207InnerLogValid leaf6207CoversExact leaf6207LowerChecked

private noncomputable def leaf6208Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (39/64), chiHi := (5/8) }

private noncomputable def leaf6208Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109019/67108864) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356625408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (161638619/134217728) }, upper := { exponent := 1, mantissa := (159/128) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi322LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714856445/68713250816) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6208InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf6208LocalValidity :
    LeafFacts leaf6208Box leaf6208Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6208Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356625408) }) = true
      norm_num [leaf6208Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6208CertificateValid :
    WideCertificateValid leaf6208Box leaf6208Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi322ValidityFacts
    leaf6208LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6208CoverageChecked :
    coverageCheck (innerAD leaf6208Box) leaf6208InnerLog = true := by
  rfl'

private theorem leaf6208InnerLogValid :
    leaf6208InnerLog.Valid 8 (innerAD leaf6208Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf6208CoverageChecked

private noncomputable def leaf6208InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629473/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6208InputLogOnePlusV_eq :
    leaf6208InputLogOnePlusV = outerEnclosure 24
      (leaf6208Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6208RoundedFacts : LeafRoundedFacts 8
    leaf6208Certificate.logOnePlusV leaf6208InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6208InputLogOnePlusV_eq }

private noncomputable def leaf6208Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi322InputQChi innerPair279Input
    leaf6208InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6208LowerChecked :
    lowerCheck 24 leaf6208Box leaf6208Inputs = true := by
  rfl'

private theorem leaf6208CoversExact : CoversExact 8
    leaf6208Box leaf6208Certificate leaf6208InnerLog leaf6208Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi322RoundedFacts
    innerPair279RoundedFacts leaf6208RoundedFacts (by rfl)

private theorem leaf6208FlatSound : Sound leaf6208Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6208CertificateValid
    leaf6208InnerLogValid leaf6208CoversExact leaf6208LowerChecked

private noncomputable def leaf6209Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (9/16), chiHi := (37/64) }

private noncomputable def leaf6209Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109015/67108864) }, vSqrt := { lower := (65531/65536), upper := (2454196809/2454055936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (156723723/134217728) }, upper := { exponent := 1, mantissa := (2467/2048) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi86LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4908252745/4908111872) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6209InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf6209LocalValidity :
    LeafFacts leaf6209Box leaf6209Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6209Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2454196809/2454055936) }) = true
      norm_num [leaf6209Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6209CertificateValid :
    WideCertificateValid leaf6209Box leaf6209Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi86ValidityFacts
    leaf6209LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6209CoverageChecked :
    coverageCheck (innerAD leaf6209Box) leaf6209InnerLog = true := by
  rfl'

private theorem leaf6209InnerLogValid :
    leaf6209InnerLog.Valid 8 (innerAD leaf6209Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf6209CoverageChecked

private noncomputable def leaf6209InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814781/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6209InputLogOnePlusV_eq :
    leaf6209InputLogOnePlusV = outerEnclosure 24
      (leaf6209Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6209RoundedFacts : LeafRoundedFacts 8
    leaf6209Certificate.logOnePlusV leaf6209InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6209InputLogOnePlusV_eq }

private noncomputable def leaf6209Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi86InputQChi innerPair273Input
    leaf6209InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6209LowerChecked :
    lowerCheck 24 leaf6209Box leaf6209Inputs = true := by
  rfl'

private theorem leaf6209CoversExact : CoversExact 8
    leaf6209Box leaf6209Certificate leaf6209InnerLog leaf6209Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi86RoundedFacts
    innerPair273RoundedFacts leaf6209RoundedFacts (by rfl)

private theorem leaf6209FlatSound : Sound leaf6209Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6209CertificateValid
    leaf6209InnerLogValid leaf6209CoversExact leaf6209LowerChecked

private noncomputable def leaf6210Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (37/64), chiHi := (19/32) }

private noncomputable def leaf6210Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109017/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178351616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (159213937/134217728) }, upper := { exponent := 1, mantissa := (1253/1024) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi87LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357729279/34356703232) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6210InnerLog : WideLogData :=
  innerPair274Data

set_option maxRecDepth 1000000 in
private theorem leaf6210LocalValidity :
    LeafFacts leaf6210Box leaf6210Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6210Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178351616) }) = true
      norm_num [leaf6210Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6210CertificateValid :
    WideCertificateValid leaf6210Box leaf6210Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi87ValidityFacts
    leaf6210LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6210CoverageChecked :
    coverageCheck (innerAD leaf6210Box) leaf6210InnerLog = true := by
  rfl'

private theorem leaf6210InnerLogValid :
    leaf6210InnerLog.Valid 8 (innerAD leaf6210Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint79PositiveFacts.valid leaf6210CoverageChecked

private noncomputable def leaf6210InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814791/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6210InputLogOnePlusV_eq :
    leaf6210InputLogOnePlusV = outerEnclosure 24
      (leaf6210Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6210RoundedFacts : LeafRoundedFacts 8
    leaf6210Certificate.logOnePlusV leaf6210InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6210InputLogOnePlusV_eq }

private noncomputable def leaf6210Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi87InputQChi innerPair274Input
    leaf6210InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6210LowerChecked :
    lowerCheck 24 leaf6210Box leaf6210Inputs = true := by
  rfl'

private theorem leaf6210CoversExact : CoversExact 8
    leaf6210Box leaf6210Certificate leaf6210InnerLog leaf6210Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi87RoundedFacts
    innerPair274RoundedFacts leaf6210RoundedFacts (by rfl)

private theorem leaf6210FlatSound : Sound leaf6210Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6210CertificateValid
    leaf6210InnerLogValid leaf6210CoversExact leaf6210LowerChecked

private noncomputable def leaf6211Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (9/16), chiHi := (37/64) }

private noncomputable def leaf6211Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109017/67108864) }, vSqrt := { lower := (32765/32768), upper := (5726459221/5726117888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (159082873/134217728) }, upper := { exponent := 1, mantissa := (313/256) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi86LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (11452577109/11452235776) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6211InnerLog : WideLogData :=
  innerPair578Data

set_option maxRecDepth 1000000 in
private theorem leaf6211LocalValidity :
    LeafFacts leaf6211Box leaf6211Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6211Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (5726459221/5726117888) }) = true
      norm_num [leaf6211Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6211CertificateValid :
    WideCertificateValid leaf6211Box leaf6211Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi86ValidityFacts
    leaf6211LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6211CoverageChecked :
    coverageCheck (innerAD leaf6211Box) leaf6211InnerLog = true := by
  rfl'

private theorem leaf6211InnerLogValid :
    leaf6211InnerLog.Valid 8 (innerAD leaf6211Box) :=
  wideLogDataValid_of_cachedCheck endpoint299PositiveFacts
    endpoint403PositiveFacts.valid leaf6211CoverageChecked

private noncomputable def leaf6211InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629581/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6211InputLogOnePlusV_eq :
    leaf6211InputLogOnePlusV = outerEnclosure 24
      (leaf6211Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6211RoundedFacts : LeafRoundedFacts 8
    leaf6211Certificate.logOnePlusV leaf6211InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6211InputLogOnePlusV_eq }

private noncomputable def leaf6211Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi86InputQChi innerPair578Input
    leaf6211InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6211LowerChecked :
    lowerCheck 24 leaf6211Box leaf6211Inputs = true := by
  rfl'

private theorem leaf6211CoversExact : CoversExact 8
    leaf6211Box leaf6211Certificate leaf6211InnerLog leaf6211Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi86RoundedFacts
    innerPair578RoundedFacts leaf6211RoundedFacts (by rfl)

private theorem leaf6211FlatSound : Sound leaf6211Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6211CertificateValid
    leaf6211InnerLogValid leaf6211CoversExact leaf6211LowerChecked

private noncomputable def leaf6212Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (37/64), chiHi := (19/32) }

private noncomputable def leaf6212Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109019/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356625408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (161638619/134217728) }, upper := { exponent := 1, mantissa := (159/128) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi87LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714856445/68713250816) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6212InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf6212LocalValidity :
    LeafFacts leaf6212Box leaf6212Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6212Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356625408) }) = true
      norm_num [leaf6212Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6212CertificateValid :
    WideCertificateValid leaf6212Box leaf6212Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi87ValidityFacts
    leaf6212LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6212CoverageChecked :
    coverageCheck (innerAD leaf6212Box) leaf6212InnerLog = true := by
  rfl'

private theorem leaf6212InnerLogValid :
    leaf6212InnerLog.Valid 8 (innerAD leaf6212Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf6212CoverageChecked

private noncomputable def leaf6212InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629473/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6212InputLogOnePlusV_eq :
    leaf6212InputLogOnePlusV = outerEnclosure 24
      (leaf6212Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6212RoundedFacts : LeafRoundedFacts 8
    leaf6212Certificate.logOnePlusV leaf6212InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6212InputLogOnePlusV_eq }

private noncomputable def leaf6212Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi87InputQChi innerPair279Input
    leaf6212InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6212LowerChecked :
    lowerCheck 24 leaf6212Box leaf6212Inputs = true := by
  rfl'

private theorem leaf6212CoversExact : CoversExact 8
    leaf6212Box leaf6212Certificate leaf6212InnerLog leaf6212Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi87RoundedFacts
    innerPair279RoundedFacts leaf6212RoundedFacts (by rfl)

private theorem leaf6212FlatSound : Sound leaf6212Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6212CertificateValid
    leaf6212InnerLogValid leaf6212CoversExact leaf6212LowerChecked

private noncomputable def leaf6213Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (19/32), chiHi := (39/64) }

private noncomputable def leaf6213Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109019/67108864) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356623360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (161704151/134217728) }, upper := { exponent := 1, mantissa := (2545/2048) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi321LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714854397/68713246720) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6213InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf6213LocalValidity :
    LeafFacts leaf6213Box leaf6213Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6213Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356623360) }) = true
      norm_num [leaf6213Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6213CertificateValid :
    WideCertificateValid leaf6213Box leaf6213Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi321ValidityFacts
    leaf6213LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6213CoverageChecked :
    coverageCheck (innerAD leaf6213Box) leaf6213InnerLog = true := by
  rfl'

private theorem leaf6213InnerLogValid :
    leaf6213InnerLog.Valid 8 (innerAD leaf6213Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf6213CoverageChecked

private noncomputable def leaf6213InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629473/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6213InputLogOnePlusV_eq :
    leaf6213InputLogOnePlusV = outerEnclosure 24
      (leaf6213Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6213RoundedFacts : LeafRoundedFacts 8
    leaf6213Certificate.logOnePlusV leaf6213InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6213InputLogOnePlusV_eq }

private noncomputable def leaf6213Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi321InputQChi innerPair279Input
    leaf6213InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6213LowerChecked :
    lowerCheck 24 leaf6213Box leaf6213Inputs = true := by
  rfl'

private theorem leaf6213CoversExact : CoversExact 8
    leaf6213Box leaf6213Certificate leaf6213InnerLog leaf6213Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi321RoundedFacts
    innerPair279RoundedFacts leaf6213RoundedFacts (by rfl)

private theorem leaf6213FlatSound : Sound leaf6213Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6213CertificateValid
    leaf6213InnerLogValid leaf6213CoversExact leaf6213LowerChecked

private noncomputable def leaf6214Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (39/64), chiHi := (5/8) }

private noncomputable def leaf6214Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109021/67108864) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356543488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (164194365/134217728) }, upper := { exponent := 1, mantissa := (323/256) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi322LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714774525/68713086976) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6214InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6214LocalValidity :
    LeafFacts leaf6214Box leaf6214Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6214Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356543488) }) = true
      norm_num [leaf6214Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6214CertificateValid :
    WideCertificateValid leaf6214Box leaf6214Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi322ValidityFacts
    leaf6214LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6214CoverageChecked :
    coverageCheck (innerAD leaf6214Box) leaf6214InnerLog = true := by
  rfl'

private theorem leaf6214InnerLogValid :
    leaf6214InnerLog.Valid 8 (innerAD leaf6214Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6214CoverageChecked

private noncomputable def leaf6214InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629493/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6214InputLogOnePlusV_eq :
    leaf6214InputLogOnePlusV = outerEnclosure 24
      (leaf6214Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6214RoundedFacts : LeafRoundedFacts 8
    leaf6214Certificate.logOnePlusV leaf6214InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6214InputLogOnePlusV_eq }

private noncomputable def leaf6214Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi322InputQChi innerPair286Input
    leaf6214InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6214LowerChecked :
    lowerCheck 24 leaf6214Box leaf6214Inputs = true := by
  rfl'

private theorem leaf6214CoversExact : CoversExact 8
    leaf6214Box leaf6214Certificate leaf6214InnerLog leaf6214Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi322RoundedFacts
    innerPair286RoundedFacts leaf6214RoundedFacts (by rfl)

private theorem leaf6214FlatSound : Sound leaf6214Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6214CertificateValid
    leaf6214InnerLogValid leaf6214CoversExact leaf6214LowerChecked

private noncomputable def leaf6215Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (19/32), chiHi := (39/64) }

private noncomputable def leaf6215Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109021/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356543488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (164194365/134217728) }, upper := { exponent := 1, mantissa := (323/256) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi321LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714774525/68713086976) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6215InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6215LocalValidity :
    LeafFacts leaf6215Box leaf6215Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6215Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356543488) }) = true
      norm_num [leaf6215Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6215CertificateValid :
    WideCertificateValid leaf6215Box leaf6215Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi321ValidityFacts
    leaf6215LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6215CoverageChecked :
    coverageCheck (innerAD leaf6215Box) leaf6215InnerLog = true := by
  rfl'

private theorem leaf6215InnerLogValid :
    leaf6215InnerLog.Valid 8 (innerAD leaf6215Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6215CoverageChecked

private noncomputable def leaf6215InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629493/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6215InputLogOnePlusV_eq :
    leaf6215InputLogOnePlusV = outerEnclosure 24
      (leaf6215Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6215RoundedFacts : LeafRoundedFacts 8
    leaf6215Certificate.logOnePlusV leaf6215InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6215InputLogOnePlusV_eq }

private noncomputable def leaf6215Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi321InputQChi innerPair286Input
    leaf6215InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6215LowerChecked :
    lowerCheck 24 leaf6215Box leaf6215Inputs = true := by
  rfl'

private theorem leaf6215CoversExact : CoversExact 8
    leaf6215Box leaf6215Certificate leaf6215InnerLog leaf6215Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi321RoundedFacts
    innerPair286RoundedFacts leaf6215RoundedFacts (by rfl)

private theorem leaf6215FlatSound : Sound leaf6215Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6215CertificateValid
    leaf6215InnerLogValid leaf6215CoversExact leaf6215LowerChecked

private noncomputable def leaf6216Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (39/64), chiHi := (5/8) }

private noncomputable def leaf6216Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109023/67108864) }, vSqrt := { lower := (32765/32768), upper := (880980283/880934912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (166750111/134217728) }, upper := { exponent := 1, mantissa := (41/32) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi322LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1761915195/1761869824) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6216InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6216LocalValidity :
    LeafFacts leaf6216Box leaf6216Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6216Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (880980283/880934912) }) = true
      norm_num [leaf6216Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6216CertificateValid :
    WideCertificateValid leaf6216Box leaf6216Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi322ValidityFacts
    leaf6216LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6216CoverageChecked :
    coverageCheck (innerAD leaf6216Box) leaf6216InnerLog = true := by
  rfl'

private theorem leaf6216InnerLogValid :
    leaf6216InnerLog.Valid 8 (innerAD leaf6216Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6216CoverageChecked

private noncomputable def leaf6216InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629513/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6216InputLogOnePlusV_eq :
    leaf6216InputLogOnePlusV = outerEnclosure 24
      (leaf6216Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6216RoundedFacts : LeafRoundedFacts 8
    leaf6216Certificate.logOnePlusV leaf6216InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6216InputLogOnePlusV_eq }

private noncomputable def leaf6216Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi322InputQChi innerPair286Input
    leaf6216InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6216LowerChecked :
    lowerCheck 24 leaf6216Box leaf6216Inputs = true := by
  rfl'

private theorem leaf6216CoversExact : CoversExact 8
    leaf6216Box leaf6216Certificate leaf6216InnerLog leaf6216Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi322RoundedFacts
    innerPair286RoundedFacts leaf6216RoundedFacts (by rfl)

private theorem leaf6216FlatSound : Sound leaf6216Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6216CertificateValid
    leaf6216InnerLogValid leaf6216CoversExact leaf6216LowerChecked

private noncomputable def component124Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component124Node0_sound : Sound component124Node0Box :=
  sound_of_literal_split component124Node0Box leaf6182Box leaf6183Box
    .chi (33/64) (by rfl) (by rfl)
    leaf6182FlatSound leaf6183FlatSound

private noncomputable def component124Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component124Node1_sound : Sound component124Node1Box :=
  sound_of_literal_split component124Node1Box leaf6184Box leaf6185Box
    .chi (33/64) (by rfl) (by rfl)
    leaf6184FlatSound leaf6185FlatSound

private noncomputable def component124Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component124Node2_sound : Sound component124Node2Box :=
  sound_of_literal_split component124Node2Box component124Node0Box component124Node1Box
    .k (37/16) (by rfl) (by rfl)
    component124Node0_sound component124Node1_sound

private noncomputable def component124Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component124Node3_sound : Sound component124Node3Box :=
  sound_of_literal_split component124Node3Box leaf6186Box leaf6187Box
    .chi (35/64) (by rfl) (by rfl)
    leaf6186FlatSound leaf6187FlatSound

private noncomputable def component124Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component124Node4_sound : Sound component124Node4Box :=
  sound_of_literal_split component124Node4Box leaf6188Box leaf6189Box
    .chi (35/64) (by rfl) (by rfl)
    leaf6188FlatSound leaf6189FlatSound

private noncomputable def component124Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component124Node5_sound : Sound component124Node5Box :=
  sound_of_literal_split component124Node5Box component124Node3Box component124Node4Box
    .k (37/16) (by rfl) (by rfl)
    component124Node3_sound component124Node4_sound

private noncomputable def component124Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component124Node6_sound : Sound component124Node6Box :=
  sound_of_literal_split component124Node6Box component124Node2Box component124Node5Box
    .chi (17/32) (by rfl) (by rfl)
    component124Node2_sound component124Node5_sound

private noncomputable def component124Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component124Node7_sound : Sound component124Node7Box :=
  sound_of_literal_split component124Node7Box leaf6190Box leaf6191Box
    .k (77/32) (by rfl) (by rfl)
    leaf6190FlatSound leaf6191FlatSound

private noncomputable def component124Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component124Node8_sound : Sound component124Node8Box :=
  sound_of_literal_split component124Node8Box component124Node7Box leaf6192Box
    .chi (33/64) (by rfl) (by rfl)
    component124Node7_sound leaf6192FlatSound

private noncomputable def component124Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component124Node9_sound : Sound component124Node9Box :=
  sound_of_literal_split component124Node9Box leaf6193Box leaf6194Box
    .k (79/32) (by rfl) (by rfl)
    leaf6193FlatSound leaf6194FlatSound

private noncomputable def component124Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component124Node10_sound : Sound component124Node10Box :=
  sound_of_literal_split component124Node10Box leaf6195Box leaf6196Box
    .k (79/32) (by rfl) (by rfl)
    leaf6195FlatSound leaf6196FlatSound

private noncomputable def component124Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component124Node11_sound : Sound component124Node11Box :=
  sound_of_literal_split component124Node11Box component124Node9Box component124Node10Box
    .chi (33/64) (by rfl) (by rfl)
    component124Node9_sound component124Node10_sound

private noncomputable def component124Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component124Node12_sound : Sound component124Node12Box :=
  sound_of_literal_split component124Node12Box component124Node8Box component124Node11Box
    .k (39/16) (by rfl) (by rfl)
    component124Node8_sound component124Node11_sound

private noncomputable def component124Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component124Node13_sound : Sound component124Node13Box :=
  sound_of_literal_split component124Node13Box leaf6197Box leaf6198Box
    .chi (35/64) (by rfl) (by rfl)
    leaf6197FlatSound leaf6198FlatSound

private noncomputable def component124Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component124Node14_sound : Sound component124Node14Box :=
  sound_of_literal_split component124Node14Box leaf6199Box leaf6200Box
    .chi (35/64) (by rfl) (by rfl)
    leaf6199FlatSound leaf6200FlatSound

private noncomputable def component124Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component124Node15_sound : Sound component124Node15Box :=
  sound_of_literal_split component124Node15Box component124Node13Box component124Node14Box
    .k (39/16) (by rfl) (by rfl)
    component124Node13_sound component124Node14_sound

private noncomputable def component124Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component124Node16_sound : Sound component124Node16Box :=
  sound_of_literal_split component124Node16Box component124Node12Box component124Node15Box
    .chi (17/32) (by rfl) (by rfl)
    component124Node12_sound component124Node15_sound

private noncomputable def component124Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component124Node17_sound : Sound component124Node17Box :=
  sound_of_literal_split component124Node17Box component124Node6Box component124Node16Box
    .k (19/8) (by rfl) (by rfl)
    component124Node6_sound component124Node16_sound

private noncomputable def component124Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component124Node18_sound : Sound component124Node18Box :=
  sound_of_literal_split component124Node18Box leaf6201Box leaf6202Box
    .chi (37/64) (by rfl) (by rfl)
    leaf6201FlatSound leaf6202FlatSound

private noncomputable def component124Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component124Node19_sound : Sound component124Node19Box :=
  sound_of_literal_split component124Node19Box leaf6203Box leaf6204Box
    .chi (37/64) (by rfl) (by rfl)
    leaf6203FlatSound leaf6204FlatSound

private noncomputable def component124Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component124Node20_sound : Sound component124Node20Box :=
  sound_of_literal_split component124Node20Box component124Node18Box component124Node19Box
    .k (37/16) (by rfl) (by rfl)
    component124Node18_sound component124Node19_sound

private noncomputable def component124Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component124Node21_sound : Sound component124Node21Box :=
  sound_of_literal_split component124Node21Box leaf6205Box leaf6206Box
    .chi (39/64) (by rfl) (by rfl)
    leaf6205FlatSound leaf6206FlatSound

private noncomputable def component124Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component124Node22_sound : Sound component124Node22Box :=
  sound_of_literal_split component124Node22Box leaf6207Box leaf6208Box
    .chi (39/64) (by rfl) (by rfl)
    leaf6207FlatSound leaf6208FlatSound

private noncomputable def component124Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component124Node23_sound : Sound component124Node23Box :=
  sound_of_literal_split component124Node23Box component124Node21Box component124Node22Box
    .k (37/16) (by rfl) (by rfl)
    component124Node21_sound component124Node22_sound

private noncomputable def component124Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component124Node24_sound : Sound component124Node24Box :=
  sound_of_literal_split component124Node24Box component124Node20Box component124Node23Box
    .chi (19/32) (by rfl) (by rfl)
    component124Node20_sound component124Node23_sound

private noncomputable def component124Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component124Node25_sound : Sound component124Node25Box :=
  sound_of_literal_split component124Node25Box leaf6209Box leaf6210Box
    .chi (37/64) (by rfl) (by rfl)
    leaf6209FlatSound leaf6210FlatSound

private noncomputable def component124Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component124Node26_sound : Sound component124Node26Box :=
  sound_of_literal_split component124Node26Box leaf6211Box leaf6212Box
    .chi (37/64) (by rfl) (by rfl)
    leaf6211FlatSound leaf6212FlatSound

private noncomputable def component124Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component124Node27_sound : Sound component124Node27Box :=
  sound_of_literal_split component124Node27Box component124Node25Box component124Node26Box
    .k (39/16) (by rfl) (by rfl)
    component124Node25_sound component124Node26_sound

private noncomputable def component124Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component124Node28_sound : Sound component124Node28Box :=
  sound_of_literal_split component124Node28Box leaf6213Box leaf6214Box
    .chi (39/64) (by rfl) (by rfl)
    leaf6213FlatSound leaf6214FlatSound

private noncomputable def component124Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component124Node29_sound : Sound component124Node29Box :=
  sound_of_literal_split component124Node29Box leaf6215Box leaf6216Box
    .chi (39/64) (by rfl) (by rfl)
    leaf6215FlatSound leaf6216FlatSound

private noncomputable def component124Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component124Node30_sound : Sound component124Node30Box :=
  sound_of_literal_split component124Node30Box component124Node28Box component124Node29Box
    .k (39/16) (by rfl) (by rfl)
    component124Node28_sound component124Node29_sound

private noncomputable def component124Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component124Node31_sound : Sound component124Node31Box :=
  sound_of_literal_split component124Node31Box component124Node27Box component124Node30Box
    .chi (19/32) (by rfl) (by rfl)
    component124Node27_sound component124Node30_sound

private noncomputable def component124Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component124Node32_sound : Sound component124Node32Box :=
  sound_of_literal_split component124Node32Box component124Node24Box component124Node31Box
    .k (19/8) (by rfl) (by rfl)
    component124Node24_sound component124Node31_sound

noncomputable def component124Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
theorem component124_sound : Sound component124Box :=
  sound_of_literal_split component124Box component124Node17Box component124Node32Box
    .chi (9/16) (by rfl) (by rfl)
    component124Node17_sound component124Node32_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
