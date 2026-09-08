import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch9
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

private noncomputable def leaf6151Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf6151Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108995/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178754048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (134180735/67108864) }, upper := { exponent := 1, mantissa := (2113/2048) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358131711/34357508096) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6151InnerLog : WideLogData :=
  innerPair532Data

set_option maxRecDepth 1000000 in
private theorem leaf6151LocalValidity :
    LeafFacts leaf6151Box leaf6151Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6151Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178754048) }) = true
      norm_num [leaf6151Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6151CertificateValid :
    WideCertificateValid leaf6151Box leaf6151Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi82ValidityFacts
    leaf6151LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6151CoverageChecked :
    coverageCheck (innerAD leaf6151Box) leaf6151InnerLog = true := by
  rfl'

private theorem leaf6151InnerLogValid :
    leaf6151InnerLog.Valid 8 (innerAD leaf6151Box) :=
  wideLogDataValid_of_cachedCheck endpoint267PositiveFacts
    endpoint86PositiveFacts.valid leaf6151CoverageChecked

private noncomputable def leaf6151InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6151InputLogOnePlusV_eq :
    leaf6151InputLogOnePlusV = outerEnclosure 24
      (leaf6151Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6151RoundedFacts : LeafRoundedFacts 8
    leaf6151Certificate.logOnePlusV leaf6151InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6151InputLogOnePlusV_eq }

private noncomputable def leaf6151Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi82InputQChi innerPair532Input
    leaf6151InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6151LowerChecked :
    lowerCheck 24 leaf6151Box leaf6151Inputs = true := by
  rfl'

private theorem leaf6151CoversExact : CoversExact 8
    leaf6151Box leaf6151Certificate leaf6151InnerLog leaf6151Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi82RoundedFacts
    innerPair532RoundedFacts leaf6151RoundedFacts (by rfl)

private theorem leaf6151FlatSound : Sound leaf6151Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6151CertificateValid
    leaf6151InnerLogValid leaf6151CoversExact leaf6151LowerChecked

private noncomputable def leaf6152Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (33/64), chiHi := (17/32) }

private noncomputable def leaf6152Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108997/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178720256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (136277757/134217728) }, upper := { exponent := 1, mantissa := (1073/1024) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi83LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358097919/34357440512) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6152InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf6152LocalValidity :
    LeafFacts leaf6152Box leaf6152Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6152Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178720256) }) = true
      norm_num [leaf6152Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6152CertificateValid :
    WideCertificateValid leaf6152Box leaf6152Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi83ValidityFacts
    leaf6152LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6152CoverageChecked :
    coverageCheck (innerAD leaf6152Box) leaf6152InnerLog = true := by
  rfl'

private theorem leaf6152InnerLogValid :
    leaf6152InnerLog.Valid 8 (innerAD leaf6152Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf6152CoverageChecked

private noncomputable def leaf6152InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814701/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6152InputLogOnePlusV_eq :
    leaf6152InputLogOnePlusV = outerEnclosure 24
      (leaf6152Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6152RoundedFacts : LeafRoundedFacts 8
    leaf6152Certificate.logOnePlusV leaf6152InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6152InputLogOnePlusV_eq }

private noncomputable def leaf6152Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi83InputQChi innerPair117Input
    leaf6152InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6152LowerChecked :
    lowerCheck 24 leaf6152Box leaf6152Inputs = true := by
  rfl'

private theorem leaf6152CoversExact : CoversExact 8
    leaf6152Box leaf6152Certificate leaf6152InnerLog leaf6152Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi83RoundedFacts
    innerPair117RoundedFacts leaf6152RoundedFacts (by rfl)

private theorem leaf6152FlatSound : Sound leaf6152Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6152CertificateValid
    leaf6152InnerLogValid leaf6152CoversExact leaf6152LowerChecked

private noncomputable def leaf6153Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf6153Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108997/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178720256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (136277757/134217728) }, upper := { exponent := 1, mantissa := (1073/1024) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358097919/34357440512) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6153InnerLog : WideLogData :=
  innerPair117Data

set_option maxRecDepth 1000000 in
private theorem leaf6153LocalValidity :
    LeafFacts leaf6153Box leaf6153Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6153Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178720256) }) = true
      norm_num [leaf6153Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6153CertificateValid :
    WideCertificateValid leaf6153Box leaf6153Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi82ValidityFacts
    leaf6153LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6153CoverageChecked :
    coverageCheck (innerAD leaf6153Box) leaf6153InnerLog = true := by
  rfl'

private theorem leaf6153InnerLogValid :
    leaf6153InnerLog.Valid 8 (innerAD leaf6153Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint73PositiveFacts.valid leaf6153CoverageChecked

private noncomputable def leaf6153InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814701/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6153InputLogOnePlusV_eq :
    leaf6153InputLogOnePlusV = outerEnclosure 24
      (leaf6153Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6153RoundedFacts : LeafRoundedFacts 8
    leaf6153Certificate.logOnePlusV leaf6153InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6153InputLogOnePlusV_eq }

private noncomputable def leaf6153Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi82InputQChi innerPair117Input
    leaf6153InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6153LowerChecked :
    lowerCheck 24 leaf6153Box leaf6153Inputs = true := by
  rfl'

private theorem leaf6153CoversExact : CoversExact 8
    leaf6153Box leaf6153Certificate leaf6153InnerLog leaf6153Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi82RoundedFacts
    innerPair117RoundedFacts leaf6153RoundedFacts (by rfl)

private theorem leaf6153FlatSound : Sound leaf6153Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6153CertificateValid
    leaf6153InnerLogValid leaf6153CoversExact leaf6153LowerChecked

private noncomputable def leaf6154Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (33/64), chiHi := (17/32) }

private noncomputable def leaf6154Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108999/67108864) }, vSqrt := { lower := (65531/65536), upper := (818065603/818032640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (138440311/134217728) }, upper := { exponent := 1, mantissa := (545/512) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi83LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (1636098243/1636065280) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6154InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf6154LocalValidity :
    LeafFacts leaf6154Box leaf6154Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6154Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (818065603/818032640) }) = true
      norm_num [leaf6154Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6154CertificateValid :
    WideCertificateValid leaf6154Box leaf6154Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi83ValidityFacts
    leaf6154LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6154CoverageChecked :
    coverageCheck (innerAD leaf6154Box) leaf6154InnerLog = true := by
  rfl'

private theorem leaf6154InnerLogValid :
    leaf6154InnerLog.Valid 8 (innerAD leaf6154Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf6154CoverageChecked

private noncomputable def leaf6154InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6154InputLogOnePlusV_eq :
    leaf6154InputLogOnePlusV = outerEnclosure 24
      (leaf6154Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6154RoundedFacts : LeafRoundedFacts 8
    leaf6154Certificate.logOnePlusV leaf6154InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6154InputLogOnePlusV_eq }

private noncomputable def leaf6154Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi83InputQChi innerPair243Input
    leaf6154InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6154LowerChecked :
    lowerCheck 24 leaf6154Box leaf6154Inputs = true := by
  rfl'

private theorem leaf6154CoversExact : CoversExact 8
    leaf6154Box leaf6154Certificate leaf6154InnerLog leaf6154Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi83RoundedFacts
    innerPair243RoundedFacts leaf6154RoundedFacts (by rfl)

private theorem leaf6154FlatSound : Sound leaf6154Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6154CertificateValid
    leaf6154InnerLogValid leaf6154CoversExact leaf6154LowerChecked

private noncomputable def leaf6155Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (17/32), chiHi := (35/64) }

private noncomputable def leaf6155Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108999/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178686464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (138374779/134217728) }, upper := { exponent := 1, mantissa := (2179/2048) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi84LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358064127/34357372928) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6155InnerLog : WideLogData :=
  innerPair118Data

set_option maxRecDepth 1000000 in
private theorem leaf6155LocalValidity :
    LeafFacts leaf6155Box leaf6155Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6155Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178686464) }) = true
      norm_num [leaf6155Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6155CertificateValid :
    WideCertificateValid leaf6155Box leaf6155Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi84ValidityFacts
    leaf6155LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6155CoverageChecked :
    coverageCheck (innerAD leaf6155Box) leaf6155InnerLog = true := by
  rfl'

private theorem leaf6155InnerLogValid :
    leaf6155InnerLog.Valid 8 (innerAD leaf6155Box) :=
  wideLogDataValid_of_cachedCheck endpoint24PositiveFacts
    endpoint74PositiveFacts.valid leaf6155CoverageChecked

private noncomputable def leaf6155InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6155InputLogOnePlusV_eq :
    leaf6155InputLogOnePlusV = outerEnclosure 24
      (leaf6155Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6155RoundedFacts : LeafRoundedFacts 8
    leaf6155Certificate.logOnePlusV leaf6155InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6155InputLogOnePlusV_eq }

private noncomputable def leaf6155Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi84InputQChi innerPair118Input
    leaf6155InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6155LowerChecked :
    lowerCheck 24 leaf6155Box leaf6155Inputs = true := by
  rfl'

private theorem leaf6155CoversExact : CoversExact 8
    leaf6155Box leaf6155Certificate leaf6155InnerLog leaf6155Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi84RoundedFacts
    innerPair118RoundedFacts leaf6155RoundedFacts (by rfl)

private theorem leaf6155FlatSound : Sound leaf6155Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6155CertificateValid
    leaf6155InnerLogValid leaf6155CoversExact leaf6155LowerChecked

private noncomputable def leaf6156Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (35/64), chiHi := (9/16) }

private noncomputable def leaf6156Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109001/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178652672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (140471801/134217728) }, upper := { exponent := 1, mantissa := (553/512) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi85LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358030335/34357305344) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6156InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf6156LocalValidity :
    LeafFacts leaf6156Box leaf6156Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6156Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178652672) }) = true
      norm_num [leaf6156Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6156CertificateValid :
    WideCertificateValid leaf6156Box leaf6156Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi85ValidityFacts
    leaf6156LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6156CoverageChecked :
    coverageCheck (innerAD leaf6156Box) leaf6156InnerLog = true := by
  rfl'

private theorem leaf6156InnerLogValid :
    leaf6156InnerLog.Valid 8 (innerAD leaf6156Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf6156CoverageChecked

private noncomputable def leaf6156InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6156InputLogOnePlusV_eq :
    leaf6156InputLogOnePlusV = outerEnclosure 24
      (leaf6156Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6156RoundedFacts : LeafRoundedFacts 8
    leaf6156Certificate.logOnePlusV leaf6156InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6156InputLogOnePlusV_eq }

private noncomputable def leaf6156Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi85InputQChi innerPair243Input
    leaf6156InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6156LowerChecked :
    lowerCheck 24 leaf6156Box leaf6156Inputs = true := by
  rfl'

private theorem leaf6156CoversExact : CoversExact 8
    leaf6156Box leaf6156Certificate leaf6156InnerLog leaf6156Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi85RoundedFacts
    innerPair243RoundedFacts leaf6156RoundedFacts (by rfl)

private theorem leaf6156FlatSound : Sound leaf6156Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6156CertificateValid
    leaf6156InnerLogValid leaf6156CoversExact leaf6156LowerChecked

private noncomputable def leaf6157Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (17/32), chiHi := (35/64) }

private noncomputable def leaf6157Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109001/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178650624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (140602865/134217728) }, upper := { exponent := 1, mantissa := (1107/1024) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi84LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358028287/34357301248) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6157InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf6157LocalValidity :
    LeafFacts leaf6157Box leaf6157Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6157Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178650624) }) = true
      norm_num [leaf6157Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6157CertificateValid :
    WideCertificateValid leaf6157Box leaf6157Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi84ValidityFacts
    leaf6157LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6157CoverageChecked :
    coverageCheck (innerAD leaf6157Box) leaf6157InnerLog = true := by
  rfl'

private theorem leaf6157InnerLogValid :
    leaf6157InnerLog.Valid 8 (innerAD leaf6157Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf6157CoverageChecked

private noncomputable def leaf6157InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907359/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6157InputLogOnePlusV_eq :
    leaf6157InputLogOnePlusV = outerEnclosure 24
      (leaf6157Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6157RoundedFacts : LeafRoundedFacts 8
    leaf6157Certificate.logOnePlusV leaf6157InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6157InputLogOnePlusV_eq }

private noncomputable def leaf6157Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi84InputQChi innerPair243Input
    leaf6157InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6157LowerChecked :
    lowerCheck 24 leaf6157Box leaf6157Inputs = true := by
  rfl'

private theorem leaf6157CoversExact : CoversExact 8
    leaf6157Box leaf6157Certificate leaf6157InnerLog leaf6157Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi84RoundedFacts
    innerPair243RoundedFacts leaf6157RoundedFacts (by rfl)

private theorem leaf6157FlatSound : Sound leaf6157Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6157CertificateValid
    leaf6157InnerLogValid leaf6157CoversExact leaf6157LowerChecked

private noncomputable def leaf6158Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (35/64), chiHi := (9/16) }

private noncomputable def leaf6158Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109003/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178615808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (142765419/134217728) }, upper := { exponent := 1, mantissa := (281/256) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi85LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357993471/34357231616) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6158InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf6158LocalValidity :
    LeafFacts leaf6158Box leaf6158Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6158Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178615808) }) = true
      norm_num [leaf6158Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6158CertificateValid :
    WideCertificateValid leaf6158Box leaf6158Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi85ValidityFacts
    leaf6158LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6158CoverageChecked :
    coverageCheck (innerAD leaf6158Box) leaf6158InnerLog = true := by
  rfl'

private theorem leaf6158InnerLogValid :
    leaf6158InnerLog.Valid 8 (innerAD leaf6158Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf6158CoverageChecked

private noncomputable def leaf6158InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6158InputLogOnePlusV_eq :
    leaf6158InputLogOnePlusV = outerEnclosure 24
      (leaf6158Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6158RoundedFacts : LeafRoundedFacts 8
    leaf6158Certificate.logOnePlusV leaf6158InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6158InputLogOnePlusV_eq }

private noncomputable def leaf6158Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi85InputQChi innerPair250Input
    leaf6158InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6158LowerChecked :
    lowerCheck 24 leaf6158Box leaf6158Inputs = true := by
  rfl'

private theorem leaf6158CoversExact : CoversExact 8
    leaf6158Box leaf6158Certificate leaf6158InnerLog leaf6158Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi85RoundedFacts
    innerPair250RoundedFacts leaf6158RoundedFacts (by rfl)

private theorem leaf6158FlatSound : Sound leaf6158Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6158CertificateValid
    leaf6158InnerLogValid leaf6158CoversExact leaf6158LowerChecked

private noncomputable def leaf6159Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf6159Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67108999/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178686464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (138374779/134217728) }, upper := { exponent := 1, mantissa := (2179/2048) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358064127/34357372928) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6159InnerLog : WideLogData :=
  innerPair330Data

set_option maxRecDepth 1000000 in
private theorem leaf6159LocalValidity :
    LeafFacts leaf6159Box leaf6159Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6159Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178686464) }) = true
      norm_num [leaf6159Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6159CertificateValid :
    WideCertificateValid leaf6159Box leaf6159Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi82ValidityFacts
    leaf6159LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6159CoverageChecked :
    coverageCheck (innerAD leaf6159Box) leaf6159InnerLog = true := by
  rfl'

private theorem leaf6159InnerLogValid :
    leaf6159InnerLog.Valid 8 (innerAD leaf6159Box) :=
  wideLogDataValid_of_cachedCheck endpoint87PositiveFacts
    endpoint289PositiveFacts.valid leaf6159CoverageChecked

private noncomputable def leaf6159InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6159InputLogOnePlusV_eq :
    leaf6159InputLogOnePlusV = outerEnclosure 24
      (leaf6159Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6159RoundedFacts : LeafRoundedFacts 8
    leaf6159Certificate.logOnePlusV leaf6159InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6159InputLogOnePlusV_eq }

private noncomputable def leaf6159Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi82InputQChi innerPair330Input
    leaf6159InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6159LowerChecked :
    lowerCheck 24 leaf6159Box leaf6159Inputs = true := by
  rfl'

private theorem leaf6159CoversExact : CoversExact 8
    leaf6159Box leaf6159Certificate leaf6159InnerLog leaf6159Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi82RoundedFacts
    innerPair330RoundedFacts leaf6159RoundedFacts (by rfl)

private theorem leaf6159FlatSound : Sound leaf6159Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6159CertificateValid
    leaf6159InnerLogValid leaf6159CoversExact leaf6159LowerChecked

private noncomputable def leaf6160Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (33/64), chiHi := (17/32) }

private noncomputable def leaf6160Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109001/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178650624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (140602865/134217728) }, upper := { exponent := 1, mantissa := (1107/1024) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi83LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358028287/34357301248) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6160InnerLog : WideLogData :=
  innerPair243Data

set_option maxRecDepth 1000000 in
private theorem leaf6160LocalValidity :
    LeafFacts leaf6160Box leaf6160Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6160Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178650624) }) = true
      norm_num [leaf6160Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6160CertificateValid :
    WideCertificateValid leaf6160Box leaf6160Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi83ValidityFacts
    leaf6160LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6160CoverageChecked :
    coverageCheck (innerAD leaf6160Box) leaf6160InnerLog = true := by
  rfl'

private theorem leaf6160InnerLogValid :
    leaf6160InnerLog.Valid 8 (innerAD leaf6160Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint74PositiveFacts.valid leaf6160CoverageChecked

private noncomputable def leaf6160InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907359/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6160InputLogOnePlusV_eq :
    leaf6160InputLogOnePlusV = outerEnclosure 24
      (leaf6160Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6160RoundedFacts : LeafRoundedFacts 8
    leaf6160Certificate.logOnePlusV leaf6160InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6160InputLogOnePlusV_eq }

private noncomputable def leaf6160Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi83InputQChi innerPair243Input
    leaf6160InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6160LowerChecked :
    lowerCheck 24 leaf6160Box leaf6160Inputs = true := by
  rfl'

private theorem leaf6160CoversExact : CoversExact 8
    leaf6160Box leaf6160Certificate leaf6160InnerLog leaf6160Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi83RoundedFacts
    innerPair243RoundedFacts leaf6160RoundedFacts (by rfl)

private theorem leaf6160FlatSound : Sound leaf6160Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6160CertificateValid
    leaf6160InnerLogValid leaf6160CoversExact leaf6160LowerChecked

private noncomputable def leaf6161Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (1/2), chiHi := (33/64) }

private noncomputable def leaf6161Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109001/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178652672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (140471801/134217728) }, upper := { exponent := 1, mantissa := (553/512) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi82LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34358030335/34357305344) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6161InnerLog : WideLogData :=
  innerPair326Data

set_option maxRecDepth 1000000 in
private theorem leaf6161LocalValidity :
    LeafFacts leaf6161Box leaf6161Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6161Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178652672) }) = true
      norm_num [leaf6161Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6161CertificateValid :
    WideCertificateValid leaf6161Box leaf6161Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi82ValidityFacts
    leaf6161LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6161CoverageChecked :
    coverageCheck (innerAD leaf6161Box) leaf6161InnerLog = true := by
  rfl'

private theorem leaf6161InnerLogValid :
    leaf6161InnerLog.Valid 8 (innerAD leaf6161Box) :=
  wideLogDataValid_of_cachedCheck endpoint86PositiveFacts
    endpoint337PositiveFacts.valid leaf6161CoverageChecked

private noncomputable def leaf6161InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6161InputLogOnePlusV_eq :
    leaf6161InputLogOnePlusV = outerEnclosure 24
      (leaf6161Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6161RoundedFacts : LeafRoundedFacts 8
    leaf6161Certificate.logOnePlusV leaf6161InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6161InputLogOnePlusV_eq }

private noncomputable def leaf6161Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi82InputQChi innerPair326Input
    leaf6161InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6161LowerChecked :
    lowerCheck 24 leaf6161Box leaf6161Inputs = true := by
  rfl'

private theorem leaf6161CoversExact : CoversExact 8
    leaf6161Box leaf6161Certificate leaf6161InnerLog leaf6161Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi82RoundedFacts
    innerPair326RoundedFacts leaf6161RoundedFacts (by rfl)

private theorem leaf6161FlatSound : Sound leaf6161Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6161CertificateValid
    leaf6161InnerLogValid leaf6161CoversExact leaf6161LowerChecked

private noncomputable def leaf6162Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (33/64), chiHi := (17/32) }

private noncomputable def leaf6162Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109003/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178615808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (142765419/134217728) }, upper := { exponent := 1, mantissa := (281/256) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi83LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357993471/34357231616) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6162InnerLog : WideLogData :=
  innerPair254Data

set_option maxRecDepth 1000000 in
private theorem leaf6162LocalValidity :
    LeafFacts leaf6162Box leaf6162Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6162Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178615808) }) = true
      norm_num [leaf6162Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6162CertificateValid :
    WideCertificateValid leaf6162Box leaf6162Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi83ValidityFacts
    leaf6162LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6162CoverageChecked :
    coverageCheck (innerAD leaf6162Box) leaf6162InnerLog = true := by
  rfl'

private theorem leaf6162InnerLogValid :
    leaf6162InnerLog.Valid 8 (innerAD leaf6162Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint291PositiveFacts.valid leaf6162CoverageChecked

private noncomputable def leaf6162InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6162InputLogOnePlusV_eq :
    leaf6162InputLogOnePlusV = outerEnclosure 24
      (leaf6162Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6162RoundedFacts : LeafRoundedFacts 8
    leaf6162Certificate.logOnePlusV leaf6162InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6162InputLogOnePlusV_eq }

private noncomputable def leaf6162Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi83InputQChi innerPair254Input
    leaf6162InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6162LowerChecked :
    lowerCheck 24 leaf6162Box leaf6162Inputs = true := by
  rfl'

private theorem leaf6162CoversExact : CoversExact 8
    leaf6162Box leaf6162Certificate leaf6162InnerLog leaf6162Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi83RoundedFacts
    innerPair254RoundedFacts leaf6162RoundedFacts (by rfl)

private theorem leaf6162FlatSound : Sound leaf6162Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6162CertificateValid
    leaf6162InnerLogValid leaf6162CoversExact leaf6162LowerChecked

private noncomputable def leaf6163Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (17/32), chiHi := (35/64) }

private noncomputable def leaf6163Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109003/67108864) }, vSqrt := { lower := (65531/65536), upper := (184724491/184716288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (142830951/134217728) }, upper := { exponent := 1, mantissa := (2249/2048) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi84LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (369440779/369432576) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6163InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf6163LocalValidity :
    LeafFacts leaf6163Box leaf6163Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6163Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (184724491/184716288) }) = true
      norm_num [leaf6163Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6163CertificateValid :
    WideCertificateValid leaf6163Box leaf6163Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi84ValidityFacts
    leaf6163LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6163CoverageChecked :
    coverageCheck (innerAD leaf6163Box) leaf6163InnerLog = true := by
  rfl'

private theorem leaf6163InnerLogValid :
    leaf6163InnerLog.Valid 8 (innerAD leaf6163Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf6163CoverageChecked

private noncomputable def leaf6163InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6163InputLogOnePlusV_eq :
    leaf6163InputLogOnePlusV = outerEnclosure 24
      (leaf6163Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6163RoundedFacts : LeafRoundedFacts 8
    leaf6163Certificate.logOnePlusV leaf6163InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6163InputLogOnePlusV_eq }

private noncomputable def leaf6163Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi84InputQChi innerPair250Input
    leaf6163InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6163LowerChecked :
    lowerCheck 24 leaf6163Box leaf6163Inputs = true := by
  rfl'

private theorem leaf6163CoversExact : CoversExact 8
    leaf6163Box leaf6163Certificate leaf6163InnerLog leaf6163Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi84RoundedFacts
    innerPair250RoundedFacts leaf6163RoundedFacts (by rfl)

private theorem leaf6163FlatSound : Sound leaf6163Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6163CertificateValid
    leaf6163InnerLogValid leaf6163CoversExact leaf6163LowerChecked

private noncomputable def leaf6164Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (35/64), chiHi := (9/16) }

private noncomputable def leaf6164Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109005/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178578944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (145059037/134217728) }, upper := { exponent := 1, mantissa := (571/512) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi85LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357956607/34357157888) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6164InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf6164LocalValidity :
    LeafFacts leaf6164Box leaf6164Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6164Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178578944) }) = true
      norm_num [leaf6164Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6164CertificateValid :
    WideCertificateValid leaf6164Box leaf6164Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi85ValidityFacts
    leaf6164LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6164CoverageChecked :
    coverageCheck (innerAD leaf6164Box) leaf6164InnerLog = true := by
  rfl'

private theorem leaf6164InnerLogValid :
    leaf6164InnerLog.Valid 8 (innerAD leaf6164Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf6164CoverageChecked

private noncomputable def leaf6164InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629471/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6164InputLogOnePlusV_eq :
    leaf6164InputLogOnePlusV = outerEnclosure 24
      (leaf6164Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6164RoundedFacts : LeafRoundedFacts 8
    leaf6164Certificate.logOnePlusV leaf6164InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6164InputLogOnePlusV_eq }

private noncomputable def leaf6164Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi85InputQChi innerPair250Input
    leaf6164InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6164LowerChecked :
    lowerCheck 24 leaf6164Box leaf6164Inputs = true := by
  rfl'

private theorem leaf6164CoversExact : CoversExact 8
    leaf6164Box leaf6164Certificate leaf6164InnerLog leaf6164Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi85RoundedFacts
    innerPair250RoundedFacts leaf6164RoundedFacts (by rfl)

private theorem leaf6164FlatSound : Sound leaf6164Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6164CertificateValid
    leaf6164InnerLogValid leaf6164CoversExact leaf6164LowerChecked

private noncomputable def leaf6165Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (17/32), chiHi := (35/64) }

private noncomputable def leaf6165Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109005/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178578944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (145059037/134217728) }, upper := { exponent := 1, mantissa := (571/512) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi84LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357956607/34357157888) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6165InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf6165LocalValidity :
    LeafFacts leaf6165Box leaf6165Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6165Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178578944) }) = true
      norm_num [leaf6165Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6165CertificateValid :
    WideCertificateValid leaf6165Box leaf6165Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi84ValidityFacts
    leaf6165LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6165CoverageChecked :
    coverageCheck (innerAD leaf6165Box) leaf6165InnerLog = true := by
  rfl'

private theorem leaf6165InnerLogValid :
    leaf6165InnerLog.Valid 8 (innerAD leaf6165Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf6165CoverageChecked

private noncomputable def leaf6165InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629471/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6165InputLogOnePlusV_eq :
    leaf6165InputLogOnePlusV = outerEnclosure 24
      (leaf6165Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6165RoundedFacts : LeafRoundedFacts 8
    leaf6165Certificate.logOnePlusV leaf6165InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6165InputLogOnePlusV_eq }

private noncomputable def leaf6165Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi84InputQChi innerPair250Input
    leaf6165InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6165LowerChecked :
    lowerCheck 24 leaf6165Box leaf6165Inputs = true := by
  rfl'

private theorem leaf6165CoversExact : CoversExact 8
    leaf6165Box leaf6165Certificate leaf6165InnerLog leaf6165Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi84RoundedFacts
    innerPair250RoundedFacts leaf6165RoundedFacts (by rfl)

private theorem leaf6165FlatSound : Sound leaf6165Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6165CertificateValid
    leaf6165InnerLogValid leaf6165CoversExact leaf6165LowerChecked

private noncomputable def leaf6166Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (35/64), chiHi := (9/16) }

private noncomputable def leaf6166Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109007/67108864) }, vSqrt := { lower := (65531/65536), upper := (2454196809/2454077440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (147352655/134217728) }, upper := { exponent := 1, mantissa := (145/128) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi85LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4908274249/4908154880) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6166InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf6166LocalValidity :
    LeafFacts leaf6166Box leaf6166Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6166Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2454196809/2454077440) }) = true
      norm_num [leaf6166Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6166CertificateValid :
    WideCertificateValid leaf6166Box leaf6166Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi85ValidityFacts
    leaf6166LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6166CoverageChecked :
    coverageCheck (innerAD leaf6166Box) leaf6166InnerLog = true := by
  rfl'

private theorem leaf6166InnerLogValid :
    leaf6166InnerLog.Valid 8 (innerAD leaf6166Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf6166CoverageChecked

private noncomputable def leaf6166InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629489/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6166InputLogOnePlusV_eq :
    leaf6166InputLogOnePlusV = outerEnclosure 24
      (leaf6166Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6166RoundedFacts : LeafRoundedFacts 8
    leaf6166Certificate.logOnePlusV leaf6166InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6166InputLogOnePlusV_eq }

private noncomputable def leaf6166Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi85InputQChi innerPair257Input
    leaf6166InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6166LowerChecked :
    lowerCheck 24 leaf6166Box leaf6166Inputs = true := by
  rfl'

private theorem leaf6166CoversExact : CoversExact 8
    leaf6166Box leaf6166Certificate leaf6166InnerLog leaf6166Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi85RoundedFacts
    innerPair257RoundedFacts leaf6166RoundedFacts (by rfl)

private theorem leaf6166FlatSound : Sound leaf6166Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6166CertificateValid
    leaf6166InnerLogValid leaf6166CoversExact leaf6166LowerChecked

private noncomputable def leaf6167Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (9/16), chiHi := (37/64) }

private noncomputable def leaf6167Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109003/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178618880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (142568823/134217728) }, upper := { exponent := 1, mantissa := (2245/2048) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi86LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357996543/34357237760) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6167InnerLog : WideLogData :=
  innerPair244Data

set_option maxRecDepth 1000000 in
private theorem leaf6167LocalValidity :
    LeafFacts leaf6167Box leaf6167Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6167Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178618880) }) = true
      norm_num [leaf6167Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6167CertificateValid :
    WideCertificateValid leaf6167Box leaf6167Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi86ValidityFacts
    leaf6167LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6167CoverageChecked :
    coverageCheck (innerAD leaf6167Box) leaf6167InnerLog = true := by
  rfl'

private theorem leaf6167InnerLogValid :
    leaf6167InnerLog.Valid 8 (innerAD leaf6167Box) :=
  wideLogDataValid_of_cachedCheck endpoint72PositiveFacts
    endpoint75PositiveFacts.valid leaf6167CoverageChecked

private noncomputable def leaf6167InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6167InputLogOnePlusV_eq :
    leaf6167InputLogOnePlusV = outerEnclosure 24
      (leaf6167Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6167RoundedFacts : LeafRoundedFacts 8
    leaf6167Certificate.logOnePlusV leaf6167InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6167InputLogOnePlusV_eq }

private noncomputable def leaf6167Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi86InputQChi innerPair244Input
    leaf6167InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6167LowerChecked :
    lowerCheck 24 leaf6167Box leaf6167Inputs = true := by
  rfl'

private theorem leaf6167CoversExact : CoversExact 8
    leaf6167Box leaf6167Certificate leaf6167InnerLog leaf6167Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi86RoundedFacts
    innerPair244RoundedFacts leaf6167RoundedFacts (by rfl)

private theorem leaf6167FlatSound : Sound leaf6167Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6167CertificateValid
    leaf6167InnerLogValid leaf6167CoversExact leaf6167LowerChecked

private noncomputable def leaf6168Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (37/64), chiHi := (19/32) }

private noncomputable def leaf6168Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109005/67108864) }, vSqrt := { lower := (65531/65536), upper := (2454196809/2454083584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (144665845/134217728) }, upper := { exponent := 1, mantissa := (1139/1024) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi87LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4908280393/4908167168) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6168InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf6168LocalValidity :
    LeafFacts leaf6168Box leaf6168Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6168Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2454196809/2454083584) }) = true
      norm_num [leaf6168Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6168CertificateValid :
    WideCertificateValid leaf6168Box leaf6168Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi87ValidityFacts
    leaf6168LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6168CoverageChecked :
    coverageCheck (innerAD leaf6168Box) leaf6168InnerLog = true := by
  rfl'

private theorem leaf6168InnerLogValid :
    leaf6168InnerLog.Valid 8 (innerAD leaf6168Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf6168CoverageChecked

private noncomputable def leaf6168InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907367/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6168InputLogOnePlusV_eq :
    leaf6168InputLogOnePlusV = outerEnclosure 24
      (leaf6168Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6168RoundedFacts : LeafRoundedFacts 8
    leaf6168Certificate.logOnePlusV leaf6168InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6168InputLogOnePlusV_eq }

private noncomputable def leaf6168Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi87InputQChi innerPair250Input
    leaf6168InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6168LowerChecked :
    lowerCheck 24 leaf6168Box leaf6168Inputs = true := by
  rfl'

private theorem leaf6168CoversExact : CoversExact 8
    leaf6168Box leaf6168Certificate leaf6168InnerLog leaf6168Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi87RoundedFacts
    innerPair250RoundedFacts leaf6168RoundedFacts (by rfl)

private theorem leaf6168FlatSound : Sound leaf6168Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6168CertificateValid
    leaf6168InnerLogValid leaf6168CoversExact leaf6168LowerChecked

private noncomputable def leaf6169Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (9/16), chiHi := (37/64) }

private noncomputable def leaf6169Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109005/67108864) }, vSqrt := { lower := (65531/65536), upper := (5726459221/5726193664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (144927973/134217728) }, upper := { exponent := 1, mantissa := (1141/1024) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi86LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11452652885/11452387328) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6169InnerLog : WideLogData :=
  innerPair250Data

set_option maxRecDepth 1000000 in
private theorem leaf6169LocalValidity :
    LeafFacts leaf6169Box leaf6169Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6169Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5726459221/5726193664) }) = true
      norm_num [leaf6169Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6169CertificateValid :
    WideCertificateValid leaf6169Box leaf6169Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi86ValidityFacts
    leaf6169LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6169CoverageChecked :
    coverageCheck (innerAD leaf6169Box) leaf6169InnerLog = true := by
  rfl'

private theorem leaf6169InnerLogValid :
    leaf6169InnerLog.Valid 8 (innerAD leaf6169Box) :=
  wideLogDataValid_of_cachedCheck endpoint73PositiveFacts
    endpoint75PositiveFacts.valid leaf6169CoverageChecked

private noncomputable def leaf6169InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814735/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6169InputLogOnePlusV_eq :
    leaf6169InputLogOnePlusV = outerEnclosure 24
      (leaf6169Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6169RoundedFacts : LeafRoundedFacts 8
    leaf6169Certificate.logOnePlusV leaf6169InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6169InputLogOnePlusV_eq }

private noncomputable def leaf6169Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi86InputQChi innerPair250Input
    leaf6169InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6169LowerChecked :
    lowerCheck 24 leaf6169Box leaf6169Inputs = true := by
  rfl'

private theorem leaf6169CoversExact : CoversExact 8
    leaf6169Box leaf6169Certificate leaf6169InnerLog leaf6169Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi86RoundedFacts
    innerPair250RoundedFacts leaf6169RoundedFacts (by rfl)

private theorem leaf6169FlatSound : Sound leaf6169Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6169CertificateValid
    leaf6169InnerLogValid leaf6169CoversExact leaf6169LowerChecked

private noncomputable def leaf6170Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (37/64), chiHi := (19/32) }

private noncomputable def leaf6170Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109007/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178546176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (147090527/134217728) }, upper := { exponent := 1, mantissa := (579/512) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi87LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357923839/34357092352) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6170InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf6170LocalValidity :
    LeafFacts leaf6170Box leaf6170Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6170Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178546176) }) = true
      norm_num [leaf6170Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6170CertificateValid :
    WideCertificateValid leaf6170Box leaf6170Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi87ValidityFacts
    leaf6170LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6170CoverageChecked :
    coverageCheck (innerAD leaf6170Box) leaf6170InnerLog = true := by
  rfl'

private theorem leaf6170InnerLogValid :
    leaf6170InnerLog.Valid 8 (innerAD leaf6170Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf6170CoverageChecked

private noncomputable def leaf6170InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629487/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6170InputLogOnePlusV_eq :
    leaf6170InputLogOnePlusV = outerEnclosure 24
      (leaf6170Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6170RoundedFacts : LeafRoundedFacts 8
    leaf6170Certificate.logOnePlusV leaf6170InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6170InputLogOnePlusV_eq }

private noncomputable def leaf6170Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi87InputQChi innerPair257Input
    leaf6170InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6170LowerChecked :
    lowerCheck 24 leaf6170Box leaf6170Inputs = true := by
  rfl'

private theorem leaf6170CoversExact : CoversExact 8
    leaf6170Box leaf6170Certificate leaf6170InnerLog leaf6170Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi87RoundedFacts
    innerPair257RoundedFacts leaf6170RoundedFacts (by rfl)

private theorem leaf6170FlatSound : Sound leaf6170Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6170CertificateValid
    leaf6170InnerLogValid leaf6170CoversExact leaf6170LowerChecked

private noncomputable def leaf6171Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (19/32), chiHi := (5/8) }

private noncomputable def leaf6171Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554537/33554432) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178517504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (73365017/67108864) }, upper := { exponent := 1, mantissa := (293/256) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi73LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357895167/34357035008) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6171InnerLog : WideLogData :=
  innerPair613Data

set_option maxRecDepth 1000000 in
private theorem leaf6171LocalValidity :
    LeafFacts leaf6171Box leaf6171Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6171Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178517504) }) = true
      norm_num [leaf6171Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6171CertificateValid :
    WideCertificateValid leaf6171Box leaf6171Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi73ValidityFacts
    leaf6171LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6171CoverageChecked :
    coverageCheck (innerAD leaf6171Box) leaf6171InnerLog = true := by
  rfl'

private theorem leaf6171InnerLogValid :
    leaf6171InnerLog.Valid 8 (innerAD leaf6171Box) :=
  wideLogDataValid_of_cachedCheck endpoint337PositiveFacts
    endpoint298PositiveFacts.valid leaf6171CoverageChecked

private noncomputable def leaf6171InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629501/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6171InputLogOnePlusV_eq :
    leaf6171InputLogOnePlusV = outerEnclosure 24
      (leaf6171Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6171RoundedFacts : LeafRoundedFacts 8
    leaf6171Certificate.logOnePlusV leaf6171InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6171InputLogOnePlusV_eq }

private noncomputable def leaf6171Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi73InputQChi innerPair613Input
    leaf6171InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6171LowerChecked :
    lowerCheck 24 leaf6171Box leaf6171Inputs = true := by
  rfl'

private theorem leaf6171CoversExact : CoversExact 8
    leaf6171Box leaf6171Certificate leaf6171InnerLog leaf6171Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi73RoundedFacts
    innerPair613RoundedFacts leaf6171RoundedFacts (by rfl)

private theorem leaf6171FlatSound : Sound leaf6171Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6171CertificateValid
    leaf6171InnerLogValid leaf6171CoversExact leaf6171LowerChecked

private noncomputable def leaf6172Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (19/32), chiHi := (39/64) }

private noncomputable def leaf6172Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109009/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178511360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (149253081/134217728) }, upper := { exponent := 1, mantissa := (1175/1024) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi321LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357889023/34357022720) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6172InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf6172LocalValidity :
    LeafFacts leaf6172Box leaf6172Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6172Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178511360) }) = true
      norm_num [leaf6172Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6172CertificateValid :
    WideCertificateValid leaf6172Box leaf6172Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi321ValidityFacts
    leaf6172LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6172CoverageChecked :
    coverageCheck (innerAD leaf6172Box) leaf6172InnerLog = true := by
  rfl'

private theorem leaf6172InnerLogValid :
    leaf6172InnerLog.Valid 8 (innerAD leaf6172Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf6172CoverageChecked

private noncomputable def leaf6172InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (181711/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf6172InputLogOnePlusV_eq :
    leaf6172InputLogOnePlusV = outerEnclosure 24
      (leaf6172Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6172RoundedFacts : LeafRoundedFacts 8
    leaf6172Certificate.logOnePlusV leaf6172InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6172InputLogOnePlusV_eq }

private noncomputable def leaf6172Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi321InputQChi innerPair257Input
    leaf6172InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6172LowerChecked :
    lowerCheck 24 leaf6172Box leaf6172Inputs = true := by
  rfl'

private theorem leaf6172CoversExact : CoversExact 8
    leaf6172Box leaf6172Certificate leaf6172InnerLog leaf6172Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi321RoundedFacts
    innerPair257RoundedFacts leaf6172RoundedFacts (by rfl)

private theorem leaf6172FlatSound : Sound leaf6172Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6172CertificateValid
    leaf6172InnerLogValid leaf6172CoversExact leaf6172LowerChecked

private noncomputable def leaf6173Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (39/64), chiHi := (5/8) }

private noncomputable def leaf6173Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109011/67108864) }, vSqrt := { lower := (65531/65536), upper := (5726459221/5726158848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (151415635/134217728) }, upper := { exponent := 1, mantissa := (149/128) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi322LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11452618069/11452317696) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6173InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6173LocalValidity :
    LeafFacts leaf6173Box leaf6173Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6173Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5726459221/5726158848) }) = true
      norm_num [leaf6173Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6173CertificateValid :
    WideCertificateValid leaf6173Box leaf6173Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi322ValidityFacts
    leaf6173LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6173CoverageChecked :
    coverageCheck (innerAD leaf6173Box) leaf6173InnerLog = true := by
  rfl'

private theorem leaf6173InnerLogValid :
    leaf6173InnerLog.Valid 8 (innerAD leaf6173Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6173CoverageChecked

private noncomputable def leaf6173InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629521/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6173InputLogOnePlusV_eq :
    leaf6173InputLogOnePlusV = outerEnclosure 24
      (leaf6173Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6173RoundedFacts : LeafRoundedFacts 8
    leaf6173Certificate.logOnePlusV leaf6173InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6173InputLogOnePlusV_eq }

private noncomputable def leaf6173Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi322InputQChi innerPair265Input
    leaf6173InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6173LowerChecked :
    lowerCheck 24 leaf6173Box leaf6173Inputs = true := by
  rfl'

private theorem leaf6173CoversExact : CoversExact 8
    leaf6173Box leaf6173Certificate leaf6173InnerLog leaf6173Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi322RoundedFacts
    innerPair265RoundedFacts leaf6173RoundedFacts (by rfl)

private theorem leaf6173FlatSound : Sound leaf6173Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6173CertificateValid
    leaf6173InnerLogValid leaf6173CoversExact leaf6173LowerChecked

private noncomputable def leaf6174Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (9/16), chiHi := (37/64) }

private noncomputable def leaf6174Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109007/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178543104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (147287123/134217728) }, upper := { exponent := 1, mantissa := (2319/2048) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi86LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357920767/34357086208) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6174InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf6174LocalValidity :
    LeafFacts leaf6174Box leaf6174Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6174Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178543104) }) = true
      norm_num [leaf6174Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6174CertificateValid :
    WideCertificateValid leaf6174Box leaf6174Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi86ValidityFacts
    leaf6174LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6174CoverageChecked :
    coverageCheck (innerAD leaf6174Box) leaf6174InnerLog = true := by
  rfl'

private theorem leaf6174InnerLogValid :
    leaf6174InnerLog.Valid 8 (innerAD leaf6174Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf6174CoverageChecked

private noncomputable def leaf6174InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (726843/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6174InputLogOnePlusV_eq :
    leaf6174InputLogOnePlusV = outerEnclosure 24
      (leaf6174Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6174RoundedFacts : LeafRoundedFacts 8
    leaf6174Certificate.logOnePlusV leaf6174InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6174InputLogOnePlusV_eq }

private noncomputable def leaf6174Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi86InputQChi innerPair257Input
    leaf6174InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6174LowerChecked :
    lowerCheck 24 leaf6174Box leaf6174Inputs = true := by
  rfl'

private theorem leaf6174CoversExact : CoversExact 8
    leaf6174Box leaf6174Certificate leaf6174InnerLog leaf6174Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi86RoundedFacts
    innerPair257RoundedFacts leaf6174RoundedFacts (by rfl)

private theorem leaf6174FlatSound : Sound leaf6174Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6174CertificateValid
    leaf6174InnerLogValid leaf6174CoversExact leaf6174LowerChecked

private noncomputable def leaf6175Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (37/64), chiHi := (19/32) }

private noncomputable def leaf6175Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109009/67108864) }, vSqrt := { lower := (65531/65536), upper := (5726459221/5726169088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (149515209/134217728) }, upper := { exponent := 1, mantissa := (1177/1024) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi87LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11452628309/11452338176) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6175InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf6175LocalValidity :
    LeafFacts leaf6175Box leaf6175Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6175Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5726459221/5726169088) }) = true
      norm_num [leaf6175Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6175CertificateValid :
    WideCertificateValid leaf6175Box leaf6175Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi87ValidityFacts
    leaf6175LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6175CoverageChecked :
    coverageCheck (innerAD leaf6175Box) leaf6175InnerLog = true := by
  rfl'

private theorem leaf6175InnerLogValid :
    leaf6175InnerLog.Valid 8 (innerAD leaf6175Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf6175CoverageChecked

private noncomputable def leaf6175InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814753/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6175InputLogOnePlusV_eq :
    leaf6175InputLogOnePlusV = outerEnclosure 24
      (leaf6175Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6175RoundedFacts : LeafRoundedFacts 8
    leaf6175Certificate.logOnePlusV leaf6175InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6175InputLogOnePlusV_eq }

private noncomputable def leaf6175Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi87InputQChi innerPair257Input
    leaf6175InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6175LowerChecked :
    lowerCheck 24 leaf6175Box leaf6175Inputs = true := by
  rfl'

private theorem leaf6175CoversExact : CoversExact 8
    leaf6175Box leaf6175Certificate leaf6175InnerLog leaf6175Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi87RoundedFacts
    innerPair257RoundedFacts leaf6175RoundedFacts (by rfl)

private theorem leaf6175FlatSound : Sound leaf6175Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6175CertificateValid
    leaf6175InnerLogValid leaf6175CoversExact leaf6175LowerChecked

private noncomputable def leaf6176Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (9/16), chiHi := (37/64) }

private noncomputable def leaf6176Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109009/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178505216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (149646273/134217728) }, upper := { exponent := 1, mantissa := (589/512) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi86LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357882879/34357010432) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6176InnerLog : WideLogData :=
  innerPair257Data

set_option maxRecDepth 1000000 in
private theorem leaf6176LocalValidity :
    LeafFacts leaf6176Box leaf6176Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6176Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178505216) }) = true
      norm_num [leaf6176Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6176CertificateValid :
    WideCertificateValid leaf6176Box leaf6176Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi86ValidityFacts
    leaf6176LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6176CoverageChecked :
    coverageCheck (innerAD leaf6176Box) leaf6176InnerLog = true := by
  rfl'

private theorem leaf6176InnerLogValid :
    leaf6176InnerLog.Valid 8 (innerAD leaf6176Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint76PositiveFacts.valid leaf6176CoverageChecked

private noncomputable def leaf6176InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629507/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6176InputLogOnePlusV_eq :
    leaf6176InputLogOnePlusV = outerEnclosure 24
      (leaf6176Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6176RoundedFacts : LeafRoundedFacts 8
    leaf6176Certificate.logOnePlusV leaf6176InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6176InputLogOnePlusV_eq }

private noncomputable def leaf6176Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi86InputQChi innerPair257Input
    leaf6176InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6176LowerChecked :
    lowerCheck 24 leaf6176Box leaf6176Inputs = true := by
  rfl'

private theorem leaf6176CoversExact : CoversExact 8
    leaf6176Box leaf6176Certificate leaf6176InnerLog leaf6176Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi86RoundedFacts
    innerPair257RoundedFacts leaf6176RoundedFacts (by rfl)

private theorem leaf6176FlatSound : Sound leaf6176Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6176CertificateValid
    leaf6176InnerLogValid leaf6176CoversExact leaf6176LowerChecked

private noncomputable def leaf6177Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (37/64), chiHi := (19/32) }

private noncomputable def leaf6177Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109011/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178468352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (151939891/134217728) }, upper := { exponent := 1, mantissa := (299/256) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi87LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357846015/34356936704) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6177InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6177LocalValidity :
    LeafFacts leaf6177Box leaf6177Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6177Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178468352) }) = true
      norm_num [leaf6177Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6177CertificateValid :
    WideCertificateValid leaf6177Box leaf6177Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi87ValidityFacts
    leaf6177LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6177CoverageChecked :
    coverageCheck (innerAD leaf6177Box) leaf6177InnerLog = true := by
  rfl'

private theorem leaf6177InnerLogValid :
    leaf6177InnerLog.Valid 8 (innerAD leaf6177Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6177CoverageChecked

private noncomputable def leaf6177InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629525/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6177InputLogOnePlusV_eq :
    leaf6177InputLogOnePlusV = outerEnclosure 24
      (leaf6177Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6177RoundedFacts : LeafRoundedFacts 8
    leaf6177Certificate.logOnePlusV leaf6177InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6177InputLogOnePlusV_eq }

private noncomputable def leaf6177Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi87InputQChi innerPair265Input
    leaf6177InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6177LowerChecked :
    lowerCheck 24 leaf6177Box leaf6177Inputs = true := by
  rfl'

private theorem leaf6177CoversExact : CoversExact 8
    leaf6177Box leaf6177Certificate leaf6177InnerLog leaf6177Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi87RoundedFacts
    innerPair265RoundedFacts leaf6177RoundedFacts (by rfl)

private theorem leaf6177FlatSound : Sound leaf6177Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6177CertificateValid
    leaf6177InnerLogValid leaf6177CoversExact leaf6177LowerChecked

private noncomputable def leaf6178Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (19/32), chiHi := (39/64) }

private noncomputable def leaf6178Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109011/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178471424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (151743295/134217728) }, upper := { exponent := 1, mantissa := (2389/2048) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi321LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357849087/34356942848) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6178InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6178LocalValidity :
    LeafFacts leaf6178Box leaf6178Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6178Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178471424) }) = true
      norm_num [leaf6178Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6178CertificateValid :
    WideCertificateValid leaf6178Box leaf6178Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi321ValidityFacts
    leaf6178LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6178CoverageChecked :
    coverageCheck (innerAD leaf6178Box) leaf6178InnerLog = true := by
  rfl'

private theorem leaf6178InnerLogValid :
    leaf6178InnerLog.Valid 8 (innerAD leaf6178Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6178CoverageChecked

private noncomputable def leaf6178InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629523/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6178InputLogOnePlusV_eq :
    leaf6178InputLogOnePlusV = outerEnclosure 24
      (leaf6178Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6178RoundedFacts : LeafRoundedFacts 8
    leaf6178Certificate.logOnePlusV leaf6178InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6178InputLogOnePlusV_eq }

private noncomputable def leaf6178Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi321InputQChi innerPair265Input
    leaf6178InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6178LowerChecked :
    lowerCheck 24 leaf6178Box leaf6178Inputs = true := by
  rfl'

private theorem leaf6178CoversExact : CoversExact 8
    leaf6178Box leaf6178Certificate leaf6178InnerLog leaf6178Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi321RoundedFacts
    innerPair265RoundedFacts leaf6178RoundedFacts (by rfl)

private theorem leaf6178FlatSound : Sound leaf6178Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6178CertificateValid
    leaf6178InnerLogValid leaf6178CoversExact leaf6178LowerChecked

private noncomputable def leaf6179Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (39/64), chiHi := (5/8) }

private noncomputable def leaf6179Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109013/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178435584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (153971381/134217728) }, upper := { exponent := 1, mantissa := (303/256) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi322LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357813247/34356871168) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6179InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6179LocalValidity :
    LeafFacts leaf6179Box leaf6179Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6179Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178435584) }) = true
      norm_num [leaf6179Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6179CertificateValid :
    WideCertificateValid leaf6179Box leaf6179Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi322ValidityFacts
    leaf6179LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6179CoverageChecked :
    coverageCheck (innerAD leaf6179Box) leaf6179InnerLog = true := by
  rfl'

private theorem leaf6179InnerLogValid :
    leaf6179InnerLog.Valid 8 (innerAD leaf6179Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6179CoverageChecked

private noncomputable def leaf6179InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629541/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6179InputLogOnePlusV_eq :
    leaf6179InputLogOnePlusV = outerEnclosure 24
      (leaf6179Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6179RoundedFacts : LeafRoundedFacts 8
    leaf6179Certificate.logOnePlusV leaf6179InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6179InputLogOnePlusV_eq }

private noncomputable def leaf6179Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi322InputQChi innerPair265Input
    leaf6179InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6179LowerChecked :
    lowerCheck 24 leaf6179Box leaf6179Inputs = true := by
  rfl'

private theorem leaf6179CoversExact : CoversExact 8
    leaf6179Box leaf6179Certificate leaf6179InnerLog leaf6179Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi322RoundedFacts
    innerPair265RoundedFacts leaf6179RoundedFacts (by rfl)

private theorem leaf6179FlatSound : Sound leaf6179Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6179CertificateValid
    leaf6179InnerLogValid leaf6179CoversExact leaf6179LowerChecked

private noncomputable def leaf6180Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (19/32), chiHi := (39/64) }

private noncomputable def leaf6180Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109013/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178431488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (154233509/134217728) }, upper := { exponent := 1, mantissa := (607/512) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi321LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357809151/34356862976) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6180InnerLog : WideLogData :=
  innerPair265Data

set_option maxRecDepth 1000000 in
private theorem leaf6180LocalValidity :
    LeafFacts leaf6180Box leaf6180Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6180Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178431488) }) = true
      norm_num [leaf6180Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6180CertificateValid :
    WideCertificateValid leaf6180Box leaf6180Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi321ValidityFacts
    leaf6180LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6180CoverageChecked :
    coverageCheck (innerAD leaf6180Box) leaf6180InnerLog = true := by
  rfl'

private theorem leaf6180InnerLogValid :
    leaf6180InnerLog.Valid 8 (innerAD leaf6180Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint77PositiveFacts.valid leaf6180CoverageChecked

private noncomputable def leaf6180InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629543/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6180InputLogOnePlusV_eq :
    leaf6180InputLogOnePlusV = outerEnclosure 24
      (leaf6180Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6180RoundedFacts : LeafRoundedFacts 8
    leaf6180Certificate.logOnePlusV leaf6180InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6180InputLogOnePlusV_eq }

private noncomputable def leaf6180Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi321InputQChi innerPair265Input
    leaf6180InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6180LowerChecked :
    lowerCheck 24 leaf6180Box leaf6180Inputs = true := by
  rfl'

private theorem leaf6180CoversExact : CoversExact 8
    leaf6180Box leaf6180Certificate leaf6180InnerLog leaf6180Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi321RoundedFacts
    innerPair265RoundedFacts leaf6180RoundedFacts (by rfl)

private theorem leaf6180FlatSound : Sound leaf6180Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6180CertificateValid
    leaf6180InnerLogValid leaf6180CoversExact leaf6180LowerChecked

private noncomputable def leaf6181Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (39/64), chiHi := (5/8) }

private noncomputable def leaf6181Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109015/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178394624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (156527127/134217728) }, upper := { exponent := 1, mantissa := (77/64) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi322LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357772287/34356789248) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6181InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf6181LocalValidity :
    LeafFacts leaf6181Box leaf6181Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6181Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178394624) }) = true
      norm_num [leaf6181Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6181CertificateValid :
    WideCertificateValid leaf6181Box leaf6181Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi322ValidityFacts
    leaf6181LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6181CoverageChecked :
    coverageCheck (innerAD leaf6181Box) leaf6181InnerLog = true := by
  rfl'

private theorem leaf6181InnerLogValid :
    leaf6181InnerLog.Valid 8 (innerAD leaf6181Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf6181CoverageChecked

private noncomputable def leaf6181InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629561/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6181InputLogOnePlusV_eq :
    leaf6181InputLogOnePlusV = outerEnclosure 24
      (leaf6181Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6181RoundedFacts : LeafRoundedFacts 8
    leaf6181Certificate.logOnePlusV leaf6181InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6181InputLogOnePlusV_eq }

private noncomputable def leaf6181Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi322InputQChi innerPair273Input
    leaf6181InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6181LowerChecked :
    lowerCheck 24 leaf6181Box leaf6181Inputs = true := by
  rfl'

private theorem leaf6181CoversExact : CoversExact 8
    leaf6181Box leaf6181Certificate leaf6181InnerLog leaf6181Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi322RoundedFacts
    innerPair273RoundedFacts leaf6181RoundedFacts (by rfl)

private theorem leaf6181FlatSound : Sound leaf6181Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6181CertificateValid
    leaf6181InnerLogValid leaf6181CoversExact leaf6181LowerChecked

private noncomputable def component123Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component123Node0_sound : Sound component123Node0Box :=
  sound_of_literal_split component123Node0Box leaf6151Box leaf6152Box
    .chi (33/64) (by rfl) (by rfl)
    leaf6151FlatSound leaf6152FlatSound

private noncomputable def component123Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component123Node1_sound : Sound component123Node1Box :=
  sound_of_literal_split component123Node1Box leaf6153Box leaf6154Box
    .chi (33/64) (by rfl) (by rfl)
    leaf6153FlatSound leaf6154FlatSound

private noncomputable def component123Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component123Node2_sound : Sound component123Node2Box :=
  sound_of_literal_split component123Node2Box component123Node0Box component123Node1Box
    .k (33/16) (by rfl) (by rfl)
    component123Node0_sound component123Node1_sound

private noncomputable def component123Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component123Node3_sound : Sound component123Node3Box :=
  sound_of_literal_split component123Node3Box leaf6155Box leaf6156Box
    .chi (35/64) (by rfl) (by rfl)
    leaf6155FlatSound leaf6156FlatSound

private noncomputable def component123Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component123Node4_sound : Sound component123Node4Box :=
  sound_of_literal_split component123Node4Box leaf6157Box leaf6158Box
    .chi (35/64) (by rfl) (by rfl)
    leaf6157FlatSound leaf6158FlatSound

private noncomputable def component123Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component123Node5_sound : Sound component123Node5Box :=
  sound_of_literal_split component123Node5Box component123Node3Box component123Node4Box
    .k (33/16) (by rfl) (by rfl)
    component123Node3_sound component123Node4_sound

private noncomputable def component123Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component123Node6_sound : Sound component123Node6Box :=
  sound_of_literal_split component123Node6Box component123Node2Box component123Node5Box
    .chi (17/32) (by rfl) (by rfl)
    component123Node2_sound component123Node5_sound

private noncomputable def component123Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component123Node7_sound : Sound component123Node7Box :=
  sound_of_literal_split component123Node7Box leaf6159Box leaf6160Box
    .chi (33/64) (by rfl) (by rfl)
    leaf6159FlatSound leaf6160FlatSound

private noncomputable def component123Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component123Node8_sound : Sound component123Node8Box :=
  sound_of_literal_split component123Node8Box leaf6161Box leaf6162Box
    .chi (33/64) (by rfl) (by rfl)
    leaf6161FlatSound leaf6162FlatSound

private noncomputable def component123Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component123Node9_sound : Sound component123Node9Box :=
  sound_of_literal_split component123Node9Box component123Node7Box component123Node8Box
    .k (35/16) (by rfl) (by rfl)
    component123Node7_sound component123Node8_sound

private noncomputable def component123Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component123Node10_sound : Sound component123Node10Box :=
  sound_of_literal_split component123Node10Box leaf6163Box leaf6164Box
    .chi (35/64) (by rfl) (by rfl)
    leaf6163FlatSound leaf6164FlatSound

private noncomputable def component123Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component123Node11_sound : Sound component123Node11Box :=
  sound_of_literal_split component123Node11Box leaf6165Box leaf6166Box
    .chi (35/64) (by rfl) (by rfl)
    leaf6165FlatSound leaf6166FlatSound

private noncomputable def component123Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component123Node12_sound : Sound component123Node12Box :=
  sound_of_literal_split component123Node12Box component123Node10Box component123Node11Box
    .k (35/16) (by rfl) (by rfl)
    component123Node10_sound component123Node11_sound

private noncomputable def component123Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component123Node13_sound : Sound component123Node13Box :=
  sound_of_literal_split component123Node13Box component123Node9Box component123Node12Box
    .chi (17/32) (by rfl) (by rfl)
    component123Node9_sound component123Node12_sound

private noncomputable def component123Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component123Node14_sound : Sound component123Node14Box :=
  sound_of_literal_split component123Node14Box component123Node6Box component123Node13Box
    .k (17/8) (by rfl) (by rfl)
    component123Node6_sound component123Node13_sound

private noncomputable def component123Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component123Node15_sound : Sound component123Node15Box :=
  sound_of_literal_split component123Node15Box leaf6167Box leaf6168Box
    .chi (37/64) (by rfl) (by rfl)
    leaf6167FlatSound leaf6168FlatSound

private noncomputable def component123Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component123Node16_sound : Sound component123Node16Box :=
  sound_of_literal_split component123Node16Box leaf6169Box leaf6170Box
    .chi (37/64) (by rfl) (by rfl)
    leaf6169FlatSound leaf6170FlatSound

private noncomputable def component123Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component123Node17_sound : Sound component123Node17Box :=
  sound_of_literal_split component123Node17Box component123Node15Box component123Node16Box
    .k (33/16) (by rfl) (by rfl)
    component123Node15_sound component123Node16_sound

private noncomputable def component123Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component123Node18_sound : Sound component123Node18Box :=
  sound_of_literal_split component123Node18Box leaf6172Box leaf6173Box
    .chi (39/64) (by rfl) (by rfl)
    leaf6172FlatSound leaf6173FlatSound

private noncomputable def component123Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component123Node19_sound : Sound component123Node19Box :=
  sound_of_literal_split component123Node19Box leaf6171Box component123Node18Box
    .k (33/16) (by rfl) (by rfl)
    leaf6171FlatSound component123Node18_sound

private noncomputable def component123Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component123Node20_sound : Sound component123Node20Box :=
  sound_of_literal_split component123Node20Box component123Node17Box component123Node19Box
    .chi (19/32) (by rfl) (by rfl)
    component123Node17_sound component123Node19_sound

private noncomputable def component123Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component123Node21_sound : Sound component123Node21Box :=
  sound_of_literal_split component123Node21Box leaf6174Box leaf6175Box
    .chi (37/64) (by rfl) (by rfl)
    leaf6174FlatSound leaf6175FlatSound

private noncomputable def component123Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component123Node22_sound : Sound component123Node22Box :=
  sound_of_literal_split component123Node22Box leaf6176Box leaf6177Box
    .chi (37/64) (by rfl) (by rfl)
    leaf6176FlatSound leaf6177FlatSound

private noncomputable def component123Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component123Node23_sound : Sound component123Node23Box :=
  sound_of_literal_split component123Node23Box component123Node21Box component123Node22Box
    .k (35/16) (by rfl) (by rfl)
    component123Node21_sound component123Node22_sound

private noncomputable def component123Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component123Node24_sound : Sound component123Node24Box :=
  sound_of_literal_split component123Node24Box leaf6178Box leaf6179Box
    .chi (39/64) (by rfl) (by rfl)
    leaf6178FlatSound leaf6179FlatSound

private noncomputable def component123Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component123Node25_sound : Sound component123Node25Box :=
  sound_of_literal_split component123Node25Box leaf6180Box leaf6181Box
    .chi (39/64) (by rfl) (by rfl)
    leaf6180FlatSound leaf6181FlatSound

private noncomputable def component123Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component123Node26_sound : Sound component123Node26Box :=
  sound_of_literal_split component123Node26Box component123Node24Box component123Node25Box
    .k (35/16) (by rfl) (by rfl)
    component123Node24_sound component123Node25_sound

private noncomputable def component123Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component123Node27_sound : Sound component123Node27Box :=
  sound_of_literal_split component123Node27Box component123Node23Box component123Node26Box
    .chi (19/32) (by rfl) (by rfl)
    component123Node23_sound component123Node26_sound

private noncomputable def component123Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component123Node28_sound : Sound component123Node28Box :=
  sound_of_literal_split component123Node28Box component123Node20Box component123Node27Box
    .k (17/8) (by rfl) (by rfl)
    component123Node20_sound component123Node27_sound

noncomputable def component123Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
theorem component123_sound : Sound component123Box :=
  sound_of_literal_split component123Box component123Node14Box component123Node28Box
    .chi (9/16) (by rfl) (by rfl)
    component123Node14_sound component123Node28_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
