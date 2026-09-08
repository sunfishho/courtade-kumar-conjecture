import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
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

private noncomputable def leaf825Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf825Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217835/134217728) }, vSqrt := { lower := (65531/65536), upper := (11184832/11184601) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (171931287/134217728) }, upper := { exponent := 0, mantissa := (2677/2048) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (22369433/22369202) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf825InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf825LocalValidity :
    LeafFacts leaf825Box leaf825Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf825Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (11184832/11184601) }) = true
      norm_num [leaf825Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf825CertificateValid :
    WideCertificateValid leaf825Box leaf825Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi107ValidityFacts
    leaf825LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf825CoverageChecked :
    coverageCheck (innerAD leaf825Box) leaf825InnerLog = true := by
  rfl'

private theorem leaf825InnerLogValid :
    leaf825InnerLog.Valid 8 (innerAD leaf825Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf825CoverageChecked

private noncomputable def leaf825InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf825InputLogOnePlusV_eq :
    leaf825InputLogOnePlusV = outerEnclosure 24
      (leaf825Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf825RoundedFacts : LeafRoundedFacts 8
    leaf825Certificate.logOnePlusV leaf825InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf825InputLogOnePlusV_eq }

private noncomputable def leaf825Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi107InputQChi innerPair16Input
    leaf825InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf825LowerChecked :
    lowerCheck 24 leaf825Box leaf825Inputs = true := by
  rfl'

private theorem leaf825CoversExact : CoversExact 8
    leaf825Box leaf825Certificate leaf825InnerLog leaf825Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi107RoundedFacts
    innerPair16RoundedFacts leaf825RoundedFacts (by rfl)

private theorem leaf825FlatSound : Sound leaf825Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf825CertificateValid
    leaf825InnerLogValid leaf825CoversExact leaf825LowerChecked

private noncomputable def leaf826Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf826Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217837/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777248/16776883) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (174290437/134217728) }, upper := { exponent := 0, mantissa := (1357/1024) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554131/33553766) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf826InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf826LocalValidity :
    LeafFacts leaf826Box leaf826Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf826Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777248/16776883) }) = true
      norm_num [leaf826Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf826CertificateValid :
    WideCertificateValid leaf826Box leaf826Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi108ValidityFacts
    leaf826LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf826CoverageChecked :
    coverageCheck (innerAD leaf826Box) leaf826InnerLog = true := by
  rfl'

private theorem leaf826InnerLogValid :
    leaf826InnerLog.Valid 8 (innerAD leaf826Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf826CoverageChecked

private noncomputable def leaf826InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf826InputLogOnePlusV_eq :
    leaf826InputLogOnePlusV = outerEnclosure 24
      (leaf826Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf826RoundedFacts : LeafRoundedFacts 8
    leaf826Certificate.logOnePlusV leaf826InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf826InputLogOnePlusV_eq }

private noncomputable def leaf826Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi108InputQChi innerPair17Input
    leaf826InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf826LowerChecked :
    lowerCheck 24 leaf826Box leaf826Inputs = true := by
  rfl'

private theorem leaf826CoversExact : CoversExact 8
    leaf826Box leaf826Certificate leaf826InnerLog leaf826Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi108RoundedFacts
    innerPair17RoundedFacts leaf826RoundedFacts (by rfl)

private theorem leaf826FlatSound : Sound leaf826Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf826CertificateValid
    leaf826InnerLogValid leaf826CoversExact leaf826LowerChecked

private noncomputable def leaf827Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf827Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217837/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777248/16776893) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (172979797/134217728) }, upper := { exponent := 0, mantissa := (1347/1024) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554141/33553786) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf827InnerLog : WideLogData :=
  innerPair129Data

set_option maxRecDepth 1000000 in
private theorem leaf827LocalValidity :
    LeafFacts leaf827Box leaf827Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf827Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777248/16776893) }) = true
      norm_num [leaf827Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf827CertificateValid :
    WideCertificateValid leaf827Box leaf827Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi107ValidityFacts
    leaf827LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf827CoverageChecked :
    coverageCheck (innerAD leaf827Box) leaf827InnerLog = true := by
  rfl'

private theorem leaf827InnerLogValid :
    leaf827InnerLog.Valid 8 (innerAD leaf827Box) :=
  wideLogDataValid_of_cachedCheck endpoint28PositiveFacts
    endpoint9PositiveFacts.valid leaf827CoverageChecked

private noncomputable def leaf827InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf827InputLogOnePlusV_eq :
    leaf827InputLogOnePlusV = outerEnclosure 24
      (leaf827Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf827RoundedFacts : LeafRoundedFacts 8
    leaf827Certificate.logOnePlusV leaf827InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf827InputLogOnePlusV_eq }

private noncomputable def leaf827Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi107InputQChi innerPair129Input
    leaf827InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf827LowerChecked :
    lowerCheck 24 leaf827Box leaf827Inputs = true := by
  rfl'

private theorem leaf827CoversExact : CoversExact 8
    leaf827Box leaf827Certificate leaf827InnerLog leaf827Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi107RoundedFacts
    innerPair129RoundedFacts leaf827RoundedFacts (by rfl)

private theorem leaf827FlatSound : Sound leaf827Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf827CertificateValid
    leaf827InnerLogValid leaf827CoversExact leaf827LowerChecked

private noncomputable def leaf828Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf828Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217839/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388624/8388437) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (175404479/134217728) }, upper := { exponent := 0, mantissa := (683/512) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777061/16776874) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf828InnerLog : WideLogData :=
  innerPair131Data

set_option maxRecDepth 1000000 in
private theorem leaf828LocalValidity :
    LeafFacts leaf828Box leaf828Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf828Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388624/8388437) }) = true
      norm_num [leaf828Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf828CertificateValid :
    WideCertificateValid leaf828Box leaf828Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi108ValidityFacts
    leaf828LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf828CoverageChecked :
    coverageCheck (innerAD leaf828Box) leaf828InnerLog = true := by
  rfl'

private theorem leaf828InnerLogValid :
    leaf828InnerLog.Valid 8 (innerAD leaf828Box) :=
  wideLogDataValid_of_cachedCheck endpoint29PositiveFacts
    endpoint37PositiveFacts.valid leaf828CoverageChecked

private noncomputable def leaf828InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf828InputLogOnePlusV_eq :
    leaf828InputLogOnePlusV = outerEnclosure 24
      (leaf828Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf828RoundedFacts : LeafRoundedFacts 8
    leaf828Certificate.logOnePlusV leaf828InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf828InputLogOnePlusV_eq }

private noncomputable def leaf828Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi108InputQChi innerPair131Input
    leaf828InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf828LowerChecked :
    lowerCheck 24 leaf828Box leaf828Inputs = true := by
  rfl'

private theorem leaf828CoversExact : CoversExact 8
    leaf828Box leaf828Certificate leaf828InnerLog leaf828Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi108RoundedFacts
    innerPair131RoundedFacts leaf828RoundedFacts (by rfl)

private theorem leaf828FlatSound : Sound leaf828Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf828CertificateValid
    leaf828InnerLogValid leaf828CoversExact leaf828LowerChecked

private noncomputable def leaf829Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf829Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217839/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554496/33553729) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (176649587/134217728) }, upper := { exponent := 0, mantissa := (2751/2048) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108225/67107458) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf829InnerLog : WideLogData :=
  innerPair25Data

set_option maxRecDepth 1000000 in
private theorem leaf829LocalValidity :
    LeafFacts leaf829Box leaf829Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf829Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554496/33553729) }) = true
      norm_num [leaf829Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf829CertificateValid :
    WideCertificateValid leaf829Box leaf829Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi109ValidityFacts
    leaf829LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf829CoverageChecked :
    coverageCheck (innerAD leaf829Box) leaf829InnerLog = true := by
  rfl'

private theorem leaf829InnerLogValid :
    leaf829InnerLog.Valid 8 (innerAD leaf829Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint37PositiveFacts.valid leaf829CoverageChecked

private noncomputable def leaf829InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf829InputLogOnePlusV_eq :
    leaf829InputLogOnePlusV = outerEnclosure 24
      (leaf829Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf829RoundedFacts : LeafRoundedFacts 8
    leaf829Certificate.logOnePlusV leaf829InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf829InputLogOnePlusV_eq }

private noncomputable def leaf829Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi109InputQChi innerPair25Input
    leaf829InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf829LowerChecked :
    lowerCheck 24 leaf829Box leaf829Inputs = true := by
  rfl'

private theorem leaf829CoversExact : CoversExact 8
    leaf829Box leaf829Certificate leaf829InnerLog leaf829Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi109RoundedFacts
    innerPair25RoundedFacts leaf829RoundedFacts (by rfl)

private theorem leaf829FlatSound : Sound leaf829Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf829CertificateValid
    leaf829InnerLogValid leaf829CoversExact leaf829LowerChecked

private noncomputable def leaf830Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf830Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217841/134217728) }, vSqrt := { lower := (65531/65536), upper := (2796208/2796141) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (179008737/134217728) }, upper := { exponent := 0, mantissa := (697/512) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (5592349/5592282) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf830InnerLog : WideLogData :=
  innerPair392Data

set_option maxRecDepth 1000000 in
private theorem leaf830LocalValidity :
    LeafFacts leaf830Box leaf830Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf830Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2796208/2796141) }) = true
      norm_num [leaf830Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf830CertificateValid :
    WideCertificateValid leaf830Box leaf830Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi110ValidityFacts
    leaf830LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf830CoverageChecked :
    coverageCheck (innerAD leaf830Box) leaf830InnerLog = true := by
  rfl'

private theorem leaf830InnerLogValid :
    leaf830InnerLog.Valid 8 (innerAD leaf830Box) :=
  wideLogDataValid_of_cachedCheck endpoint103PositiveFacts
    endpoint104PositiveFacts.valid leaf830CoverageChecked

private noncomputable def leaf830InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814641/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf830InputLogOnePlusV_eq :
    leaf830InputLogOnePlusV = outerEnclosure 24
      (leaf830Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf830RoundedFacts : LeafRoundedFacts 8
    leaf830Certificate.logOnePlusV leaf830InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf830InputLogOnePlusV_eq }

private noncomputable def leaf830Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi110InputQChi innerPair392Input
    leaf830InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf830LowerChecked :
    lowerCheck 24 leaf830Box leaf830Inputs = true := by
  rfl'

private theorem leaf830CoversExact : CoversExact 8
    leaf830Box leaf830Certificate leaf830InnerLog leaf830Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi110RoundedFacts
    innerPair392RoundedFacts leaf830RoundedFacts (by rfl)

private theorem leaf830FlatSound : Sound leaf830Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf830CertificateValid
    leaf830InnerLogValid leaf830CoversExact leaf830LowerChecked

private noncomputable def leaf831Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf831Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217841/134217728) }, vSqrt := { lower := (65531/65536), upper := (5592416/5592285) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (177829161/134217728) }, upper := { exponent := 0, mantissa := (1385/1024) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (11184701/11184570) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf831InnerLog : WideLogData :=
  innerPair393Data

set_option maxRecDepth 1000000 in
private theorem leaf831LocalValidity :
    LeafFacts leaf831Box leaf831Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf831Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (5592416/5592285) }) = true
      norm_num [leaf831Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf831CertificateValid :
    WideCertificateValid leaf831Box leaf831Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi109ValidityFacts
    leaf831LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf831CoverageChecked :
    coverageCheck (innerAD leaf831Box) leaf831InnerLog = true := by
  rfl'

private theorem leaf831InnerLogValid :
    leaf831InnerLog.Valid 8 (innerAD leaf831Box) :=
  wideLogDataValid_of_cachedCheck endpoint105PositiveFacts
    endpoint106PositiveFacts.valid leaf831CoverageChecked

private noncomputable def leaf831InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf831InputLogOnePlusV_eq :
    leaf831InputLogOnePlusV = outerEnclosure 24
      (leaf831Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf831RoundedFacts : LeafRoundedFacts 8
    leaf831Certificate.logOnePlusV leaf831InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf831InputLogOnePlusV_eq }

private noncomputable def leaf831Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi109InputQChi innerPair393Input
    leaf831InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf831LowerChecked :
    lowerCheck 24 leaf831Box leaf831Inputs = true := by
  rfl'

private theorem leaf831CoversExact : CoversExact 8
    leaf831Box leaf831Certificate leaf831InnerLog leaf831Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi109RoundedFacts
    innerPair393RoundedFacts leaf831RoundedFacts (by rfl)

private theorem leaf831FlatSound : Sound leaf831Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf831CertificateValid
    leaf831InnerLogValid leaf831CoversExact leaf831LowerChecked

private noncomputable def leaf832Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf832Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435645/268435456) }, vSqrt := { lower := (65531/65536), upper := (986896/986873) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (360540493/268435456) }, upper := { exponent := 0, mantissa := (1399/1024) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (1973769/1973746) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf832InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf832LocalValidity :
    LeafFacts leaf832Box leaf832Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf832Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (986896/986873) }) = true
      norm_num [leaf832Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf832CertificateValid :
    WideCertificateValid leaf832Box leaf832Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi110ValidityFacts
    leaf832LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf832CoverageChecked :
    coverageCheck (innerAD leaf832Box) leaf832InnerLog = true := by
  rfl'

private theorem leaf832InnerLogValid :
    leaf832InnerLog.Valid 8 (innerAD leaf832Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf832CoverageChecked

private noncomputable def leaf832InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf832InputLogOnePlusV_eq :
    leaf832InputLogOnePlusV = outerEnclosure 24
      (leaf832Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf832RoundedFacts : LeafRoundedFacts 8
    leaf832Certificate.logOnePlusV leaf832InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf832InputLogOnePlusV_eq }

private noncomputable def leaf832Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi110InputQChi innerPair21Input
    leaf832InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf832LowerChecked :
    lowerCheck 24 leaf832Box leaf832Inputs = true := by
  rfl'

private theorem leaf832CoversExact : CoversExact 8
    leaf832Box leaf832Certificate leaf832InnerLog leaf832Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi110RoundedFacts
    innerPair21RoundedFacts leaf832RoundedFacts (by rfl)

private theorem leaf832FlatSound : Sound leaf832Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf832CertificateValid
    leaf832InnerLogValid leaf832CoversExact leaf832LowerChecked

private noncomputable def leaf833Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf833Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435647/268435456) }, vSqrt := { lower := (65531/65536), upper := (4194308/4194209) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (361785599/268435456) }, upper := { exponent := 0, mantissa := (351/256) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388517/8388418) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf833InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf833LocalValidity :
    LeafFacts leaf833Box leaf833Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf833Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194308/4194209) }) = true
      norm_num [leaf833Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf833CertificateValid :
    WideCertificateValid leaf833Box leaf833Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi110ValidityFacts
    leaf833LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf833CoverageChecked :
    coverageCheck (innerAD leaf833Box) leaf833InnerLog = true := by
  rfl'

private theorem leaf833InnerLogValid :
    leaf833InnerLog.Valid 8 (innerAD leaf833Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf833CoverageChecked

private noncomputable def leaf833InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf833InputLogOnePlusV_eq :
    leaf833InputLogOnePlusV = outerEnclosure 24
      (leaf833Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf833RoundedFacts : LeafRoundedFacts 8
    leaf833Certificate.logOnePlusV leaf833InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf833InputLogOnePlusV_eq }

private noncomputable def leaf833Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi110InputQChi innerPair21Input
    leaf833InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf833LowerChecked :
    lowerCheck 24 leaf833Box leaf833Inputs = true := by
  rfl'

private theorem leaf833CoversExact : CoversExact 8
    leaf833Box leaf833Certificate leaf833InnerLog leaf833Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi110RoundedFacts
    innerPair21RoundedFacts leaf833RoundedFacts (by rfl)

private theorem leaf833FlatSound : Sound leaf833Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf833CertificateValid
    leaf833InnerLogValid leaf833CoversExact leaf833LowerChecked

private noncomputable def leaf834Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf834Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217839/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554496/33553769) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (174028307/134217728) }, upper := { exponent := 0, mantissa := (2711/2048) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108265/67107538) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf834InnerLog : WideLogData :=
  innerPair129Data

set_option maxRecDepth 1000000 in
private theorem leaf834LocalValidity :
    LeafFacts leaf834Box leaf834Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf834Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554496/33553769) }) = true
      norm_num [leaf834Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf834CertificateValid :
    WideCertificateValid leaf834Box leaf834Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi107ValidityFacts
    leaf834LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf834CoverageChecked :
    coverageCheck (innerAD leaf834Box) leaf834InnerLog = true := by
  rfl'

private theorem leaf834InnerLogValid :
    leaf834InnerLog.Valid 8 (innerAD leaf834Box) :=
  wideLogDataValid_of_cachedCheck endpoint28PositiveFacts
    endpoint9PositiveFacts.valid leaf834CoverageChecked

private noncomputable def leaf834InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814631/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf834InputLogOnePlusV_eq :
    leaf834InputLogOnePlusV = outerEnclosure 24
      (leaf834Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf834RoundedFacts : LeafRoundedFacts 8
    leaf834Certificate.logOnePlusV leaf834InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf834InputLogOnePlusV_eq }

private noncomputable def leaf834Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi107InputQChi innerPair129Input
    leaf834InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf834LowerChecked :
    lowerCheck 24 leaf834Box leaf834Inputs = true := by
  rfl'

private theorem leaf834CoversExact : CoversExact 8
    leaf834Box leaf834Certificate leaf834InnerLog leaf834Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi107RoundedFacts
    innerPair129RoundedFacts leaf834RoundedFacts (by rfl)

private theorem leaf834FlatSound : Sound leaf834Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf834CertificateValid
    leaf834InnerLogValid leaf834CoversExact leaf834LowerChecked

private noncomputable def leaf835Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf835Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435645/268435456) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553739) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (353069845/268435456) }, upper := { exponent := 0, mantissa := (2741/2048) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108203/67107478) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf835InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf835LocalValidity :
    LeafFacts leaf835Box leaf835Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf835Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553739) }) = true
      norm_num [leaf835Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf835CertificateValid :
    WideCertificateValid leaf835Box leaf835Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi108ValidityFacts
    leaf835LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf835CoverageChecked :
    coverageCheck (innerAD leaf835Box) leaf835InnerLog = true := by
  rfl'

private theorem leaf835InnerLogValid :
    leaf835InnerLog.Valid 8 (innerAD leaf835Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf835CoverageChecked

private noncomputable def leaf835InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814631/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf835InputLogOnePlusV_eq :
    leaf835InputLogOnePlusV = outerEnclosure 24
      (leaf835Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf835RoundedFacts : LeafRoundedFacts 8
    leaf835Certificate.logOnePlusV leaf835InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf835InputLogOnePlusV_eq }

private noncomputable def leaf835Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi108InputQChi innerPair21Input
    leaf835InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf835LowerChecked :
    lowerCheck 24 leaf835Box leaf835Inputs = true := by
  rfl'

private theorem leaf835CoversExact : CoversExact 8
    leaf835Box leaf835Certificate leaf835InnerLog leaf835Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi108RoundedFacts
    innerPair21RoundedFacts leaf835RoundedFacts (by rfl)

private theorem leaf835FlatSound : Sound leaf835Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf835CertificateValid
    leaf835InnerLogValid leaf835CoversExact leaf835LowerChecked

private noncomputable def leaf836Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf836Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435647/268435456) }, vSqrt := { lower := (65531/65536), upper := (16777232/16776865) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (354183887/268435456) }, upper := { exponent := 0, mantissa := (1375/1024) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554097/33553730) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf836InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf836LocalValidity :
    LeafFacts leaf836Box leaf836Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf836Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777232/16776865) }) = true
      norm_num [leaf836Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf836CertificateValid :
    WideCertificateValid leaf836Box leaf836Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi108ValidityFacts
    leaf836LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf836CoverageChecked :
    coverageCheck (innerAD leaf836Box) leaf836InnerLog = true := by
  rfl'

private theorem leaf836InnerLogValid :
    leaf836InnerLog.Valid 8 (innerAD leaf836Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf836CoverageChecked

private noncomputable def leaf836InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (726829/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf836InputLogOnePlusV_eq :
    leaf836InputLogOnePlusV = outerEnclosure 24
      (leaf836Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf836RoundedFacts : LeafRoundedFacts 8
    leaf836Certificate.logOnePlusV leaf836InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf836InputLogOnePlusV_eq }

private noncomputable def leaf836Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi108InputQChi innerPair21Input
    leaf836InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf836LowerChecked :
    lowerCheck 24 leaf836Box leaf836Inputs = true := by
  rfl'

private theorem leaf836CoversExact : CoversExact 8
    leaf836Box leaf836Certificate leaf836InnerLog leaf836Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi108RoundedFacts
    innerPair21RoundedFacts leaf836RoundedFacts (by rfl)

private theorem leaf836FlatSound : Sound leaf836Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf836CertificateValid
    leaf836InnerLogValid leaf836CoversExact leaf836LowerChecked

private noncomputable def leaf837Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf837Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435647/268435456) }, vSqrt := { lower := (65531/65536), upper := (67108928/67107521) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (350186435/268435456) }, upper := { exponent := 0, mantissa := (5439/4096) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (134216449/134215042) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf837InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf837LocalValidity :
    LeafFacts leaf837Box leaf837Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf837Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (67108928/67107521) }) = true
      norm_num [leaf837Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf837CertificateValid :
    WideCertificateValid leaf837Box leaf837Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi107ValidityFacts
    leaf837LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf837CoverageChecked :
    coverageCheck (innerAD leaf837Box) leaf837InnerLog = true := by
  rfl'

private theorem leaf837InnerLogValid :
    leaf837InnerLog.Valid 8 (innerAD leaf837Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf837CoverageChecked

private noncomputable def leaf837InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf837InputLogOnePlusV_eq :
    leaf837InputLogOnePlusV = outerEnclosure 24
      (leaf837Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf837RoundedFacts : LeafRoundedFacts 8
    leaf837Certificate.logOnePlusV leaf837InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf837InputLogOnePlusV_eq }

private noncomputable def leaf837Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi107InputQChi innerPair17Input
    leaf837InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf837LowerChecked :
    lowerCheck 24 leaf837Box leaf837Inputs = true := by
  rfl'

private theorem leaf837CoversExact : CoversExact 8
    leaf837Box leaf837Certificate leaf837InnerLog leaf837Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi107RoundedFacts
    innerPair17RoundedFacts leaf837RoundedFacts (by rfl)

private theorem leaf837FlatSound : Sound leaf837Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf837CertificateValid
    leaf837InnerLogValid leaf837CoversExact leaf837LowerChecked

private noncomputable def leaf838Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (1/8), chiHi := (17/128) }

private noncomputable def leaf838Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435649/268435456) }, vSqrt := { lower := (32765/32768), upper := (4194308/4194219) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (351234945/268435456) }, upper := { exponent := 0, mantissa := (341/256) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi107LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388527/8388438) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf838InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf838LocalValidity :
    LeafFacts leaf838Box leaf838Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf838Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194308/4194219) }) = true
      norm_num [leaf838Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf838CertificateValid :
    WideCertificateValid leaf838Box leaf838Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi107ValidityFacts
    leaf838LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf838CoverageChecked :
    coverageCheck (innerAD leaf838Box) leaf838InnerLog = true := by
  rfl'

private theorem leaf838InnerLogValid :
    leaf838InnerLog.Valid 8 (innerAD leaf838Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf838CoverageChecked

private noncomputable def leaf838InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf838InputLogOnePlusV_eq :
    leaf838InputLogOnePlusV = outerEnclosure 24
      (leaf838Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf838RoundedFacts : LeafRoundedFacts 8
    leaf838Certificate.logOnePlusV leaf838InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf838InputLogOnePlusV_eq }

private noncomputable def leaf838Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi107InputQChi innerPair17Input
    leaf838InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf838LowerChecked :
    lowerCheck 24 leaf838Box leaf838Inputs = true := by
  rfl'

private theorem leaf838CoversExact : CoversExact 8
    leaf838Box leaf838Certificate leaf838InnerLog leaf838Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi107RoundedFacts
    innerPair17RoundedFacts leaf838RoundedFacts (by rfl)

private theorem leaf838FlatSound : Sound leaf838Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf838CertificateValid
    leaf838InnerLogValid leaf838CoversExact leaf838LowerChecked

private noncomputable def leaf839Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf839Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435649/268435456) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553721) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (355297929/268435456) }, upper := { exponent := 0, mantissa := (2759/2048) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108185/67107442) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf839InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf839LocalValidity :
    LeafFacts leaf839Box leaf839Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf839Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553721) }) = true
      norm_num [leaf839Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf839CertificateValid :
    WideCertificateValid leaf839Box leaf839Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi108ValidityFacts
    leaf839LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf839CoverageChecked :
    coverageCheck (innerAD leaf839Box) leaf839InnerLog = true := by
  rfl'

private theorem leaf839InnerLogValid :
    leaf839InnerLog.Valid 8 (innerAD leaf839Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf839CoverageChecked

private noncomputable def leaf839InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814633/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf839InputLogOnePlusV_eq :
    leaf839InputLogOnePlusV = outerEnclosure 24
      (leaf839Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf839RoundedFacts : LeafRoundedFacts 8
    leaf839Certificate.logOnePlusV leaf839InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf839InputLogOnePlusV_eq }

private noncomputable def leaf839Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi108InputQChi innerPair21Input
    leaf839InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf839LowerChecked :
    lowerCheck 24 leaf839Box leaf839Inputs = true := by
  rfl'

private theorem leaf839CoversExact : CoversExact 8
    leaf839Box leaf839Certificate leaf839InnerLog leaf839Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi108RoundedFacts
    innerPair21RoundedFacts leaf839RoundedFacts (by rfl)

private theorem leaf839FlatSound : Sound leaf839Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf839CertificateValid
    leaf839InnerLogValid leaf839CoversExact leaf839LowerChecked

private noncomputable def leaf840Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (17/128), chiHi := (9/64) }

private noncomputable def leaf840Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435651/268435456) }, vSqrt := { lower := (32765/32768), upper := (2097154/2097107) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (356411971/268435456) }, upper := { exponent := 0, mantissa := (173/128) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi108LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4194261/4194214) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf840InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf840LocalValidity :
    LeafFacts leaf840Box leaf840Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf840Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2097154/2097107) }) = true
      norm_num [leaf840Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf840CertificateValid :
    WideCertificateValid leaf840Box leaf840Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi108ValidityFacts
    leaf840LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf840CoverageChecked :
    coverageCheck (innerAD leaf840Box) leaf840InnerLog = true := by
  rfl'

private theorem leaf840InnerLogValid :
    leaf840InnerLog.Valid 8 (innerAD leaf840Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf840CoverageChecked

private noncomputable def leaf840InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf840InputLogOnePlusV_eq :
    leaf840InputLogOnePlusV = outerEnclosure 24
      (leaf840Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf840RoundedFacts : LeafRoundedFacts 8
    leaf840Certificate.logOnePlusV leaf840InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf840InputLogOnePlusV_eq }

private noncomputable def leaf840Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi108InputQChi innerPair21Input
    leaf840InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf840LowerChecked :
    lowerCheck 24 leaf840Box leaf840Inputs = true := by
  rfl'

private theorem leaf840CoversExact : CoversExact 8
    leaf840Box leaf840Certificate leaf840InnerLog leaf840Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi108RoundedFacts
    innerPair21RoundedFacts leaf840RoundedFacts (by rfl)

private theorem leaf840FlatSound : Sound leaf840Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf840CertificateValid
    leaf840InnerLogValid leaf840CoversExact leaf840LowerChecked

private noncomputable def leaf841Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf841Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435647/268435456) }, vSqrt := { lower := (65531/65536), upper := (67108928/67107401) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (358050275/268435456) }, upper := { exponent := 0, mantissa := (5559/4096) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (134216329/134214802) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf841InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf841LocalValidity :
    LeafFacts leaf841Box leaf841Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf841Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (67108928/67107401) }) = true
      norm_num [leaf841Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf841CertificateValid :
    WideCertificateValid leaf841Box leaf841Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi109ValidityFacts
    leaf841LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf841CoverageChecked :
    coverageCheck (innerAD leaf841Box) leaf841InnerLog = true := by
  rfl'

private theorem leaf841InnerLogValid :
    leaf841InnerLog.Valid 8 (innerAD leaf841Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf841CoverageChecked

private noncomputable def leaf841InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf841InputLogOnePlusV_eq :
    leaf841InputLogOnePlusV = outerEnclosure 24
      (leaf841Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf841RoundedFacts : LeafRoundedFacts 8
    leaf841Certificate.logOnePlusV leaf841InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf841InputLogOnePlusV_eq }

private noncomputable def leaf841Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi109InputQChi innerPair21Input
    leaf841InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf841LowerChecked :
    lowerCheck 24 leaf841Box leaf841Inputs = true := by
  rfl'

private theorem leaf841CoversExact : CoversExact 8
    leaf841Box leaf841Certificate leaf841InnerLog leaf841Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi109RoundedFacts
    innerPair21RoundedFacts leaf841RoundedFacts (by rfl)

private theorem leaf841FlatSound : Sound leaf841Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf841CertificateValid
    leaf841InnerLogValid leaf841CoversExact leaf841LowerChecked

private noncomputable def leaf842Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf842Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435649/268435456) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553691) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (359229849/268435456) }, upper := { exponent := 0, mantissa := (2789/2048) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108155/67107382) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf842InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf842LocalValidity :
    LeafFacts leaf842Box leaf842Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf842Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553691) }) = true
      norm_num [leaf842Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf842CertificateValid :
    WideCertificateValid leaf842Box leaf842Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi109ValidityFacts
    leaf842LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf842CoverageChecked :
    coverageCheck (innerAD leaf842Box) leaf842InnerLog = true := by
  rfl'

private theorem leaf842InnerLogValid :
    leaf842InnerLog.Valid 8 (innerAD leaf842Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf842CoverageChecked

private noncomputable def leaf842InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814637/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf842InputLogOnePlusV_eq :
    leaf842InputLogOnePlusV = outerEnclosure 24
      (leaf842Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf842RoundedFacts : LeafRoundedFacts 8
    leaf842Certificate.logOnePlusV leaf842InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf842InputLogOnePlusV_eq }

private noncomputable def leaf842Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi109InputQChi innerPair21Input
    leaf842InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf842LowerChecked :
    lowerCheck 24 leaf842Box leaf842Inputs = true := by
  rfl'

private theorem leaf842CoversExact : CoversExact 8
    leaf842Box leaf842Certificate leaf842InnerLog leaf842Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi109RoundedFacts
    innerPair21RoundedFacts leaf842RoundedFacts (by rfl)

private theorem leaf842FlatSound : Sound leaf842Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf842CertificateValid
    leaf842InnerLogValid leaf842CoversExact leaf842LowerChecked

private noncomputable def leaf843Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf843Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435649/268435456) }, vSqrt := { lower := (65531/65536), upper := (16777232/16776831) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (363030705/268435456) }, upper := { exponent := 0, mantissa := (1409/1024) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554063/33553662) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf843InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf843LocalValidity :
    LeafFacts leaf843Box leaf843Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf843Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777232/16776831) }) = true
      norm_num [leaf843Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf843CertificateValid :
    WideCertificateValid leaf843Box leaf843Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi110ValidityFacts
    leaf843LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf843CoverageChecked :
    coverageCheck (innerAD leaf843Box) leaf843InnerLog = true := by
  rfl'

private theorem leaf843InnerLogValid :
    leaf843InnerLog.Valid 8 (innerAD leaf843Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf843CoverageChecked

private noncomputable def leaf843InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf843InputLogOnePlusV_eq :
    leaf843InputLogOnePlusV = outerEnclosure 24
      (leaf843Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf843RoundedFacts : LeafRoundedFacts 8
    leaf843Certificate.logOnePlusV leaf843InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf843InputLogOnePlusV_eq }

private noncomputable def leaf843Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi110InputQChi innerPair22Input
    leaf843InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf843LowerChecked :
    lowerCheck 24 leaf843Box leaf843Inputs = true := by
  rfl'

private theorem leaf843CoversExact : CoversExact 8
    leaf843Box leaf843Certificate leaf843InnerLog leaf843Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi110RoundedFacts
    innerPair22RoundedFacts leaf843RoundedFacts (by rfl)

private theorem leaf843FlatSound : Sound leaf843Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf843CertificateValid
    leaf843InnerLogValid leaf843CoversExact leaf843LowerChecked

private noncomputable def leaf844Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf844Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435651/268435456) }, vSqrt := { lower := (65531/65536), upper := (8388616/8388413) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (364275811/268435456) }, upper := { exponent := 0, mantissa := (707/512) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777029/16776826) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf844InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf844LocalValidity :
    LeafFacts leaf844Box leaf844Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf844Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388616/8388413) }) = true
      norm_num [leaf844Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf844CertificateValid :
    WideCertificateValid leaf844Box leaf844Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi110ValidityFacts
    leaf844LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf844CoverageChecked :
    coverageCheck (innerAD leaf844Box) leaf844InnerLog = true := by
  rfl'

private theorem leaf844InnerLogValid :
    leaf844InnerLog.Valid 8 (innerAD leaf844Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf844CoverageChecked

private noncomputable def leaf844InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf844InputLogOnePlusV_eq :
    leaf844InputLogOnePlusV = outerEnclosure 24
      (leaf844Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf844RoundedFacts : LeafRoundedFacts 8
    leaf844Certificate.logOnePlusV leaf844InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf844InputLogOnePlusV_eq }

private noncomputable def leaf844Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi110InputQChi innerPair22Input
    leaf844InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf844LowerChecked :
    lowerCheck 24 leaf844Box leaf844Inputs = true := by
  rfl'

private theorem leaf844CoversExact : CoversExact 8
    leaf844Box leaf844Certificate leaf844InnerLog leaf844Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi110RoundedFacts
    innerPair22RoundedFacts leaf844RoundedFacts (by rfl)

private theorem leaf844FlatSound : Sound leaf844Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf844CertificateValid
    leaf844InnerLogValid leaf844CoversExact leaf844LowerChecked

private noncomputable def leaf845Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf845Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435651/268435456) }, vSqrt := { lower := (65531/65536), upper := (67108928/67107363) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (360409423/268435456) }, upper := { exponent := 0, mantissa := (5597/4096) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (134216291/134214726) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf845InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf845LocalValidity :
    LeafFacts leaf845Box leaf845Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf845Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (67108928/67107363) }) = true
      norm_num [leaf845Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf845CertificateValid :
    WideCertificateValid leaf845Box leaf845Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi109ValidityFacts
    leaf845LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf845CoverageChecked :
    coverageCheck (innerAD leaf845Box) leaf845InnerLog = true := by
  rfl'

private theorem leaf845InnerLogValid :
    leaf845InnerLog.Valid 8 (innerAD leaf845Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf845CoverageChecked

private noncomputable def leaf845InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf845InputLogOnePlusV_eq :
    leaf845InputLogOnePlusV = outerEnclosure 24
      (leaf845Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf845RoundedFacts : LeafRoundedFacts 8
    leaf845Certificate.logOnePlusV leaf845InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf845InputLogOnePlusV_eq }

private noncomputable def leaf845Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi109InputQChi innerPair21Input
    leaf845InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf845LowerChecked :
    lowerCheck 24 leaf845Box leaf845Inputs = true := by
  rfl'

private theorem leaf845CoversExact : CoversExact 8
    leaf845Box leaf845Certificate leaf845InnerLog leaf845Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi109RoundedFacts
    innerPair21RoundedFacts leaf845RoundedFacts (by rfl)

private theorem leaf845FlatSound : Sound leaf845Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf845CertificateValid
    leaf845InnerLogValid leaf845CoversExact leaf845LowerChecked

private noncomputable def leaf846Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (9/64), chiHi := (19/128) }

private noncomputable def leaf846Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435653/268435456) }, vSqrt := { lower := (32765/32768), upper := (4194308/4194209) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (361588997/268435456) }, upper := { exponent := 0, mantissa := (351/256) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi109LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388517/8388418) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf846InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf846LocalValidity :
    LeafFacts leaf846Box leaf846Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf846Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194308/4194209) }) = true
      norm_num [leaf846Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf846CertificateValid :
    WideCertificateValid leaf846Box leaf846Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi109ValidityFacts
    leaf846LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf846CoverageChecked :
    coverageCheck (innerAD leaf846Box) leaf846InnerLog = true := by
  rfl'

private theorem leaf846InnerLogValid :
    leaf846InnerLog.Valid 8 (innerAD leaf846Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf846CoverageChecked

private noncomputable def leaf846InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf846InputLogOnePlusV_eq :
    leaf846InputLogOnePlusV = outerEnclosure 24
      (leaf846Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf846RoundedFacts : LeafRoundedFacts 8
    leaf846Certificate.logOnePlusV leaf846InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf846InputLogOnePlusV_eq }

private noncomputable def leaf846Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi109InputQChi innerPair21Input
    leaf846InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf846LowerChecked :
    lowerCheck 24 leaf846Box leaf846Inputs = true := by
  rfl'

private theorem leaf846CoversExact : CoversExact 8
    leaf846Box leaf846Certificate leaf846InnerLog leaf846Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi109RoundedFacts
    innerPair21RoundedFacts leaf846RoundedFacts (by rfl)

private theorem leaf846FlatSound : Sound leaf846Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf846CertificateValid
    leaf846InnerLogValid leaf846CoversExact leaf846LowerChecked

private noncomputable def leaf847Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf847Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435653/268435456) }, vSqrt := { lower := (65531/65536), upper := (16777232/16776821) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (365520917/268435456) }, upper := { exponent := 0, mantissa := (1419/1024) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554053/33553642) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf847InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf847LocalValidity :
    LeafFacts leaf847Box leaf847Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf847Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777232/16776821) }) = true
      norm_num [leaf847Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf847CertificateValid :
    WideCertificateValid leaf847Box leaf847Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi110ValidityFacts
    leaf847LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf847CoverageChecked :
    coverageCheck (innerAD leaf847Box) leaf847InnerLog = true := by
  rfl'

private theorem leaf847InnerLogValid :
    leaf847InnerLog.Valid 8 (innerAD leaf847Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf847CoverageChecked

private noncomputable def leaf847InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf847InputLogOnePlusV_eq :
    leaf847InputLogOnePlusV = outerEnclosure 24
      (leaf847Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf847RoundedFacts : LeafRoundedFacts 8
    leaf847Certificate.logOnePlusV leaf847InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf847InputLogOnePlusV_eq }

private noncomputable def leaf847Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi110InputQChi innerPair22Input
    leaf847InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf847LowerChecked :
    lowerCheck 24 leaf847Box leaf847Inputs = true := by
  rfl'

private theorem leaf847CoversExact : CoversExact 8
    leaf847Box leaf847Certificate leaf847InnerLog leaf847Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi110RoundedFacts
    innerPair22RoundedFacts leaf847RoundedFacts (by rfl)

private theorem leaf847FlatSound : Sound leaf847Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf847CertificateValid
    leaf847InnerLogValid leaf847CoversExact leaf847LowerChecked

private noncomputable def leaf848Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (19/128), chiHi := (5/32) }

private noncomputable def leaf848Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435655/268435456) }, vSqrt := { lower := (32765/32768), upper := (1048577/1048551) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (366766023/268435456) }, upper := { exponent := 0, mantissa := (89/64) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi110LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (1048564/1048551) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf848InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf848LocalValidity :
    LeafFacts leaf848Box leaf848Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf848Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1048577/1048551) }) = true
      norm_num [leaf848Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf848CertificateValid :
    WideCertificateValid leaf848Box leaf848Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi110ValidityFacts
    leaf848LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf848CoverageChecked :
    coverageCheck (innerAD leaf848Box) leaf848InnerLog = true := by
  rfl'

private theorem leaf848InnerLogValid :
    leaf848InnerLog.Valid 8 (innerAD leaf848Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf848CoverageChecked

private noncomputable def leaf848InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf848InputLogOnePlusV_eq :
    leaf848InputLogOnePlusV = outerEnclosure 24
      (leaf848Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf848RoundedFacts : LeafRoundedFacts 8
    leaf848Certificate.logOnePlusV leaf848InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf848InputLogOnePlusV_eq }

private noncomputable def leaf848Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi110InputQChi innerPair22Input
    leaf848InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf848LowerChecked :
    lowerCheck 24 leaf848Box leaf848Inputs = true := by
  rfl'

private theorem leaf848CoversExact : CoversExact 8
    leaf848Box leaf848Certificate leaf848InnerLog leaf848Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi110RoundedFacts
    innerPair22RoundedFacts leaf848RoundedFacts (by rfl)

private theorem leaf848FlatSound : Sound leaf848Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf848CertificateValid
    leaf848InnerLogValid leaf848CoversExact leaf848LowerChecked

private noncomputable def leaf849Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf849Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217895/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553629) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (181367835/134217728) }, upper := { exponent := 0, mantissa := (2851/2048) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108093/67107258) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf849InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf849LocalValidity :
    LeafFacts leaf849Box leaf849Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf849Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553629) }) = true
      norm_num [leaf849Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf849CertificateValid :
    WideCertificateValid leaf849Box leaf849Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi42ValidityFacts
    leaf849LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf849CoverageChecked :
    coverageCheck (innerAD leaf849Box) leaf849InnerLog = true := by
  rfl'

private theorem leaf849InnerLogValid :
    leaf849InnerLog.Valid 8 (innerAD leaf849Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf849CoverageChecked

private noncomputable def leaf849InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf849InputLogOnePlusV_eq :
    leaf849InputLogOnePlusV = outerEnclosure 24
      (leaf849Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf849RoundedFacts : LeafRoundedFacts 8
    leaf849Certificate.logOnePlusV leaf849InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf849InputLogOnePlusV_eq }

private noncomputable def leaf849Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi42InputQChi innerPair22Input
    leaf849InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf849LowerChecked :
    lowerCheck 24 leaf849Box leaf849Inputs = true := by
  rfl'

private theorem leaf849CoversExact : CoversExact 8
    leaf849Box leaf849Certificate leaf849InnerLog leaf849Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi42RoundedFacts
    innerPair22RoundedFacts leaf849RoundedFacts (by rfl)

private theorem leaf849FlatSound : Sound leaf849Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf849CertificateValid
    leaf849InnerLogValid leaf849CoversExact leaf849LowerChecked

private noncomputable def leaf850Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf850Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217897/134217728) }, vSqrt := { lower := (65531/65536), upper := (16777232/16776809) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (182023153/134217728) }, upper := { exponent := 0, mantissa := (1431/1024) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554041/33553618) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf850InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf850LocalValidity :
    LeafFacts leaf850Box leaf850Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf850Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777232/16776809) }) = true
      norm_num [leaf850Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf850CertificateValid :
    WideCertificateValid leaf850Box leaf850Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi42ValidityFacts
    leaf850LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf850CoverageChecked :
    coverageCheck (innerAD leaf850Box) leaf850InnerLog = true := by
  rfl'

private theorem leaf850InnerLogValid :
    leaf850InnerLog.Valid 8 (innerAD leaf850Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf850CoverageChecked

private noncomputable def leaf850InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907323/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf850InputLogOnePlusV_eq :
    leaf850InputLogOnePlusV = outerEnclosure 24
      (leaf850Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf850RoundedFacts : LeafRoundedFacts 8
    leaf850Certificate.logOnePlusV leaf850InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf850InputLogOnePlusV_eq }

private noncomputable def leaf850Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi42InputQChi innerPair22Input
    leaf850InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf850LowerChecked :
    lowerCheck 24 leaf850Box leaf850Inputs = true := by
  rfl'

private theorem leaf850CoversExact : CoversExact 8
    leaf850Box leaf850Certificate leaf850InnerLog leaf850Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi42RoundedFacts
    innerPair22RoundedFacts leaf850RoundedFacts (by rfl)

private theorem leaf850FlatSound : Sound leaf850Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf850CertificateValid
    leaf850InnerLogValid leaf850CoversExact leaf850LowerChecked

private noncomputable def leaf851Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf851Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217897/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388616/8388389) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (186086137/134217728) }, upper := { exponent := 0, mantissa := (731/512) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777005/16776778) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf851InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf851LocalValidity :
    LeafFacts leaf851Box leaf851Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf851Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388616/8388389) }) = true
      norm_num [leaf851Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf851CertificateValid :
    WideCertificateValid leaf851Box leaf851Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi43ValidityFacts
    leaf851LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf851CoverageChecked :
    coverageCheck (innerAD leaf851Box) leaf851InnerLog = true := by
  rfl'

private theorem leaf851InnerLogValid :
    leaf851InnerLog.Valid 8 (innerAD leaf851Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf851CoverageChecked

private noncomputable def leaf851InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907327/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf851InputLogOnePlusV_eq :
    leaf851InputLogOnePlusV = outerEnclosure 24
      (leaf851Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf851RoundedFacts : LeafRoundedFacts 8
    leaf851Certificate.logOnePlusV leaf851InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf851InputLogOnePlusV_eq }

private noncomputable def leaf851Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi43InputQChi innerPair26Input
    leaf851InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf851LowerChecked :
    lowerCheck 24 leaf851Box leaf851Inputs = true := by
  rfl'

private theorem leaf851CoversExact : CoversExact 8
    leaf851Box leaf851Certificate leaf851InnerLog leaf851Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi43RoundedFacts
    innerPair26RoundedFacts leaf851RoundedFacts (by rfl)

private theorem leaf851FlatSound : Sound leaf851Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf851CertificateValid
    leaf851InnerLogValid leaf851CoversExact leaf851LowerChecked

private noncomputable def leaf852Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf852Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217899/134217728) }, vSqrt := { lower := (65531/65536), upper := (4194308/4194193) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (186806987/134217728) }, upper := { exponent := 0, mantissa := (367/256) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388501/8388386) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf852InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf852LocalValidity :
    LeafFacts leaf852Box leaf852Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf852Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194308/4194193) }) = true
      norm_num [leaf852Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf852CertificateValid :
    WideCertificateValid leaf852Box leaf852Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi43ValidityFacts
    leaf852LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf852CoverageChecked :
    coverageCheck (innerAD leaf852Box) leaf852InnerLog = true := by
  rfl'

private theorem leaf852InnerLogValid :
    leaf852InnerLog.Valid 8 (innerAD leaf852Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf852CoverageChecked

private noncomputable def leaf852InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf852InputLogOnePlusV_eq :
    leaf852InputLogOnePlusV = outerEnclosure 24
      (leaf852Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf852RoundedFacts : LeafRoundedFacts 8
    leaf852Certificate.logOnePlusV leaf852InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf852InputLogOnePlusV_eq }

private noncomputable def leaf852Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi43InputQChi innerPair26Input
    leaf852InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf852LowerChecked :
    lowerCheck 24 leaf852Box leaf852Inputs = true := by
  rfl'

private theorem leaf852CoversExact : CoversExact 8
    leaf852Box leaf852Certificate leaf852InnerLog leaf852Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi43RoundedFacts
    innerPair26RoundedFacts leaf852RoundedFacts (by rfl)

private theorem leaf852FlatSound : Sound leaf852Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf852CertificateValid
    leaf852InnerLogValid leaf852CoversExact leaf852LowerChecked

private noncomputable def leaf853Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf853Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217899/134217728) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553607) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (182678471/134217728) }, upper := { exponent := 0, mantissa := (2873/2048) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108071/67107214) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf853InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf853LocalValidity :
    LeafFacts leaf853Box leaf853Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf853Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553607) }) = true
      norm_num [leaf853Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf853CertificateValid :
    WideCertificateValid leaf853Box leaf853Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi42ValidityFacts
    leaf853LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf853CoverageChecked :
    coverageCheck (innerAD leaf853Box) leaf853InnerLog = true := by
  rfl'

private theorem leaf853InnerLogValid :
    leaf853InnerLog.Valid 8 (innerAD leaf853Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf853CoverageChecked

private noncomputable def leaf853InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf853InputLogOnePlusV_eq :
    leaf853InputLogOnePlusV = outerEnclosure 24
      (leaf853Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf853RoundedFacts : LeafRoundedFacts 8
    leaf853Certificate.logOnePlusV leaf853InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf853InputLogOnePlusV_eq }

private noncomputable def leaf853Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi42InputQChi innerPair22Input
    leaf853InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf853LowerChecked :
    lowerCheck 24 leaf853Box leaf853Inputs = true := by
  rfl'

private theorem leaf853CoversExact : CoversExact 8
    leaf853Box leaf853Certificate leaf853InnerLog leaf853Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi42RoundedFacts
    innerPair22RoundedFacts leaf853RoundedFacts (by rfl)

private theorem leaf853FlatSound : Sound leaf853Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf853CertificateValid
    leaf853InnerLogValid leaf853CoversExact leaf853LowerChecked

private noncomputable def leaf854Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf854Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217901/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388616/8388399) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (183333789/134217728) }, upper := { exponent := 0, mantissa := (721/512) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16777015/16776798) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf854InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf854LocalValidity :
    LeafFacts leaf854Box leaf854Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf854Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388616/8388399) }) = true
      norm_num [leaf854Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf854CertificateValid :
    WideCertificateValid leaf854Box leaf854Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi42ValidityFacts
    leaf854LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf854CoverageChecked :
    coverageCheck (innerAD leaf854Box) leaf854InnerLog = true := by
  rfl'

private theorem leaf854InnerLogValid :
    leaf854InnerLog.Valid 8 (innerAD leaf854Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf854CoverageChecked

private noncomputable def leaf854InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf854InputLogOnePlusV_eq :
    leaf854InputLogOnePlusV = outerEnclosure 24
      (leaf854Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf854RoundedFacts : LeafRoundedFacts 8
    leaf854Certificate.logOnePlusV leaf854InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf854InputLogOnePlusV_eq }

private noncomputable def leaf854Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi42InputQChi innerPair22Input
    leaf854InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf854LowerChecked :
    lowerCheck 24 leaf854Box leaf854Inputs = true := by
  rfl'

private theorem leaf854CoversExact : CoversExact 8
    leaf854Box leaf854Certificate leaf854InnerLog leaf854Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi42RoundedFacts
    innerPair22RoundedFacts leaf854RoundedFacts (by rfl)

private theorem leaf854FlatSound : Sound leaf854Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf854CertificateValid
    leaf854InnerLogValid leaf854CoversExact leaf854LowerChecked

private noncomputable def leaf855Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf855Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217901/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388616/8388383) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (187527837/134217728) }, upper := { exponent := 0, mantissa := (737/512) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16776999/16776766) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf855InnerLog : WideLogData :=
  innerPair138Data

set_option maxRecDepth 1000000 in
private theorem leaf855LocalValidity :
    LeafFacts leaf855Box leaf855Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf855Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388616/8388383) }) = true
      norm_num [leaf855Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf855CertificateValid :
    WideCertificateValid leaf855Box leaf855Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi43ValidityFacts
    leaf855LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf855CoverageChecked :
    coverageCheck (innerAD leaf855Box) leaf855InnerLog = true := by
  rfl'

private theorem leaf855InnerLogValid :
    leaf855InnerLog.Valid 8 (innerAD leaf855Box) :=
  wideLogDataValid_of_cachedCheck endpoint34PositiveFacts
    endpoint41PositiveFacts.valid leaf855CoverageChecked

private noncomputable def leaf855InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814657/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf855InputLogOnePlusV_eq :
    leaf855InputLogOnePlusV = outerEnclosure 24
      (leaf855Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf855RoundedFacts : LeafRoundedFacts 8
    leaf855Certificate.logOnePlusV leaf855InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf855InputLogOnePlusV_eq }

private noncomputable def leaf855Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi43InputQChi innerPair138Input
    leaf855InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf855LowerChecked :
    lowerCheck 24 leaf855Box leaf855Inputs = true := by
  rfl'

private theorem leaf855CoversExact : CoversExact 8
    leaf855Box leaf855Certificate leaf855InnerLog leaf855Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi43RoundedFacts
    innerPair138RoundedFacts leaf855RoundedFacts (by rfl)

private theorem leaf855FlatSound : Sound leaf855Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf855CertificateValid
    leaf855InnerLogValid leaf855CoversExact leaf855LowerChecked

private noncomputable def leaf856Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf856Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217903/134217728) }, vSqrt := { lower := (65531/65536), upper := (2097154/2097095) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (188248687/134217728) }, upper := { exponent := 0, mantissa := (185/128) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (4194249/4194190) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf856InnerLog : WideLogData :=
  innerPair138Data

set_option maxRecDepth 1000000 in
private theorem leaf856LocalValidity :
    LeafFacts leaf856Box leaf856Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf856Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (2097154/2097095) }) = true
      norm_num [leaf856Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf856CertificateValid :
    WideCertificateValid leaf856Box leaf856Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi43ValidityFacts
    leaf856LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf856CoverageChecked :
    coverageCheck (innerAD leaf856Box) leaf856InnerLog = true := by
  rfl'

private theorem leaf856InnerLogValid :
    leaf856InnerLog.Valid 8 (innerAD leaf856Box) :=
  wideLogDataValid_of_cachedCheck endpoint34PositiveFacts
    endpoint41PositiveFacts.valid leaf856CoverageChecked

private noncomputable def leaf856InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629317/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf856InputLogOnePlusV_eq :
    leaf856InputLogOnePlusV = outerEnclosure 24
      (leaf856Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf856RoundedFacts : LeafRoundedFacts 8
    leaf856Certificate.logOnePlusV leaf856InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf856InputLogOnePlusV_eq }

private noncomputable def leaf856Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi43InputQChi innerPair138Input
    leaf856InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf856LowerChecked :
    lowerCheck 24 leaf856Box leaf856Inputs = true := by
  rfl'

private theorem leaf856CoversExact : CoversExact 8
    leaf856Box leaf856Certificate leaf856InnerLog leaf856Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi43RoundedFacts
    innerPair138RoundedFacts leaf856RoundedFacts (by rfl)

private theorem leaf856FlatSound : Sound leaf856Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf856CertificateValid
    leaf856InnerLogValid leaf856CoversExact leaf856LowerChecked

private noncomputable def leaf857Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf857Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435651/268435456) }, vSqrt := { lower := (65531/65536), upper := (67108928/67107247) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (368011135/268435456) }, upper := { exponent := 0, mantissa := (5713/4096) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (134216175/134214494) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf857InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf857LocalValidity :
    LeafFacts leaf857Box leaf857Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf857Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (67108928/67107247) }) = true
      norm_num [leaf857Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf857CertificateValid :
    WideCertificateValid leaf857Box leaf857Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi111ValidityFacts
    leaf857LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf857CoverageChecked :
    coverageCheck (innerAD leaf857Box) leaf857InnerLog = true := by
  rfl'

private theorem leaf857InnerLogValid :
    leaf857InnerLog.Valid 8 (innerAD leaf857Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf857CoverageChecked

private noncomputable def leaf857InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf857InputLogOnePlusV_eq :
    leaf857InputLogOnePlusV = outerEnclosure 24
      (leaf857Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf857RoundedFacts : LeafRoundedFacts 8
    leaf857Certificate.logOnePlusV leaf857InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf857InputLogOnePlusV_eq }

private noncomputable def leaf857Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi111InputQChi innerPair22Input
    leaf857InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf857LowerChecked :
    lowerCheck 24 leaf857Box leaf857Inputs = true := by
  rfl'

private theorem leaf857CoversExact : CoversExact 8
    leaf857Box leaf857Certificate leaf857InnerLog leaf857Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi111RoundedFacts
    innerPair22RoundedFacts leaf857RoundedFacts (by rfl)

private theorem leaf857FlatSound : Sound leaf857Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf857CertificateValid
    leaf857InnerLogValid leaf857CoversExact leaf857LowerChecked

private noncomputable def leaf858Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf858Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435653/268435456) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553613) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (369321773/268435456) }, upper := { exponent := 0, mantissa := (2867/2048) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108077/67107226) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf858InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf858LocalValidity :
    LeafFacts leaf858Box leaf858Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf858Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553613) }) = true
      norm_num [leaf858Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf858CertificateValid :
    WideCertificateValid leaf858Box leaf858Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi111ValidityFacts
    leaf858LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf858CoverageChecked :
    coverageCheck (innerAD leaf858Box) leaf858InnerLog = true := by
  rfl'

private theorem leaf858InnerLogValid :
    leaf858InnerLog.Valid 8 (innerAD leaf858Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf858CoverageChecked

private noncomputable def leaf858InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf858InputLogOnePlusV_eq :
    leaf858InputLogOnePlusV = outerEnclosure 24
      (leaf858Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf858RoundedFacts : LeafRoundedFacts 8
    leaf858Certificate.logOnePlusV leaf858InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf858InputLogOnePlusV_eq }

private noncomputable def leaf858Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi111InputQChi innerPair26Input
    leaf858InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf858LowerChecked :
    lowerCheck 24 leaf858Box leaf858Inputs = true := by
  rfl'

private theorem leaf858CoversExact : CoversExact 8
    leaf858Box leaf858Certificate leaf858InnerLog leaf858Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi111RoundedFacts
    innerPair26RoundedFacts leaf858RoundedFacts (by rfl)

private theorem leaf858FlatSound : Sound leaf858Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf858CertificateValid
    leaf858InnerLogValid leaf858CoversExact leaf858LowerChecked

private noncomputable def leaf859Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf859Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435653/268435456) }, vSqrt := { lower := (65531/65536), upper := (33554464/33553585) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (372991565/268435456) }, upper := { exponent := 0, mantissa := (2895/2048) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (67108049/67107170) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf859InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf859LocalValidity :
    LeafFacts leaf859Box leaf859Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf859Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (33554464/33553585) }) = true
      norm_num [leaf859Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf859CertificateValid :
    WideCertificateValid leaf859Box leaf859Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi112ValidityFacts
    leaf859LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf859CoverageChecked :
    coverageCheck (innerAD leaf859Box) leaf859InnerLog = true := by
  rfl'

private theorem leaf859InnerLogValid :
    leaf859InnerLog.Valid 8 (innerAD leaf859Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf859CoverageChecked

private noncomputable def leaf859InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907325/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf859InputLogOnePlusV_eq :
    leaf859InputLogOnePlusV = outerEnclosure 24
      (leaf859Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf859RoundedFacts : LeafRoundedFacts 8
    leaf859Certificate.logOnePlusV leaf859InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf859InputLogOnePlusV_eq }

private noncomputable def leaf859Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi112InputQChi innerPair26Input
    leaf859InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf859LowerChecked :
    lowerCheck 24 leaf859Box leaf859Inputs = true := by
  rfl'

private theorem leaf859CoversExact : CoversExact 8
    leaf859Box leaf859Certificate leaf859InnerLog leaf859Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi112RoundedFacts
    innerPair26RoundedFacts leaf859RoundedFacts (by rfl)

private theorem leaf859FlatSound : Sound leaf859Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf859CertificateValid
    leaf859InnerLogValid leaf859CoversExact leaf859LowerChecked

private noncomputable def leaf860Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf860Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435655/268435456) }, vSqrt := { lower := (65531/65536), upper := (16777232/16776787) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (374367735/268435456) }, upper := { exponent := 0, mantissa := (1453/1024) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (33554019/33553574) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf860InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf860LocalValidity :
    LeafFacts leaf860Box leaf860Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf860Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (16777232/16776787) }) = true
      norm_num [leaf860Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf860CertificateValid :
    WideCertificateValid leaf860Box leaf860Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi112ValidityFacts
    leaf860LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf860CoverageChecked :
    coverageCheck (innerAD leaf860Box) leaf860InnerLog = true := by
  rfl'

private theorem leaf860InnerLogValid :
    leaf860InnerLog.Valid 8 (innerAD leaf860Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf860CoverageChecked

private noncomputable def leaf860InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf860InputLogOnePlusV_eq :
    leaf860InputLogOnePlusV = outerEnclosure 24
      (leaf860Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf860RoundedFacts : LeafRoundedFacts 8
    leaf860Certificate.logOnePlusV leaf860InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf860InputLogOnePlusV_eq }

private noncomputable def leaf860Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi112InputQChi innerPair26Input
    leaf860InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf860LowerChecked :
    lowerCheck 24 leaf860Box leaf860Inputs = true := by
  rfl'

private theorem leaf860CoversExact : CoversExact 8
    leaf860Box leaf860Certificate leaf860InnerLog leaf860Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi112RoundedFacts
    innerPair26RoundedFacts leaf860RoundedFacts (by rfl)

private theorem leaf860FlatSound : Sound leaf860Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf860CertificateValid
    leaf860InnerLogValid leaf860CoversExact leaf860LowerChecked

private noncomputable def leaf861Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf861Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217905/134217728) }, vSqrt := { lower := (65531/65536), upper := (8388616/8388377) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (188969537/134217728) }, upper := { exponent := 0, mantissa := (743/512) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16776993/16776754) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf861InnerLog : WideLogData :=
  innerPair144Data

set_option maxRecDepth 1000000 in
private theorem leaf861LocalValidity :
    LeafFacts leaf861Box leaf861Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf861Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388616/8388377) }) = true
      norm_num [leaf861Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf861CertificateValid :
    WideCertificateValid leaf861Box leaf861Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi43ValidityFacts
    leaf861LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf861CoverageChecked :
    coverageCheck (innerAD leaf861Box) leaf861InnerLog = true := by
  rfl'

private theorem leaf861InnerLogValid :
    leaf861InnerLog.Valid 8 (innerAD leaf861Box) :=
  wideLogDataValid_of_cachedCheck endpoint38PositiveFacts
    endpoint41PositiveFacts.valid leaf861CoverageChecked

private noncomputable def leaf861InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453665/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf861InputLogOnePlusV_eq :
    leaf861InputLogOnePlusV = outerEnclosure 24
      (leaf861Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf861RoundedFacts : LeafRoundedFacts 8
    leaf861Certificate.logOnePlusV leaf861InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf861InputLogOnePlusV_eq }

private noncomputable def leaf861Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi43InputQChi innerPair144Input
    leaf861InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf861LowerChecked :
    lowerCheck 24 leaf861Box leaf861Inputs = true := by
  rfl'

private theorem leaf861CoversExact : CoversExact 8
    leaf861Box leaf861Certificate leaf861InnerLog leaf861Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi43RoundedFacts
    innerPair144RoundedFacts leaf861RoundedFacts (by rfl)

private theorem leaf861FlatSound : Sound leaf861Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf861CertificateValid
    leaf861InnerLogValid leaf861CoversExact leaf861LowerChecked

private noncomputable def leaf862Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf862Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (134217907/134217728) }, vSqrt := { lower := (65531/65536), upper := (4194308/4194187) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (189690387/134217728) }, upper := { exponent := 0, mantissa := (373/256) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (8388495/8388374) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf862InnerLog : WideLogData :=
  innerPair394Data

set_option maxRecDepth 1000000 in
private theorem leaf862LocalValidity :
    LeafFacts leaf862Box leaf862Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf862Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4194308/4194187) }) = true
      norm_num [leaf862Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf862CertificateValid :
    WideCertificateValid leaf862Box leaf862Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi43ValidityFacts
    leaf862LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf862CoverageChecked :
    coverageCheck (innerAD leaf862Box) leaf862InnerLog = true := by
  rfl'

private theorem leaf862InnerLogValid :
    leaf862InnerLog.Valid 8 (innerAD leaf862Box) :=
  wideLogDataValid_of_cachedCheck endpoint107PositiveFacts
    endpoint108PositiveFacts.valid leaf862CoverageChecked

private noncomputable def leaf862InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629323/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf862InputLogOnePlusV_eq :
    leaf862InputLogOnePlusV = outerEnclosure 24
      (leaf862Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf862RoundedFacts : LeafRoundedFacts 8
    leaf862Certificate.logOnePlusV leaf862InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf862InputLogOnePlusV_eq }

private noncomputable def leaf862Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi43InputQChi innerPair394Input
    leaf862InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf862LowerChecked :
    lowerCheck 24 leaf862Box leaf862Inputs = true := by
  rfl'

private theorem leaf862CoversExact : CoversExact 8
    leaf862Box leaf862Certificate leaf862InnerLog leaf862Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi43RoundedFacts
    innerPair394RoundedFacts leaf862RoundedFacts (by rfl)

private theorem leaf862FlatSound : Sound leaf862Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf862CertificateValid
    leaf862InnerLogValid leaf862CoversExact leaf862LowerChecked

private noncomputable def leaf863Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf863Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435655/268435456) }, vSqrt := { lower := (65531/65536), upper := (67108928/67107205) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (370632411/268435456) }, upper := { exponent := 0, mantissa := (5755/4096) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (134216133/134214410) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf863InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf863LocalValidity :
    LeafFacts leaf863Box leaf863Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf863Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (67108928/67107205) }) = true
      norm_num [leaf863Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf863CertificateValid :
    WideCertificateValid leaf863Box leaf863Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi111ValidityFacts
    leaf863LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf863CoverageChecked :
    coverageCheck (innerAD leaf863Box) leaf863InnerLog = true := by
  rfl'

private theorem leaf863InnerLogValid :
    leaf863InnerLog.Valid 8 (innerAD leaf863Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf863CoverageChecked

private noncomputable def leaf863InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf863InputLogOnePlusV_eq :
    leaf863InputLogOnePlusV = outerEnclosure 24
      (leaf863Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf863RoundedFacts : LeafRoundedFacts 8
    leaf863Certificate.logOnePlusV leaf863InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf863InputLogOnePlusV_eq }

private noncomputable def leaf863Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi111InputQChi innerPair26Input
    leaf863InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf863LowerChecked :
    lowerCheck 24 leaf863Box leaf863Inputs = true := by
  rfl'

private theorem leaf863CoversExact : CoversExact 8
    leaf863Box leaf863Certificate leaf863InnerLog leaf863Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi111RoundedFacts
    innerPair26RoundedFacts leaf863RoundedFacts (by rfl)

private theorem leaf863FlatSound : Sound leaf863Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf863CertificateValid
    leaf863InnerLogValid leaf863CoversExact leaf863LowerChecked

private noncomputable def leaf864Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf864Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435657/268435456) }, vSqrt := { lower := (32765/32768), upper := (4194308/4194199) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (371943049/268435456) }, upper := { exponent := 0, mantissa := (361/256) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8388507/8388398) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf864InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf864LocalValidity :
    LeafFacts leaf864Box leaf864Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf864Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4194308/4194199) }) = true
      norm_num [leaf864Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf864CertificateValid :
    WideCertificateValid leaf864Box leaf864Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi111ValidityFacts
    leaf864LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf864CoverageChecked :
    coverageCheck (innerAD leaf864Box) leaf864InnerLog = true := by
  rfl'

private theorem leaf864InnerLogValid :
    leaf864InnerLog.Valid 8 (innerAD leaf864Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf864CoverageChecked

private noncomputable def leaf864InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf864InputLogOnePlusV_eq :
    leaf864InputLogOnePlusV = outerEnclosure 24
      (leaf864Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf864RoundedFacts : LeafRoundedFacts 8
    leaf864Certificate.logOnePlusV leaf864InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf864InputLogOnePlusV_eq }

private noncomputable def leaf864Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi111InputQChi innerPair26Input
    leaf864InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf864LowerChecked :
    lowerCheck 24 leaf864Box leaf864Inputs = true := by
  rfl'

private theorem leaf864CoversExact : CoversExact 8
    leaf864Box leaf864Certificate leaf864InnerLog leaf864Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi111RoundedFacts
    innerPair26RoundedFacts leaf864RoundedFacts (by rfl)

private theorem leaf864FlatSound : Sound leaf864Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf864CertificateValid
    leaf864InnerLogValid leaf864CoversExact leaf864LowerChecked

private noncomputable def leaf865Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf865Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435657/268435456) }, vSqrt := { lower := (65531/65536), upper := (1973792/1973739) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (375743905/268435456) }, upper := { exponent := 0, mantissa := (2917/2048) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (3947531/3947478) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf865InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf865LocalValidity :
    LeafFacts leaf865Box leaf865Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf865Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (1973792/1973739) }) = true
      norm_num [leaf865Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf865CertificateValid :
    WideCertificateValid leaf865Box leaf865Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi112ValidityFacts
    leaf865LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf865CoverageChecked :
    coverageCheck (innerAD leaf865Box) leaf865InnerLog = true := by
  rfl'

private theorem leaf865InnerLogValid :
    leaf865InnerLog.Valid 8 (innerAD leaf865Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf865CoverageChecked

private noncomputable def leaf865InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf865InputLogOnePlusV_eq :
    leaf865InputLogOnePlusV = outerEnclosure 24
      (leaf865Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf865RoundedFacts : LeafRoundedFacts 8
    leaf865Certificate.logOnePlusV leaf865InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf865InputLogOnePlusV_eq }

private noncomputable def leaf865Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi112InputQChi innerPair26Input
    leaf865InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf865LowerChecked :
    lowerCheck 24 leaf865Box leaf865Inputs = true := by
  rfl'

private theorem leaf865CoversExact : CoversExact 8
    leaf865Box leaf865Certificate leaf865InnerLog leaf865Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi112RoundedFacts
    innerPair26RoundedFacts leaf865RoundedFacts (by rfl)

private theorem leaf865FlatSound : Sound leaf865Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf865CertificateValid
    leaf865InnerLogValid leaf865CoversExact leaf865LowerChecked

private noncomputable def leaf866Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf866Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435659/268435456) }, vSqrt := { lower := (32765/32768), upper := (2097154/2097097) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (377120075/268435456) }, upper := { exponent := 0, mantissa := (183/128) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (4194251/4194194) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf866InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf866LocalValidity :
    LeafFacts leaf866Box leaf866Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf866Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (2097154/2097097) }) = true
      norm_num [leaf866Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf866CertificateValid :
    WideCertificateValid leaf866Box leaf866Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi112ValidityFacts
    leaf866LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf866CoverageChecked :
    coverageCheck (innerAD leaf866Box) leaf866InnerLog = true := by
  rfl'

private theorem leaf866InnerLogValid :
    leaf866InnerLog.Valid 8 (innerAD leaf866Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf866CoverageChecked

private noncomputable def leaf866InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf866InputLogOnePlusV_eq :
    leaf866InputLogOnePlusV = outerEnclosure 24
      (leaf866Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf866RoundedFacts : LeafRoundedFacts 8
    leaf866Certificate.logOnePlusV leaf866InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf866InputLogOnePlusV_eq }

private noncomputable def leaf866Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi112InputQChi innerPair26Input
    leaf866InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf866LowerChecked :
    lowerCheck 24 leaf866Box leaf866Inputs = true := by
  rfl'

private theorem leaf866CoversExact : CoversExact 8
    leaf866Box leaf866Certificate leaf866InnerLog leaf866Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi112RoundedFacts
    innerPair26RoundedFacts leaf866RoundedFacts (by rfl)

private theorem leaf866FlatSound : Sound leaf866Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf866CertificateValid
    leaf866InnerLogValid leaf866CoversExact leaf866LowerChecked

private noncomputable def leaf867Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (11/64), chiHi := (23/128) }

private noncomputable def leaf867Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435659/268435456) }, vSqrt := { lower := (65531/65536), upper := (67108928/67107047) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (380855399/268435456) }, upper := { exponent := 0, mantissa := (5913/4096) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi113LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (134215975/134214094) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf867InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf867LocalValidity :
    LeafFacts leaf867Box leaf867Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf867Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (67108928/67107047) }) = true
      norm_num [leaf867Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf867CertificateValid :
    WideCertificateValid leaf867Box leaf867Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi113ValidityFacts
    leaf867LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf867CoverageChecked :
    coverageCheck (innerAD leaf867Box) leaf867InnerLog = true := by
  rfl'

private theorem leaf867InnerLogValid :
    leaf867InnerLog.Valid 8 (innerAD leaf867Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf867CoverageChecked

private noncomputable def leaf867InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907329/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf867InputLogOnePlusV_eq :
    leaf867InputLogOnePlusV = outerEnclosure 24
      (leaf867Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf867RoundedFacts : LeafRoundedFacts 8
    leaf867Certificate.logOnePlusV leaf867InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf867InputLogOnePlusV_eq }

private noncomputable def leaf867Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi113InputQChi innerPair27Input
    leaf867InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf867LowerChecked :
    lowerCheck 24 leaf867Box leaf867Inputs = true := by
  rfl'

private theorem leaf867CoversExact : CoversExact 8
    leaf867Box leaf867Certificate leaf867InnerLog leaf867Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi113RoundedFacts
    innerPair27RoundedFacts leaf867RoundedFacts (by rfl)

private theorem leaf867FlatSound : Sound leaf867Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf867CertificateValid
    leaf867InnerLogValid leaf867CoversExact leaf867LowerChecked

private noncomputable def leaf868Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (23/128), chiHi := (3/16) }

private noncomputable def leaf868Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435661/268435456) }, vSqrt := { lower := (65531/65536), upper := (8388616/8388371) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (385966893/268435456) }, upper := { exponent := 0, mantissa := (749/512) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi114LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (16776987/16776742) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf868InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf868LocalValidity :
    LeafFacts leaf868Box leaf868Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf868Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (8388616/8388371) }) = true
      norm_num [leaf868Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf868CertificateValid :
    WideCertificateValid leaf868Box leaf868Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi114ValidityFacts
    leaf868LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf868CoverageChecked :
    coverageCheck (innerAD leaf868Box) leaf868InnerLog = true := by
  rfl'

private theorem leaf868InnerLogValid :
    leaf868InnerLog.Valid 8 (innerAD leaf868Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf868CoverageChecked

private noncomputable def leaf868InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf868InputLogOnePlusV_eq :
    leaf868InputLogOnePlusV = outerEnclosure 24
      (leaf868Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf868RoundedFacts : LeafRoundedFacts 8
    leaf868Certificate.logOnePlusV leaf868InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf868InputLogOnePlusV_eq }

private noncomputable def leaf868Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi114InputQChi innerPair34Input
    leaf868InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf868LowerChecked :
    lowerCheck 24 leaf868Box leaf868Inputs = true := by
  rfl'

private theorem leaf868CoversExact : CoversExact 8
    leaf868Box leaf868Certificate leaf868InnerLog leaf868Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi114RoundedFacts
    innerPair34RoundedFacts leaf868RoundedFacts (by rfl)

private theorem leaf868FlatSound : Sound leaf868Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf868CertificateValid
    leaf868InnerLogValid leaf868CoversExact leaf868LowerChecked

private noncomputable def leaf869Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (11/64), chiHi := (23/128) }

private noncomputable def leaf869Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435661/268435456) }, vSqrt := { lower := (32765/32768), upper := (246724/246717) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (382297101/268435456) }, upper := { exponent := 0, mantissa := (371/256) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi113LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (493441/493434) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf869InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf869LocalValidity :
    LeafFacts leaf869Box leaf869Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf869Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (246724/246717) }) = true
      norm_num [leaf869Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf869CertificateValid :
    WideCertificateValid leaf869Box leaf869Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi113ValidityFacts
    leaf869LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf869CoverageChecked :
    coverageCheck (innerAD leaf869Box) leaf869InnerLog = true := by
  rfl'

private theorem leaf869InnerLogValid :
    leaf869InnerLog.Valid 8 (innerAD leaf869Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf869CoverageChecked

private noncomputable def leaf869InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629319/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf869InputLogOnePlusV_eq :
    leaf869InputLogOnePlusV = outerEnclosure 24
      (leaf869Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf869RoundedFacts : LeafRoundedFacts 8
    leaf869Certificate.logOnePlusV leaf869InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf869InputLogOnePlusV_eq }

private noncomputable def leaf869Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi113InputQChi innerPair27Input
    leaf869InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf869LowerChecked :
    lowerCheck 24 leaf869Box leaf869Inputs = true := by
  rfl'

private theorem leaf869CoversExact : CoversExact 8
    leaf869Box leaf869Certificate leaf869InnerLog leaf869Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi113RoundedFacts
    innerPair27RoundedFacts leaf869RoundedFacts (by rfl)

private theorem leaf869FlatSound : Sound leaf869Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf869CertificateValid
    leaf869InnerLogValid leaf869CoversExact leaf869LowerChecked

private noncomputable def leaf870Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (23/128), chiHi := (3/16) }

private noncomputable def leaf870Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435663/268435456) }, vSqrt := { lower := (32765/32768), upper := (1048577/1048546) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (387474127/268435456) }, upper := { exponent := 0, mantissa := (47/32) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi114LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2097123/2097092) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf870InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf870LocalValidity :
    LeafFacts leaf870Box leaf870Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf870Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1048577/1048546) }) = true
      norm_num [leaf870Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf870CertificateValid :
    WideCertificateValid leaf870Box leaf870Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi114ValidityFacts
    leaf870LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf870CoverageChecked :
    coverageCheck (innerAD leaf870Box) leaf870InnerLog = true := by
  rfl'

private theorem leaf870InnerLogValid :
    leaf870InnerLog.Valid 8 (innerAD leaf870Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf870CoverageChecked

private noncomputable def leaf870InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf870InputLogOnePlusV_eq :
    leaf870InputLogOnePlusV = outerEnclosure 24
      (leaf870Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf870RoundedFacts : LeafRoundedFacts 8
    leaf870Certificate.logOnePlusV leaf870InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf870InputLogOnePlusV_eq }

private noncomputable def leaf870Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi114InputQChi innerPair34Input
    leaf870InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf870LowerChecked :
    lowerCheck 24 leaf870Box leaf870Inputs = true := by
  rfl'

private theorem leaf870CoversExact : CoversExact 8
    leaf870Box leaf870Certificate leaf870InnerLog leaf870Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi114RoundedFacts
    innerPair34RoundedFacts leaf870RoundedFacts (by rfl)

private theorem leaf870FlatSound : Sound leaf870Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf870CertificateValid
    leaf870InnerLogValid leaf870CoversExact leaf870LowerChecked

private noncomputable def component20Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component20Node0_sound : Sound component20Node0Box :=
  sound_of_literal_split component20Node0Box leaf825Box leaf826Box
    .chi (17/128) (by rfl) (by rfl)
    leaf825FlatSound leaf826FlatSound

private noncomputable def component20Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component20Node1_sound : Sound component20Node1Box :=
  sound_of_literal_split component20Node1Box leaf827Box leaf828Box
    .chi (17/128) (by rfl) (by rfl)
    leaf827FlatSound leaf828FlatSound

private noncomputable def component20Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component20Node2_sound : Sound component20Node2Box :=
  sound_of_literal_split component20Node2Box component20Node0Box component20Node1Box
    .k (37/16) (by rfl) (by rfl)
    component20Node0_sound component20Node1_sound

private noncomputable def component20Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component20Node3_sound : Sound component20Node3Box :=
  sound_of_literal_split component20Node3Box leaf829Box leaf830Box
    .chi (19/128) (by rfl) (by rfl)
    leaf829FlatSound leaf830FlatSound

private noncomputable def component20Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component20Node4_sound : Sound component20Node4Box :=
  sound_of_literal_split component20Node4Box leaf832Box leaf833Box
    .k (75/32) (by rfl) (by rfl)
    leaf832FlatSound leaf833FlatSound

private noncomputable def component20Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component20Node5_sound : Sound component20Node5Box :=
  sound_of_literal_split component20Node5Box leaf831Box component20Node4Box
    .chi (19/128) (by rfl) (by rfl)
    leaf831FlatSound component20Node4_sound

private noncomputable def component20Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component20Node6_sound : Sound component20Node6Box :=
  sound_of_literal_split component20Node6Box component20Node3Box component20Node5Box
    .k (37/16) (by rfl) (by rfl)
    component20Node3_sound component20Node5_sound

private noncomputable def component20Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component20Node7_sound : Sound component20Node7Box :=
  sound_of_literal_split component20Node7Box component20Node2Box component20Node6Box
    .chi (9/64) (by rfl) (by rfl)
    component20Node2_sound component20Node6_sound

private noncomputable def component20Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component20Node8_sound : Sound component20Node8Box :=
  sound_of_literal_split component20Node8Box leaf835Box leaf836Box
    .k (77/32) (by rfl) (by rfl)
    leaf835FlatSound leaf836FlatSound

private noncomputable def component20Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component20Node9_sound : Sound component20Node9Box :=
  sound_of_literal_split component20Node9Box leaf834Box component20Node8Box
    .chi (17/128) (by rfl) (by rfl)
    leaf834FlatSound component20Node8_sound

private noncomputable def component20Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (1/8), chiHi := (17/128) }

set_option maxRecDepth 1000000 in
private theorem component20Node10_sound : Sound component20Node10Box :=
  sound_of_literal_split component20Node10Box leaf837Box leaf838Box
    .k (79/32) (by rfl) (by rfl)
    leaf837FlatSound leaf838FlatSound

private noncomputable def component20Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (17/128), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component20Node11_sound : Sound component20Node11Box :=
  sound_of_literal_split component20Node11Box leaf839Box leaf840Box
    .k (79/32) (by rfl) (by rfl)
    leaf839FlatSound leaf840FlatSound

private noncomputable def component20Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component20Node12_sound : Sound component20Node12Box :=
  sound_of_literal_split component20Node12Box component20Node10Box component20Node11Box
    .chi (17/128) (by rfl) (by rfl)
    component20Node10_sound component20Node11_sound

private noncomputable def component20Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (1/8), chiHi := (9/64) }

set_option maxRecDepth 1000000 in
private theorem component20Node13_sound : Sound component20Node13Box :=
  sound_of_literal_split component20Node13Box component20Node9Box component20Node12Box
    .k (39/16) (by rfl) (by rfl)
    component20Node9_sound component20Node12_sound

private noncomputable def component20Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component20Node14_sound : Sound component20Node14Box :=
  sound_of_literal_split component20Node14Box leaf841Box leaf842Box
    .k (77/32) (by rfl) (by rfl)
    leaf841FlatSound leaf842FlatSound

private noncomputable def component20Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component20Node15_sound : Sound component20Node15Box :=
  sound_of_literal_split component20Node15Box leaf843Box leaf844Box
    .k (77/32) (by rfl) (by rfl)
    leaf843FlatSound leaf844FlatSound

private noncomputable def component20Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component20Node16_sound : Sound component20Node16Box :=
  sound_of_literal_split component20Node16Box component20Node14Box component20Node15Box
    .chi (19/128) (by rfl) (by rfl)
    component20Node14_sound component20Node15_sound

private noncomputable def component20Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component20Node17_sound : Sound component20Node17Box :=
  sound_of_literal_split component20Node17Box leaf845Box leaf846Box
    .k (79/32) (by rfl) (by rfl)
    leaf845FlatSound leaf846FlatSound

private noncomputable def component20Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component20Node18_sound : Sound component20Node18Box :=
  sound_of_literal_split component20Node18Box leaf847Box leaf848Box
    .k (79/32) (by rfl) (by rfl)
    leaf847FlatSound leaf848FlatSound

private noncomputable def component20Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component20Node19_sound : Sound component20Node19Box :=
  sound_of_literal_split component20Node19Box component20Node17Box component20Node18Box
    .chi (19/128) (by rfl) (by rfl)
    component20Node17_sound component20Node18_sound

private noncomputable def component20Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component20Node20_sound : Sound component20Node20Box :=
  sound_of_literal_split component20Node20Box component20Node16Box component20Node19Box
    .k (39/16) (by rfl) (by rfl)
    component20Node16_sound component20Node19_sound

private noncomputable def component20Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component20Node21_sound : Sound component20Node21Box :=
  sound_of_literal_split component20Node21Box component20Node13Box component20Node20Box
    .chi (9/64) (by rfl) (by rfl)
    component20Node13_sound component20Node20_sound

private noncomputable def component20Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component20Node22_sound : Sound component20Node22Box :=
  sound_of_literal_split component20Node22Box component20Node7Box component20Node21Box
    .k (19/8) (by rfl) (by rfl)
    component20Node7_sound component20Node21_sound

private noncomputable def component20Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component20Node23_sound : Sound component20Node23Box :=
  sound_of_literal_split component20Node23Box leaf849Box leaf850Box
    .k (73/32) (by rfl) (by rfl)
    leaf849FlatSound leaf850FlatSound

private noncomputable def component20Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component20Node24_sound : Sound component20Node24Box :=
  sound_of_literal_split component20Node24Box leaf851Box leaf852Box
    .k (73/32) (by rfl) (by rfl)
    leaf851FlatSound leaf852FlatSound

private noncomputable def component20Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component20Node25_sound : Sound component20Node25Box :=
  sound_of_literal_split component20Node25Box component20Node23Box component20Node24Box
    .chi (11/64) (by rfl) (by rfl)
    component20Node23_sound component20Node24_sound

private noncomputable def component20Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component20Node26_sound : Sound component20Node26Box :=
  sound_of_literal_split component20Node26Box leaf853Box leaf854Box
    .k (75/32) (by rfl) (by rfl)
    leaf853FlatSound leaf854FlatSound

private noncomputable def component20Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component20Node27_sound : Sound component20Node27Box :=
  sound_of_literal_split component20Node27Box leaf855Box leaf856Box
    .k (75/32) (by rfl) (by rfl)
    leaf855FlatSound leaf856FlatSound

private noncomputable def component20Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component20Node28_sound : Sound component20Node28Box :=
  sound_of_literal_split component20Node28Box component20Node26Box component20Node27Box
    .chi (11/64) (by rfl) (by rfl)
    component20Node26_sound component20Node27_sound

private noncomputable def component20Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component20Node29_sound : Sound component20Node29Box :=
  sound_of_literal_split component20Node29Box component20Node25Box component20Node28Box
    .k (37/16) (by rfl) (by rfl)
    component20Node25_sound component20Node28_sound

private noncomputable def component20Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component20Node30_sound : Sound component20Node30Box :=
  sound_of_literal_split component20Node30Box leaf857Box leaf858Box
    .k (77/32) (by rfl) (by rfl)
    leaf857FlatSound leaf858FlatSound

private noncomputable def component20Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component20Node31_sound : Sound component20Node31Box :=
  sound_of_literal_split component20Node31Box leaf859Box leaf860Box
    .k (77/32) (by rfl) (by rfl)
    leaf859FlatSound leaf860FlatSound

private noncomputable def component20Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component20Node32_sound : Sound component20Node32Box :=
  sound_of_literal_split component20Node32Box component20Node30Box component20Node31Box
    .chi (21/128) (by rfl) (by rfl)
    component20Node30_sound component20Node31_sound

private noncomputable def component20Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component20Node33_sound : Sound component20Node33Box :=
  sound_of_literal_split component20Node33Box leaf861Box leaf862Box
    .k (77/32) (by rfl) (by rfl)
    leaf861FlatSound leaf862FlatSound

private noncomputable def component20Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component20Node34_sound : Sound component20Node34Box :=
  sound_of_literal_split component20Node34Box component20Node32Box component20Node33Box
    .chi (11/64) (by rfl) (by rfl)
    component20Node32_sound component20Node33_sound

private noncomputable def component20Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component20Node35_sound : Sound component20Node35Box :=
  sound_of_literal_split component20Node35Box leaf863Box leaf864Box
    .k (79/32) (by rfl) (by rfl)
    leaf863FlatSound leaf864FlatSound

private noncomputable def component20Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component20Node36_sound : Sound component20Node36Box :=
  sound_of_literal_split component20Node36Box leaf865Box leaf866Box
    .k (79/32) (by rfl) (by rfl)
    leaf865FlatSound leaf866FlatSound

private noncomputable def component20Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component20Node37_sound : Sound component20Node37Box :=
  sound_of_literal_split component20Node37Box component20Node35Box component20Node36Box
    .chi (21/128) (by rfl) (by rfl)
    component20Node35_sound component20Node36_sound

private noncomputable def component20Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component20Node38_sound : Sound component20Node38Box :=
  sound_of_literal_split component20Node38Box leaf867Box leaf868Box
    .chi (23/128) (by rfl) (by rfl)
    leaf867FlatSound leaf868FlatSound

private noncomputable def component20Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component20Node39_sound : Sound component20Node39Box :=
  sound_of_literal_split component20Node39Box leaf869Box leaf870Box
    .chi (23/128) (by rfl) (by rfl)
    leaf869FlatSound leaf870FlatSound

private noncomputable def component20Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component20Node40_sound : Sound component20Node40Box :=
  sound_of_literal_split component20Node40Box component20Node38Box component20Node39Box
    .k (79/32) (by rfl) (by rfl)
    component20Node38_sound component20Node39_sound

private noncomputable def component20Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component20Node41_sound : Sound component20Node41Box :=
  sound_of_literal_split component20Node41Box component20Node37Box component20Node40Box
    .chi (11/64) (by rfl) (by rfl)
    component20Node37_sound component20Node40_sound

private noncomputable def component20Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component20Node42_sound : Sound component20Node42Box :=
  sound_of_literal_split component20Node42Box component20Node34Box component20Node41Box
    .k (39/16) (by rfl) (by rfl)
    component20Node34_sound component20Node41_sound

private noncomputable def component20Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component20Node43_sound : Sound component20Node43Box :=
  sound_of_literal_split component20Node43Box component20Node29Box component20Node42Box
    .k (19/8) (by rfl) (by rfl)
    component20Node29_sound component20Node42_sound

noncomputable def component20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
theorem component20_sound : Sound component20Box :=
  sound_of_literal_split component20Box component20Node22Box component20Node43Box
    .chi (5/32) (by rfl) (by rfl)
    component20Node22_sound component20Node43_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
