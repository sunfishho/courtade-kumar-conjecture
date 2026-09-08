import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch7
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

private noncomputable def leaf3910Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf3910Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435699/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716076032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (478104847/268435456) }, upper := { exponent := 0, mantissa := (7417/4096) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434569727/137432152064) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf3910InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3910LocalValidity :
    LeafFacts leaf3910Box leaf3910Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3910Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716076032) }) = true
      norm_num [leaf3910Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3910CertificateValid :
    WideCertificateValid leaf3910Box leaf3910Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi249ValidityFacts
    leaf3910LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3910CoverageChecked :
    coverageCheck (innerAD leaf3910Box) leaf3910InnerLog = true := by
  rfl'

private theorem leaf3910InnerLogValid :
    leaf3910InnerLog.Valid 8 (innerAD leaf3910Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3910CoverageChecked

private noncomputable def leaf3910InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (181709/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf3910InputLogOnePlusV_eq :
    leaf3910InputLogOnePlusV = outerEnclosure 24
      (leaf3910Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3910RoundedFacts : LeafRoundedFacts 8
    leaf3910Certificate.logOnePlusV leaf3910InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3910InputLogOnePlusV_eq }

private noncomputable def leaf3910Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi249InputQChi innerPair71Input
    leaf3910InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3910LowerChecked :
    lowerCheck 24 leaf3910Box leaf3910Inputs = true := by
  rfl'

private theorem leaf3910CoversExact : CoversExact 8
    leaf3910Box leaf3910Certificate leaf3910InnerLog leaf3910Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi249RoundedFacts
    innerPair71RoundedFacts leaf3910RoundedFacts (by rfl)

private theorem leaf3910FlatSound : Sound leaf3910Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3910CertificateValid
    leaf3910InnerLogValid leaf3910CoversExact leaf3910LowerChecked

private noncomputable def leaf3911Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf3911Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435701/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715993088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (483347405/268435456) }, upper := { exponent := 0, mantissa := (3749/2048) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434486783/137431986176) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf3911InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3911LocalValidity :
    LeafFacts leaf3911Box leaf3911Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3911Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715993088) }) = true
      norm_num [leaf3911Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3911CertificateValid :
    WideCertificateValid leaf3911Box leaf3911Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi250ValidityFacts
    leaf3911LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3911CoverageChecked :
    coverageCheck (innerAD leaf3911Box) leaf3911InnerLog = true := by
  rfl'

private theorem leaf3911InnerLogValid :
    leaf3911InnerLog.Valid 8 (innerAD leaf3911Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3911CoverageChecked

private noncomputable def leaf3911InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3911InputLogOnePlusV_eq :
    leaf3911InputLogOnePlusV = outerEnclosure 24
      (leaf3911Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3911RoundedFacts : LeafRoundedFacts 8
    leaf3911Certificate.logOnePlusV leaf3911InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3911InputLogOnePlusV_eq }

private noncomputable def leaf3911Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi250InputQChi innerPair72Input
    leaf3911InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3911LowerChecked :
    lowerCheck 24 leaf3911Box leaf3911Inputs = true := by
  rfl'

private theorem leaf3911CoversExact : CoversExact 8
    leaf3911Box leaf3911Certificate leaf3911InnerLog leaf3911Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi250RoundedFacts
    innerPair72RoundedFacts leaf3911RoundedFacts (by rfl)

private theorem leaf3911FlatSound : Sound leaf3911Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3911CertificateValid
    leaf3911InnerLogValid leaf3911CoversExact leaf3911LowerChecked

private noncomputable def leaf3912Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf3912Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435701/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716034048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (480726125/268435456) }, upper := { exponent := 0, mantissa := (3729/2048) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434527743/137432068096) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf3912InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3912LocalValidity :
    LeafFacts leaf3912Box leaf3912Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3912Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716034048) }) = true
      norm_num [leaf3912Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3912CertificateValid :
    WideCertificateValid leaf3912Box leaf3912Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi249ValidityFacts
    leaf3912LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3912CoverageChecked :
    coverageCheck (innerAD leaf3912Box) leaf3912InnerLog = true := by
  rfl'

private theorem leaf3912InnerLogValid :
    leaf3912InnerLog.Valid 8 (innerAD leaf3912Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3912CoverageChecked

private noncomputable def leaf3912InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3912InputLogOnePlusV_eq :
    leaf3912InputLogOnePlusV = outerEnclosure 24
      (leaf3912Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3912RoundedFacts : LeafRoundedFacts 8
    leaf3912Certificate.logOnePlusV leaf3912InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3912InputLogOnePlusV_eq }

private noncomputable def leaf3912Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi249InputQChi innerPair72Input
    leaf3912InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3912LowerChecked :
    lowerCheck 24 leaf3912Box leaf3912Inputs = true := by
  rfl'

private theorem leaf3912CoversExact : CoversExact 8
    leaf3912Box leaf3912Certificate leaf3912InnerLog leaf3912Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi249RoundedFacts
    innerPair72RoundedFacts leaf3912RoundedFacts (by rfl)

private theorem leaf3912FlatSound : Sound leaf3912Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3912CertificateValid
    leaf3912InnerLogValid leaf3912CoversExact leaf3912LowerChecked

private noncomputable def leaf3913Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf3913Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435703/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743190016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (486034215/268435456) }, upper := { exponent := 0, mantissa := (1885/1024) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486888755/27486380032) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf3913InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3913LocalValidity :
    LeafFacts leaf3913Box leaf3913Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3913Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743190016) }) = true
      norm_num [leaf3913Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3913CertificateValid :
    WideCertificateValid leaf3913Box leaf3913Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi250ValidityFacts
    leaf3913LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3913CoverageChecked :
    coverageCheck (innerAD leaf3913Box) leaf3913InnerLog = true := by
  rfl'

private theorem leaf3913InnerLogValid :
    leaf3913InnerLog.Valid 8 (innerAD leaf3913Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3913CoverageChecked

private noncomputable def leaf3913InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3913InputLogOnePlusV_eq :
    leaf3913InputLogOnePlusV = outerEnclosure 24
      (leaf3913Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3913RoundedFacts : LeafRoundedFacts 8
    leaf3913Certificate.logOnePlusV leaf3913InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3913InputLogOnePlusV_eq }

private noncomputable def leaf3913Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi250InputQChi innerPair72Input
    leaf3913InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3913LowerChecked :
    lowerCheck 24 leaf3913Box leaf3913Inputs = true := by
  rfl'

private theorem leaf3913CoversExact : CoversExact 8
    leaf3913Box leaf3913Certificate leaf3913InnerLog leaf3913Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi250RoundedFacts
    innerPair72RoundedFacts leaf3913RoundedFacts (by rfl)

private theorem leaf3913FlatSound : Sound leaf3913Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3913CertificateValid
    leaf3913InnerLogValid leaf3913CoversExact leaf3913LowerChecked

private noncomputable def leaf3914Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3914Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217933/134217728) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743165440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (244278517/134217728) }, upper := { exponent := 0, mantissa := (1915/1024) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486864179/27486330880) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf3914InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3914LocalValidity :
    LeafFacts leaf3914Box leaf3914Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3914Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743165440) }) = true
      norm_num [leaf3914Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3914CertificateValid :
    WideCertificateValid leaf3914Box leaf3914Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi59ValidityFacts
    leaf3914LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3914CoverageChecked :
    coverageCheck (innerAD leaf3914Box) leaf3914InnerLog = true := by
  rfl'

private theorem leaf3914InnerLogValid :
    leaf3914InnerLog.Valid 8 (innerAD leaf3914Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3914CoverageChecked

private noncomputable def leaf3914InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3914InputLogOnePlusV_eq :
    leaf3914InputLogOnePlusV = outerEnclosure 24
      (leaf3914Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3914RoundedFacts : LeafRoundedFacts 8
    leaf3914Certificate.logOnePlusV leaf3914InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3914InputLogOnePlusV_eq }

private noncomputable def leaf3914Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi59InputQChi innerPair91Input
    leaf3914InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3914LowerChecked :
    lowerCheck 24 leaf3914Box leaf3914Inputs = true := by
  rfl'

private theorem leaf3914CoversExact : CoversExact 8
    leaf3914Box leaf3914Certificate leaf3914InnerLog leaf3914Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi59RoundedFacts
    innerPair91RoundedFacts leaf3914RoundedFacts (by rfl)

private theorem leaf3914FlatSound : Sound leaf3914Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3914CertificateValid
    leaf3914InnerLogValid leaf3914CoversExact leaf3914LowerChecked

private noncomputable def leaf3915Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3915Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217935/134217728) }, vSqrt := { lower := (32765/32768), upper := (4042264335/4042104832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (245654687/134217728) }, upper := { exponent := 0, mantissa := (963/512) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8084369167/8084209664) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf3915InnerLog : WideLogData :=
  innerPair216Data

set_option maxRecDepth 1000000 in
private theorem leaf3915LocalValidity :
    LeafFacts leaf3915Box leaf3915Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3915Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4042264335/4042104832) }) = true
      norm_num [leaf3915Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3915CertificateValid :
    WideCertificateValid leaf3915Box leaf3915Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi59ValidityFacts
    leaf3915LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3915CoverageChecked :
    coverageCheck (innerAD leaf3915Box) leaf3915InnerLog = true := by
  rfl'

private theorem leaf3915InnerLogValid :
    leaf3915InnerLog.Valid 8 (innerAD leaf3915Box) :=
  wideLogDataValid_of_cachedCheck endpoint64PositiveFacts
    endpoint252PositiveFacts.valid leaf3915CoverageChecked

private noncomputable def leaf3915InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3915InputLogOnePlusV_eq :
    leaf3915InputLogOnePlusV = outerEnclosure 24
      (leaf3915Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3915RoundedFacts : LeafRoundedFacts 8
    leaf3915Certificate.logOnePlusV leaf3915InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3915InputLogOnePlusV_eq }

private noncomputable def leaf3915Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi59InputQChi innerPair216Input
    leaf3915InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3915LowerChecked :
    lowerCheck 24 leaf3915Box leaf3915Inputs = true := by
  rfl'

private theorem leaf3915CoversExact : CoversExact 8
    leaf3915Box leaf3915Certificate leaf3915InnerLog leaf3915Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi59RoundedFacts
    innerPair216RoundedFacts leaf3915RoundedFacts (by rfl)

private theorem leaf3915FlatSound : Sound leaf3915Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3915CertificateValid
    leaf3915InnerLogValid leaf3915CoversExact leaf3915LowerChecked

private noncomputable def leaf3916Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf3916Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435703/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905330688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (483347403/268435456) }, upper := { exponent := 0, mantissa := (7499/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811495253/45810661376) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf3916InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3916LocalValidity :
    LeafFacts leaf3916Box leaf3916Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3916Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905330688) }) = true
      norm_num [leaf3916Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3916CertificateValid :
    WideCertificateValid leaf3916Box leaf3916Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi249ValidityFacts
    leaf3916LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3916CoverageChecked :
    coverageCheck (innerAD leaf3916Box) leaf3916InnerLog = true := by
  rfl'

private theorem leaf3916InnerLogValid :
    leaf3916InnerLog.Valid 8 (innerAD leaf3916Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3916CoverageChecked

private noncomputable def leaf3916InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3916InputLogOnePlusV_eq :
    leaf3916InputLogOnePlusV = outerEnclosure 24
      (leaf3916Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3916RoundedFacts : LeafRoundedFacts 8
    leaf3916Certificate.logOnePlusV leaf3916InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3916InputLogOnePlusV_eq }

private noncomputable def leaf3916Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi249InputQChi innerPair72Input
    leaf3916InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3916LowerChecked :
    lowerCheck 24 leaf3916Box leaf3916Inputs = true := by
  rfl'

private theorem leaf3916CoversExact : CoversExact 8
    leaf3916Box leaf3916Certificate leaf3916InnerLog leaf3916Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi249RoundedFacts
    innerPair72RoundedFacts leaf3916RoundedFacts (by rfl)

private theorem leaf3916FlatSound : Sound leaf3916Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3916CertificateValid
    leaf3916InnerLogValid leaf3916CoversExact leaf3916LowerChecked

private noncomputable def leaf3917Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf3917Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435705/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715907072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (488721025/268435456) }, upper := { exponent := 0, mantissa := (3791/2048) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434400767/137431814144) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf3917InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3917LocalValidity :
    LeafFacts leaf3917Box leaf3917Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3917Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715907072) }) = true
      norm_num [leaf3917Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3917CertificateValid :
    WideCertificateValid leaf3917Box leaf3917Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi250ValidityFacts
    leaf3917LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3917CoverageChecked :
    coverageCheck (innerAD leaf3917Box) leaf3917InnerLog = true := by
  rfl'

private theorem leaf3917InnerLogValid :
    leaf3917InnerLog.Valid 8 (innerAD leaf3917Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3917CoverageChecked

private noncomputable def leaf3917InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3917InputLogOnePlusV_eq :
    leaf3917InputLogOnePlusV = outerEnclosure 24
      (leaf3917Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3917RoundedFacts : LeafRoundedFacts 8
    leaf3917Certificate.logOnePlusV leaf3917InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3917InputLogOnePlusV_eq }

private noncomputable def leaf3917Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi250InputQChi innerPair91Input
    leaf3917InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3917LowerChecked :
    lowerCheck 24 leaf3917Box leaf3917Inputs = true := by
  rfl'

private theorem leaf3917CoversExact : CoversExact 8
    leaf3917Box leaf3917Certificate leaf3917InnerLog leaf3917Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi250RoundedFacts
    innerPair91RoundedFacts leaf3917RoundedFacts (by rfl)

private theorem leaf3917FlatSound : Sound leaf3917Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3917CertificateValid
    leaf3917InnerLogValid leaf3917CoversExact leaf3917LowerChecked

private noncomputable def leaf3918Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf3918Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435705/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743190016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (485968681/268435456) }, upper := { exponent := 0, mantissa := (1885/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486888755/27486380032) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf3918InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3918LocalValidity :
    LeafFacts leaf3918Box leaf3918Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3918Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743190016) }) = true
      norm_num [leaf3918Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3918CertificateValid :
    WideCertificateValid leaf3918Box leaf3918Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi249ValidityFacts
    leaf3918LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3918CoverageChecked :
    coverageCheck (innerAD leaf3918Box) leaf3918InnerLog = true := by
  rfl'

private theorem leaf3918InnerLogValid :
    leaf3918InnerLog.Valid 8 (innerAD leaf3918Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3918CoverageChecked

private noncomputable def leaf3918InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3918InputLogOnePlusV_eq :
    leaf3918InputLogOnePlusV = outerEnclosure 24
      (leaf3918Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3918RoundedFacts : LeafRoundedFacts 8
    leaf3918Certificate.logOnePlusV leaf3918InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3918InputLogOnePlusV_eq }

private noncomputable def leaf3918Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi249InputQChi innerPair72Input
    leaf3918InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3918LowerChecked :
    lowerCheck 24 leaf3918Box leaf3918Inputs = true := by
  rfl'

private theorem leaf3918CoversExact : CoversExact 8
    leaf3918Box leaf3918Certificate leaf3918InnerLog leaf3918Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi249RoundedFacts
    innerPair72RoundedFacts leaf3918RoundedFacts (by rfl)

private theorem leaf3918FlatSound : Sound leaf3918Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3918CertificateValid
    leaf3918InnerLogValid leaf3918CoversExact leaf3918LowerChecked

private noncomputable def leaf3919Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf3919Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435707/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715864064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (491407835/268435456) }, upper := { exponent := 0, mantissa := (953/512) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434357759/137431728128) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf3919InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3919LocalValidity :
    LeafFacts leaf3919Box leaf3919Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3919Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715864064) }) = true
      norm_num [leaf3919Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3919CertificateValid :
    WideCertificateValid leaf3919Box leaf3919Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi250ValidityFacts
    leaf3919LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3919CoverageChecked :
    coverageCheck (innerAD leaf3919Box) leaf3919InnerLog = true := by
  rfl'

private theorem leaf3919InnerLogValid :
    leaf3919InnerLog.Valid 8 (innerAD leaf3919Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3919CoverageChecked

private noncomputable def leaf3919InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814701/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3919InputLogOnePlusV_eq :
    leaf3919InputLogOnePlusV = outerEnclosure 24
      (leaf3919Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3919RoundedFacts : LeafRoundedFacts 8
    leaf3919Certificate.logOnePlusV leaf3919InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3919InputLogOnePlusV_eq }

private noncomputable def leaf3919Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi250InputQChi innerPair91Input
    leaf3919InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3919LowerChecked :
    lowerCheck 24 leaf3919Box leaf3919Inputs = true := by
  rfl'

private theorem leaf3919CoversExact : CoversExact 8
    leaf3919Box leaf3919Certificate leaf3919InnerLog leaf3919Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi250RoundedFacts
    innerPair91RoundedFacts leaf3919RoundedFacts (by rfl)

private theorem leaf3919FlatSound : Sound leaf3919Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3919CertificateValid
    leaf3919InnerLogValid leaf3919CoversExact leaf3919LowerChecked

private noncomputable def leaf3920Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf3920Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435707/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743164416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (494094647/268435456) }, upper := { exponent := 0, mantissa := (7665/4096) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486863155/27486328832) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf3920InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3920LocalValidity :
    LeafFacts leaf3920Box leaf3920Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3920Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743164416) }) = true
      norm_num [leaf3920Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3920CertificateValid :
    WideCertificateValid leaf3920Box leaf3920Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi251ValidityFacts
    leaf3920LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3920CoverageChecked :
    coverageCheck (innerAD leaf3920Box) leaf3920InnerLog = true := by
  rfl'

private theorem leaf3920InnerLogValid :
    leaf3920InnerLog.Valid 8 (innerAD leaf3920Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3920CoverageChecked

private noncomputable def leaf3920InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3920InputLogOnePlusV_eq :
    leaf3920InputLogOnePlusV = outerEnclosure 24
      (leaf3920Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3920RoundedFacts : LeafRoundedFacts 8
    leaf3920Certificate.logOnePlusV leaf3920InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3920InputLogOnePlusV_eq }

private noncomputable def leaf3920Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi251InputQChi innerPair91Input
    leaf3920InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3920LowerChecked :
    lowerCheck 24 leaf3920Box leaf3920Inputs = true := by
  rfl'

private theorem leaf3920CoversExact : CoversExact 8
    leaf3920Box leaf3920Certificate leaf3920InnerLog leaf3920Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi251RoundedFacts
    innerPair91RoundedFacts leaf3920RoundedFacts (by rfl)

private theorem leaf3920FlatSound : Sound leaf3920Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3920CertificateValid
    leaf3920InnerLogValid leaf3920CoversExact leaf3920LowerChecked

private noncomputable def leaf3921Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf3921Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435709/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905245696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (499468269/268435456) }, upper := { exponent := 0, mantissa := (1937/1024) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811410261/45810491392) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf3921InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3921LocalValidity :
    LeafFacts leaf3921Box leaf3921Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3921Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905245696) }) = true
      norm_num [leaf3921Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3921CertificateValid :
    WideCertificateValid leaf3921Box leaf3921Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi252ValidityFacts
    leaf3921LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3921CoverageChecked :
    coverageCheck (innerAD leaf3921Box) leaf3921InnerLog = true := by
  rfl'

private theorem leaf3921InnerLogValid :
    leaf3921InnerLog.Valid 8 (innerAD leaf3921Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3921CoverageChecked

private noncomputable def leaf3921InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3921InputLogOnePlusV_eq :
    leaf3921InputLogOnePlusV = outerEnclosure 24
      (leaf3921Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3921RoundedFacts : LeafRoundedFacts 8
    leaf3921Certificate.logOnePlusV leaf3921InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3921InputLogOnePlusV_eq }

private noncomputable def leaf3921Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi252InputQChi innerPair92Input
    leaf3921InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3921LowerChecked :
    lowerCheck 24 leaf3921Box leaf3921Inputs = true := by
  rfl'

private theorem leaf3921CoversExact : CoversExact 8
    leaf3921Box leaf3921Certificate leaf3921InnerLog leaf3921Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi252RoundedFacts
    innerPair92RoundedFacts leaf3921RoundedFacts (by rfl)

private theorem leaf3921FlatSound : Sound leaf3921Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3921CertificateValid
    leaf3921InnerLogValid leaf3921CoversExact leaf3921LowerChecked

private noncomputable def leaf3922Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf3922Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435709/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715778048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (496846989/268435456) }, upper := { exponent := 0, mantissa := (1927/1024) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434271743/137431556096) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf3922InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3922LocalValidity :
    LeafFacts leaf3922Box leaf3922Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3922Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715778048) }) = true
      norm_num [leaf3922Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3922CertificateValid :
    WideCertificateValid leaf3922Box leaf3922Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi251ValidityFacts
    leaf3922LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3922CoverageChecked :
    coverageCheck (innerAD leaf3922Box) leaf3922InnerLog = true := by
  rfl'

private theorem leaf3922InnerLogValid :
    leaf3922InnerLog.Valid 8 (innerAD leaf3922Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3922CoverageChecked

private noncomputable def leaf3922InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3922InputLogOnePlusV_eq :
    leaf3922InputLogOnePlusV = outerEnclosure 24
      (leaf3922Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3922RoundedFacts : LeafRoundedFacts 8
    leaf3922Certificate.logOnePlusV leaf3922InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3922InputLogOnePlusV_eq }

private noncomputable def leaf3922Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi251InputQChi innerPair92Input
    leaf3922InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3922LowerChecked :
    lowerCheck 24 leaf3922Box leaf3922Inputs = true := by
  rfl'

private theorem leaf3922CoversExact : CoversExact 8
    leaf3922Box leaf3922Certificate leaf3922InnerLog leaf3922Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi251RoundedFacts
    innerPair92RoundedFacts leaf3922RoundedFacts (by rfl)

private theorem leaf3922FlatSound : Sound leaf3922Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3922CertificateValid
    leaf3922InnerLogValid leaf3922CoversExact leaf3922LowerChecked

private noncomputable def leaf3923Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf3923Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435711/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715692032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (502286143/268435456) }, upper := { exponent := 0, mantissa := (487/256) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434185727/137431384064) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf3923InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3923LocalValidity :
    LeafFacts leaf3923Box leaf3923Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3923Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715692032) }) = true
      norm_num [leaf3923Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3923CertificateValid :
    WideCertificateValid leaf3923Box leaf3923Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi252ValidityFacts
    leaf3923LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3923CoverageChecked :
    coverageCheck (innerAD leaf3923Box) leaf3923InnerLog = true := by
  rfl'

private theorem leaf3923InnerLogValid :
    leaf3923InnerLog.Valid 8 (innerAD leaf3923Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3923CoverageChecked

private noncomputable def leaf3923InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629423/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3923InputLogOnePlusV_eq :
    leaf3923InputLogOnePlusV = outerEnclosure 24
      (leaf3923Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3923RoundedFacts : LeafRoundedFacts 8
    leaf3923Certificate.logOnePlusV leaf3923InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3923InputLogOnePlusV_eq }

private noncomputable def leaf3923Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi252InputQChi innerPair92Input
    leaf3923InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3923LowerChecked :
    lowerCheck 24 leaf3923Box leaf3923Inputs = true := by
  rfl'

private theorem leaf3923CoversExact : CoversExact 8
    leaf3923Box leaf3923Certificate leaf3923InnerLog leaf3923Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi252RoundedFacts
    innerPair92RoundedFacts leaf3923RoundedFacts (by rfl)

private theorem leaf3923FlatSound : Sound leaf3923Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3923CertificateValid
    leaf3923InnerLogValid leaf3923CoversExact leaf3923LowerChecked

private noncomputable def leaf3924Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3924Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217935/134217728) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715661312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (249521075/134217728) }, upper := { exponent := 0, mantissa := (3911/2048) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434155007/137431322624) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf3924InnerLog : WideLogData :=
  innerPair201Data

set_option maxRecDepth 1000000 in
private theorem leaf3924LocalValidity :
    LeafFacts leaf3924Box leaf3924Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3924Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715661312) }) = true
      norm_num [leaf3924Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3924CertificateValid :
    WideCertificateValid leaf3924Box leaf3924Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi60ValidityFacts
    leaf3924LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3924CoverageChecked :
    coverageCheck (innerAD leaf3924Box) leaf3924InnerLog = true := by
  rfl'

private theorem leaf3924InnerLogValid :
    leaf3924InnerLog.Valid 8 (innerAD leaf3924Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint81PositiveFacts.valid leaf3924CoverageChecked

private noncomputable def leaf3924InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3924InputLogOnePlusV_eq :
    leaf3924InputLogOnePlusV = outerEnclosure 24
      (leaf3924Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3924RoundedFacts : LeafRoundedFacts 8
    leaf3924Certificate.logOnePlusV leaf3924InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3924InputLogOnePlusV_eq }

private noncomputable def leaf3924Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi60InputQChi innerPair201Input
    leaf3924InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3924LowerChecked :
    lowerCheck 24 leaf3924Box leaf3924Inputs = true := by
  rfl'

private theorem leaf3924CoversExact : CoversExact 8
    leaf3924Box leaf3924Certificate leaf3924InnerLog leaf3924Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi60RoundedFacts
    innerPair201RoundedFacts leaf3924RoundedFacts (by rfl)

private theorem leaf3924FlatSound : Sound leaf3924Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3924CertificateValid
    leaf3924InnerLogValid leaf3924CoversExact leaf3924LowerChecked

private noncomputable def leaf3925Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3925Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217937/134217728) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905204736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (250962777/134217728) }, upper := { exponent := 0, mantissa := (1967/1024) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811369301/45810409472) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf3925InnerLog : WideLogData :=
  innerPair484Data

set_option maxRecDepth 1000000 in
private theorem leaf3925LocalValidity :
    LeafFacts leaf3925Box leaf3925Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3925Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905204736) }) = true
      norm_num [leaf3925Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3925CertificateValid :
    WideCertificateValid leaf3925Box leaf3925Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi60ValidityFacts
    leaf3925LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3925CoverageChecked :
    coverageCheck (innerAD leaf3925Box) leaf3925InnerLog = true := by
  rfl'

private theorem leaf3925InnerLogValid :
    leaf3925InnerLog.Valid 8 (innerAD leaf3925Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint81PositiveFacts.valid leaf3925CoverageChecked

private noncomputable def leaf3925InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453679/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3925InputLogOnePlusV_eq :
    leaf3925InputLogOnePlusV = outerEnclosure 24
      (leaf3925Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3925RoundedFacts : LeafRoundedFacts 8
    leaf3925Certificate.logOnePlusV leaf3925InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3925InputLogOnePlusV_eq }

private noncomputable def leaf3925Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi60InputQChi innerPair484Input
    leaf3925InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3925LowerChecked :
    lowerCheck 24 leaf3925Box leaf3925Inputs = true := by
  rfl'

private theorem leaf3925CoversExact : CoversExact 8
    leaf3925Box leaf3925Certificate leaf3925InnerLog leaf3925Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi60RoundedFacts
    innerPair484RoundedFacts leaf3925RoundedFacts (by rfl)

private theorem leaf3925FlatSound : Sound leaf3925Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3925CertificateValid
    leaf3925InnerLogValid leaf3925CoversExact leaf3925LowerChecked

private noncomputable def leaf3926Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3926Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217937/134217728) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715495424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (254763633/134217728) }, upper := { exponent := 0, mantissa := (499/256) } }, logOuter := sk99LogOuterCertificate, logK := sk99LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137433989119/137430990848) } }, logDArg := sk99LogDArgCertificate }

private noncomputable def leaf3926InnerLog : WideLogData :=
  innerPair228Data

set_option maxRecDepth 1000000 in
private theorem leaf3926LocalValidity :
    LeafFacts leaf3926Box leaf3926Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3926Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715495424) }) = true
      norm_num [leaf3926Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3926CertificateValid :
    WideCertificateValid leaf3926Box leaf3926Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk99ValidityFacts chi61ValidityFacts
    leaf3926LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3926CoverageChecked :
    coverageCheck (innerAD leaf3926Box) leaf3926InnerLog = true := by
  rfl'

private theorem leaf3926InnerLogValid :
    leaf3926InnerLog.Valid 8 (innerAD leaf3926Box) :=
  wideLogDataValid_of_cachedCheck endpoint69PositiveFacts
    endpoint71PositiveFacts.valid leaf3926CoverageChecked

private noncomputable def leaf3926InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629447/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3926InputLogOnePlusV_eq :
    leaf3926InputLogOnePlusV = outerEnclosure 24
      (leaf3926Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3926RoundedFacts : LeafRoundedFacts 8
    leaf3926Certificate.logOnePlusV leaf3926InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3926InputLogOnePlusV_eq }

private noncomputable def leaf3926Inputs : Inputs :=
  inputsOfCaches globalInput sk99RoundedInputs
    chi61InputQChi innerPair228Input
    leaf3926InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3926LowerChecked :
    lowerCheck 24 leaf3926Box leaf3926Inputs = true := by
  rfl'

private theorem leaf3926CoversExact : CoversExact 8
    leaf3926Box leaf3926Certificate leaf3926InnerLog leaf3926Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk99RoundedFacts chi61RoundedFacts
    innerPair228RoundedFacts leaf3926RoundedFacts (by rfl)

private theorem leaf3926FlatSound : Sound leaf3926Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3926CertificateValid
    leaf3926InnerLogValid leaf3926CoversExact leaf3926LowerChecked

private noncomputable def leaf3927Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3927Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217939/134217728) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715446272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (256270867/134217728) }, upper := { exponent := 0, mantissa := (251/128) } }, logOuter := sk100LogOuterCertificate, logK := sk100LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137433939967/137430892544) } }, logDArg := sk100LogDArgCertificate }

private noncomputable def leaf3927InnerLog : WideLogData :=
  innerPair234Data

set_option maxRecDepth 1000000 in
private theorem leaf3927LocalValidity :
    LeafFacts leaf3927Box leaf3927Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3927Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715446272) }) = true
      norm_num [leaf3927Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3927CertificateValid :
    WideCertificateValid leaf3927Box leaf3927Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk100ValidityFacts chi61ValidityFacts
    leaf3927LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3927CoverageChecked :
    coverageCheck (innerAD leaf3927Box) leaf3927InnerLog = true := by
  rfl'

private theorem leaf3927InnerLogValid :
    leaf3927InnerLog.Valid 8 (innerAD leaf3927Box) :=
  wideLogDataValid_of_cachedCheck endpoint70PositiveFacts
    endpoint85PositiveFacts.valid leaf3927CoverageChecked

private noncomputable def leaf3927InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3927InputLogOnePlusV_eq :
    leaf3927InputLogOnePlusV = outerEnclosure 24
      (leaf3927Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3927RoundedFacts : LeafRoundedFacts 8
    leaf3927Certificate.logOnePlusV leaf3927InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3927InputLogOnePlusV_eq }

private noncomputable def leaf3927Inputs : Inputs :=
  inputsOfCaches globalInput sk100RoundedInputs
    chi61InputQChi innerPair234Input
    leaf3927InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3927LowerChecked :
    lowerCheck 24 leaf3927Box leaf3927Inputs = true := by
  rfl'

private theorem leaf3927CoversExact : CoversExact 8
    leaf3927Box leaf3927Certificate leaf3927InnerLog leaf3927Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk100RoundedFacts chi61RoundedFacts
    innerPair234RoundedFacts leaf3927RoundedFacts (by rfl)

private theorem leaf3927FlatSound : Sound leaf3927Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3927CertificateValid
    leaf3927InnerLogValid leaf3927CoversExact leaf3927LowerChecked

private noncomputable def leaf3928Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3928Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217939/134217728) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715567104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (252404479/134217728) }, upper := { exponent := 0, mantissa := (3957/2048) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434060799/137431134208) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf3928InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3928LocalValidity :
    LeafFacts leaf3928Box leaf3928Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3928Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715567104) }) = true
      norm_num [leaf3928Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3928CertificateValid :
    WideCertificateValid leaf3928Box leaf3928Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi60ValidityFacts
    leaf3928LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3928CoverageChecked :
    coverageCheck (innerAD leaf3928Box) leaf3928InnerLog = true := by
  rfl'

private theorem leaf3928InnerLogValid :
    leaf3928InnerLog.Valid 8 (innerAD leaf3928Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3928CoverageChecked

private noncomputable def leaf3928InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814719/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3928InputLogOnePlusV_eq :
    leaf3928InputLogOnePlusV = outerEnclosure 24
      (leaf3928Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3928RoundedFacts : LeafRoundedFacts 8
    leaf3928Certificate.logOnePlusV leaf3928InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3928InputLogOnePlusV_eq }

private noncomputable def leaf3928Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi60InputQChi innerPair100Input
    leaf3928InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3928LowerChecked :
    lowerCheck 24 leaf3928Box leaf3928Inputs = true := by
  rfl'

private theorem leaf3928CoversExact : CoversExact 8
    leaf3928Box leaf3928Certificate leaf3928InnerLog leaf3928Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi60RoundedFacts
    innerPair100RoundedFacts leaf3928RoundedFacts (by rfl)

private theorem leaf3928FlatSound : Sound leaf3928Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3928CertificateValid
    leaf3928InnerLogValid leaf3928CoversExact leaf3928LowerChecked

private noncomputable def leaf3929Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3929Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217941/134217728) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743104000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (253846181/134217728) }, upper := { exponent := 0, mantissa := (995/512) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486802739/27486208000) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf3929InnerLog : WideLogData :=
  innerPair232Data

set_option maxRecDepth 1000000 in
private theorem leaf3929LocalValidity :
    LeafFacts leaf3929Box leaf3929Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3929Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743104000) }) = true
      norm_num [leaf3929Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3929CertificateValid :
    WideCertificateValid leaf3929Box leaf3929Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi60ValidityFacts
    leaf3929LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3929CoverageChecked :
    coverageCheck (innerAD leaf3929Box) leaf3929InnerLog = true := by
  rfl'

private theorem leaf3929InnerLogValid :
    leaf3929InnerLog.Valid 8 (innerAD leaf3929Box) :=
  wideLogDataValid_of_cachedCheck endpoint69PositiveFacts
    endpoint287PositiveFacts.valid leaf3929CoverageChecked

private noncomputable def leaf3929InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907361/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3929InputLogOnePlusV_eq :
    leaf3929InputLogOnePlusV = outerEnclosure 24
      (leaf3929Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3929RoundedFacts : LeafRoundedFacts 8
    leaf3929Certificate.logOnePlusV leaf3929InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3929InputLogOnePlusV_eq }

private noncomputable def leaf3929Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi60InputQChi innerPair232Input
    leaf3929InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3929LowerChecked :
    lowerCheck 24 leaf3929Box leaf3929Inputs = true := by
  rfl'

private theorem leaf3929CoversExact : CoversExact 8
    leaf3929Box leaf3929Certificate leaf3929InnerLog leaf3929Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi60RoundedFacts
    innerPair232RoundedFacts leaf3929RoundedFacts (by rfl)

private theorem leaf3929FlatSound : Sound leaf3929Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3929CertificateValid
    leaf3929InnerLogValid leaf3929CoversExact leaf3929LowerChecked

private noncomputable def leaf3930Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3930Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217941/134217728) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743079424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (257778101/134217728) }, upper := { exponent := 0, mantissa := (505/256) } }, logOuter := sk101LogOuterCertificate, logK := sk101LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486778163/27486158848) } }, logDArg := sk101LogDArgCertificate }

private noncomputable def leaf3930InnerLog : WideLogData :=
  innerPair236Data

set_option maxRecDepth 1000000 in
private theorem leaf3930LocalValidity :
    LeafFacts leaf3930Box leaf3930Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3930Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743079424) }) = true
      norm_num [leaf3930Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3930CertificateValid :
    WideCertificateValid leaf3930Box leaf3930Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk101ValidityFacts chi61ValidityFacts
    leaf3930LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3930CoverageChecked :
    coverageCheck (innerAD leaf3930Box) leaf3930InnerLog = true := by
  rfl'

private theorem leaf3930InnerLogValid :
    leaf3930InnerLog.Valid 8 (innerAD leaf3930Box) :=
  wideLogDataValid_of_cachedCheck endpoint70PositiveFacts
    endpoint267PositiveFacts.valid leaf3930CoverageChecked

private noncomputable def leaf3930InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629459/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3930InputLogOnePlusV_eq :
    leaf3930InputLogOnePlusV = outerEnclosure 24
      (leaf3930Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3930RoundedFacts : LeafRoundedFacts 8
    leaf3930Certificate.logOnePlusV leaf3930InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3930InputLogOnePlusV_eq }

private noncomputable def leaf3930Inputs : Inputs :=
  inputsOfCaches globalInput sk101RoundedInputs
    chi61InputQChi innerPair236Input
    leaf3930InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3930LowerChecked :
    lowerCheck 24 leaf3930Box leaf3930Inputs = true := by
  rfl'

private theorem leaf3930CoversExact : CoversExact 8
    leaf3930Box leaf3930Certificate leaf3930InnerLog leaf3930Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk101RoundedFacts chi61RoundedFacts
    innerPair236RoundedFacts leaf3930RoundedFacts (by rfl)

private theorem leaf3930FlatSound : Sound leaf3930Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3930CertificateValid
    leaf3930InnerLogValid leaf3930CoversExact leaf3930LowerChecked

private noncomputable def leaf3931Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3931Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217943/134217728) }, vSqrt := { lower := (32765/32768), upper := (1108345889/1108312064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (259285335/134217728) }, upper := { exponent := 0, mantissa := (127/64) } }, logOuter := sk102LogOuterCertificate, logK := sk102LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2216657953/2216624128) } }, logDArg := sk102LogDArgCertificate }

private noncomputable def leaf3931InnerLog : WideLogData :=
  innerPair308Data

set_option maxRecDepth 1000000 in
private theorem leaf3931LocalValidity :
    LeafFacts leaf3931Box leaf3931Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3931Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1108345889/1108312064) }) = true
      norm_num [leaf3931Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3931CertificateValid :
    WideCertificateValid leaf3931Box leaf3931Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk102ValidityFacts chi61ValidityFacts
    leaf3931LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3931CoverageChecked :
    coverageCheck (innerAD leaf3931Box) leaf3931InnerLog = true := by
  rfl'

private theorem leaf3931InnerLogValid :
    leaf3931InnerLog.Valid 8 (innerAD leaf3931Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint267PositiveFacts.valid leaf3931CoverageChecked

private noncomputable def leaf3931InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3931InputLogOnePlusV_eq :
    leaf3931InputLogOnePlusV = outerEnclosure 24
      (leaf3931Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3931RoundedFacts : LeafRoundedFacts 8
    leaf3931Certificate.logOnePlusV leaf3931InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3931InputLogOnePlusV_eq }

private noncomputable def leaf3931Inputs : Inputs :=
  inputsOfCaches globalInput sk102RoundedInputs
    chi61InputQChi innerPair308Input
    leaf3931InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3931LowerChecked :
    lowerCheck 24 leaf3931Box leaf3931Inputs = true := by
  rfl'

private theorem leaf3931CoversExact : CoversExact 8
    leaf3931Box leaf3931Certificate leaf3931InnerLog leaf3931Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk102RoundedFacts chi61RoundedFacts
    innerPair308RoundedFacts leaf3931RoundedFacts (by rfl)

private theorem leaf3931FlatSound : Sound leaf3931Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3931CertificateValid
    leaf3931InnerLogValid leaf3931CoversExact leaf3931LowerChecked

private noncomputable def leaf3932Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf3932Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435707/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715908096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (488589959/268435456) }, upper := { exponent := 0, mantissa := (7581/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434401791/137431816192) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf3932InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3932LocalValidity :
    LeafFacts leaf3932Box leaf3932Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3932Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715908096) }) = true
      norm_num [leaf3932Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3932CertificateValid :
    WideCertificateValid leaf3932Box leaf3932Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi249ValidityFacts
    leaf3932LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3932CoverageChecked :
    coverageCheck (innerAD leaf3932Box) leaf3932InnerLog = true := by
  rfl'

private theorem leaf3932InnerLogValid :
    leaf3932InnerLog.Valid 8 (innerAD leaf3932Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3932CoverageChecked

private noncomputable def leaf3932InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3932InputLogOnePlusV_eq :
    leaf3932InputLogOnePlusV = outerEnclosure 24
      (leaf3932Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3932RoundedFacts : LeafRoundedFacts 8
    leaf3932Certificate.logOnePlusV leaf3932InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3932InputLogOnePlusV_eq }

private noncomputable def leaf3932Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi249InputQChi innerPair91Input
    leaf3932InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3932LowerChecked :
    lowerCheck 24 leaf3932Box leaf3932Inputs = true := by
  rfl'

private theorem leaf3932CoversExact : CoversExact 8
    leaf3932Box leaf3932Certificate leaf3932InnerLog leaf3932Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi249RoundedFacts
    innerPair91RoundedFacts leaf3932RoundedFacts (by rfl)

private theorem leaf3932FlatSound : Sound leaf3932Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3932CertificateValid
    leaf3932InnerLogValid leaf3932CoversExact leaf3932LowerChecked

private noncomputable def leaf3933Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf3933Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435709/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715821056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (494094645/268435456) }, upper := { exponent := 0, mantissa := (3833/2048) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434314751/137431642112) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf3933InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3933LocalValidity :
    LeafFacts leaf3933Box leaf3933Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3933Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715821056) }) = true
      norm_num [leaf3933Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3933CertificateValid :
    WideCertificateValid leaf3933Box leaf3933Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi250ValidityFacts
    leaf3933LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3933CoverageChecked :
    coverageCheck (innerAD leaf3933Box) leaf3933InnerLog = true := by
  rfl'

private theorem leaf3933InnerLogValid :
    leaf3933InnerLog.Valid 8 (innerAD leaf3933Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3933CoverageChecked

private noncomputable def leaf3933InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3933InputLogOnePlusV_eq :
    leaf3933InputLogOnePlusV = outerEnclosure 24
      (leaf3933Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3933RoundedFacts : LeafRoundedFacts 8
    leaf3933Certificate.logOnePlusV leaf3933InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3933InputLogOnePlusV_eq }

private noncomputable def leaf3933Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi250InputQChi innerPair91Input
    leaf3933InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3933LowerChecked :
    lowerCheck 24 leaf3933Box leaf3933Inputs = true := by
  rfl'

private theorem leaf3933CoversExact : CoversExact 8
    leaf3933Box leaf3933Certificate leaf3933InnerLog leaf3933Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi250RoundedFacts
    innerPair91RoundedFacts leaf3933RoundedFacts (by rfl)

private theorem leaf3933FlatSound : Sound leaf3933Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3933CertificateValid
    leaf3933InnerLogValid leaf3933CoversExact leaf3933LowerChecked

private noncomputable def leaf3934Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf3934Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435709/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905288704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (491211237/268435456) }, upper := { exponent := 0, mantissa := (3811/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811453269/45810577408) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf3934InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3934LocalValidity :
    LeafFacts leaf3934Box leaf3934Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3934Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905288704) }) = true
      norm_num [leaf3934Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3934CertificateValid :
    WideCertificateValid leaf3934Box leaf3934Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi249ValidityFacts
    leaf3934LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3934CoverageChecked :
    coverageCheck (innerAD leaf3934Box) leaf3934InnerLog = true := by
  rfl'

private theorem leaf3934InnerLogValid :
    leaf3934InnerLog.Valid 8 (innerAD leaf3934Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3934CoverageChecked

private noncomputable def leaf3934InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814701/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3934InputLogOnePlusV_eq :
    leaf3934InputLogOnePlusV = outerEnclosure 24
      (leaf3934Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3934RoundedFacts : LeafRoundedFacts 8
    leaf3934Certificate.logOnePlusV leaf3934InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3934InputLogOnePlusV_eq }

private noncomputable def leaf3934Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi249InputQChi innerPair91Input
    leaf3934InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3934LowerChecked :
    lowerCheck 24 leaf3934Box leaf3934Inputs = true := by
  rfl'

private theorem leaf3934CoversExact : CoversExact 8
    leaf3934Box leaf3934Certificate leaf3934InnerLog leaf3934Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi249RoundedFacts
    innerPair91RoundedFacts leaf3934RoundedFacts (by rfl)

private theorem leaf3934FlatSound : Sound leaf3934Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3934CertificateValid
    leaf3934InnerLogValid leaf3934CoversExact leaf3934LowerChecked

private noncomputable def leaf3935Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf3935Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435711/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715778048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (496781455/268435456) }, upper := { exponent := 0, mantissa := (1927/1024) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434271743/137431556096) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf3935InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3935LocalValidity :
    LeafFacts leaf3935Box leaf3935Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3935Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715778048) }) = true
      norm_num [leaf3935Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3935CertificateValid :
    WideCertificateValid leaf3935Box leaf3935Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi250ValidityFacts
    leaf3935LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3935CoverageChecked :
    coverageCheck (innerAD leaf3935Box) leaf3935InnerLog = true := by
  rfl'

private theorem leaf3935InnerLogValid :
    leaf3935InnerLog.Valid 8 (innerAD leaf3935Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3935CoverageChecked

private noncomputable def leaf3935InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3935InputLogOnePlusV_eq :
    leaf3935InputLogOnePlusV = outerEnclosure 24
      (leaf3935Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3935RoundedFacts : LeafRoundedFacts 8
    leaf3935Certificate.logOnePlusV leaf3935InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3935InputLogOnePlusV_eq }

private noncomputable def leaf3935Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi250InputQChi innerPair92Input
    leaf3935InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3935LowerChecked :
    lowerCheck 24 leaf3935Box leaf3935Inputs = true := by
  rfl'

private theorem leaf3935CoversExact : CoversExact 8
    leaf3935Box leaf3935Certificate leaf3935InnerLog leaf3935Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi250RoundedFacts
    innerPair92RoundedFacts leaf3935RoundedFacts (by rfl)

private theorem leaf3935FlatSound : Sound leaf3935Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3935CertificateValid
    leaf3935InnerLogValid leaf3935CoversExact leaf3935LowerChecked

private noncomputable def leaf3936Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf3936Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435711/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905244672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (499599331/268435456) }, upper := { exponent := 0, mantissa := (7751/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811409237/45810489344) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf3936InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3936LocalValidity :
    LeafFacts leaf3936Box leaf3936Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3936Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905244672) }) = true
      norm_num [leaf3936Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3936CertificateValid :
    WideCertificateValid leaf3936Box leaf3936Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi251ValidityFacts
    leaf3936LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3936CoverageChecked :
    coverageCheck (innerAD leaf3936Box) leaf3936InnerLog = true := by
  rfl'

private theorem leaf3936InnerLogValid :
    leaf3936InnerLog.Valid 8 (innerAD leaf3936Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3936CoverageChecked

private noncomputable def leaf3936InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3936InputLogOnePlusV_eq :
    leaf3936InputLogOnePlusV = outerEnclosure 24
      (leaf3936Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3936RoundedFacts : LeafRoundedFacts 8
    leaf3936Certificate.logOnePlusV leaf3936InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3936InputLogOnePlusV_eq }

private noncomputable def leaf3936Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi251InputQChi innerPair92Input
    leaf3936InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3936LowerChecked :
    lowerCheck 24 leaf3936Box leaf3936Inputs = true := by
  rfl'

private theorem leaf3936CoversExact : CoversExact 8
    leaf3936Box leaf3936Certificate leaf3936InnerLog leaf3936Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi251RoundedFacts
    innerPair92RoundedFacts leaf3936RoundedFacts (by rfl)

private theorem leaf3936FlatSound : Sound leaf3936Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3936CertificateValid
    leaf3936InnerLogValid leaf3936CoversExact leaf3936LowerChecked

private noncomputable def leaf3937Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf3937Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435713/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715646976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (505104017/268435456) }, upper := { exponent := 0, mantissa := (1959/1024) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434140671/137431293952) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf3937InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3937LocalValidity :
    LeafFacts leaf3937Box leaf3937Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3937Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715646976) }) = true
      norm_num [leaf3937Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3937CertificateValid :
    WideCertificateValid leaf3937Box leaf3937Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi252ValidityFacts
    leaf3937LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3937CoverageChecked :
    coverageCheck (innerAD leaf3937Box) leaf3937InnerLog = true := by
  rfl'

private theorem leaf3937InnerLogValid :
    leaf3937InnerLog.Valid 8 (innerAD leaf3937Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3937CoverageChecked

private noncomputable def leaf3937InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907357/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3937InputLogOnePlusV_eq :
    leaf3937InputLogOnePlusV = outerEnclosure 24
      (leaf3937Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3937RoundedFacts : LeafRoundedFacts 8
    leaf3937Certificate.logOnePlusV leaf3937InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3937InputLogOnePlusV_eq }

private noncomputable def leaf3937Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi252InputQChi innerPair100Input
    leaf3937InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3937LowerChecked :
    lowerCheck 24 leaf3937Box leaf3937Inputs = true := by
  rfl'

private theorem leaf3937CoversExact : CoversExact 8
    leaf3937Box leaf3937Certificate leaf3937InnerLog leaf3937Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi252RoundedFacts
    innerPair100RoundedFacts leaf3937RoundedFacts (by rfl)

private theorem leaf3937FlatSound : Sound leaf3937Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3937CertificateValid
    leaf3937InnerLogValid leaf3937CoversExact leaf3937LowerChecked

private noncomputable def leaf3938Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf3938Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435713/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715689984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (502351673/268435456) }, upper := { exponent := 0, mantissa := (3897/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434183679/137431379968) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf3938InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3938LocalValidity :
    LeafFacts leaf3938Box leaf3938Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3938Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715689984) }) = true
      norm_num [leaf3938Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3938CertificateValid :
    WideCertificateValid leaf3938Box leaf3938Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi251ValidityFacts
    leaf3938LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3938CoverageChecked :
    coverageCheck (innerAD leaf3938Box) leaf3938InnerLog = true := by
  rfl'

private theorem leaf3938InnerLogValid :
    leaf3938InnerLog.Valid 8 (innerAD leaf3938Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3938CoverageChecked

private noncomputable def leaf3938InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629423/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3938InputLogOnePlusV_eq :
    leaf3938InputLogOnePlusV = outerEnclosure 24
      (leaf3938Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3938RoundedFacts : LeafRoundedFacts 8
    leaf3938Certificate.logOnePlusV leaf3938InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3938InputLogOnePlusV_eq }

private noncomputable def leaf3938Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi251InputQChi innerPair92Input
    leaf3938InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3938LowerChecked :
    lowerCheck 24 leaf3938Box leaf3938Inputs = true := by
  rfl'

private theorem leaf3938CoversExact : CoversExact 8
    leaf3938Box leaf3938Certificate leaf3938InnerLog leaf3938Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi251RoundedFacts
    innerPair92RoundedFacts leaf3938RoundedFacts (by rfl)

private theorem leaf3938FlatSound : Sound leaf3938Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3938CertificateValid
    leaf3938InnerLogValid leaf3938CoversExact leaf3938LowerChecked

private noncomputable def leaf3939Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf3939Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435715/268435456) }, vSqrt := { lower := (32765/32768), upper := (4581232913/4581040128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (507921891/268435456) }, upper := { exponent := 0, mantissa := (985/512) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9162273041/9162080256) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf3939InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3939LocalValidity :
    LeafFacts leaf3939Box leaf3939Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3939Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4581232913/4581040128) }) = true
      norm_num [leaf3939Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3939CertificateValid :
    WideCertificateValid leaf3939Box leaf3939Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi252ValidityFacts
    leaf3939LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3939CoverageChecked :
    coverageCheck (innerAD leaf3939Box) leaf3939InnerLog = true := by
  rfl'

private theorem leaf3939InnerLogValid :
    leaf3939InnerLog.Valid 8 (innerAD leaf3939Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3939CoverageChecked

private noncomputable def leaf3939InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814717/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3939InputLogOnePlusV_eq :
    leaf3939InputLogOnePlusV = outerEnclosure 24
      (leaf3939Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3939RoundedFacts : LeafRoundedFacts 8
    leaf3939Certificate.logOnePlusV leaf3939InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3939InputLogOnePlusV_eq }

private noncomputable def leaf3939Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi252InputQChi innerPair100Input
    leaf3939InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3939LowerChecked :
    lowerCheck 24 leaf3939Box leaf3939Inputs = true := by
  rfl'

private theorem leaf3939CoversExact : CoversExact 8
    leaf3939Box leaf3939Certificate leaf3939InnerLog leaf3939Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi252RoundedFacts
    innerPair100RoundedFacts leaf3939RoundedFacts (by rfl)

private theorem leaf3939FlatSound : Sound leaf3939Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3939CertificateValid
    leaf3939InnerLogValid leaf3939CoversExact leaf3939LowerChecked

private noncomputable def leaf3940Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf3940Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435711/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715824128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (493832515/268435456) }, upper := { exponent := 0, mantissa := (7663/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434317823/137431648256) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf3940InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3940LocalValidity :
    LeafFacts leaf3940Box leaf3940Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3940Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715824128) }) = true
      norm_num [leaf3940Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3940CertificateValid :
    WideCertificateValid leaf3940Box leaf3940Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi249ValidityFacts
    leaf3940LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3940CoverageChecked :
    coverageCheck (innerAD leaf3940Box) leaf3940InnerLog = true := by
  rfl'

private theorem leaf3940InnerLogValid :
    leaf3940InnerLog.Valid 8 (innerAD leaf3940Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3940CoverageChecked

private noncomputable def leaf3940InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3940InputLogOnePlusV_eq :
    leaf3940InputLogOnePlusV = outerEnclosure 24
      (leaf3940Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3940RoundedFacts : LeafRoundedFacts 8
    leaf3940Certificate.logOnePlusV leaf3940InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3940InputLogOnePlusV_eq }

private noncomputable def leaf3940Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi249InputQChi innerPair91Input
    leaf3940InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3940LowerChecked :
    lowerCheck 24 leaf3940Box leaf3940Inputs = true := by
  rfl'

private theorem leaf3940CoversExact : CoversExact 8
    leaf3940Box leaf3940Certificate leaf3940InnerLog leaf3940Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi249RoundedFacts
    innerPair91RoundedFacts leaf3940RoundedFacts (by rfl)

private theorem leaf3940FlatSound : Sound leaf3940Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3940CertificateValid
    leaf3940InnerLogValid leaf3940CoversExact leaf3940LowerChecked

private noncomputable def leaf3941Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf3941Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435713/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743147008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (499468265/268435456) }, upper := { exponent := 0, mantissa := (3875/2048) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27486845747/27486294016) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf3941InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3941LocalValidity :
    LeafFacts leaf3941Box leaf3941Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3941Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743147008) }) = true
      norm_num [leaf3941Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3941CertificateValid :
    WideCertificateValid leaf3941Box leaf3941Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi250ValidityFacts
    leaf3941LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3941CoverageChecked :
    coverageCheck (innerAD leaf3941Box) leaf3941InnerLog = true := by
  rfl'

private theorem leaf3941InnerLogValid :
    leaf3941InnerLog.Valid 8 (innerAD leaf3941Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3941CoverageChecked

private noncomputable def leaf3941InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3941InputLogOnePlusV_eq :
    leaf3941InputLogOnePlusV = outerEnclosure 24
      (leaf3941Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3941RoundedFacts : LeafRoundedFacts 8
    leaf3941Certificate.logOnePlusV leaf3941InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3941InputLogOnePlusV_eq }

private noncomputable def leaf3941Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi250InputQChi innerPair92Input
    leaf3941InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3941LowerChecked :
    lowerCheck 24 leaf3941Box leaf3941Inputs = true := by
  rfl'

private theorem leaf3941CoversExact : CoversExact 8
    leaf3941Box leaf3941Certificate leaf3941InnerLog leaf3941Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi250RoundedFacts
    innerPair92RoundedFacts leaf3941RoundedFacts (by rfl)

private theorem leaf3941FlatSound : Sound leaf3941Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3941CertificateValid
    leaf3941InnerLogValid leaf3941CoversExact leaf3941LowerChecked

private noncomputable def leaf3942Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (5/16), chiHi := (41/128) }

private noncomputable def leaf3942Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435713/268435456) }, vSqrt := { lower := (32765/32768), upper := (4042264335/4042104832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (496453793/268435456) }, upper := { exponent := 0, mantissa := (963/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi249LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8084369167/8084209664) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf3942InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3942LocalValidity :
    LeafFacts leaf3942Box leaf3942Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3942Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4042264335/4042104832) }) = true
      norm_num [leaf3942Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3942CertificateValid :
    WideCertificateValid leaf3942Box leaf3942Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi249ValidityFacts
    leaf3942LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3942CoverageChecked :
    coverageCheck (innerAD leaf3942Box) leaf3942InnerLog = true := by
  rfl'

private theorem leaf3942InnerLogValid :
    leaf3942InnerLog.Valid 8 (innerAD leaf3942Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3942CoverageChecked

private noncomputable def leaf3942InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3942InputLogOnePlusV_eq :
    leaf3942InputLogOnePlusV = outerEnclosure 24
      (leaf3942Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3942RoundedFacts : LeafRoundedFacts 8
    leaf3942Certificate.logOnePlusV leaf3942InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3942InputLogOnePlusV_eq }

private noncomputable def leaf3942Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi249InputQChi innerPair92Input
    leaf3942InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3942LowerChecked :
    lowerCheck 24 leaf3942Box leaf3942Inputs = true := by
  rfl'

private theorem leaf3942CoversExact : CoversExact 8
    leaf3942Box leaf3942Certificate leaf3942InnerLog leaf3942Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi249RoundedFacts
    innerPair92RoundedFacts leaf3942RoundedFacts (by rfl)

private theorem leaf3942FlatSound : Sound leaf3942Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3942CertificateValid
    leaf3942InnerLogValid leaf3942CoversExact leaf3942LowerChecked

private noncomputable def leaf3943Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (41/128), chiHi := (21/64) }

private noncomputable def leaf3943Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435715/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715692032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (502155075/268435456) }, upper := { exponent := 0, mantissa := (487/256) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi250LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434185727/137431384064) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf3943InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3943LocalValidity :
    LeafFacts leaf3943Box leaf3943Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3943Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715692032) }) = true
      norm_num [leaf3943Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3943CertificateValid :
    WideCertificateValid leaf3943Box leaf3943Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi250ValidityFacts
    leaf3943LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3943CoverageChecked :
    coverageCheck (innerAD leaf3943Box) leaf3943InnerLog = true := by
  rfl'

private theorem leaf3943InnerLogValid :
    leaf3943InnerLog.Valid 8 (innerAD leaf3943Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3943CoverageChecked

private noncomputable def leaf3943InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629423/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3943InputLogOnePlusV_eq :
    leaf3943InputLogOnePlusV = outerEnclosure 24
      (leaf3943Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3943RoundedFacts : LeafRoundedFacts 8
    leaf3943Certificate.logOnePlusV leaf3943InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3943InputLogOnePlusV_eq }

private noncomputable def leaf3943Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi250InputQChi innerPair92Input
    leaf3943InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3943LowerChecked :
    lowerCheck 24 leaf3943Box leaf3943Inputs = true := by
  rfl'

private theorem leaf3943CoversExact : CoversExact 8
    leaf3943Box leaf3943Certificate leaf3943InnerLog leaf3943Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi250RoundedFacts
    innerPair92RoundedFacts leaf3943RoundedFacts (by rfl)

private theorem leaf3943FlatSound : Sound leaf3943Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3943CertificateValid
    leaf3943InnerLogValid leaf3943CoversExact leaf3943LowerChecked

private noncomputable def leaf3944Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf3944Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435715/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715645952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (505104015/268435456) }, upper := { exponent := 0, mantissa := (7837/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434139647/137431291904) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf3944InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3944LocalValidity :
    LeafFacts leaf3944Box leaf3944Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3944Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715645952) }) = true
      norm_num [leaf3944Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3944CertificateValid :
    WideCertificateValid leaf3944Box leaf3944Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi251ValidityFacts
    leaf3944LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3944CoverageChecked :
    coverageCheck (innerAD leaf3944Box) leaf3944InnerLog = true := by
  rfl'

private theorem leaf3944InnerLogValid :
    leaf3944InnerLog.Valid 8 (innerAD leaf3944Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3944CoverageChecked

private noncomputable def leaf3944InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907357/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3944InputLogOnePlusV_eq :
    leaf3944InputLogOnePlusV = outerEnclosure 24
      (leaf3944Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3944RoundedFacts : LeafRoundedFacts 8
    leaf3944Certificate.logOnePlusV leaf3944InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3944InputLogOnePlusV_eq }

private noncomputable def leaf3944Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi251InputQChi innerPair100Input
    leaf3944InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3944LowerChecked :
    lowerCheck 24 leaf3944Box leaf3944Inputs = true := by
  rfl'

private theorem leaf3944CoversExact : CoversExact 8
    leaf3944Box leaf3944Certificate leaf3944InnerLog leaf3944Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi251RoundedFacts
    innerPair100RoundedFacts leaf3944RoundedFacts (by rfl)

private theorem leaf3944FlatSound : Sound leaf3944Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3944CertificateValid
    leaf3944InnerLogValid leaf3944CoversExact leaf3944LowerChecked

private noncomputable def leaf3945Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf3945Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435717/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715556864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (510739765/268435456) }, upper := { exponent := 0, mantissa := (1981/1024) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434050559/137431113728) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf3945InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3945LocalValidity :
    LeafFacts leaf3945Box leaf3945Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3945Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715556864) }) = true
      norm_num [leaf3945Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3945CertificateValid :
    WideCertificateValid leaf3945Box leaf3945Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi252ValidityFacts
    leaf3945LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3945CoverageChecked :
    coverageCheck (innerAD leaf3945Box) leaf3945InnerLog = true := by
  rfl'

private theorem leaf3945InnerLogValid :
    leaf3945InnerLog.Valid 8 (innerAD leaf3945Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3945CoverageChecked

private noncomputable def leaf3945InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3945InputLogOnePlusV_eq :
    leaf3945InputLogOnePlusV = outerEnclosure 24
      (leaf3945Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3945RoundedFacts : LeafRoundedFacts 8
    leaf3945Certificate.logOnePlusV leaf3945InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3945InputLogOnePlusV_eq }

private noncomputable def leaf3945Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi252InputQChi innerPair100Input
    leaf3945InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3945LowerChecked :
    lowerCheck 24 leaf3945Box leaf3945Inputs = true := by
  rfl'

private theorem leaf3945CoversExact : CoversExact 8
    leaf3945Box leaf3945Certificate leaf3945InnerLog leaf3945Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi252RoundedFacts
    innerPair100RoundedFacts leaf3945RoundedFacts (by rfl)

private theorem leaf3945FlatSound : Sound leaf3945Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3945CertificateValid
    leaf3945InnerLogValid leaf3945CoversExact leaf3945LowerChecked

private noncomputable def leaf3946Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (21/64), chiHi := (43/128) }

private noncomputable def leaf3946Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435717/268435456) }, vSqrt := { lower := (32765/32768), upper := (4581232913/4581040128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (507856357/268435456) }, upper := { exponent := 0, mantissa := (985/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi251LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9162273041/9162080256) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf3946InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3946LocalValidity :
    LeafFacts leaf3946Box leaf3946Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3946Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4581232913/4581040128) }) = true
      norm_num [leaf3946Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3946CertificateValid :
    WideCertificateValid leaf3946Box leaf3946Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi251ValidityFacts
    leaf3946LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3946CoverageChecked :
    coverageCheck (innerAD leaf3946Box) leaf3946InnerLog = true := by
  rfl'

private theorem leaf3946InnerLogValid :
    leaf3946InnerLog.Valid 8 (innerAD leaf3946Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3946CoverageChecked

private noncomputable def leaf3946InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814717/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3946InputLogOnePlusV_eq :
    leaf3946InputLogOnePlusV = outerEnclosure 24
      (leaf3946Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3946RoundedFacts : LeafRoundedFacts 8
    leaf3946Certificate.logOnePlusV leaf3946InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3946InputLogOnePlusV_eq }

private noncomputable def leaf3946Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi251InputQChi innerPair100Input
    leaf3946InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3946LowerChecked :
    lowerCheck 24 leaf3946Box leaf3946Inputs = true := by
  rfl'

private theorem leaf3946CoversExact : CoversExact 8
    leaf3946Box leaf3946Certificate leaf3946InnerLog leaf3946Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi251RoundedFacts
    innerPair100RoundedFacts leaf3946RoundedFacts (by rfl)

private theorem leaf3946FlatSound : Sound leaf3946Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3946CertificateValid
    leaf3946InnerLogValid leaf3946CoversExact leaf3946LowerChecked

private noncomputable def leaf3947Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (43/128), chiHi := (11/32) }

private noncomputable def leaf3947Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435719/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715511808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (513557639/268435456) }, upper := { exponent := 0, mantissa := (249/128) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi252LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434005503/137431023616) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf3947InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3947LocalValidity :
    LeafFacts leaf3947Box leaf3947Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3947Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715511808) }) = true
      norm_num [leaf3947Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3947CertificateValid :
    WideCertificateValid leaf3947Box leaf3947Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi252ValidityFacts
    leaf3947LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3947CoverageChecked :
    coverageCheck (innerAD leaf3947Box) leaf3947InnerLog = true := by
  rfl'

private theorem leaf3947InnerLogValid :
    leaf3947InnerLog.Valid 8 (innerAD leaf3947Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3947CoverageChecked

private noncomputable def leaf3947InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3947InputLogOnePlusV_eq :
    leaf3947InputLogOnePlusV = outerEnclosure 24
      (leaf3947Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3947RoundedFacts : LeafRoundedFacts 8
    leaf3947Certificate.logOnePlusV leaf3947InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3947InputLogOnePlusV_eq }

private noncomputable def leaf3947Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi252InputQChi innerPair101Input
    leaf3947InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3947LowerChecked :
    lowerCheck 24 leaf3947Box leaf3947Inputs = true := by
  rfl'

private theorem leaf3947CoversExact : CoversExact 8
    leaf3947Box leaf3947Certificate leaf3947InnerLog leaf3947Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi252RoundedFacts
    innerPair101RoundedFacts leaf3947RoundedFacts (by rfl)

private theorem leaf3947FlatSound : Sound leaf3947Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3947CertificateValid
    leaf3947InnerLogValid leaf3947CoversExact leaf3947LowerChecked

private noncomputable def leaf3948Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf3948Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435715/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715559936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (510608703/268435456) }, upper := { exponent := 0, mantissa := (7921/4096) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434053631/137431119872) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf3948InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3948LocalValidity :
    LeafFacts leaf3948Box leaf3948Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3948Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715559936) }) = true
      norm_num [leaf3948Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3948CertificateValid :
    WideCertificateValid leaf3948Box leaf3948Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi253ValidityFacts
    leaf3948LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3948CoverageChecked :
    coverageCheck (innerAD leaf3948Box) leaf3948InnerLog = true := by
  rfl'

private theorem leaf3948InnerLogValid :
    leaf3948InnerLog.Valid 8 (innerAD leaf3948Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3948CoverageChecked

private noncomputable def leaf3948InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629439/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3948InputLogOnePlusV_eq :
    leaf3948InputLogOnePlusV = outerEnclosure 24
      (leaf3948Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3948RoundedFacts : LeafRoundedFacts 8
    leaf3948Certificate.logOnePlusV leaf3948InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3948InputLogOnePlusV_eq }

private noncomputable def leaf3948Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi253InputQChi innerPair100Input
    leaf3948InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3948LowerChecked :
    lowerCheck 24 leaf3948Box leaf3948Inputs = true := by
  rfl'

private theorem leaf3948CoversExact : CoversExact 8
    leaf3948Box leaf3948Certificate leaf3948InnerLog leaf3948Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi253RoundedFacts
    innerPair100RoundedFacts leaf3948RoundedFacts (by rfl)

private theorem leaf3948FlatSound : Sound leaf3948Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3948CertificateValid
    leaf3948InnerLogValid leaf3948CoversExact leaf3948LowerChecked

private noncomputable def leaf3949Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf3949Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435717/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905157632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (516113389/268435456) }, upper := { exponent := 0, mantissa := (4003/2048) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811322197/45810315264) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf3949InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3949LocalValidity :
    LeafFacts leaf3949Box leaf3949Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3949Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905157632) }) = true
      norm_num [leaf3949Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3949CertificateValid :
    WideCertificateValid leaf3949Box leaf3949Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi254ValidityFacts
    leaf3949LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3949CoverageChecked :
    coverageCheck (innerAD leaf3949Box) leaf3949InnerLog = true := by
  rfl'

private theorem leaf3949InnerLogValid :
    leaf3949InnerLog.Valid 8 (innerAD leaf3949Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3949CoverageChecked

private noncomputable def leaf3949InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814725/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3949InputLogOnePlusV_eq :
    leaf3949InputLogOnePlusV = outerEnclosure 24
      (leaf3949Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3949RoundedFacts : LeafRoundedFacts 8
    leaf3949Certificate.logOnePlusV leaf3949InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3949InputLogOnePlusV_eq }

private noncomputable def leaf3949Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi254InputQChi innerPair101Input
    leaf3949InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3949LowerChecked :
    lowerCheck 24 leaf3949Box leaf3949Inputs = true := by
  rfl'

private theorem leaf3949CoversExact : CoversExact 8
    leaf3949Box leaf3949Certificate leaf3949InnerLog leaf3949Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi254RoundedFacts
    innerPair101RoundedFacts leaf3949RoundedFacts (by rfl)

private theorem leaf3949FlatSound : Sound leaf3949Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3949CertificateValid
    leaf3949InnerLogValid leaf3949CoversExact leaf3949LowerChecked

private noncomputable def leaf3950Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf3950Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435717/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715513856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (513492109/268435456) }, upper := { exponent := 0, mantissa := (3983/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434007551/137431027712) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf3950InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3950LocalValidity :
    LeafFacts leaf3950Box leaf3950Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3950Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715513856) }) = true
      norm_num [leaf3950Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3950CertificateValid :
    WideCertificateValid leaf3950Box leaf3950Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi253ValidityFacts
    leaf3950LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3950CoverageChecked :
    coverageCheck (innerAD leaf3950Box) leaf3950InnerLog = true := by
  rfl'

private theorem leaf3950InnerLogValid :
    leaf3950InnerLog.Valid 8 (innerAD leaf3950Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3950CoverageChecked

private noncomputable def leaf3950InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3950InputLogOnePlusV_eq :
    leaf3950InputLogOnePlusV = outerEnclosure 24
      (leaf3950Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3950RoundedFacts : LeafRoundedFacts 8
    leaf3950Certificate.logOnePlusV leaf3950InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3950InputLogOnePlusV_eq }

private noncomputable def leaf3950Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi253InputQChi innerPair101Input
    leaf3950InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3950LowerChecked :
    lowerCheck 24 leaf3950Box leaf3950Inputs = true := by
  rfl'

private theorem leaf3950CoversExact : CoversExact 8
    leaf3950Box leaf3950Certificate leaf3950InnerLog leaf3950Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi253RoundedFacts
    innerPair101RoundedFacts leaf3950RoundedFacts (by rfl)

private theorem leaf3950FlatSound : Sound leaf3950Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3950CertificateValid
    leaf3950InnerLogValid leaf3950CoversExact leaf3950LowerChecked

private noncomputable def leaf3951Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf3951Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435719/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715425792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (519062327/268435456) }, upper := { exponent := 0, mantissa := (2013/1024) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137433919487/137430851584) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf3951InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3951LocalValidity :
    LeafFacts leaf3951Box leaf3951Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3951Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715425792) }) = true
      norm_num [leaf3951Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3951CertificateValid :
    WideCertificateValid leaf3951Box leaf3951Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi254ValidityFacts
    leaf3951LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3951CoverageChecked :
    coverageCheck (innerAD leaf3951Box) leaf3951InnerLog = true := by
  rfl'

private theorem leaf3951InnerLogValid :
    leaf3951InnerLog.Valid 8 (innerAD leaf3951Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3951CoverageChecked

private noncomputable def leaf3951InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629455/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3951InputLogOnePlusV_eq :
    leaf3951InputLogOnePlusV = outerEnclosure 24
      (leaf3951Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3951RoundedFacts : LeafRoundedFacts 8
    leaf3951Certificate.logOnePlusV leaf3951InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3951InputLogOnePlusV_eq }

private noncomputable def leaf3951Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi254InputQChi innerPair101Input
    leaf3951InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3951LowerChecked :
    lowerCheck 24 leaf3951Box leaf3951Inputs = true := by
  rfl'

private theorem leaf3951CoversExact : CoversExact 8
    leaf3951Box leaf3951Certificate leaf3951InnerLog leaf3951Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi254RoundedFacts
    innerPair101RoundedFacts leaf3951RoundedFacts (by rfl)

private theorem leaf3951FlatSound : Sound leaf3951Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3951CertificateValid
    leaf3951InnerLogValid leaf3951CoversExact leaf3951LowerChecked

private noncomputable def leaf3952Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3952Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217945/134217728) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357649408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (260792569/134217728) }, upper := { exponent := 0, mantissa := (511/256) } }, logOuter := sk105LogOuterCertificate, logK := sk105LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716371967/68715298816) } }, logDArg := sk105LogDArgCertificate }

private noncomputable def leaf3952InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf3952LocalValidity :
    LeafFacts leaf3952Box leaf3952Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3952Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357649408) }) = true
      norm_num [leaf3952Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3952CertificateValid :
    WideCertificateValid leaf3952Box leaf3952Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk105ValidityFacts chi61ValidityFacts
    leaf3952LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3952CoverageChecked :
    coverageCheck (innerAD leaf3952Box) leaf3952InnerLog = true := by
  rfl'

private theorem leaf3952InnerLogValid :
    leaf3952InnerLog.Valid 8 (innerAD leaf3952Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf3952CoverageChecked

private noncomputable def leaf3952InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3952InputLogOnePlusV_eq :
    leaf3952InputLogOnePlusV = outerEnclosure 24
      (leaf3952Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3952RoundedFacts : LeafRoundedFacts 8
    leaf3952Certificate.logOnePlusV leaf3952InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3952InputLogOnePlusV_eq }

private noncomputable def leaf3952Inputs : Inputs :=
  inputsOfCaches globalInput sk105RoundedInputs
    chi61InputQChi innerPair108Input
    leaf3952InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3952LowerChecked :
    lowerCheck 24 leaf3952Box leaf3952Inputs = true := by
  rfl'

private theorem leaf3952CoversExact : CoversExact 8
    leaf3952Box leaf3952Certificate leaf3952InnerLog leaf3952Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk105RoundedFacts chi61RoundedFacts
    innerPair108RoundedFacts leaf3952RoundedFacts (by rfl)

private theorem leaf3952FlatSound : Sound leaf3952Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3952CertificateValid
    leaf3952InnerLogValid leaf3952CoversExact leaf3952LowerChecked

private noncomputable def leaf3953Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf3953Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435721/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357668864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (524632545/268435456) }, upper := { exponent := 0, mantissa := (4069/2048) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716391423/68715337728) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf3953InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf3953LocalValidity :
    LeafFacts leaf3953Box leaf3953Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3953Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357668864) }) = true
      norm_num [leaf3953Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3953CertificateValid :
    WideCertificateValid leaf3953Box leaf3953Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi255ValidityFacts
    leaf3953LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3953CoverageChecked :
    coverageCheck (innerAD leaf3953Box) leaf3953InnerLog = true := by
  rfl'

private theorem leaf3953InnerLogValid :
    leaf3953InnerLog.Valid 8 (innerAD leaf3953Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf3953CoverageChecked

private noncomputable def leaf3953InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814669/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3953InputLogOnePlusV_eq :
    leaf3953InputLogOnePlusV = outerEnclosure 24
      (leaf3953Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3953RoundedFacts : LeafRoundedFacts 8
    leaf3953Certificate.logOnePlusV leaf3953InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3953InputLogOnePlusV_eq }

private noncomputable def leaf3953Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi255InputQChi innerPair108Input
    leaf3953InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3953LowerChecked :
    lowerCheck 24 leaf3953Box leaf3953Inputs = true := by
  rfl'

private theorem leaf3953CoversExact : CoversExact 8
    leaf3953Box leaf3953Certificate leaf3953InnerLog leaf3953Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi255RoundedFacts
    innerPair108RoundedFacts leaf3953RoundedFacts (by rfl)

private theorem leaf3953FlatSound : Sound leaf3953Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3953CertificateValid
    leaf3953InnerLogValid leaf3953CoversExact leaf3953LowerChecked

private noncomputable def leaf3954Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf3954Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435723/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357624832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (530202763/268435456) }, upper := { exponent := 1, mantissa := (257/256) } }, logOuter := sk106LogOuterCertificate, logK := sk106LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716347391/68715249664) } }, logDArg := sk106LogDArgCertificate }

private noncomputable def leaf3954InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3954LocalValidity :
    LeafFacts leaf3954Box leaf3954Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3954Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357624832) }) = true
      norm_num [leaf3954Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3954CertificateValid :
    WideCertificateValid leaf3954Box leaf3954Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk106ValidityFacts chi256ValidityFacts
    leaf3954LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3954CoverageChecked :
    coverageCheck (innerAD leaf3954Box) leaf3954InnerLog = true := by
  rfl'

private theorem leaf3954InnerLogValid :
    leaf3954InnerLog.Valid 8 (innerAD leaf3954Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3954CoverageChecked

private noncomputable def leaf3954InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3954InputLogOnePlusV_eq :
    leaf3954InputLogOnePlusV = outerEnclosure 24
      (leaf3954Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3954RoundedFacts : LeafRoundedFacts 8
    leaf3954Certificate.logOnePlusV leaf3954InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3954InputLogOnePlusV_eq }

private noncomputable def leaf3954Inputs : Inputs :=
  inputsOfCaches globalInput sk106RoundedInputs
    chi256InputQChi innerPair110Input
    leaf3954InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3954LowerChecked :
    lowerCheck 24 leaf3954Box leaf3954Inputs = true := by
  rfl'

private theorem leaf3954CoversExact : CoversExact 8
    leaf3954Box leaf3954Certificate leaf3954InnerLog leaf3954Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk106RoundedFacts chi256RoundedFacts
    innerPair110RoundedFacts leaf3954RoundedFacts (by rfl)

private theorem leaf3954FlatSound : Sound leaf3954Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3954CertificateValid
    leaf3954InnerLogValid leaf3954CoversExact leaf3954LowerChecked

private noncomputable def leaf3955Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf3955Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435719/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715467776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (516375515/268435456) }, upper := { exponent := 0, mantissa := (8011/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137433961471/137430935552) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf3955InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3955LocalValidity :
    LeafFacts leaf3955Box leaf3955Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3955Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715467776) }) = true
      norm_num [leaf3955Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3955CertificateValid :
    WideCertificateValid leaf3955Box leaf3955Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi253ValidityFacts
    leaf3955LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3955CoverageChecked :
    coverageCheck (innerAD leaf3955Box) leaf3955InnerLog = true := by
  rfl'

private theorem leaf3955InnerLogValid :
    leaf3955InnerLog.Valid 8 (innerAD leaf3955Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3955CoverageChecked

private noncomputable def leaf3955InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814725/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3955InputLogOnePlusV_eq :
    leaf3955InputLogOnePlusV = outerEnclosure 24
      (leaf3955Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3955RoundedFacts : LeafRoundedFacts 8
    leaf3955Certificate.logOnePlusV leaf3955InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3955InputLogOnePlusV_eq }

private noncomputable def leaf3955Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi253InputQChi innerPair101Input
    leaf3955InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3955LowerChecked :
    lowerCheck 24 leaf3955Box leaf3955Inputs = true := by
  rfl'

private theorem leaf3955CoversExact : CoversExact 8
    leaf3955Box leaf3955Certificate leaf3955InnerLog leaf3955Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi253RoundedFacts
    innerPair101RoundedFacts leaf3955RoundedFacts (by rfl)

private theorem leaf3955FlatSound : Sound leaf3955Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3955CertificateValid
    leaf3955InnerLogValid leaf3955CoversExact leaf3955LowerChecked

private noncomputable def leaf3956Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf3956Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435721/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715378688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (522011265/268435456) }, upper := { exponent := 0, mantissa := (4049/2048) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137433872383/137430757376) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf3956InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf3956LocalValidity :
    LeafFacts leaf3956Box leaf3956Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3956Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715378688) }) = true
      norm_num [leaf3956Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3956CertificateValid :
    WideCertificateValid leaf3956Box leaf3956Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi254ValidityFacts
    leaf3956LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3956CoverageChecked :
    coverageCheck (innerAD leaf3956Box) leaf3956InnerLog = true := by
  rfl'

private theorem leaf3956InnerLogValid :
    leaf3956InnerLog.Valid 8 (innerAD leaf3956Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf3956CoverageChecked

private noncomputable def leaf3956InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3956InputLogOnePlusV_eq :
    leaf3956InputLogOnePlusV = outerEnclosure 24
      (leaf3956Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3956RoundedFacts : LeafRoundedFacts 8
    leaf3956Certificate.logOnePlusV leaf3956InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3956InputLogOnePlusV_eq }

private noncomputable def leaf3956Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi254InputQChi innerPair108Input
    leaf3956InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3956LowerChecked :
    lowerCheck 24 leaf3956Box leaf3956Inputs = true := by
  rfl'

private theorem leaf3956CoversExact : CoversExact 8
    leaf3956Box leaf3956Certificate leaf3956InnerLog leaf3956Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi254RoundedFacts
    innerPair108RoundedFacts leaf3956RoundedFacts (by rfl)

private theorem leaf3956FlatSound : Sound leaf3956Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3956CertificateValid
    leaf3956InnerLogValid leaf3956CoversExact leaf3956LowerChecked

private noncomputable def leaf3957Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (11/32), chiHi := (45/128) }

private noncomputable def leaf3957Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435721/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715421696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (519258921/268435456) }, upper := { exponent := 0, mantissa := (1007/512) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi253LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137433915391/137430843392) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf3957InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf3957LocalValidity :
    LeafFacts leaf3957Box leaf3957Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3957Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715421696) }) = true
      norm_num [leaf3957Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3957CertificateValid :
    WideCertificateValid leaf3957Box leaf3957Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi253ValidityFacts
    leaf3957LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3957CoverageChecked :
    coverageCheck (innerAD leaf3957Box) leaf3957InnerLog = true := by
  rfl'

private theorem leaf3957InnerLogValid :
    leaf3957InnerLog.Valid 8 (innerAD leaf3957Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf3957CoverageChecked

private noncomputable def leaf3957InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3957InputLogOnePlusV_eq :
    leaf3957InputLogOnePlusV = outerEnclosure 24
      (leaf3957Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3957RoundedFacts : LeafRoundedFacts 8
    leaf3957Certificate.logOnePlusV leaf3957InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3957InputLogOnePlusV_eq }

private noncomputable def leaf3957Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi253InputQChi innerPair101Input
    leaf3957InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3957LowerChecked :
    lowerCheck 24 leaf3957Box leaf3957Inputs = true := by
  rfl'

private theorem leaf3957CoversExact : CoversExact 8
    leaf3957Box leaf3957Certificate leaf3957InnerLog leaf3957Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi253RoundedFacts
    innerPair101RoundedFacts leaf3957RoundedFacts (by rfl)

private theorem leaf3957FlatSound : Sound leaf3957Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3957CertificateValid
    leaf3957InnerLogValid leaf3957CoversExact leaf3957LowerChecked

private noncomputable def leaf3958Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (45/128), chiHi := (23/64) }

private noncomputable def leaf3958Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435723/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357665792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (524960203/268435456) }, upper := { exponent := 0, mantissa := (509/256) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi254LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716388351/68715331584) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf3958InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf3958LocalValidity :
    LeafFacts leaf3958Box leaf3958Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3958Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357665792) }) = true
      norm_num [leaf3958Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3958CertificateValid :
    WideCertificateValid leaf3958Box leaf3958Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi254ValidityFacts
    leaf3958LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3958CoverageChecked :
    coverageCheck (innerAD leaf3958Box) leaf3958InnerLog = true := by
  rfl'

private theorem leaf3958InnerLogValid :
    leaf3958InnerLog.Valid 8 (innerAD leaf3958Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf3958CoverageChecked

private noncomputable def leaf3958InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629339/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3958InputLogOnePlusV_eq :
    leaf3958InputLogOnePlusV = outerEnclosure 24
      (leaf3958Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3958RoundedFacts : LeafRoundedFacts 8
    leaf3958Certificate.logOnePlusV leaf3958InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3958InputLogOnePlusV_eq }

private noncomputable def leaf3958Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi254InputQChi innerPair108Input
    leaf3958InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3958LowerChecked :
    lowerCheck 24 leaf3958Box leaf3958Inputs = true := by
  rfl'

private theorem leaf3958CoversExact : CoversExact 8
    leaf3958Box leaf3958Certificate leaf3958InnerLog leaf3958Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi254RoundedFacts
    innerPair108RoundedFacts leaf3958RoundedFacts (by rfl)

private theorem leaf3958FlatSound : Sound leaf3958Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3958CertificateValid
    leaf3958InnerLogValid leaf3958CoversExact leaf3958LowerChecked

private noncomputable def leaf3959Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf3959Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435723/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357644800) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (527647015/268435456) }, upper := { exponent := 0, mantissa := (8185/4096) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716367359/68715289600) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf3959InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf3959LocalValidity :
    LeafFacts leaf3959Box leaf3959Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3959Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357644800) }) = true
      norm_num [leaf3959Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3959CertificateValid :
    WideCertificateValid leaf3959Box leaf3959Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi255ValidityFacts
    leaf3959LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3959CoverageChecked :
    coverageCheck (innerAD leaf3959Box) leaf3959InnerLog = true := by
  rfl'

private theorem leaf3959InnerLogValid :
    leaf3959InnerLog.Valid 8 (innerAD leaf3959Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf3959CoverageChecked

private noncomputable def leaf3959InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf3959InputLogOnePlusV_eq :
    leaf3959InputLogOnePlusV = outerEnclosure 24
      (leaf3959Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3959RoundedFacts : LeafRoundedFacts 8
    leaf3959Certificate.logOnePlusV leaf3959InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3959InputLogOnePlusV_eq }

private noncomputable def leaf3959Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi255InputQChi innerPair108Input
    leaf3959InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3959LowerChecked :
    lowerCheck 24 leaf3959Box leaf3959Inputs = true := by
  rfl'

private theorem leaf3959CoversExact : CoversExact 8
    leaf3959Box leaf3959Certificate leaf3959InnerLog leaf3959Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi255RoundedFacts
    innerPair108RoundedFacts leaf3959RoundedFacts (by rfl)

private theorem leaf3959FlatSound : Sound leaf3959Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3959CertificateValid
    leaf3959InnerLogValid leaf3959CoversExact leaf3959LowerChecked

private noncomputable def leaf3960Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf3960Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435725/268435456) }, vSqrt := { lower := (32765/32768), upper := (4908388937/4908228608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (533282765/268435456) }, upper := { exponent := 1, mantissa := (517/512) } }, logOuter := sk103LogOuterCertificate, logK := sk103LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9816617545/9816457216) } }, logDArg := sk103LogDArgCertificate }

private noncomputable def leaf3960InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3960LocalValidity :
    LeafFacts leaf3960Box leaf3960Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3960Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4908388937/4908228608) }) = true
      norm_num [leaf3960Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3960CertificateValid :
    WideCertificateValid leaf3960Box leaf3960Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk103ValidityFacts chi256ValidityFacts
    leaf3960LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3960CoverageChecked :
    coverageCheck (innerAD leaf3960Box) leaf3960InnerLog = true := by
  rfl'

private theorem leaf3960InnerLogValid :
    leaf3960InnerLog.Valid 8 (innerAD leaf3960Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3960CoverageChecked

private noncomputable def leaf3960InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3960InputLogOnePlusV_eq :
    leaf3960InputLogOnePlusV = outerEnclosure 24
      (leaf3960Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3960RoundedFacts : LeafRoundedFacts 8
    leaf3960Certificate.logOnePlusV leaf3960InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3960InputLogOnePlusV_eq }

private noncomputable def leaf3960Inputs : Inputs :=
  inputsOfCaches globalInput sk103RoundedInputs
    chi256InputQChi innerPair110Input
    leaf3960InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3960LowerChecked :
    lowerCheck 24 leaf3960Box leaf3960Inputs = true := by
  rfl'

private theorem leaf3960CoversExact : CoversExact 8
    leaf3960Box leaf3960Certificate leaf3960InnerLog leaf3960Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk103RoundedFacts chi256RoundedFacts
    innerPair110RoundedFacts leaf3960RoundedFacts (by rfl)

private theorem leaf3960FlatSound : Sound leaf3960Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3960CertificateValid
    leaf3960InnerLogValid leaf3960CoversExact leaf3960LowerChecked

private noncomputable def leaf3961Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (23/64), chiHi := (47/128) }

private noncomputable def leaf3961Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435725/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357620736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (530661485/268435456) }, upper := { exponent := 1, mantissa := (1029/1024) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi255LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716343295/68715241472) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf3961InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3961LocalValidity :
    LeafFacts leaf3961Box leaf3961Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3961Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357620736) }) = true
      norm_num [leaf3961Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3961CertificateValid :
    WideCertificateValid leaf3961Box leaf3961Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi255ValidityFacts
    leaf3961LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3961CoverageChecked :
    coverageCheck (innerAD leaf3961Box) leaf3961InnerLog = true := by
  rfl'

private theorem leaf3961InnerLogValid :
    leaf3961InnerLog.Valid 8 (innerAD leaf3961Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3961CoverageChecked

private noncomputable def leaf3961InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3961InputLogOnePlusV_eq :
    leaf3961InputLogOnePlusV = outerEnclosure 24
      (leaf3961Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3961RoundedFacts : LeafRoundedFacts 8
    leaf3961Certificate.logOnePlusV leaf3961InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3961InputLogOnePlusV_eq }

private noncomputable def leaf3961Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi255InputQChi innerPair110Input
    leaf3961InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3961LowerChecked :
    lowerCheck 24 leaf3961Box leaf3961Inputs = true := by
  rfl'

private theorem leaf3961CoversExact : CoversExact 8
    leaf3961Box leaf3961Certificate leaf3961InnerLog leaf3961Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi255RoundedFacts
    innerPair110RoundedFacts leaf3961RoundedFacts (by rfl)

private theorem leaf3961FlatSound : Sound leaf3961Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3961CertificateValid
    leaf3961InnerLogValid leaf3961CoversExact leaf3961LowerChecked

private noncomputable def leaf3962Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (47/128), chiHi := (3/8) }

private noncomputable def leaf3962Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (268435727/268435456) }, vSqrt := { lower := (32765/32768), upper := (34358722559/34357575680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (536362767/268435456) }, upper := { exponent := 1, mantissa := (65/64) } }, logOuter := sk104LogOuterCertificate, logK := sk104LogKCertificate, logChi := chi256LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68716298239/68715151360) } }, logDArg := sk104LogDArgCertificate }

private noncomputable def leaf3962InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf3962LocalValidity :
    LeafFacts leaf3962Box leaf3962Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3962Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358722559/34357575680) }) = true
      norm_num [leaf3962Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3962CertificateValid :
    WideCertificateValid leaf3962Box leaf3962Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk104ValidityFacts chi256ValidityFacts
    leaf3962LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3962CoverageChecked :
    coverageCheck (innerAD leaf3962Box) leaf3962InnerLog = true := by
  rfl'

private theorem leaf3962InnerLogValid :
    leaf3962InnerLog.Valid 8 (innerAD leaf3962Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf3962CoverageChecked

private noncomputable def leaf3962InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3962InputLogOnePlusV_eq :
    leaf3962InputLogOnePlusV = outerEnclosure 24
      (leaf3962Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3962RoundedFacts : LeafRoundedFacts 8
    leaf3962Certificate.logOnePlusV leaf3962InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3962InputLogOnePlusV_eq }

private noncomputable def leaf3962Inputs : Inputs :=
  inputsOfCaches globalInput sk104RoundedInputs
    chi256InputQChi innerPair110Input
    leaf3962InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3962LowerChecked :
    lowerCheck 24 leaf3962Box leaf3962Inputs = true := by
  rfl'

private theorem leaf3962CoversExact : CoversExact 8
    leaf3962Box leaf3962Certificate leaf3962InnerLog leaf3962Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk104RoundedFacts chi256RoundedFacts
    innerPair110RoundedFacts leaf3962RoundedFacts (by rfl)

private theorem leaf3962FlatSound : Sound leaf3962Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3962CertificateValid
    leaf3962InnerLogValid leaf3962CoversExact leaf3962LowerChecked

private noncomputable def component80Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (81/32), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node0_sound : Sound component80Node0Box :=
  sound_of_literal_split component80Node0Box leaf3910Box leaf3911Box
    .chi (41/128) (by rfl) (by rfl)
    leaf3910FlatSound leaf3911FlatSound

private noncomputable def component80Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (81/32), kHi := (41/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node1_sound : Sound component80Node1Box :=
  sound_of_literal_split component80Node1Box leaf3912Box leaf3913Box
    .chi (41/128) (by rfl) (by rfl)
    leaf3912FlatSound leaf3913FlatSound

private noncomputable def component80Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node2_sound : Sound component80Node2Box :=
  sound_of_literal_split component80Node2Box component80Node0Box component80Node1Box
    .k (81/32) (by rfl) (by rfl)
    component80Node0_sound component80Node1_sound

private noncomputable def component80Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component80Node3_sound : Sound component80Node3Box :=
  sound_of_literal_split component80Node3Box leaf3914Box leaf3915Box
    .k (81/32) (by rfl) (by rfl)
    leaf3914FlatSound leaf3915FlatSound

private noncomputable def component80Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component80Node4_sound : Sound component80Node4Box :=
  sound_of_literal_split component80Node4Box component80Node2Box component80Node3Box
    .chi (21/64) (by rfl) (by rfl)
    component80Node2_sound component80Node3_sound

private noncomputable def component80Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node5_sound : Sound component80Node5Box :=
  sound_of_literal_split component80Node5Box leaf3916Box leaf3917Box
    .chi (41/128) (by rfl) (by rfl)
    leaf3916FlatSound leaf3917FlatSound

private noncomputable def component80Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node6_sound : Sound component80Node6Box :=
  sound_of_literal_split component80Node6Box leaf3918Box leaf3919Box
    .chi (41/128) (by rfl) (by rfl)
    leaf3918FlatSound leaf3919FlatSound

private noncomputable def component80Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node7_sound : Sound component80Node7Box :=
  sound_of_literal_split component80Node7Box component80Node5Box component80Node6Box
    .k (83/32) (by rfl) (by rfl)
    component80Node5_sound component80Node6_sound

private noncomputable def component80Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (83/32), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component80Node8_sound : Sound component80Node8Box :=
  sound_of_literal_split component80Node8Box leaf3920Box leaf3921Box
    .chi (43/128) (by rfl) (by rfl)
    leaf3920FlatSound leaf3921FlatSound

private noncomputable def component80Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (83/32), kHi := (21/8), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component80Node9_sound : Sound component80Node9Box :=
  sound_of_literal_split component80Node9Box leaf3922Box leaf3923Box
    .chi (43/128) (by rfl) (by rfl)
    leaf3922FlatSound leaf3923FlatSound

private noncomputable def component80Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component80Node10_sound : Sound component80Node10Box :=
  sound_of_literal_split component80Node10Box component80Node8Box component80Node9Box
    .k (83/32) (by rfl) (by rfl)
    component80Node8_sound component80Node9_sound

private noncomputable def component80Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component80Node11_sound : Sound component80Node11Box :=
  sound_of_literal_split component80Node11Box component80Node7Box component80Node10Box
    .chi (21/64) (by rfl) (by rfl)
    component80Node7_sound component80Node10_sound

private noncomputable def component80Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component80Node12_sound : Sound component80Node12Box :=
  sound_of_literal_split component80Node12Box component80Node4Box component80Node11Box
    .k (41/16) (by rfl) (by rfl)
    component80Node4_sound component80Node11_sound

private noncomputable def component80Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node13_sound : Sound component80Node13Box :=
  sound_of_literal_split component80Node13Box leaf3924Box leaf3925Box
    .k (81/32) (by rfl) (by rfl)
    leaf3924FlatSound leaf3925FlatSound

private noncomputable def component80Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component80Node14_sound : Sound component80Node14Box :=
  sound_of_literal_split component80Node14Box leaf3926Box leaf3927Box
    .k (81/32) (by rfl) (by rfl)
    leaf3926FlatSound leaf3927FlatSound

private noncomputable def component80Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (41/16), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component80Node15_sound : Sound component80Node15Box :=
  sound_of_literal_split component80Node15Box component80Node13Box component80Node14Box
    .chi (23/64) (by rfl) (by rfl)
    component80Node13_sound component80Node14_sound

private noncomputable def component80Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node16_sound : Sound component80Node16Box :=
  sound_of_literal_split component80Node16Box leaf3928Box leaf3929Box
    .k (83/32) (by rfl) (by rfl)
    leaf3928FlatSound leaf3929FlatSound

private noncomputable def component80Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component80Node17_sound : Sound component80Node17Box :=
  sound_of_literal_split component80Node17Box leaf3930Box leaf3931Box
    .k (83/32) (by rfl) (by rfl)
    leaf3930FlatSound leaf3931FlatSound

private noncomputable def component80Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (41/16), kHi := (21/8), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component80Node18_sound : Sound component80Node18Box :=
  sound_of_literal_split component80Node18Box component80Node16Box component80Node17Box
    .chi (23/64) (by rfl) (by rfl)
    component80Node16_sound component80Node17_sound

private noncomputable def component80Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component80Node19_sound : Sound component80Node19Box :=
  sound_of_literal_split component80Node19Box component80Node15Box component80Node18Box
    .k (41/16) (by rfl) (by rfl)
    component80Node15_sound component80Node18_sound

private noncomputable def component80Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (21/8), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component80Node20_sound : Sound component80Node20Box :=
  sound_of_literal_split component80Node20Box component80Node12Box component80Node19Box
    .chi (11/32) (by rfl) (by rfl)
    component80Node12_sound component80Node19_sound

private noncomputable def component80Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node21_sound : Sound component80Node21Box :=
  sound_of_literal_split component80Node21Box leaf3932Box leaf3933Box
    .chi (41/128) (by rfl) (by rfl)
    leaf3932FlatSound leaf3933FlatSound

private noncomputable def component80Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node22_sound : Sound component80Node22Box :=
  sound_of_literal_split component80Node22Box leaf3934Box leaf3935Box
    .chi (41/128) (by rfl) (by rfl)
    leaf3934FlatSound leaf3935FlatSound

private noncomputable def component80Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node23_sound : Sound component80Node23Box :=
  sound_of_literal_split component80Node23Box component80Node21Box component80Node22Box
    .k (85/32) (by rfl) (by rfl)
    component80Node21_sound component80Node22_sound

private noncomputable def component80Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component80Node24_sound : Sound component80Node24Box :=
  sound_of_literal_split component80Node24Box leaf3936Box leaf3937Box
    .chi (43/128) (by rfl) (by rfl)
    leaf3936FlatSound leaf3937FlatSound

private noncomputable def component80Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component80Node25_sound : Sound component80Node25Box :=
  sound_of_literal_split component80Node25Box leaf3938Box leaf3939Box
    .chi (43/128) (by rfl) (by rfl)
    leaf3938FlatSound leaf3939FlatSound

private noncomputable def component80Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component80Node26_sound : Sound component80Node26Box :=
  sound_of_literal_split component80Node26Box component80Node24Box component80Node25Box
    .k (85/32) (by rfl) (by rfl)
    component80Node24_sound component80Node25_sound

private noncomputable def component80Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component80Node27_sound : Sound component80Node27Box :=
  sound_of_literal_split component80Node27Box component80Node23Box component80Node26Box
    .chi (21/64) (by rfl) (by rfl)
    component80Node23_sound component80Node26_sound

private noncomputable def component80Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node28_sound : Sound component80Node28Box :=
  sound_of_literal_split component80Node28Box leaf3940Box leaf3941Box
    .chi (41/128) (by rfl) (by rfl)
    leaf3940FlatSound leaf3941FlatSound

private noncomputable def component80Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node29_sound : Sound component80Node29Box :=
  sound_of_literal_split component80Node29Box leaf3942Box leaf3943Box
    .chi (41/128) (by rfl) (by rfl)
    leaf3942FlatSound leaf3943FlatSound

private noncomputable def component80Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node30_sound : Sound component80Node30Box :=
  sound_of_literal_split component80Node30Box component80Node28Box component80Node29Box
    .k (87/32) (by rfl) (by rfl)
    component80Node28_sound component80Node29_sound

private noncomputable def component80Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component80Node31_sound : Sound component80Node31Box :=
  sound_of_literal_split component80Node31Box leaf3944Box leaf3945Box
    .chi (43/128) (by rfl) (by rfl)
    leaf3944FlatSound leaf3945FlatSound

private noncomputable def component80Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component80Node32_sound : Sound component80Node32Box :=
  sound_of_literal_split component80Node32Box leaf3946Box leaf3947Box
    .chi (43/128) (by rfl) (by rfl)
    leaf3946FlatSound leaf3947FlatSound

private noncomputable def component80Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component80Node33_sound : Sound component80Node33Box :=
  sound_of_literal_split component80Node33Box component80Node31Box component80Node32Box
    .k (87/32) (by rfl) (by rfl)
    component80Node31_sound component80Node32_sound

private noncomputable def component80Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component80Node34_sound : Sound component80Node34Box :=
  sound_of_literal_split component80Node34Box component80Node30Box component80Node33Box
    .chi (21/64) (by rfl) (by rfl)
    component80Node30_sound component80Node33_sound

private noncomputable def component80Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component80Node35_sound : Sound component80Node35Box :=
  sound_of_literal_split component80Node35Box component80Node27Box component80Node34Box
    .k (43/16) (by rfl) (by rfl)
    component80Node27_sound component80Node34_sound

private noncomputable def component80Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (85/32), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node36_sound : Sound component80Node36Box :=
  sound_of_literal_split component80Node36Box leaf3948Box leaf3949Box
    .chi (45/128) (by rfl) (by rfl)
    leaf3948FlatSound leaf3949FlatSound

private noncomputable def component80Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node37_sound : Sound component80Node37Box :=
  sound_of_literal_split component80Node37Box leaf3950Box leaf3951Box
    .chi (45/128) (by rfl) (by rfl)
    leaf3950FlatSound leaf3951FlatSound

private noncomputable def component80Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node38_sound : Sound component80Node38Box :=
  sound_of_literal_split component80Node38Box component80Node36Box component80Node37Box
    .k (85/32) (by rfl) (by rfl)
    component80Node36_sound component80Node37_sound

private noncomputable def component80Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (85/32), kHi := (43/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component80Node39_sound : Sound component80Node39Box :=
  sound_of_literal_split component80Node39Box leaf3953Box leaf3954Box
    .chi (47/128) (by rfl) (by rfl)
    leaf3953FlatSound leaf3954FlatSound

private noncomputable def component80Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component80Node40_sound : Sound component80Node40Box :=
  sound_of_literal_split component80Node40Box leaf3952Box component80Node39Box
    .k (85/32) (by rfl) (by rfl)
    leaf3952FlatSound component80Node39_sound

private noncomputable def component80Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (43/16), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component80Node41_sound : Sound component80Node41Box :=
  sound_of_literal_split component80Node41Box component80Node38Box component80Node40Box
    .chi (23/64) (by rfl) (by rfl)
    component80Node38_sound component80Node40_sound

private noncomputable def component80Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node42_sound : Sound component80Node42Box :=
  sound_of_literal_split component80Node42Box leaf3955Box leaf3956Box
    .chi (45/128) (by rfl) (by rfl)
    leaf3955FlatSound leaf3956FlatSound

private noncomputable def component80Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node43_sound : Sound component80Node43Box :=
  sound_of_literal_split component80Node43Box leaf3957Box leaf3958Box
    .chi (45/128) (by rfl) (by rfl)
    leaf3957FlatSound leaf3958FlatSound

private noncomputable def component80Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component80Node44_sound : Sound component80Node44Box :=
  sound_of_literal_split component80Node44Box component80Node42Box component80Node43Box
    .k (87/32) (by rfl) (by rfl)
    component80Node42_sound component80Node43_sound

private noncomputable def component80Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (87/32), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component80Node45_sound : Sound component80Node45Box :=
  sound_of_literal_split component80Node45Box leaf3959Box leaf3960Box
    .chi (47/128) (by rfl) (by rfl)
    leaf3959FlatSound leaf3960FlatSound

private noncomputable def component80Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (87/32), kHi := (11/4), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component80Node46_sound : Sound component80Node46Box :=
  sound_of_literal_split component80Node46Box leaf3961Box leaf3962Box
    .chi (47/128) (by rfl) (by rfl)
    leaf3961FlatSound leaf3962FlatSound

private noncomputable def component80Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component80Node47_sound : Sound component80Node47Box :=
  sound_of_literal_split component80Node47Box component80Node45Box component80Node46Box
    .k (87/32) (by rfl) (by rfl)
    component80Node45_sound component80Node46_sound

private noncomputable def component80Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (43/16), kHi := (11/4), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component80Node48_sound : Sound component80Node48Box :=
  sound_of_literal_split component80Node48Box component80Node44Box component80Node47Box
    .chi (23/64) (by rfl) (by rfl)
    component80Node44_sound component80Node47_sound

private noncomputable def component80Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component80Node49_sound : Sound component80Node49Box :=
  sound_of_literal_split component80Node49Box component80Node41Box component80Node48Box
    .k (43/16) (by rfl) (by rfl)
    component80Node41_sound component80Node48_sound

private noncomputable def component80Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/8), kHi := (11/4), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component80Node50_sound : Sound component80Node50Box :=
  sound_of_literal_split component80Node50Box component80Node35Box component80Node49Box
    .chi (11/32) (by rfl) (by rfl)
    component80Node35_sound component80Node49_sound

noncomputable def component80Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/2), kHi := (11/4), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
theorem component80_sound : Sound component80Box :=
  sound_of_literal_split component80Box component80Node20Box component80Node50Box
    .k (21/8) (by rfl) (by rfl)
    component80Node20_sound component80Node50_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
