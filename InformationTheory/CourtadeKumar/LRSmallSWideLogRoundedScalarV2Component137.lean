import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch12
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch13
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch2

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

private noncomputable def leaf6735Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (5/8), chiHi := (81/128) }

private noncomputable def leaf6735Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217995/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588835584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (406797815/268435456) }, upper := { exponent := 1, mantissa := (6341/4096) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi349LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178262271/17177671168) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6735InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6735LocalValidity :
    LeafFacts leaf6735Box leaf6735Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6735Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588835584) }) = true
      norm_num [leaf6735Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6735CertificateValid :
    WideCertificateValid leaf6735Box leaf6735Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi349ValidityFacts
    leaf6735LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6735CoverageChecked :
    coverageCheck (innerAD leaf6735Box) leaf6735InnerLog = true := by
  rfl'

private theorem leaf6735InnerLogValid :
    leaf6735InnerLog.Valid 8 (innerAD leaf6735Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6735CoverageChecked

private noncomputable def leaf6735InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814829/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6735InputLogOnePlusV_eq :
    leaf6735InputLogOnePlusV = outerEnclosure 24
      (leaf6735Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6735RoundedFacts : LeafRoundedFacts 8
    leaf6735Certificate.logOnePlusV leaf6735InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6735InputLogOnePlusV_eq }

private noncomputable def leaf6735Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi349InputQChi innerPair382Input
    leaf6735InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6735LowerChecked :
    lowerCheck 24 leaf6735Box leaf6735Inputs = true := by
  rfl'

private theorem leaf6735CoversExact : CoversExact 8
    leaf6735Box leaf6735Certificate leaf6735InnerLog leaf6735Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi349RoundedFacts
    innerPair382RoundedFacts leaf6735RoundedFacts (by rfl)

private theorem leaf6735FlatSound : Sound leaf6735Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6735CertificateValid
    leaf6735InnerLogValid leaf6735CoversExact leaf6735LowerChecked

private noncomputable def leaf6736Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (81/128), chiHi := (41/64) }

private noncomputable def leaf6736Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217997/134217728) }, vSqrt := { lower := (65529/65536), upper := (2863142229/2862940672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (410205477/268435456) }, upper := { exponent := 1, mantissa := (3197/2048) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi350LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5726082901/5725881344) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6736InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6736LocalValidity :
    LeafFacts leaf6736Box leaf6736Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6736Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2863142229/2862940672) }) = true
      norm_num [leaf6736Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6736CertificateValid :
    WideCertificateValid leaf6736Box leaf6736Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi350ValidityFacts
    leaf6736LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6736CoverageChecked :
    coverageCheck (innerAD leaf6736Box) leaf6736InnerLog = true := by
  rfl'

private theorem leaf6736InnerLogValid :
    leaf6736InnerLog.Valid 8 (innerAD leaf6736Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6736CoverageChecked

private noncomputable def leaf6736InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629671/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6736InputLogOnePlusV_eq :
    leaf6736InputLogOnePlusV = outerEnclosure 24
      (leaf6736Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6736RoundedFacts : LeafRoundedFacts 8
    leaf6736Certificate.logOnePlusV leaf6736InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6736InputLogOnePlusV_eq }

private noncomputable def leaf6736Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi350InputQChi innerPair382Input
    leaf6736InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6736LowerChecked :
    lowerCheck 24 leaf6736Box leaf6736Inputs = true := by
  rfl'

private theorem leaf6736CoversExact : CoversExact 8
    leaf6736Box leaf6736Certificate leaf6736InnerLog leaf6736Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi350RoundedFacts
    innerPair382RoundedFacts leaf6736RoundedFacts (by rfl)

private theorem leaf6736FlatSound : Sound leaf6736Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6736CertificateValid
    leaf6736InnerLogValid leaf6736CoversExact leaf6736LowerChecked

private noncomputable def leaf6737Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (5/8), chiHi := (81/128) }

private noncomputable def leaf6737Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217997/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588814848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (412040373/268435456) }, upper := { exponent := 1, mantissa := (3211/2048) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi349LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178241535/17177629696) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6737InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6737LocalValidity :
    LeafFacts leaf6737Box leaf6737Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6737Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588814848) }) = true
      norm_num [leaf6737Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6737CertificateValid :
    WideCertificateValid leaf6737Box leaf6737Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi349ValidityFacts
    leaf6737LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6737CoverageChecked :
    coverageCheck (innerAD leaf6737Box) leaf6737InnerLog = true := by
  rfl'

private theorem leaf6737InnerLogValid :
    leaf6737InnerLog.Valid 8 (innerAD leaf6737Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6737CoverageChecked

private noncomputable def leaf6737InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814839/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6737InputLogOnePlusV_eq :
    leaf6737InputLogOnePlusV = outerEnclosure 24
      (leaf6737Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6737RoundedFacts : LeafRoundedFacts 8
    leaf6737Certificate.logOnePlusV leaf6737InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6737InputLogOnePlusV_eq }

private noncomputable def leaf6737Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi349InputQChi innerPair744Input
    leaf6737InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6737LowerChecked :
    lowerCheck 24 leaf6737Box leaf6737Inputs = true := by
  rfl'

private theorem leaf6737CoversExact : CoversExact 8
    leaf6737Box leaf6737Certificate leaf6737InnerLog leaf6737Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi349RoundedFacts
    innerPair744RoundedFacts leaf6737RoundedFacts (by rfl)

private theorem leaf6737FlatSound : Sound leaf6737Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6737CertificateValid
    leaf6737InnerLogValid leaf6737CoversExact leaf6737LowerChecked

private noncomputable def leaf6738Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (81/128), chiHi := (41/64) }

private noncomputable def leaf6738Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217999/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588801024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (415513567/268435456) }, upper := { exponent := 1, mantissa := (1619/1024) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi350LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178227711/17177602048) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6738InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6738LocalValidity :
    LeafFacts leaf6738Box leaf6738Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6738Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588801024) }) = true
      norm_num [leaf6738Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6738CertificateValid :
    WideCertificateValid leaf6738Box leaf6738Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi350ValidityFacts
    leaf6738LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6738CoverageChecked :
    coverageCheck (innerAD leaf6738Box) leaf6738InnerLog = true := by
  rfl'

private theorem leaf6738InnerLogValid :
    leaf6738InnerLog.Valid 8 (innerAD leaf6738Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6738CoverageChecked

private noncomputable def leaf6738InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907423/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6738InputLogOnePlusV_eq :
    leaf6738InputLogOnePlusV = outerEnclosure 24
      (leaf6738Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6738RoundedFacts : LeafRoundedFacts 8
    leaf6738Certificate.logOnePlusV leaf6738InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6738InputLogOnePlusV_eq }

private noncomputable def leaf6738Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi350InputQChi innerPair744Input
    leaf6738InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6738LowerChecked :
    lowerCheck 24 leaf6738Box leaf6738Inputs = true := by
  rfl'

private theorem leaf6738CoversExact : CoversExact 8
    leaf6738Box leaf6738Certificate leaf6738InnerLog leaf6738Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi350RoundedFacts
    innerPair744RoundedFacts leaf6738RoundedFacts (by rfl)

private theorem leaf6738FlatSound : Sound leaf6738Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6738CertificateValid
    leaf6738InnerLogValid leaf6738CoversExact leaf6738LowerChecked

private noncomputable def leaf6739Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6739Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109053/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588794880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (206790133/134217728) }, upper := { exponent := 1, mantissa := (1625/1024) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178221567/17177589760) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6739InnerLog : WideLogData :=
  innerPair833Data

set_option maxRecDepth 1000000 in
private theorem leaf6739LocalValidity :
    LeafFacts leaf6739Box leaf6739Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6739Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588794880) }) = true
      norm_num [leaf6739Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6739CertificateValid :
    WideCertificateValid leaf6739Box leaf6739Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi324ValidityFacts
    leaf6739LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6739CoverageChecked :
    coverageCheck (innerAD leaf6739Box) leaf6739InnerLog = true := by
  rfl'

private theorem leaf6739InnerLogValid :
    leaf6739InnerLog.Valid 8 (innerAD leaf6739Box) :=
  wideLogDataValid_of_cachedCheck endpoint527PositiveFacts
    endpoint531PositiveFacts.valid leaf6739CoverageChecked

private noncomputable def leaf6739InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814849/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6739InputLogOnePlusV_eq :
    leaf6739InputLogOnePlusV = outerEnclosure 24
      (leaf6739Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6739RoundedFacts : LeafRoundedFacts 8
    leaf6739Certificate.logOnePlusV leaf6739InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6739InputLogOnePlusV_eq }

private noncomputable def leaf6739Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi324InputQChi innerPair833Input
    leaf6739InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6739LowerChecked :
    lowerCheck 24 leaf6739Box leaf6739Inputs = true := by
  rfl'

private theorem leaf6739CoversExact : CoversExact 8
    leaf6739Box leaf6739Certificate leaf6739InnerLog leaf6739Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi324RoundedFacts
    innerPair833RoundedFacts leaf6739RoundedFacts (by rfl)

private theorem leaf6739FlatSound : Sound leaf6739Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6739CertificateValid
    leaf6739InnerLogValid leaf6739CoversExact leaf6739LowerChecked

private noncomputable def leaf6740Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (41/64), chiHi := (83/128) }

private noncomputable def leaf6740Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218001/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588787200) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (418986761/268435456) }, upper := { exponent := 1, mantissa := (3265/2048) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi351LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178213887/17177574400) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6740InnerLog : WideLogData :=
  innerPair745Data

set_option maxRecDepth 1000000 in
private theorem leaf6740LocalValidity :
    LeafFacts leaf6740Box leaf6740Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6740Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588787200) }) = true
      norm_num [leaf6740Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6740CertificateValid :
    WideCertificateValid leaf6740Box leaf6740Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi351ValidityFacts
    leaf6740LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6740CoverageChecked :
    coverageCheck (innerAD leaf6740Box) leaf6740InnerLog = true := by
  rfl'

private theorem leaf6740InnerLogValid :
    leaf6740InnerLog.Valid 8 (innerAD leaf6740Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint485PositiveFacts.valid leaf6740CoverageChecked

private noncomputable def leaf6740InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629705/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6740InputLogOnePlusV_eq :
    leaf6740InputLogOnePlusV = outerEnclosure 24
      (leaf6740Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6740RoundedFacts : LeafRoundedFacts 8
    leaf6740Certificate.logOnePlusV leaf6740InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6740InputLogOnePlusV_eq }

private noncomputable def leaf6740Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi351InputQChi innerPair745Input
    leaf6740InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6740LowerChecked :
    lowerCheck 24 leaf6740Box leaf6740Inputs = true := by
  rfl'

private theorem leaf6740CoversExact : CoversExact 8
    leaf6740Box leaf6740Certificate leaf6740InnerLog leaf6740Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi351RoundedFacts
    innerPair745RoundedFacts leaf6740RoundedFacts (by rfl)

private theorem leaf6740FlatSound : Sound leaf6740Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6740CertificateValid
    leaf6740InnerLogValid leaf6740CoversExact leaf6740LowerChecked

private noncomputable def leaf6741Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (83/128), chiHi := (21/32) }

private noncomputable def leaf6741Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218003/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588773376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (422459955/268435456) }, upper := { exponent := 1, mantissa := (823/512) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi352LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178200063/17177546752) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6741InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6741LocalValidity :
    LeafFacts leaf6741Box leaf6741Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6741Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588773376) }) = true
      norm_num [leaf6741Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6741CertificateValid :
    WideCertificateValid leaf6741Box leaf6741Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi352ValidityFacts
    leaf6741LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6741CoverageChecked :
    coverageCheck (innerAD leaf6741Box) leaf6741InnerLog = true := by
  rfl'

private theorem leaf6741InnerLogValid :
    leaf6741InnerLog.Valid 8 (innerAD leaf6741Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6741CoverageChecked

private noncomputable def leaf6741InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629719/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6741InputLogOnePlusV_eq :
    leaf6741InputLogOnePlusV = outerEnclosure 24
      (leaf6741Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6741RoundedFacts : LeafRoundedFacts 8
    leaf6741Certificate.logOnePlusV leaf6741InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6741InputLogOnePlusV_eq }

private noncomputable def leaf6741Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi352InputQChi innerPair749Input
    leaf6741InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6741LowerChecked :
    lowerCheck 24 leaf6741Box leaf6741Inputs = true := by
  rfl'

private theorem leaf6741CoversExact : CoversExact 8
    leaf6741Box leaf6741Certificate leaf6741InnerLog leaf6741Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi352RoundedFacts
    innerPair749RoundedFacts leaf6741RoundedFacts (by rfl)

private theorem leaf6741FlatSound : Sound leaf6741Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6741CertificateValid
    leaf6741InnerLogValid leaf6741CoversExact leaf6741LowerChecked

private noncomputable def leaf6742Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6742Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109055/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588767744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (210197795/134217728) }, upper := { exponent := 1, mantissa := (3303/2048) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178194431/17177535488) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6742InnerLog : WideLogData :=
  innerPair753Data

set_option maxRecDepth 1000000 in
private theorem leaf6742LocalValidity :
    LeafFacts leaf6742Box leaf6742Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6742Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588767744) }) = true
      norm_num [leaf6742Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6742CertificateValid :
    WideCertificateValid leaf6742Box leaf6742Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi325ValidityFacts
    leaf6742LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6742CoverageChecked :
    coverageCheck (innerAD leaf6742Box) leaf6742InnerLog = true := by
  rfl'

private theorem leaf6742InnerLogValid :
    leaf6742InnerLog.Valid 8 (innerAD leaf6742Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint496PositiveFacts.valid leaf6742CoverageChecked

private noncomputable def leaf6742InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907431/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6742InputLogOnePlusV_eq :
    leaf6742InputLogOnePlusV = outerEnclosure 24
      (leaf6742Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6742RoundedFacts : LeafRoundedFacts 8
    leaf6742Certificate.logOnePlusV leaf6742InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6742InputLogOnePlusV_eq }

private noncomputable def leaf6742Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi325InputQChi innerPair753Input
    leaf6742InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6742LowerChecked :
    lowerCheck 24 leaf6742Box leaf6742Inputs = true := by
  rfl'

private theorem leaf6742CoversExact : CoversExact 8
    leaf6742Box leaf6742Certificate leaf6742InnerLog leaf6742Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi325RoundedFacts
    innerPair753RoundedFacts leaf6742RoundedFacts (by rfl)

private theorem leaf6742FlatSound : Sound leaf6742Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6742CertificateValid
    leaf6742InnerLogValid leaf6742CoversExact leaf6742LowerChecked

private noncomputable def leaf6743Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6743Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109057/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588745728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (212950137/134217728) }, upper := { exponent := 1, mantissa := (1673/1024) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178172415/17177491456) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6743InnerLog : WideLogData :=
  innerPair837Data

set_option maxRecDepth 1000000 in
private theorem leaf6743LocalValidity :
    LeafFacts leaf6743Box leaf6743Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6743Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588745728) }) = true
      norm_num [leaf6743Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6743CertificateValid :
    WideCertificateValid leaf6743Box leaf6743Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi325ValidityFacts
    leaf6743LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6743CoverageChecked :
    coverageCheck (innerAD leaf6743Box) leaf6743InnerLog = true := by
  rfl'

private theorem leaf6743InnerLogValid :
    leaf6743InnerLog.Valid 8 (innerAD leaf6743Box) :=
  wideLogDataValid_of_cachedCheck endpoint532PositiveFacts
    endpoint533PositiveFacts.valid leaf6743CoverageChecked

private noncomputable def leaf6743InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814873/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6743InputLogOnePlusV_eq :
    leaf6743InputLogOnePlusV = outerEnclosure 24
      (leaf6743Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6743RoundedFacts : LeafRoundedFacts 8
    leaf6743Certificate.logOnePlusV leaf6743InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6743InputLogOnePlusV_eq }

private noncomputable def leaf6743Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi325InputQChi innerPair837Input
    leaf6743InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6743LowerChecked :
    lowerCheck 24 leaf6743Box leaf6743Inputs = true := by
  rfl'

private theorem leaf6743CoversExact : CoversExact 8
    leaf6743Box leaf6743Certificate leaf6743InnerLog leaf6743Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi325RoundedFacts
    innerPair837RoundedFacts leaf6743RoundedFacts (by rfl)

private theorem leaf6743FlatSound : Sound leaf6743Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6743CertificateValid
    leaf6743InnerLogValid leaf6743CoversExact leaf6743LowerChecked

private noncomputable def leaf6744Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6744Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109057/67108864) }, vSqrt := { lower := (65529/65536), upper := (954380743/954304512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (213605457/134217728) }, upper := { exponent := 1, mantissa := (839/512) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1908685255/1908609024) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6744InnerLog : WideLogData :=
  innerPair838Data

set_option maxRecDepth 1000000 in
private theorem leaf6744LocalValidity :
    LeafFacts leaf6744Box leaf6744Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6744Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (954380743/954304512) }) = true
      norm_num [leaf6744Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6744CertificateValid :
    WideCertificateValid leaf6744Box leaf6744Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi326ValidityFacts
    leaf6744LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6744CoverageChecked :
    coverageCheck (innerAD leaf6744Box) leaf6744InnerLog = true := by
  rfl'

private theorem leaf6744InnerLogValid :
    leaf6744InnerLog.Valid 8 (innerAD leaf6744Box) :=
  wideLogDataValid_of_cachedCheck endpoint532PositiveFacts
    endpoint534PositiveFacts.valid leaf6744CoverageChecked

private noncomputable def leaf6744InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629751/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6744InputLogOnePlusV_eq :
    leaf6744InputLogOnePlusV = outerEnclosure 24
      (leaf6744Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6744RoundedFacts : LeafRoundedFacts 8
    leaf6744Certificate.logOnePlusV leaf6744InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6744InputLogOnePlusV_eq }

private noncomputable def leaf6744Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi326InputQChi innerPair838Input
    leaf6744InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6744LowerChecked :
    lowerCheck 24 leaf6744Box leaf6744Inputs = true := by
  rfl'

private theorem leaf6744CoversExact : CoversExact 8
    leaf6744Box leaf6744Certificate leaf6744InnerLog leaf6744Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi326RoundedFacts
    innerPair838RoundedFacts leaf6744RoundedFacts (by rfl)

private theorem leaf6744FlatSound : Sound leaf6744Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6744CertificateValid
    leaf6744InnerLogValid leaf6744CoversExact leaf6744LowerChecked

private noncomputable def leaf6745Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6745Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109059/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588718080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (216423331/134217728) }, upper := { exponent := 1, mantissa := (425/256) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178144767/17177436160) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6745InnerLog : WideLogData :=
  innerPair841Data

set_option maxRecDepth 1000000 in
private theorem leaf6745LocalValidity :
    LeafFacts leaf6745Box leaf6745Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6745Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588718080) }) = true
      norm_num [leaf6745Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6745CertificateValid :
    WideCertificateValid leaf6745Box leaf6745Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi326ValidityFacts
    leaf6745LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6745CoverageChecked :
    coverageCheck (innerAD leaf6745Box) leaf6745InnerLog = true := by
  rfl'

private theorem leaf6745InnerLogValid :
    leaf6745InnerLog.Valid 8 (innerAD leaf6745Box) :=
  wideLogDataValid_of_cachedCheck endpoint535PositiveFacts
    endpoint536PositiveFacts.valid leaf6745CoverageChecked

private noncomputable def leaf6745InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629773/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6745InputLogOnePlusV_eq :
    leaf6745InputLogOnePlusV = outerEnclosure 24
      (leaf6745Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6745RoundedFacts : LeafRoundedFacts 8
    leaf6745Certificate.logOnePlusV leaf6745InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6745InputLogOnePlusV_eq }

private noncomputable def leaf6745Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi326InputQChi innerPair841Input
    leaf6745InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6745LowerChecked :
    lowerCheck 24 leaf6745Box leaf6745Inputs = true := by
  rfl'

private theorem leaf6745CoversExact : CoversExact 8
    leaf6745Box leaf6745Certificate leaf6745InnerLog leaf6745Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi326RoundedFacts
    innerPair841RoundedFacts leaf6745RoundedFacts (by rfl)

private theorem leaf6745FlatSound : Sound leaf6745Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6745CertificateValid
    leaf6745InnerLogValid leaf6745CoversExact leaf6745LowerChecked

private noncomputable def leaf6746Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (5/8), chiHi := (81/128) }

private noncomputable def leaf6746Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217999/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588794112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (417282931/268435456) }, upper := { exponent := 1, mantissa := (6503/4096) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi349LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178220799/17177588224) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6746InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6746LocalValidity :
    LeafFacts leaf6746Box leaf6746Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6746Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588794112) }) = true
      norm_num [leaf6746Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6746CertificateValid :
    WideCertificateValid leaf6746Box leaf6746Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi349ValidityFacts
    leaf6746LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6746CoverageChecked :
    coverageCheck (innerAD leaf6746Box) leaf6746InnerLog = true := by
  rfl'

private theorem leaf6746InnerLogValid :
    leaf6746InnerLog.Valid 8 (innerAD leaf6746Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6746CoverageChecked

private noncomputable def leaf6746InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629699/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6746InputLogOnePlusV_eq :
    leaf6746InputLogOnePlusV = outerEnclosure 24
      (leaf6746Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6746RoundedFacts : LeafRoundedFacts 8
    leaf6746Certificate.logOnePlusV leaf6746InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6746InputLogOnePlusV_eq }

private noncomputable def leaf6746Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi349InputQChi innerPair744Input
    leaf6746InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6746LowerChecked :
    lowerCheck 24 leaf6746Box leaf6746Inputs = true := by
  rfl'

private theorem leaf6746CoversExact : CoversExact 8
    leaf6746Box leaf6746Certificate leaf6746InnerLog leaf6746Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi349RoundedFacts
    innerPair744RoundedFacts leaf6746RoundedFacts (by rfl)

private theorem leaf6746FlatSound : Sound leaf6746Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6746CertificateValid
    leaf6746InnerLogValid leaf6746CoversExact leaf6746LowerChecked

private noncomputable def leaf6747Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (81/128), chiHi := (41/64) }

private noncomputable def leaf6747Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218001/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588780032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (420821657/268435456) }, upper := { exponent := 1, mantissa := (3279/2048) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi350LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178206719/17177560064) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6747InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6747LocalValidity :
    LeafFacts leaf6747Box leaf6747Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6747Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588780032) }) = true
      norm_num [leaf6747Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6747CertificateValid :
    WideCertificateValid leaf6747Box leaf6747Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi350ValidityFacts
    leaf6747LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6747CoverageChecked :
    coverageCheck (innerAD leaf6747Box) leaf6747InnerLog = true := by
  rfl'

private theorem leaf6747InnerLogValid :
    leaf6747InnerLog.Valid 8 (innerAD leaf6747Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6747CoverageChecked

private noncomputable def leaf6747InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726857/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6747InputLogOnePlusV_eq :
    leaf6747InputLogOnePlusV = outerEnclosure 24
      (leaf6747Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6747RoundedFacts : LeafRoundedFacts 8
    leaf6747Certificate.logOnePlusV leaf6747InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6747InputLogOnePlusV_eq }

private noncomputable def leaf6747Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi350InputQChi innerPair749Input
    leaf6747InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6747LowerChecked :
    lowerCheck 24 leaf6747Box leaf6747Inputs = true := by
  rfl'

private theorem leaf6747CoversExact : CoversExact 8
    leaf6747Box leaf6747Certificate leaf6747InnerLog leaf6747Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi350RoundedFacts
    innerPair749RoundedFacts leaf6747RoundedFacts (by rfl)

private theorem leaf6747FlatSound : Sound leaf6747Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6747CertificateValid
    leaf6747InnerLogValid leaf6747CoversExact leaf6747LowerChecked

private noncomputable def leaf6748Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (5/8), chiHi := (81/128) }

private noncomputable def leaf6748Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218001/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588773376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (422525489/268435456) }, upper := { exponent := 1, mantissa := (823/512) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi349LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178200063/17177546752) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6748InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6748LocalValidity :
    LeafFacts leaf6748Box leaf6748Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6748Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588773376) }) = true
      norm_num [leaf6748Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6748CertificateValid :
    WideCertificateValid leaf6748Box leaf6748Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi349ValidityFacts
    leaf6748LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6748CoverageChecked :
    coverageCheck (innerAD leaf6748Box) leaf6748InnerLog = true := by
  rfl'

private theorem leaf6748InnerLogValid :
    leaf6748InnerLog.Valid 8 (innerAD leaf6748Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6748CoverageChecked

private noncomputable def leaf6748InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629719/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6748InputLogOnePlusV_eq :
    leaf6748InputLogOnePlusV = outerEnclosure 24
      (leaf6748Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6748RoundedFacts : LeafRoundedFacts 8
    leaf6748Certificate.logOnePlusV leaf6748InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6748InputLogOnePlusV_eq }

private noncomputable def leaf6748Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi349InputQChi innerPair749Input
    leaf6748InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6748LowerChecked :
    lowerCheck 24 leaf6748Box leaf6748Inputs = true := by
  rfl'

private theorem leaf6748CoversExact : CoversExact 8
    leaf6748Box leaf6748Certificate leaf6748InnerLog leaf6748Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi349RoundedFacts
    innerPair749RoundedFacts leaf6748RoundedFacts (by rfl)

private theorem leaf6748FlatSound : Sound leaf6748Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6748CertificateValid
    leaf6748InnerLogValid leaf6748CoversExact leaf6748LowerChecked

private noncomputable def leaf6749Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (81/128), chiHi := (41/64) }

private noncomputable def leaf6749Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218003/134217728) }, vSqrt := { lower := (8191/8192), upper := (954380743/954306560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (426129747/268435456) }, upper := { exponent := 1, mantissa := (415/256) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi350LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1908687303/1908613120) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6749InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6749LocalValidity :
    LeafFacts leaf6749Box leaf6749Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6749Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (954380743/954306560) }) = true
      norm_num [leaf6749Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6749CertificateValid :
    WideCertificateValid leaf6749Box leaf6749Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi350ValidityFacts
    leaf6749LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6749CoverageChecked :
    coverageCheck (innerAD leaf6749Box) leaf6749InnerLog = true := by
  rfl'

private theorem leaf6749InnerLogValid :
    leaf6749InnerLog.Valid 8 (innerAD leaf6749Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6749CoverageChecked

private noncomputable def leaf6749InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629733/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6749InputLogOnePlusV_eq :
    leaf6749InputLogOnePlusV = outerEnclosure 24
      (leaf6749Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6749RoundedFacts : LeafRoundedFacts 8
    leaf6749Certificate.logOnePlusV leaf6749InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6749InputLogOnePlusV_eq }

private noncomputable def leaf6749Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi350InputQChi innerPair749Input
    leaf6749InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6749LowerChecked :
    lowerCheck 24 leaf6749Box leaf6749Inputs = true := by
  rfl'

private theorem leaf6749CoversExact : CoversExact 8
    leaf6749Box leaf6749Certificate leaf6749InnerLog leaf6749Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi350RoundedFacts
    innerPair749RoundedFacts leaf6749RoundedFacts (by rfl)

private theorem leaf6749FlatSound : Sound leaf6749Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6749CertificateValid
    leaf6749InnerLogValid leaf6749CoversExact leaf6749LowerChecked

private noncomputable def leaf6750Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (41/64), chiHi := (83/128) }

private noncomputable def leaf6750Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218003/134217728) }, vSqrt := { lower := (65529/65536), upper := (954380743/954307328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (424360383/268435456) }, upper := { exponent := 1, mantissa := (6613/4096) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi351LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1908688071/1908614656) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6750InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6750LocalValidity :
    LeafFacts leaf6750Box leaf6750Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6750Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (954380743/954307328) }) = true
      norm_num [leaf6750Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6750CertificateValid :
    WideCertificateValid leaf6750Box leaf6750Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi351ValidityFacts
    leaf6750LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6750CoverageChecked :
    coverageCheck (innerAD leaf6750Box) leaf6750InnerLog = true := by
  rfl'

private theorem leaf6750InnerLogValid :
    leaf6750InnerLog.Valid 8 (innerAD leaf6750Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6750CoverageChecked

private noncomputable def leaf6750InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814863/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6750InputLogOnePlusV_eq :
    leaf6750InputLogOnePlusV = outerEnclosure 24
      (leaf6750Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6750RoundedFacts : LeafRoundedFacts 8
    leaf6750Certificate.logOnePlusV leaf6750InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6750InputLogOnePlusV_eq }

private noncomputable def leaf6750Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi351InputQChi innerPair749Input
    leaf6750InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6750LowerChecked :
    lowerCheck 24 leaf6750Box leaf6750Inputs = true := by
  rfl'

private theorem leaf6750CoversExact : CoversExact 8
    leaf6750Box leaf6750Certificate leaf6750InnerLog leaf6750Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi351RoundedFacts
    innerPair749RoundedFacts leaf6750RoundedFacts (by rfl)

private theorem leaf6750FlatSound : Sound leaf6750Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6750CertificateValid
    leaf6750InnerLogValid leaf6750CoversExact leaf6750LowerChecked

private noncomputable def leaf6751Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (83/128), chiHi := (21/32) }

private noncomputable def leaf6751Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218005/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588751872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (427899109/268435456) }, upper := { exponent := 1, mantissa := (1667/1024) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi352LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178178559/17177503744) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6751InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6751LocalValidity :
    LeafFacts leaf6751Box leaf6751Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6751Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588751872) }) = true
      norm_num [leaf6751Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6751CertificateValid :
    WideCertificateValid leaf6751Box leaf6751Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi352ValidityFacts
    leaf6751LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6751CoverageChecked :
    coverageCheck (innerAD leaf6751Box) leaf6751InnerLog = true := by
  rfl'

private theorem leaf6751InnerLogValid :
    leaf6751InnerLog.Valid 8 (innerAD leaf6751Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6751CoverageChecked

private noncomputable def leaf6751InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907435/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6751InputLogOnePlusV_eq :
    leaf6751InputLogOnePlusV = outerEnclosure 24
      (leaf6751Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6751RoundedFacts : LeafRoundedFacts 8
    leaf6751Certificate.logOnePlusV leaf6751InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6751InputLogOnePlusV_eq }

private noncomputable def leaf6751Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi352InputQChi innerPair755Input
    leaf6751InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6751LowerChecked :
    lowerCheck 24 leaf6751Box leaf6751Inputs = true := by
  rfl'

private theorem leaf6751CoversExact : CoversExact 8
    leaf6751Box leaf6751Certificate leaf6751InnerLog leaf6751Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi352RoundedFacts
    innerPair755RoundedFacts leaf6751RoundedFacts (by rfl)

private theorem leaf6751FlatSound : Sound leaf6751Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6751CertificateValid
    leaf6751InnerLogValid leaf6751CoversExact leaf6751LowerChecked

private noncomputable def leaf6752Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (41/64), chiHi := (83/128) }

private noncomputable def leaf6752Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218005/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588744704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (429734005/268435456) }, upper := { exponent := 1, mantissa := (837/512) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi351LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178171391/17177489408) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6752InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6752LocalValidity :
    LeafFacts leaf6752Box leaf6752Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6752Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588744704) }) = true
      norm_num [leaf6752Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6752CertificateValid :
    WideCertificateValid leaf6752Box leaf6752Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi351ValidityFacts
    leaf6752LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6752CoverageChecked :
    coverageCheck (innerAD leaf6752Box) leaf6752InnerLog = true := by
  rfl'

private theorem leaf6752InnerLogValid :
    leaf6752InnerLog.Valid 8 (innerAD leaf6752Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6752CoverageChecked

private noncomputable def leaf6752InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629747/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6752InputLogOnePlusV_eq :
    leaf6752InputLogOnePlusV = outerEnclosure 24
      (leaf6752Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6752RoundedFacts : LeafRoundedFacts 8
    leaf6752Certificate.logOnePlusV leaf6752InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6752InputLogOnePlusV_eq }

private noncomputable def leaf6752Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi351InputQChi innerPair755Input
    leaf6752InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6752LowerChecked :
    lowerCheck 24 leaf6752Box leaf6752Inputs = true := by
  rfl'

private theorem leaf6752CoversExact : CoversExact 8
    leaf6752Box leaf6752Certificate leaf6752InnerLog leaf6752Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi351RoundedFacts
    innerPair755RoundedFacts leaf6752RoundedFacts (by rfl)

private theorem leaf6752FlatSound : Sound leaf6752Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6752CertificateValid
    leaf6752InnerLogValid leaf6752CoversExact leaf6752LowerChecked

private noncomputable def leaf6753Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (83/128), chiHi := (21/32) }

private noncomputable def leaf6753Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218007/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588730368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (433338263/268435456) }, upper := { exponent := 1, mantissa := (211/128) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi352LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178157055/17177460736) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6753InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6753LocalValidity :
    LeafFacts leaf6753Box leaf6753Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6753Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588730368) }) = true
      norm_num [leaf6753Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6753CertificateValid :
    WideCertificateValid leaf6753Box leaf6753Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi352ValidityFacts
    leaf6753LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6753CoverageChecked :
    coverageCheck (innerAD leaf6753Box) leaf6753InnerLog = true := by
  rfl'

private theorem leaf6753InnerLogValid :
    leaf6753InnerLog.Valid 8 (innerAD leaf6753Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6753CoverageChecked

private noncomputable def leaf6753InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629761/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6753InputLogOnePlusV_eq :
    leaf6753InputLogOnePlusV = outerEnclosure 24
      (leaf6753Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6753RoundedFacts : LeafRoundedFacts 8
    leaf6753Certificate.logOnePlusV leaf6753InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6753InputLogOnePlusV_eq }

private noncomputable def leaf6753Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi352InputQChi innerPair755Input
    leaf6753InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6753LowerChecked :
    lowerCheck 24 leaf6753Box leaf6753Inputs = true := by
  rfl'

private theorem leaf6753CoversExact : CoversExact 8
    leaf6753Box leaf6753Certificate leaf6753InnerLog leaf6753Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi352RoundedFacts
    innerPair755RoundedFacts leaf6753RoundedFacts (by rfl)

private theorem leaf6753FlatSound : Sound leaf6753Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6753CertificateValid
    leaf6753InnerLogValid leaf6753CoversExact leaf6753LowerChecked

private noncomputable def leaf6754Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6754Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109059/67108864) }, vSqrt := { lower := (65529/65536), upper := (2863142229/2862907904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (215702479/134217728) }, upper := { exponent := 1, mantissa := (3389/2048) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5726050133/5725815808) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6754InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6754LocalValidity :
    LeafFacts leaf6754Box leaf6754Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6754Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2863142229/2862907904) }) = true
      norm_num [leaf6754Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6754CertificateValid :
    WideCertificateValid leaf6754Box leaf6754Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi325ValidityFacts
    leaf6754LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6754CoverageChecked :
    coverageCheck (innerAD leaf6754Box) leaf6754InnerLog = true := by
  rfl'

private theorem leaf6754InnerLogValid :
    leaf6754InnerLog.Valid 8 (innerAD leaf6754Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6754CoverageChecked

private noncomputable def leaf6754InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629767/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6754InputLogOnePlusV_eq :
    leaf6754InputLogOnePlusV = outerEnclosure 24
      (leaf6754Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6754RoundedFacts : LeafRoundedFacts 8
    leaf6754Certificate.logOnePlusV leaf6754InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6754InputLogOnePlusV_eq }

private noncomputable def leaf6754Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi325InputQChi innerPair755Input
    leaf6754InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6754LowerChecked :
    lowerCheck 24 leaf6754Box leaf6754Inputs = true := by
  rfl'

private theorem leaf6754CoversExact : CoversExact 8
    leaf6754Box leaf6754Certificate leaf6754InnerLog leaf6754Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi325RoundedFacts
    innerPair755RoundedFacts leaf6754RoundedFacts (by rfl)

private theorem leaf6754FlatSound : Sound leaf6754Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6754CertificateValid
    leaf6754InnerLogValid leaf6754CoversExact leaf6754LowerChecked

private noncomputable def leaf6755Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6755Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109061/67108864) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588701696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (218454821/134217728) }, upper := { exponent := 1, mantissa := (429/256) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178128383/17177403392) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6755InnerLog : WideLogData :=
  innerPair843Data

set_option maxRecDepth 1000000 in
private theorem leaf6755LocalValidity :
    LeafFacts leaf6755Box leaf6755Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6755Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588701696) }) = true
      norm_num [leaf6755Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6755CertificateValid :
    WideCertificateValid leaf6755Box leaf6755Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi325ValidityFacts
    leaf6755LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6755CoverageChecked :
    coverageCheck (innerAD leaf6755Box) leaf6755InnerLog = true := by
  rfl'

private theorem leaf6755InnerLogValid :
    leaf6755InnerLog.Valid 8 (innerAD leaf6755Box) :=
  wideLogDataValid_of_cachedCheck endpoint537PositiveFacts
    endpoint538PositiveFacts.valid leaf6755CoverageChecked

private noncomputable def leaf6755InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629789/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6755InputLogOnePlusV_eq :
    leaf6755InputLogOnePlusV = outerEnclosure 24
      (leaf6755Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6755RoundedFacts : LeafRoundedFacts 8
    leaf6755Certificate.logOnePlusV leaf6755InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6755InputLogOnePlusV_eq }

private noncomputable def leaf6755Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi325InputQChi innerPair843Input
    leaf6755InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6755LowerChecked :
    lowerCheck 24 leaf6755Box leaf6755Inputs = true := by
  rfl'

private theorem leaf6755CoversExact : CoversExact 8
    leaf6755Box leaf6755Certificate leaf6755InnerLog leaf6755Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi325RoundedFacts
    innerPair843RoundedFacts leaf6755RoundedFacts (by rfl)

private theorem leaf6755FlatSound : Sound leaf6755Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6755CertificateValid
    leaf6755InnerLogValid leaf6755CoversExact leaf6755LowerChecked

private noncomputable def leaf6756Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6756Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109061/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588695552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (219241205/134217728) }, upper := { exponent := 1, mantissa := (861/512) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178122239/17177391104) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6756InnerLog : WideLogData :=
  innerPair761Data

set_option maxRecDepth 1000000 in
private theorem leaf6756LocalValidity :
    LeafFacts leaf6756Box leaf6756Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6756Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588695552) }) = true
      norm_num [leaf6756Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6756CertificateValid :
    WideCertificateValid leaf6756Box leaf6756Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi326ValidityFacts
    leaf6756LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6756CoverageChecked :
    coverageCheck (innerAD leaf6756Box) leaf6756InnerLog = true := by
  rfl'

private theorem leaf6756InnerLogValid :
    leaf6756InnerLog.Valid 8 (innerAD leaf6756Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint487PositiveFacts.valid leaf6756CoverageChecked

private noncomputable def leaf6756InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629795/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6756InputLogOnePlusV_eq :
    leaf6756InputLogOnePlusV = outerEnclosure 24
      (leaf6756Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6756RoundedFacts : LeafRoundedFacts 8
    leaf6756Certificate.logOnePlusV leaf6756InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6756InputLogOnePlusV_eq }

private noncomputable def leaf6756Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi326InputQChi innerPair761Input
    leaf6756InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6756LowerChecked :
    lowerCheck 24 leaf6756Box leaf6756Inputs = true := by
  rfl'

private theorem leaf6756CoversExact : CoversExact 8
    leaf6756Box leaf6756Certificate leaf6756InnerLog leaf6756Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi326RoundedFacts
    innerPair761RoundedFacts leaf6756RoundedFacts (by rfl)

private theorem leaf6756FlatSound : Sound leaf6756Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6756CertificateValid
    leaf6756InnerLogValid leaf6756CoversExact leaf6756LowerChecked

private noncomputable def leaf6757Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6757Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109063/67108864) }, vSqrt := { lower := (8191/8192), upper := (2863142229/2862891008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (222059079/134217728) }, upper := { exponent := 1, mantissa := (109/64) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5726033237/5725782016) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6757InnerLog : WideLogData :=
  innerPair844Data

set_option maxRecDepth 1000000 in
private theorem leaf6757LocalValidity :
    LeafFacts leaf6757Box leaf6757Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6757Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2863142229/2862891008) }) = true
      norm_num [leaf6757Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6757CertificateValid :
    WideCertificateValid leaf6757Box leaf6757Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi326ValidityFacts
    leaf6757LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6757CoverageChecked :
    coverageCheck (innerAD leaf6757Box) leaf6757InnerLog = true := by
  rfl'

private theorem leaf6757InnerLogValid :
    leaf6757InnerLog.Valid 8 (innerAD leaf6757Box) :=
  wideLogDataValid_of_cachedCheck endpoint539PositiveFacts
    endpoint540PositiveFacts.valid leaf6757CoverageChecked

private noncomputable def leaf6757InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629817/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6757InputLogOnePlusV_eq :
    leaf6757InputLogOnePlusV = outerEnclosure 24
      (leaf6757Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6757RoundedFacts : LeafRoundedFacts 8
    leaf6757Certificate.logOnePlusV leaf6757InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6757InputLogOnePlusV_eq }

private noncomputable def leaf6757Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi326InputQChi innerPair844Input
    leaf6757InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6757LowerChecked :
    lowerCheck 24 leaf6757Box leaf6757Inputs = true := by
  rfl'

private theorem leaf6757CoversExact : CoversExact 8
    leaf6757Box leaf6757Certificate leaf6757InnerLog leaf6757Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi326RoundedFacts
    innerPair844RoundedFacts leaf6757RoundedFacts (by rfl)

private theorem leaf6757FlatSound : Sound leaf6757Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6757CertificateValid
    leaf6757InnerLogValid leaf6757CoversExact leaf6757LowerChecked

private noncomputable def leaf6758Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf6758Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109059/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588713472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (217013119/134217728) }, upper := { exponent := 1, mantissa := (3409/2048) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178140159/17177426944) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6758InnerLog : WideLogData :=
  innerPair840Data

set_option maxRecDepth 1000000 in
private theorem leaf6758LocalValidity :
    LeafFacts leaf6758Box leaf6758Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6758Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588713472) }) = true
      norm_num [leaf6758Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6758CertificateValid :
    WideCertificateValid leaf6758Box leaf6758Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi341ValidityFacts
    leaf6758LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6758CoverageChecked :
    coverageCheck (innerAD leaf6758Box) leaf6758InnerLog = true := by
  rfl'

private theorem leaf6758InnerLogValid :
    leaf6758InnerLog.Valid 8 (innerAD leaf6758Box) :=
  wideLogDataValid_of_cachedCheck endpoint535PositiveFacts
    endpoint495PositiveFacts.valid leaf6758CoverageChecked

private noncomputable def leaf6758InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629777/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6758InputLogOnePlusV_eq :
    leaf6758InputLogOnePlusV = outerEnclosure 24
      (leaf6758Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6758RoundedFacts : LeafRoundedFacts 8
    leaf6758Certificate.logOnePlusV leaf6758InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6758InputLogOnePlusV_eq }

private noncomputable def leaf6758Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi341InputQChi innerPair840Input
    leaf6758InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6758LowerChecked :
    lowerCheck 24 leaf6758Box leaf6758Inputs = true := by
  rfl'

private theorem leaf6758CoversExact : CoversExact 8
    leaf6758Box leaf6758Certificate leaf6758InnerLog leaf6758Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi341RoundedFacts
    innerPair840RoundedFacts leaf6758RoundedFacts (by rfl)

private theorem leaf6758FlatSound : Sound leaf6758Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6758CertificateValid
    leaf6758InnerLogValid leaf6758CoversExact leaf6758LowerChecked

private noncomputable def leaf6759Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf6759Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109061/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588690432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (219896525/134217728) }, upper := { exponent := 1, mantissa := (1727/1024) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178117119/17177380864) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6759InnerLog : WideLogData :=
  innerPair761Data

set_option maxRecDepth 1000000 in
private theorem leaf6759LocalValidity :
    LeafFacts leaf6759Box leaf6759Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6759Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588690432) }) = true
      norm_num [leaf6759Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6759CertificateValid :
    WideCertificateValid leaf6759Box leaf6759Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi341ValidityFacts
    leaf6759LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6759CoverageChecked :
    coverageCheck (innerAD leaf6759Box) leaf6759InnerLog = true := by
  rfl'

private theorem leaf6759InnerLogValid :
    leaf6759InnerLog.Valid 8 (innerAD leaf6759Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint487PositiveFacts.valid leaf6759CoverageChecked

private noncomputable def leaf6759InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453725/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6759InputLogOnePlusV_eq :
    leaf6759InputLogOnePlusV = outerEnclosure 24
      (leaf6759Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6759RoundedFacts : LeafRoundedFacts 8
    leaf6759Certificate.logOnePlusV leaf6759InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6759InputLogOnePlusV_eq }

private noncomputable def leaf6759Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi341InputQChi innerPair761Input
    leaf6759InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6759LowerChecked :
    lowerCheck 24 leaf6759Box leaf6759Inputs = true := by
  rfl'

private theorem leaf6759CoversExact : CoversExact 8
    leaf6759Box leaf6759Certificate leaf6759InnerLog leaf6759Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi341RoundedFacts
    innerPair761RoundedFacts leaf6759RoundedFacts (by rfl)

private theorem leaf6759FlatSound : Sound leaf6759Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6759CertificateValid
    leaf6759InnerLogValid leaf6759CoversExact leaf6759LowerChecked

private noncomputable def leaf6760Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf6760Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109061/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588686336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (220420781/134217728) }, upper := { exponent := 1, mantissa := (1731/1024) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178113023/17177372672) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6760InnerLog : WideLogData :=
  innerPair762Data

set_option maxRecDepth 1000000 in
private theorem leaf6760LocalValidity :
    LeafFacts leaf6760Box leaf6760Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6760Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588686336) }) = true
      norm_num [leaf6760Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6760CertificateValid :
    WideCertificateValid leaf6760Box leaf6760Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi342ValidityFacts
    leaf6760LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6760CoverageChecked :
    coverageCheck (innerAD leaf6760Box) leaf6760InnerLog = true := by
  rfl'

private theorem leaf6760InnerLogValid :
    leaf6760InnerLog.Valid 8 (innerAD leaf6760Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint488PositiveFacts.valid leaf6760CoverageChecked

private noncomputable def leaf6760InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907451/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6760InputLogOnePlusV_eq :
    leaf6760InputLogOnePlusV = outerEnclosure 24
      (leaf6760Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6760RoundedFacts : LeafRoundedFacts 8
    leaf6760Certificate.logOnePlusV leaf6760InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6760InputLogOnePlusV_eq }

private noncomputable def leaf6760Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi342InputQChi innerPair762Input
    leaf6760InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6760LowerChecked :
    lowerCheck 24 leaf6760Box leaf6760Inputs = true := by
  rfl'

private theorem leaf6760CoversExact : CoversExact 8
    leaf6760Box leaf6760Certificate leaf6760InnerLog leaf6760Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi342RoundedFacts
    innerPair762RoundedFacts leaf6760RoundedFacts (by rfl)

private theorem leaf6760FlatSound : Sound leaf6760Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6760CertificateValid
    leaf6760InnerLogValid leaf6760CoversExact leaf6760LowerChecked

private noncomputable def leaf6761Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf6761Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109063/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588662784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (223369719/134217728) }, upper := { exponent := 1, mantissa := (877/512) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178089471/17177325568) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6761InnerLog : WideLogData :=
  innerPair765Data

set_option maxRecDepth 1000000 in
private theorem leaf6761LocalValidity :
    LeafFacts leaf6761Box leaf6761Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6761Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588662784) }) = true
      norm_num [leaf6761Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6761CertificateValid :
    WideCertificateValid leaf6761Box leaf6761Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi342ValidityFacts
    leaf6761LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6761CoverageChecked :
    coverageCheck (innerAD leaf6761Box) leaf6761InnerLog = true := by
  rfl'

private theorem leaf6761InnerLogValid :
    leaf6761InnerLog.Valid 8 (innerAD leaf6761Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint488PositiveFacts.valid leaf6761CoverageChecked

private noncomputable def leaf6761InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629827/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6761InputLogOnePlusV_eq :
    leaf6761InputLogOnePlusV = outerEnclosure 24
      (leaf6761Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6761RoundedFacts : LeafRoundedFacts 8
    leaf6761Certificate.logOnePlusV leaf6761InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6761InputLogOnePlusV_eq }

private noncomputable def leaf6761Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi342InputQChi innerPair765Input
    leaf6761InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6761LowerChecked :
    lowerCheck 24 leaf6761Box leaf6761Inputs = true := by
  rfl'

private theorem leaf6761CoversExact : CoversExact 8
    leaf6761Box leaf6761Certificate leaf6761InnerLog leaf6761Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi342RoundedFacts
    innerPair765RoundedFacts leaf6761RoundedFacts (by rfl)

private theorem leaf6761FlatSound : Sound leaf6761Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6761CertificateValid
    leaf6761InnerLogValid leaf6761CoversExact leaf6761LowerChecked

private noncomputable def leaf6762Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf6762Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109063/67108864) }, vSqrt := { lower := (65529/65536), upper := (2863142229/2862886400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (223828443/134217728) }, upper := { exponent := 1, mantissa := (3515/2048) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5726028629/5725772800) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6762InnerLog : WideLogData :=
  innerPair765Data

set_option maxRecDepth 1000000 in
private theorem leaf6762LocalValidity :
    LeafFacts leaf6762Box leaf6762Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6762Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2863142229/2862886400) }) = true
      norm_num [leaf6762Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6762CertificateValid :
    WideCertificateValid leaf6762Box leaf6762Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi343ValidityFacts
    leaf6762LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6762CoverageChecked :
    coverageCheck (innerAD leaf6762Box) leaf6762InnerLog = true := by
  rfl'

private theorem leaf6762InnerLogValid :
    leaf6762InnerLog.Valid 8 (innerAD leaf6762Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint488PositiveFacts.valid leaf6762CoverageChecked

private noncomputable def leaf6762InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814915/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6762InputLogOnePlusV_eq :
    leaf6762InputLogOnePlusV = outerEnclosure 24
      (leaf6762Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6762RoundedFacts : LeafRoundedFacts 8
    leaf6762Certificate.logOnePlusV leaf6762InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6762InputLogOnePlusV_eq }

private noncomputable def leaf6762Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi343InputQChi innerPair765Input
    leaf6762InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6762LowerChecked :
    lowerCheck 24 leaf6762Box leaf6762Inputs = true := by
  rfl'

private theorem leaf6762CoversExact : CoversExact 8
    leaf6762Box leaf6762Certificate leaf6762InnerLog leaf6762Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi343RoundedFacts
    innerPair765RoundedFacts leaf6762RoundedFacts (by rfl)

private theorem leaf6762FlatSound : Sound leaf6762Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6762CertificateValid
    leaf6762InnerLogValid leaf6762CoversExact leaf6762LowerChecked

private noncomputable def leaf6763Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf6763Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109065/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354528256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (227236105/134217728) }, upper := { exponent := 1, mantissa := (223/128) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711710715/68709056512) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf6763InnerLog : WideLogData :=
  innerPair770Data

set_option maxRecDepth 1000000 in
private theorem leaf6763LocalValidity :
    LeafFacts leaf6763Box leaf6763Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6763Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354528256) }) = true
      norm_num [leaf6763Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6763CertificateValid :
    WideCertificateValid leaf6763Box leaf6763Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi344ValidityFacts
    leaf6763LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6763CoverageChecked :
    coverageCheck (innerAD leaf6763Box) leaf6763InnerLog = true := by
  rfl'

private theorem leaf6763InnerLogValid :
    leaf6763InnerLog.Valid 8 (innerAD leaf6763Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint489PositiveFacts.valid leaf6763CoverageChecked

private noncomputable def leaf6763InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629729/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6763InputLogOnePlusV_eq :
    leaf6763InputLogOnePlusV = outerEnclosure 24
      (leaf6763Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6763RoundedFacts : LeafRoundedFacts 8
    leaf6763Certificate.logOnePlusV leaf6763InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6763InputLogOnePlusV_eq }

private noncomputable def leaf6763Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi344InputQChi innerPair770Input
    leaf6763InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6763LowerChecked :
    lowerCheck 24 leaf6763Box leaf6763Inputs = true := by
  rfl'

private theorem leaf6763CoversExact : CoversExact 8
    leaf6763Box leaf6763Certificate leaf6763InnerLog leaf6763Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi344RoundedFacts
    innerPair770RoundedFacts leaf6763RoundedFacts (by rfl)

private theorem leaf6763FlatSound : Sound leaf6763Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6763CertificateValid
    leaf6763InnerLogValid leaf6763CoversExact leaf6763LowerChecked

private noncomputable def leaf6764Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf6764Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109065/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354540544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (226842913/134217728) }, upper := { exponent := 1, mantissa := (1781/1024) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711723003/68709081088) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6764InnerLog : WideLogData :=
  innerPair770Data

set_option maxRecDepth 1000000 in
private theorem leaf6764LocalValidity :
    LeafFacts leaf6764Box leaf6764Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6764Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354540544) }) = true
      norm_num [leaf6764Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6764CertificateValid :
    WideCertificateValid leaf6764Box leaf6764Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi343ValidityFacts
    leaf6764LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6764CoverageChecked :
    coverageCheck (innerAD leaf6764Box) leaf6764InnerLog = true := by
  rfl'

private theorem leaf6764InnerLogValid :
    leaf6764InnerLog.Valid 8 (innerAD leaf6764Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint489PositiveFacts.valid leaf6764CoverageChecked

private noncomputable def leaf6764InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814863/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6764InputLogOnePlusV_eq :
    leaf6764InputLogOnePlusV = outerEnclosure 24
      (leaf6764Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6764RoundedFacts : LeafRoundedFacts 8
    leaf6764Certificate.logOnePlusV leaf6764InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6764InputLogOnePlusV_eq }

private noncomputable def leaf6764Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi343InputQChi innerPair770Input
    leaf6764InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6764LowerChecked :
    lowerCheck 24 leaf6764Box leaf6764Inputs = true := by
  rfl'

private theorem leaf6764CoversExact : CoversExact 8
    leaf6764Box leaf6764Certificate leaf6764InnerLog leaf6764Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi343RoundedFacts
    innerPair770RoundedFacts leaf6764RoundedFacts (by rfl)

private theorem leaf6764FlatSound : Sound leaf6764Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6764CertificateValid
    leaf6764InnerLogValid leaf6764CoversExact leaf6764LowerChecked

private noncomputable def leaf6765Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf6765Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109067/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354429952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (230316107/134217728) }, upper := { exponent := 1, mantissa := (113/64) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711612411/68708859904) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf6765InnerLog : WideLogData :=
  innerPair771Data

set_option maxRecDepth 1000000 in
private theorem leaf6765LocalValidity :
    LeafFacts leaf6765Box leaf6765Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6765Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354429952) }) = true
      norm_num [leaf6765Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6765CertificateValid :
    WideCertificateValid leaf6765Box leaf6765Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi344ValidityFacts
    leaf6765LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6765CoverageChecked :
    coverageCheck (innerAD leaf6765Box) leaf6765InnerLog = true := by
  rfl'

private theorem leaf6765InnerLogValid :
    leaf6765InnerLog.Valid 8 (innerAD leaf6765Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint498PositiveFacts.valid leaf6765CoverageChecked

private noncomputable def leaf6765InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629753/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6765InputLogOnePlusV_eq :
    leaf6765InputLogOnePlusV = outerEnclosure 24
      (leaf6765Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6765RoundedFacts : LeafRoundedFacts 8
    leaf6765Certificate.logOnePlusV leaf6765InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6765InputLogOnePlusV_eq }

private noncomputable def leaf6765Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi344InputQChi innerPair771Input
    leaf6765InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6765LowerChecked :
    lowerCheck 24 leaf6765Box leaf6765Inputs = true := by
  rfl'

private theorem leaf6765CoversExact : CoversExact 8
    leaf6765Box leaf6765Certificate leaf6765InnerLog leaf6765Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi344RoundedFacts
    innerPair771RoundedFacts leaf6765RoundedFacts (by rfl)

private theorem leaf6765FlatSound : Sound leaf6765Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6765CertificateValid
    leaf6765InnerLogValid leaf6765CoversExact leaf6765LowerChecked

private noncomputable def leaf6766Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf6766Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109063/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588667392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (222779931/134217728) }, upper := { exponent := 1, mantissa := (3499/2048) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178094079/17177334784) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6766InnerLog : WideLogData :=
  innerPair765Data

set_option maxRecDepth 1000000 in
private theorem leaf6766LocalValidity :
    LeafFacts leaf6766Box leaf6766Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6766Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588667392) }) = true
      norm_num [leaf6766Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6766CertificateValid :
    WideCertificateValid leaf6766Box leaf6766Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi341ValidityFacts
    leaf6766LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6766CoverageChecked :
    coverageCheck (innerAD leaf6766Box) leaf6766InnerLog = true := by
  rfl'

private theorem leaf6766InnerLogValid :
    leaf6766InnerLog.Valid 8 (innerAD leaf6766Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint488PositiveFacts.valid leaf6766CoverageChecked

private noncomputable def leaf6766InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814911/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6766InputLogOnePlusV_eq :
    leaf6766InputLogOnePlusV = outerEnclosure 24
      (leaf6766Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6766RoundedFacts : LeafRoundedFacts 8
    leaf6766Certificate.logOnePlusV leaf6766InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6766InputLogOnePlusV_eq }

private noncomputable def leaf6766Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi341InputQChi innerPair765Input
    leaf6766InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6766LowerChecked :
    lowerCheck 24 leaf6766Box leaf6766Inputs = true := by
  rfl'

private theorem leaf6766CoversExact : CoversExact 8
    leaf6766Box leaf6766Certificate leaf6766InnerLog leaf6766Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi341RoundedFacts
    innerPair765RoundedFacts leaf6766RoundedFacts (by rfl)

private theorem leaf6766FlatSound : Sound leaf6766Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6766CertificateValid
    leaf6766InnerLogValid leaf6766CoversExact leaf6766LowerChecked

private noncomputable def leaf6767Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf6767Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109065/67108864) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588644352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (225663337/134217728) }, upper := { exponent := 1, mantissa := (443/256) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178071039/17177288704) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6767InnerLog : WideLogData :=
  innerPair846Data

set_option maxRecDepth 1000000 in
private theorem leaf6767LocalValidity :
    LeafFacts leaf6767Box leaf6767Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6767Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588644352) }) = true
      norm_num [leaf6767Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6767CertificateValid :
    WideCertificateValid leaf6767Box leaf6767Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi341ValidityFacts
    leaf6767LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6767CoverageChecked :
    coverageCheck (innerAD leaf6767Box) leaf6767InnerLog = true := by
  rfl'

private theorem leaf6767InnerLogValid :
    leaf6767InnerLog.Valid 8 (innerAD leaf6767Box) :=
  wideLogDataValid_of_cachedCheck endpoint541PositiveFacts
    endpoint542PositiveFacts.valid leaf6767CoverageChecked

private noncomputable def leaf6767InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629845/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6767InputLogOnePlusV_eq :
    leaf6767InputLogOnePlusV = outerEnclosure 24
      (leaf6767Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6767RoundedFacts : LeafRoundedFacts 8
    leaf6767Certificate.logOnePlusV leaf6767InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6767InputLogOnePlusV_eq }

private noncomputable def leaf6767Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi341InputQChi innerPair846Input
    leaf6767InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6767LowerChecked :
    lowerCheck 24 leaf6767Box leaf6767Inputs = true := by
  rfl'

private theorem leaf6767CoversExact : CoversExact 8
    leaf6767Box leaf6767Certificate leaf6767InnerLog leaf6767Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi341RoundedFacts
    innerPair846RoundedFacts leaf6767RoundedFacts (by rfl)

private theorem leaf6767FlatSound : Sound leaf6767Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6767CertificateValid
    leaf6767InnerLogValid leaf6767CoversExact leaf6767LowerChecked

private noncomputable def leaf6768Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf6768Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109065/67108864) }, vSqrt := { lower := (65529/65536), upper := (11452394153/11451518976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (226318657/134217728) }, upper := { exponent := 1, mantissa := (1777/1024) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22903913129/22903037952) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6768InnerLog : WideLogData :=
  innerPair766Data

set_option maxRecDepth 1000000 in
private theorem leaf6768LocalValidity :
    LeafFacts leaf6768Box leaf6768Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6768Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452394153/11451518976) }) = true
      norm_num [leaf6768Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6768CertificateValid :
    WideCertificateValid leaf6768Box leaf6768Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi342ValidityFacts
    leaf6768LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6768CoverageChecked :
    coverageCheck (innerAD leaf6768Box) leaf6768InnerLog = true := by
  rfl'

private theorem leaf6768InnerLogValid :
    leaf6768InnerLog.Valid 8 (innerAD leaf6768Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint489PositiveFacts.valid leaf6768CoverageChecked

private noncomputable def leaf6768InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814861/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6768InputLogOnePlusV_eq :
    leaf6768InputLogOnePlusV = outerEnclosure 24
      (leaf6768Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6768RoundedFacts : LeafRoundedFacts 8
    leaf6768Certificate.logOnePlusV leaf6768InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6768InputLogOnePlusV_eq }

private noncomputable def leaf6768Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi342InputQChi innerPair766Input
    leaf6768InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6768LowerChecked :
    lowerCheck 24 leaf6768Box leaf6768Inputs = true := by
  rfl'

private theorem leaf6768CoversExact : CoversExact 8
    leaf6768Box leaf6768Certificate leaf6768InnerLog leaf6768Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi342RoundedFacts
    innerPair766RoundedFacts leaf6768RoundedFacts (by rfl)

private theorem leaf6768FlatSound : Sound leaf6768Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6768CertificateValid
    leaf6768InnerLogValid leaf6768CoversExact leaf6768LowerChecked

private noncomputable def leaf6769Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf6769Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109067/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354462720) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (229267595/134217728) }, upper := { exponent := 1, mantissa := (225/128) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711645179/68708925440) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6769InnerLog : WideLogData :=
  innerPair845Data

set_option maxRecDepth 1000000 in
private theorem leaf6769LocalValidity :
    LeafFacts leaf6769Box leaf6769Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6769Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354462720) }) = true
      norm_num [leaf6769Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6769CertificateValid :
    WideCertificateValid leaf6769Box leaf6769Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi342ValidityFacts
    leaf6769LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6769CoverageChecked :
    coverageCheck (innerAD leaf6769Box) leaf6769InnerLog = true := by
  rfl'

private theorem leaf6769InnerLogValid :
    leaf6769InnerLog.Valid 8 (innerAD leaf6769Box) :=
  wideLogDataValid_of_cachedCheck endpoint540PositiveFacts
    endpoint543PositiveFacts.valid leaf6769CoverageChecked

private noncomputable def leaf6769InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629745/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6769InputLogOnePlusV_eq :
    leaf6769InputLogOnePlusV = outerEnclosure 24
      (leaf6769Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6769RoundedFacts : LeafRoundedFacts 8
    leaf6769Certificate.logOnePlusV leaf6769InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6769InputLogOnePlusV_eq }

private noncomputable def leaf6769Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi342InputQChi innerPair845Input
    leaf6769InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6769LowerChecked :
    lowerCheck 24 leaf6769Box leaf6769Inputs = true := by
  rfl'

private theorem leaf6769CoversExact : CoversExact 8
    leaf6769Box leaf6769Certificate leaf6769InnerLog leaf6769Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi342RoundedFacts
    innerPair845RoundedFacts leaf6769RoundedFacts (by rfl)

private theorem leaf6769FlatSound : Sound leaf6769Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6769CertificateValid
    leaf6769InnerLogValid leaf6769CoversExact leaf6769LowerChecked

private noncomputable def leaf6770Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf6770Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109067/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354444288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (229857383/134217728) }, upper := { exponent := 1, mantissa := (3609/2048) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711626747/68708888576) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6770InnerLog : WideLogData :=
  innerPair771Data

set_option maxRecDepth 1000000 in
private theorem leaf6770LocalValidity :
    LeafFacts leaf6770Box leaf6770Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6770Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354444288) }) = true
      norm_num [leaf6770Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6770CertificateValid :
    WideCertificateValid leaf6770Box leaf6770Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi343ValidityFacts
    leaf6770LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6770CoverageChecked :
    coverageCheck (innerAD leaf6770Box) leaf6770InnerLog = true := by
  rfl'

private theorem leaf6770InnerLogValid :
    leaf6770InnerLog.Valid 8 (innerAD leaf6770Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint498PositiveFacts.valid leaf6770CoverageChecked

private noncomputable def leaf6770InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629749/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6770InputLogOnePlusV_eq :
    leaf6770InputLogOnePlusV = outerEnclosure 24
      (leaf6770Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6770RoundedFacts : LeafRoundedFacts 8
    leaf6770Certificate.logOnePlusV leaf6770InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6770InputLogOnePlusV_eq }

private noncomputable def leaf6770Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi343InputQChi innerPair771Input
    leaf6770InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6770LowerChecked :
    lowerCheck 24 leaf6770Box leaf6770Inputs = true := by
  rfl'

private theorem leaf6770CoversExact : CoversExact 8
    leaf6770Box leaf6770Certificate leaf6770InnerLog leaf6770Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi343RoundedFacts
    innerPair771RoundedFacts leaf6770RoundedFacts (by rfl)

private theorem leaf6770FlatSound : Sound leaf6770Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6770CertificateValid
    leaf6770InnerLogValid leaf6770CoversExact leaf6770LowerChecked

private noncomputable def leaf6771Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf6771Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109069/67108864) }, vSqrt := { lower := (8191/8192), upper := (11452394153/11451449344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (232871853/134217728) }, upper := { exponent := 1, mantissa := (457/256) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22903843497/22902898688) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6771InnerLog : WideLogData :=
  innerPair848Data

set_option maxRecDepth 1000000 in
private theorem leaf6771LocalValidity :
    LeafFacts leaf6771Box leaf6771Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6771Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452394153/11451449344) }) = true
      norm_num [leaf6771Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6771CertificateValid :
    WideCertificateValid leaf6771Box leaf6771Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi343ValidityFacts
    leaf6771LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6771CoverageChecked :
    coverageCheck (innerAD leaf6771Box) leaf6771InnerLog = true := by
  rfl'

private theorem leaf6771InnerLogValid :
    leaf6771InnerLog.Valid 8 (innerAD leaf6771Box) :=
  wideLogDataValid_of_cachedCheck endpoint542PositiveFacts
    endpoint544PositiveFacts.valid leaf6771CoverageChecked

private noncomputable def leaf6771InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629773/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6771InputLogOnePlusV_eq :
    leaf6771InputLogOnePlusV = outerEnclosure 24
      (leaf6771Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6771RoundedFacts : LeafRoundedFacts 8
    leaf6771Certificate.logOnePlusV leaf6771InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6771InputLogOnePlusV_eq }

private noncomputable def leaf6771Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi343InputQChi innerPair848Input
    leaf6771InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6771LowerChecked :
    lowerCheck 24 leaf6771Box leaf6771Inputs = true := by
  rfl'

private theorem leaf6771CoversExact : CoversExact 8
    leaf6771Box leaf6771Certificate leaf6771InnerLog leaf6771Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi343RoundedFacts
    innerPair848RoundedFacts leaf6771RoundedFacts (by rfl)

private theorem leaf6771FlatSound : Sound leaf6771Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6771CertificateValid
    leaf6771InnerLogValid leaf6771CoversExact leaf6771LowerChecked

private noncomputable def leaf6772Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf6772Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109069/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354331648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (233396109/134217728) }, upper := { exponent := 1, mantissa := (229/128) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711514107/68708663296) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf6772InnerLog : WideLogData :=
  innerPair776Data

set_option maxRecDepth 1000000 in
private theorem leaf6772LocalValidity :
    LeafFacts leaf6772Box leaf6772Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6772Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354331648) }) = true
      norm_num [leaf6772Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6772CertificateValid :
    WideCertificateValid leaf6772Box leaf6772Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi344ValidityFacts
    leaf6772LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6772CoverageChecked :
    coverageCheck (innerAD leaf6772Box) leaf6772InnerLog = true := by
  rfl'

private theorem leaf6772InnerLogValid :
    leaf6772InnerLog.Valid 8 (innerAD leaf6772Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint500PositiveFacts.valid leaf6772CoverageChecked

private noncomputable def leaf6772InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629777/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6772InputLogOnePlusV_eq :
    leaf6772InputLogOnePlusV = outerEnclosure 24
      (leaf6772Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6772RoundedFacts : LeafRoundedFacts 8
    leaf6772Certificate.logOnePlusV leaf6772InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6772InputLogOnePlusV_eq }

private noncomputable def leaf6772Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi344InputQChi innerPair776Input
    leaf6772InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6772LowerChecked :
    lowerCheck 24 leaf6772Box leaf6772Inputs = true := by
  rfl'

private theorem leaf6772CoversExact : CoversExact 8
    leaf6772Box leaf6772Certificate leaf6772InnerLog leaf6772Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi344RoundedFacts
    innerPair776RoundedFacts leaf6772RoundedFacts (by rfl)

private theorem leaf6772FlatSound : Sound leaf6772Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6772CertificateValid
    leaf6772InnerLogValid leaf6772CoversExact leaf6772LowerChecked

private noncomputable def leaf6773Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf6773Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109071/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354233344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (236476111/134217728) }, upper := { exponent := 1, mantissa := (29/16) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711415803/68708466688) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf6773InnerLog : WideLogData :=
  innerPair778Data

set_option maxRecDepth 1000000 in
private theorem leaf6773LocalValidity :
    LeafFacts leaf6773Box leaf6773Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6773Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354233344) }) = true
      norm_num [leaf6773Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6773CertificateValid :
    WideCertificateValid leaf6773Box leaf6773Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi344ValidityFacts
    leaf6773LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6773CoverageChecked :
    coverageCheck (innerAD leaf6773Box) leaf6773InnerLog = true := by
  rfl'

private theorem leaf6773InnerLogValid :
    leaf6773InnerLog.Valid 8 (innerAD leaf6773Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint500PositiveFacts.valid leaf6773CoverageChecked

private noncomputable def leaf6773InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629801/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6773InputLogOnePlusV_eq :
    leaf6773InputLogOnePlusV = outerEnclosure 24
      (leaf6773Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6773RoundedFacts : LeafRoundedFacts 8
    leaf6773Certificate.logOnePlusV leaf6773InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6773InputLogOnePlusV_eq }

private noncomputable def leaf6773Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi344InputQChi innerPair778Input
    leaf6773InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6773LowerChecked :
    lowerCheck 24 leaf6773Box leaf6773Inputs = true := by
  rfl'

private theorem leaf6773CoversExact : CoversExact 8
    leaf6773Box leaf6773Certificate leaf6773InnerLog leaf6773Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi344RoundedFacts
    innerPair778RoundedFacts leaf6773RoundedFacts (by rfl)

private theorem leaf6773FlatSound : Sound leaf6773Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6773CertificateValid
    leaf6773InnerLogValid leaf6773CoversExact leaf6773LowerChecked

private noncomputable def component137Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component137Node0_sound : Sound component137Node0Box :=
  sound_of_literal_split component137Node0Box leaf6735Box leaf6736Box
    .chi (81/128) (by rfl) (by rfl)
    leaf6735FlatSound leaf6736FlatSound

private noncomputable def component137Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component137Node1_sound : Sound component137Node1Box :=
  sound_of_literal_split component137Node1Box leaf6737Box leaf6738Box
    .chi (81/128) (by rfl) (by rfl)
    leaf6737FlatSound leaf6738FlatSound

private noncomputable def component137Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component137Node2_sound : Sound component137Node2Box :=
  sound_of_literal_split component137Node2Box component137Node0Box component137Node1Box
    .k (53/16) (by rfl) (by rfl)
    component137Node0_sound component137Node1_sound

private noncomputable def component137Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (41/64), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component137Node3_sound : Sound component137Node3Box :=
  sound_of_literal_split component137Node3Box leaf6740Box leaf6741Box
    .chi (83/128) (by rfl) (by rfl)
    leaf6740FlatSound leaf6741FlatSound

private noncomputable def component137Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (41/64), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component137Node4_sound : Sound component137Node4Box :=
  sound_of_literal_split component137Node4Box leaf6739Box component137Node3Box
    .k (53/16) (by rfl) (by rfl)
    leaf6739FlatSound component137Node3_sound

private noncomputable def component137Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component137Node5_sound : Sound component137Node5Box :=
  sound_of_literal_split component137Node5Box component137Node2Box component137Node4Box
    .chi (41/64) (by rfl) (by rfl)
    component137Node2_sound component137Node4_sound

private noncomputable def component137Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (21/32), chiHi := (43/64) }

set_option maxRecDepth 1000000 in
private theorem component137Node6_sound : Sound component137Node6Box :=
  sound_of_literal_split component137Node6Box leaf6742Box leaf6743Box
    .k (53/16) (by rfl) (by rfl)
    leaf6742FlatSound leaf6743FlatSound

private noncomputable def component137Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (43/64), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component137Node7_sound : Sound component137Node7Box :=
  sound_of_literal_split component137Node7Box leaf6744Box leaf6745Box
    .k (53/16) (by rfl) (by rfl)
    leaf6744FlatSound leaf6745FlatSound

private noncomputable def component137Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component137Node8_sound : Sound component137Node8Box :=
  sound_of_literal_split component137Node8Box component137Node6Box component137Node7Box
    .chi (43/64) (by rfl) (by rfl)
    component137Node6_sound component137Node7_sound

private noncomputable def component137Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component137Node9_sound : Sound component137Node9Box :=
  sound_of_literal_split component137Node9Box component137Node5Box component137Node8Box
    .chi (21/32) (by rfl) (by rfl)
    component137Node5_sound component137Node8_sound

private noncomputable def component137Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component137Node10_sound : Sound component137Node10Box :=
  sound_of_literal_split component137Node10Box leaf6746Box leaf6747Box
    .chi (81/128) (by rfl) (by rfl)
    leaf6746FlatSound leaf6747FlatSound

private noncomputable def component137Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component137Node11_sound : Sound component137Node11Box :=
  sound_of_literal_split component137Node11Box leaf6748Box leaf6749Box
    .chi (81/128) (by rfl) (by rfl)
    leaf6748FlatSound leaf6749FlatSound

private noncomputable def component137Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component137Node12_sound : Sound component137Node12Box :=
  sound_of_literal_split component137Node12Box component137Node10Box component137Node11Box
    .k (55/16) (by rfl) (by rfl)
    component137Node10_sound component137Node11_sound

private noncomputable def component137Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (41/64), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component137Node13_sound : Sound component137Node13Box :=
  sound_of_literal_split component137Node13Box leaf6750Box leaf6751Box
    .chi (83/128) (by rfl) (by rfl)
    leaf6750FlatSound leaf6751FlatSound

private noncomputable def component137Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (41/64), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component137Node14_sound : Sound component137Node14Box :=
  sound_of_literal_split component137Node14Box leaf6752Box leaf6753Box
    .chi (83/128) (by rfl) (by rfl)
    leaf6752FlatSound leaf6753FlatSound

private noncomputable def component137Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (41/64), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component137Node15_sound : Sound component137Node15Box :=
  sound_of_literal_split component137Node15Box component137Node13Box component137Node14Box
    .k (55/16) (by rfl) (by rfl)
    component137Node13_sound component137Node14_sound

private noncomputable def component137Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component137Node16_sound : Sound component137Node16Box :=
  sound_of_literal_split component137Node16Box component137Node12Box component137Node15Box
    .chi (41/64) (by rfl) (by rfl)
    component137Node12_sound component137Node15_sound

private noncomputable def component137Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (21/32), chiHi := (43/64) }

set_option maxRecDepth 1000000 in
private theorem component137Node17_sound : Sound component137Node17Box :=
  sound_of_literal_split component137Node17Box leaf6754Box leaf6755Box
    .k (55/16) (by rfl) (by rfl)
    leaf6754FlatSound leaf6755FlatSound

private noncomputable def component137Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (43/64), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component137Node18_sound : Sound component137Node18Box :=
  sound_of_literal_split component137Node18Box leaf6756Box leaf6757Box
    .k (55/16) (by rfl) (by rfl)
    leaf6756FlatSound leaf6757FlatSound

private noncomputable def component137Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component137Node19_sound : Sound component137Node19Box :=
  sound_of_literal_split component137Node19Box component137Node17Box component137Node18Box
    .chi (43/64) (by rfl) (by rfl)
    component137Node17_sound component137Node18_sound

private noncomputable def component137Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component137Node20_sound : Sound component137Node20Box :=
  sound_of_literal_split component137Node20Box component137Node16Box component137Node19Box
    .chi (21/32) (by rfl) (by rfl)
    component137Node16_sound component137Node19_sound

private noncomputable def component137Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component137Node21_sound : Sound component137Node21Box :=
  sound_of_literal_split component137Node21Box component137Node9Box component137Node20Box
    .k (27/8) (by rfl) (by rfl)
    component137Node9_sound component137Node20_sound

private noncomputable def component137Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (11/16), chiHi := (45/64) }

set_option maxRecDepth 1000000 in
private theorem component137Node22_sound : Sound component137Node22Box :=
  sound_of_literal_split component137Node22Box leaf6758Box leaf6759Box
    .k (53/16) (by rfl) (by rfl)
    leaf6758FlatSound leaf6759FlatSound

private noncomputable def component137Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (45/64), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component137Node23_sound : Sound component137Node23Box :=
  sound_of_literal_split component137Node23Box leaf6760Box leaf6761Box
    .k (53/16) (by rfl) (by rfl)
    leaf6760FlatSound leaf6761FlatSound

private noncomputable def component137Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component137Node24_sound : Sound component137Node24Box :=
  sound_of_literal_split component137Node24Box component137Node22Box component137Node23Box
    .chi (45/64) (by rfl) (by rfl)
    component137Node22_sound component137Node23_sound

private noncomputable def component137Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component137Node25_sound : Sound component137Node25Box :=
  sound_of_literal_split component137Node25Box leaf6762Box leaf6763Box
    .chi (47/64) (by rfl) (by rfl)
    leaf6762FlatSound leaf6763FlatSound

private noncomputable def component137Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component137Node26_sound : Sound component137Node26Box :=
  sound_of_literal_split component137Node26Box leaf6764Box leaf6765Box
    .chi (47/64) (by rfl) (by rfl)
    leaf6764FlatSound leaf6765FlatSound

private noncomputable def component137Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component137Node27_sound : Sound component137Node27Box :=
  sound_of_literal_split component137Node27Box component137Node25Box component137Node26Box
    .k (53/16) (by rfl) (by rfl)
    component137Node25_sound component137Node26_sound

private noncomputable def component137Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component137Node28_sound : Sound component137Node28Box :=
  sound_of_literal_split component137Node28Box component137Node24Box component137Node27Box
    .chi (23/32) (by rfl) (by rfl)
    component137Node24_sound component137Node27_sound

private noncomputable def component137Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (11/16), chiHi := (45/64) }

set_option maxRecDepth 1000000 in
private theorem component137Node29_sound : Sound component137Node29Box :=
  sound_of_literal_split component137Node29Box leaf6766Box leaf6767Box
    .k (55/16) (by rfl) (by rfl)
    leaf6766FlatSound leaf6767FlatSound

private noncomputable def component137Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (45/64), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component137Node30_sound : Sound component137Node30Box :=
  sound_of_literal_split component137Node30Box leaf6768Box leaf6769Box
    .k (55/16) (by rfl) (by rfl)
    leaf6768FlatSound leaf6769FlatSound

private noncomputable def component137Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component137Node31_sound : Sound component137Node31Box :=
  sound_of_literal_split component137Node31Box component137Node29Box component137Node30Box
    .chi (45/64) (by rfl) (by rfl)
    component137Node29_sound component137Node30_sound

private noncomputable def component137Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (23/32), chiHi := (47/64) }

set_option maxRecDepth 1000000 in
private theorem component137Node32_sound : Sound component137Node32Box :=
  sound_of_literal_split component137Node32Box leaf6770Box leaf6771Box
    .k (55/16) (by rfl) (by rfl)
    leaf6770FlatSound leaf6771FlatSound

private noncomputable def component137Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (47/64), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component137Node33_sound : Sound component137Node33Box :=
  sound_of_literal_split component137Node33Box leaf6772Box leaf6773Box
    .k (55/16) (by rfl) (by rfl)
    leaf6772FlatSound leaf6773FlatSound

private noncomputable def component137Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component137Node34_sound : Sound component137Node34Box :=
  sound_of_literal_split component137Node34Box component137Node32Box component137Node33Box
    .chi (47/64) (by rfl) (by rfl)
    component137Node32_sound component137Node33_sound

private noncomputable def component137Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component137Node35_sound : Sound component137Node35Box :=
  sound_of_literal_split component137Node35Box component137Node31Box component137Node34Box
    .chi (23/32) (by rfl) (by rfl)
    component137Node31_sound component137Node34_sound

private noncomputable def component137Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component137Node36_sound : Sound component137Node36Box :=
  sound_of_literal_split component137Node36Box component137Node28Box component137Node35Box
    .k (27/8) (by rfl) (by rfl)
    component137Node28_sound component137Node35_sound

noncomputable def component137Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
theorem component137_sound : Sound component137Box :=
  sound_of_literal_split component137Box component137Node21Box component137Node36Box
    .chi (11/16) (by rfl) (by rfl)
    component137Node21_sound component137Node36_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
