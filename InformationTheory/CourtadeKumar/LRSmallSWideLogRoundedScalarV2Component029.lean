import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
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

private noncomputable def leaf1245Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1245Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435683/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717198336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (406806047/268435456) }, upper := { exponent := 0, mantissa := (6321/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435692031/137434396672) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1245InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1245LocalValidity :
    LeafFacts leaf1245Box leaf1245Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1245Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717198336) }) = true
      norm_num [leaf1245Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1245CertificateValid :
    WideCertificateValid leaf1245Box leaf1245Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi115ValidityFacts
    leaf1245LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1245CoverageChecked :
    coverageCheck (innerAD leaf1245Box) leaf1245InnerLog = true := by
  rfl'

private theorem leaf1245InnerLogValid :
    leaf1245InnerLog.Valid 8 (innerAD leaf1245Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1245CoverageChecked

private noncomputable def leaf1245InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629239/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1245InputLogOnePlusV_eq :
    leaf1245InputLogOnePlusV = outerEnclosure 24
      (leaf1245Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1245RoundedFacts : LeafRoundedFacts 8
    leaf1245Certificate.logOnePlusV leaf1245InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1245InputLogOnePlusV_eq }

private noncomputable def leaf1245Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi115InputQChi innerPair40Input
    leaf1245InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1245LowerChecked :
    lowerCheck 24 leaf1245Box leaf1245Inputs = true := by
  rfl'

private theorem leaf1245CoversExact : CoversExact 8
    leaf1245Box leaf1245Certificate leaf1245InnerLog leaf1245Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi115RoundedFacts
    innerPair40RoundedFacts leaf1245RoundedFacts (by rfl)

private theorem leaf1245FlatSound : Sound leaf1245Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1245CertificateValid
    leaf1245InnerLogValid leaf1245CoversExact leaf1245LowerChecked

private noncomputable def leaf1246Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1246Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435685/268435456) }, vSqrt := { lower := (32765/32768), upper := (4581232913/4581140480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (412572861/268435456) }, upper := { exponent := 0, mantissa := (3205/2048) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (9162373393/9162280960) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1246InnerLog : WideLogData :=
  innerPair87Data

set_option maxRecDepth 1000000 in
private theorem leaf1246LocalValidity :
    LeafFacts leaf1246Box leaf1246Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1246Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4581232913/4581140480) }) = true
      norm_num [leaf1246Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1246CertificateValid :
    WideCertificateValid leaf1246Box leaf1246Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi116ValidityFacts
    leaf1246LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1246CoverageChecked :
    coverageCheck (innerAD leaf1246Box) leaf1246InnerLog = true := by
  rfl'

private theorem leaf1246InnerLogValid :
    leaf1246InnerLog.Valid 8 (innerAD leaf1246Box) :=
  wideLogDataValid_of_cachedCheck endpoint19PositiveFacts
    endpoint47PositiveFacts.valid leaf1246CoverageChecked

private noncomputable def leaf1246InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1246InputLogOnePlusV_eq :
    leaf1246InputLogOnePlusV = outerEnclosure 24
      (leaf1246Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1246RoundedFacts : LeafRoundedFacts 8
    leaf1246Certificate.logOnePlusV leaf1246InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1246InputLogOnePlusV_eq }

private noncomputable def leaf1246Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi116InputQChi innerPair87Input
    leaf1246InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1246LowerChecked :
    lowerCheck 24 leaf1246Box leaf1246Inputs = true := by
  rfl'

private theorem leaf1246CoversExact : CoversExact 8
    leaf1246Box leaf1246Certificate leaf1246InnerLog leaf1246Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi116RoundedFacts
    innerPair87RoundedFacts leaf1246RoundedFacts (by rfl)

private theorem leaf1246FlatSound : Sound leaf1246Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1246CertificateValid
    leaf1246InnerLogValid leaf1246CoversExact leaf1246LowerChecked

private noncomputable def leaf1247Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1247Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435685/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717172736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (408378813/268435456) }, upper := { exponent := 0, mantissa := (3173/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435666431/137434345472) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1247InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1247LocalValidity :
    LeafFacts leaf1247Box leaf1247Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1247Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717172736) }) = true
      norm_num [leaf1247Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1247CertificateValid :
    WideCertificateValid leaf1247Box leaf1247Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi115ValidityFacts
    leaf1247LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1247CoverageChecked :
    coverageCheck (innerAD leaf1247Box) leaf1247InnerLog = true := by
  rfl'

private theorem leaf1247InnerLogValid :
    leaf1247InnerLog.Valid 8 (innerAD leaf1247Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1247CoverageChecked

private noncomputable def leaf1247InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814621/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1247InputLogOnePlusV_eq :
    leaf1247InputLogOnePlusV = outerEnclosure 24
      (leaf1247Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1247RoundedFacts : LeafRoundedFacts 8
    leaf1247Certificate.logOnePlusV leaf1247InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1247InputLogOnePlusV_eq }

private noncomputable def leaf1247Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi115InputQChi innerPair40Input
    leaf1247InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1247LowerChecked :
    lowerCheck 24 leaf1247Box leaf1247Inputs = true := by
  rfl'

private theorem leaf1247CoversExact : CoversExact 8
    leaf1247Box leaf1247Certificate leaf1247InnerLog leaf1247Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi115RoundedFacts
    innerPair40RoundedFacts leaf1247RoundedFacts (by rfl)

private theorem leaf1247FlatSound : Sound leaf1247Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1247CertificateValid
    leaf1247InnerLogValid leaf1247CoversExact leaf1247LowerChecked

private noncomputable def leaf1248Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1248Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435687/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717080576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (414211159/268435456) }, upper := { exponent := 0, mantissa := (1609/1024) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435574271/137434161152) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1248InnerLog : WideLogData :=
  innerPair87Data

set_option maxRecDepth 1000000 in
private theorem leaf1248LocalValidity :
    LeafFacts leaf1248Box leaf1248Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1248Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717080576) }) = true
      norm_num [leaf1248Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1248CertificateValid :
    WideCertificateValid leaf1248Box leaf1248Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi116ValidityFacts
    leaf1248LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1248CoverageChecked :
    coverageCheck (innerAD leaf1248Box) leaf1248InnerLog = true := by
  rfl'

private theorem leaf1248InnerLogValid :
    leaf1248InnerLog.Valid 8 (innerAD leaf1248Box) :=
  wideLogDataValid_of_cachedCheck endpoint19PositiveFacts
    endpoint47PositiveFacts.valid leaf1248CoverageChecked

private noncomputable def leaf1248InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1248InputLogOnePlusV_eq :
    leaf1248InputLogOnePlusV = outerEnclosure 24
      (leaf1248Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1248RoundedFacts : LeafRoundedFacts 8
    leaf1248Certificate.logOnePlusV leaf1248InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1248InputLogOnePlusV_eq }

private noncomputable def leaf1248Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi116InputQChi innerPair87Input
    leaf1248InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1248LowerChecked :
    lowerCheck 24 leaf1248Box leaf1248Inputs = true := by
  rfl'

private theorem leaf1248CoversExact : CoversExact 8
    leaf1248Box leaf1248Certificate leaf1248InnerLog leaf1248Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi116RoundedFacts
    innerPair87RoundedFacts leaf1248RoundedFacts (by rfl)

private theorem leaf1248FlatSound : Sound leaf1248Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1248CertificateValid
    leaf1248InnerLogValid leaf1248CoversExact leaf1248LowerChecked

private noncomputable def leaf1249Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1249Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435687/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717016064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (418339675/268435456) }, upper := { exponent := 0, mantissa := (6499/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435509759/137434032128) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1249InnerLog : WideLogData :=
  innerPair154Data

set_option maxRecDepth 1000000 in
private theorem leaf1249LocalValidity :
    LeafFacts leaf1249Box leaf1249Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1249Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717016064) }) = true
      norm_num [leaf1249Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1249CertificateValid :
    WideCertificateValid leaf1249Box leaf1249Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi117ValidityFacts
    leaf1249LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1249CoverageChecked :
    coverageCheck (innerAD leaf1249Box) leaf1249InnerLog = true := by
  rfl'

private theorem leaf1249InnerLogValid :
    leaf1249InnerLog.Valid 8 (innerAD leaf1249Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint44PositiveFacts.valid leaf1249CoverageChecked

private noncomputable def leaf1249InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1249InputLogOnePlusV_eq :
    leaf1249InputLogOnePlusV = outerEnclosure 24
      (leaf1249Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1249RoundedFacts : LeafRoundedFacts 8
    leaf1249Certificate.logOnePlusV leaf1249InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1249InputLogOnePlusV_eq }

private noncomputable def leaf1249Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi117InputQChi innerPair154Input
    leaf1249InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1249LowerChecked :
    lowerCheck 24 leaf1249Box leaf1249Inputs = true := by
  rfl'

private theorem leaf1249CoversExact : CoversExact 8
    leaf1249Box leaf1249Certificate leaf1249InnerLog leaf1249Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi117RoundedFacts
    innerPair154RoundedFacts leaf1249RoundedFacts (by rfl)

private theorem leaf1249FlatSound : Sound leaf1249Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1249CertificateValid
    leaf1249InnerLogValid leaf1249CoversExact leaf1249LowerChecked

private noncomputable def leaf1250Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1250Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435689/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716924928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (424106489/268435456) }, upper := { exponent := 0, mantissa := (1647/1024) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435418623/137433849856) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1250InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1250LocalValidity :
    LeafFacts leaf1250Box leaf1250Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1250Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716924928) }) = true
      norm_num [leaf1250Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1250CertificateValid :
    WideCertificateValid leaf1250Box leaf1250Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi118ValidityFacts
    leaf1250LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1250CoverageChecked :
    coverageCheck (innerAD leaf1250Box) leaf1250InnerLog = true := by
  rfl'

private theorem leaf1250InnerLogValid :
    leaf1250InnerLog.Valid 8 (innerAD leaf1250Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1250CoverageChecked

private noncomputable def leaf1250InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1250InputLogOnePlusV_eq :
    leaf1250InputLogOnePlusV = outerEnclosure 24
      (leaf1250Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1250RoundedFacts : LeafRoundedFacts 8
    leaf1250Certificate.logOnePlusV leaf1250InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1250InputLogOnePlusV_eq }

private noncomputable def leaf1250Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi118InputQChi innerPair50Input
    leaf1250InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1250LowerChecked :
    lowerCheck 24 leaf1250Box leaf1250Inputs = true := by
  rfl'

private theorem leaf1250CoversExact : CoversExact 8
    leaf1250Box leaf1250Certificate leaf1250InnerLog leaf1250Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi118RoundedFacts
    innerPair50RoundedFacts leaf1250RoundedFacts (by rfl)

private theorem leaf1250FlatSound : Sound leaf1250Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1250CertificateValid
    leaf1250InnerLogValid leaf1250CoversExact leaf1250LowerChecked

private noncomputable def leaf1251Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1251Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435689/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716988416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (420043505/268435456) }, upper := { exponent := 0, mantissa := (3263/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435482111/137433976832) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1251InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf1251LocalValidity :
    LeafFacts leaf1251Box leaf1251Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1251Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716988416) }) = true
      norm_num [leaf1251Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1251CertificateValid :
    WideCertificateValid leaf1251Box leaf1251Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi117ValidityFacts
    leaf1251LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1251CoverageChecked :
    coverageCheck (innerAD leaf1251Box) leaf1251InnerLog = true := by
  rfl'

private theorem leaf1251InnerLogValid :
    leaf1251InnerLog.Valid 8 (innerAD leaf1251Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf1251CoverageChecked

private noncomputable def leaf1251InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726829/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1251InputLogOnePlusV_eq :
    leaf1251InputLogOnePlusV = outerEnclosure 24
      (leaf1251Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1251RoundedFacts : LeafRoundedFacts 8
    leaf1251Certificate.logOnePlusV leaf1251InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1251InputLogOnePlusV_eq }

private noncomputable def leaf1251Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi117InputQChi innerPair54Input
    leaf1251InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1251LowerChecked :
    lowerCheck 24 leaf1251Box leaf1251Inputs = true := by
  rfl'

private theorem leaf1251CoversExact : CoversExact 8
    leaf1251Box leaf1251Certificate leaf1251InnerLog leaf1251Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi117RoundedFacts
    innerPair54RoundedFacts leaf1251RoundedFacts (by rfl)

private theorem leaf1251FlatSound : Sound leaf1251Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1251CertificateValid
    leaf1251InnerLogValid leaf1251CoversExact leaf1251LowerChecked

private noncomputable def leaf1252Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1252Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435691/268435456) }, vSqrt := { lower := (32765/32768), upper := (4042264335/4042170368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (425875851/268435456) }, upper := { exponent := 0, mantissa := (827/512) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8084434703/8084340736) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1252InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1252LocalValidity :
    LeafFacts leaf1252Box leaf1252Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1252Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4042264335/4042170368) }) = true
      norm_num [leaf1252Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1252CertificateValid :
    WideCertificateValid leaf1252Box leaf1252Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi118ValidityFacts
    leaf1252LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1252CoverageChecked :
    coverageCheck (innerAD leaf1252Box) leaf1252InnerLog = true := by
  rfl'

private theorem leaf1252InnerLogValid :
    leaf1252InnerLog.Valid 8 (innerAD leaf1252Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1252CoverageChecked

private noncomputable def leaf1252InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1252InputLogOnePlusV_eq :
    leaf1252InputLogOnePlusV = outerEnclosure 24
      (leaf1252Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1252RoundedFacts : LeafRoundedFacts 8
    leaf1252Certificate.logOnePlusV leaf1252InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1252InputLogOnePlusV_eq }

private noncomputable def leaf1252Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi118InputQChi innerPair50Input
    leaf1252InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1252LowerChecked :
    lowerCheck 24 leaf1252Box leaf1252Inputs = true := by
  rfl'

private theorem leaf1252CoversExact : CoversExact 8
    leaf1252Box leaf1252Certificate leaf1252InnerLog leaf1252Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi118RoundedFacts
    innerPair50RoundedFacts leaf1252RoundedFacts (by rfl)

private theorem leaf1252FlatSound : Sound leaf1252Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1252CertificateValid
    leaf1252InnerLogValid leaf1252CoversExact leaf1252LowerChecked

private noncomputable def leaf1253Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1253Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435687/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905715712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (409951579/268435456) }, upper := { exponent := 0, mantissa := (6371/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811880277/45811431424) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1253InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1253LocalValidity :
    LeafFacts leaf1253Box leaf1253Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1253Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905715712) }) = true
      norm_num [leaf1253Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1253CertificateValid :
    WideCertificateValid leaf1253Box leaf1253Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi115ValidityFacts
    leaf1253LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1253CoverageChecked :
    coverageCheck (innerAD leaf1253Box) leaf1253InnerLog = true := by
  rfl'

private theorem leaf1253InnerLogValid :
    leaf1253InnerLog.Valid 8 (innerAD leaf1253Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1253CoverageChecked

private noncomputable def leaf1253InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1253InputLogOnePlusV_eq :
    leaf1253InputLogOnePlusV = outerEnclosure 24
      (leaf1253Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1253RoundedFacts : LeafRoundedFacts 8
    leaf1253Certificate.logOnePlusV leaf1253InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1253InputLogOnePlusV_eq }

private noncomputable def leaf1253Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi115InputQChi innerPair40Input
    leaf1253InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1253LowerChecked :
    lowerCheck 24 leaf1253Box leaf1253Inputs = true := by
  rfl'

private theorem leaf1253CoversExact : CoversExact 8
    leaf1253Box leaf1253Certificate leaf1253InnerLog leaf1253Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi115RoundedFacts
    innerPair40RoundedFacts leaf1253RoundedFacts (by rfl)

private theorem leaf1253FlatSound : Sound leaf1253Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1253CertificateValid
    leaf1253InnerLogValid leaf1253CoversExact leaf1253LowerChecked

private noncomputable def leaf1254Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1254Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435689/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717053952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (415849457/268435456) }, upper := { exponent := 0, mantissa := (3231/2048) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435547647/137434107904) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1254InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf1254LocalValidity :
    LeafFacts leaf1254Box leaf1254Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1254Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717053952) }) = true
      norm_num [leaf1254Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1254CertificateValid :
    WideCertificateValid leaf1254Box leaf1254Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi116ValidityFacts
    leaf1254LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1254CoverageChecked :
    coverageCheck (innerAD leaf1254Box) leaf1254InnerLog = true := by
  rfl'

private theorem leaf1254InnerLogValid :
    leaf1254InnerLog.Valid 8 (innerAD leaf1254Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf1254CoverageChecked

private noncomputable def leaf1254InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453657/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1254InputLogOnePlusV_eq :
    leaf1254InputLogOnePlusV = outerEnclosure 24
      (leaf1254Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1254RoundedFacts : LeafRoundedFacts 8
    leaf1254Certificate.logOnePlusV leaf1254InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1254InputLogOnePlusV_eq }

private noncomputable def leaf1254Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi116InputQChi innerPair156Input
    leaf1254InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1254LowerChecked :
    lowerCheck 24 leaf1254Box leaf1254Inputs = true := by
  rfl'

private theorem leaf1254CoversExact : CoversExact 8
    leaf1254Box leaf1254Certificate leaf1254InnerLog leaf1254Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi116RoundedFacts
    innerPair156RoundedFacts leaf1254RoundedFacts (by rfl)

private theorem leaf1254FlatSound : Sound leaf1254Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1254CertificateValid
    leaf1254InnerLogValid leaf1254CoversExact leaf1254LowerChecked

private noncomputable def leaf1255Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1255Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435689/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717121536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (411524345/268435456) }, upper := { exponent := 0, mantissa := (1599/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435615231/137434243072) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1255InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1255LocalValidity :
    LeafFacts leaf1255Box leaf1255Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1255Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717121536) }) = true
      norm_num [leaf1255Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1255CertificateValid :
    WideCertificateValid leaf1255Box leaf1255Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi115ValidityFacts
    leaf1255LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1255CoverageChecked :
    coverageCheck (innerAD leaf1255Box) leaf1255InnerLog = true := by
  rfl'

private theorem leaf1255InnerLogValid :
    leaf1255InnerLog.Valid 8 (innerAD leaf1255Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1255CoverageChecked

private noncomputable def leaf1255InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf1255InputLogOnePlusV_eq :
    leaf1255InputLogOnePlusV = outerEnclosure 24
      (leaf1255Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1255RoundedFacts : LeafRoundedFacts 8
    leaf1255Certificate.logOnePlusV leaf1255InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1255InputLogOnePlusV_eq }

private noncomputable def leaf1255Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi115InputQChi innerPair40Input
    leaf1255InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1255LowerChecked :
    lowerCheck 24 leaf1255Box leaf1255Inputs = true := by
  rfl'

private theorem leaf1255CoversExact : CoversExact 8
    leaf1255Box leaf1255Certificate leaf1255InnerLog leaf1255Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi115RoundedFacts
    innerPair40RoundedFacts leaf1255RoundedFacts (by rfl)

private theorem leaf1255FlatSound : Sound leaf1255Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1255CertificateValid
    leaf1255InnerLogValid leaf1255CoversExact leaf1255LowerChecked

private noncomputable def leaf1256Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1256Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435691/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905675776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (417487755/268435456) }, upper := { exponent := 0, mantissa := (811/512) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811840341/45811351552) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1256InnerLog : WideLogData :=
  innerPair154Data

set_option maxRecDepth 1000000 in
private theorem leaf1256LocalValidity :
    LeafFacts leaf1256Box leaf1256Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1256Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905675776) }) = true
      norm_num [leaf1256Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1256CertificateValid :
    WideCertificateValid leaf1256Box leaf1256Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi116ValidityFacts
    leaf1256LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1256CoverageChecked :
    coverageCheck (innerAD leaf1256Box) leaf1256InnerLog = true := by
  rfl'

private theorem leaf1256InnerLogValid :
    leaf1256InnerLog.Valid 8 (innerAD leaf1256Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint44PositiveFacts.valid leaf1256CoverageChecked

private noncomputable def leaf1256InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907315/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1256InputLogOnePlusV_eq :
    leaf1256InputLogOnePlusV = outerEnclosure 24
      (leaf1256Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1256RoundedFacts : LeafRoundedFacts 8
    leaf1256Certificate.logOnePlusV leaf1256InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1256InputLogOnePlusV_eq }

private noncomputable def leaf1256Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi116InputQChi innerPair154Input
    leaf1256InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1256LowerChecked :
    lowerCheck 24 leaf1256Box leaf1256Inputs = true := by
  rfl'

private theorem leaf1256CoversExact : CoversExact 8
    leaf1256Box leaf1256Certificate leaf1256InnerLog leaf1256Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi116RoundedFacts
    innerPair154RoundedFacts leaf1256RoundedFacts (by rfl)

private theorem leaf1256FlatSound : Sound leaf1256Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1256CertificateValid
    leaf1256InnerLogValid leaf1256CoversExact leaf1256LowerChecked

private noncomputable def leaf1257Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1257Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435691/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716960768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (421747335/268435456) }, upper := { exponent := 0, mantissa := (6553/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435454463/137433921536) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1257InnerLog : WideLogData :=
  innerPair55Data

set_option maxRecDepth 1000000 in
private theorem leaf1257LocalValidity :
    LeafFacts leaf1257Box leaf1257Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1257Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716960768) }) = true
      norm_num [leaf1257Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1257CertificateValid :
    WideCertificateValid leaf1257Box leaf1257Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi117ValidityFacts
    leaf1257LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1257CoverageChecked :
    coverageCheck (innerAD leaf1257Box) leaf1257InnerLog = true := by
  rfl'

private theorem leaf1257InnerLogValid :
    leaf1257InnerLog.Valid 8 (innerAD leaf1257Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint46PositiveFacts.valid leaf1257CoverageChecked

private noncomputable def leaf1257InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1257InputLogOnePlusV_eq :
    leaf1257InputLogOnePlusV = outerEnclosure 24
      (leaf1257Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1257RoundedFacts : LeafRoundedFacts 8
    leaf1257Certificate.logOnePlusV leaf1257InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1257InputLogOnePlusV_eq }

private noncomputable def leaf1257Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi117InputQChi innerPair55Input
    leaf1257InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1257LowerChecked :
    lowerCheck 24 leaf1257Box leaf1257Inputs = true := by
  rfl'

private theorem leaf1257CoversExact : CoversExact 8
    leaf1257Box leaf1257Certificate leaf1257InnerLog leaf1257Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi117RoundedFacts
    innerPair55RoundedFacts leaf1257RoundedFacts (by rfl)

private theorem leaf1257FlatSound : Sound leaf1257Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1257CertificateValid
    leaf1257InnerLogValid leaf1257CoversExact leaf1257LowerChecked

private noncomputable def leaf1258Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1258Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435693/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905622528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (427645213/268435456) }, upper := { exponent := 0, mantissa := (1661/1024) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811787093/45811245056) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1258InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1258LocalValidity :
    LeafFacts leaf1258Box leaf1258Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1258Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905622528) }) = true
      norm_num [leaf1258Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1258CertificateValid :
    WideCertificateValid leaf1258Box leaf1258Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi118ValidityFacts
    leaf1258LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1258CoverageChecked :
    coverageCheck (innerAD leaf1258Box) leaf1258InnerLog = true := by
  rfl'

private theorem leaf1258InnerLogValid :
    leaf1258InnerLog.Valid 8 (innerAD leaf1258Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1258CoverageChecked

private noncomputable def leaf1258InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1258InputLogOnePlusV_eq :
    leaf1258InputLogOnePlusV = outerEnclosure 24
      (leaf1258Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1258RoundedFacts : LeafRoundedFacts 8
    leaf1258Certificate.logOnePlusV leaf1258InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1258InputLogOnePlusV_eq }

private noncomputable def leaf1258Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi118InputQChi innerPair50Input
    leaf1258InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1258LowerChecked :
    lowerCheck 24 leaf1258Box leaf1258Inputs = true := by
  rfl'

private theorem leaf1258CoversExact : CoversExact 8
    leaf1258Box leaf1258Certificate leaf1258InnerLog leaf1258Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi118RoundedFacts
    innerPair50RoundedFacts leaf1258RoundedFacts (by rfl)

private theorem leaf1258FlatSound : Sound leaf1258Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1258CertificateValid
    leaf1258InnerLogValid leaf1258CoversExact leaf1258LowerChecked

private noncomputable def leaf1259Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1259Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435693/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743386624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (423451165/268435456) }, upper := { exponent := 0, mantissa := (1645/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487085363/27486773248) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1259InnerLog : WideLogData :=
  innerPair55Data

set_option maxRecDepth 1000000 in
private theorem leaf1259LocalValidity :
    LeafFacts leaf1259Box leaf1259Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1259Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743386624) }) = true
      norm_num [leaf1259Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1259CertificateValid :
    WideCertificateValid leaf1259Box leaf1259Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi117ValidityFacts
    leaf1259LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1259CoverageChecked :
    coverageCheck (innerAD leaf1259Box) leaf1259InnerLog = true := by
  rfl'

private theorem leaf1259InnerLogValid :
    leaf1259InnerLog.Valid 8 (innerAD leaf1259Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint46PositiveFacts.valid leaf1259CoverageChecked

private noncomputable def leaf1259InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1259InputLogOnePlusV_eq :
    leaf1259InputLogOnePlusV = outerEnclosure 24
      (leaf1259Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1259RoundedFacts : LeafRoundedFacts 8
    leaf1259Certificate.logOnePlusV leaf1259InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1259InputLogOnePlusV_eq }

private noncomputable def leaf1259Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi117InputQChi innerPair55Input
    leaf1259InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1259LowerChecked :
    lowerCheck 24 leaf1259Box leaf1259Inputs = true := by
  rfl'

private theorem leaf1259CoversExact : CoversExact 8
    leaf1259Box leaf1259Certificate leaf1259InnerLog leaf1259Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi117RoundedFacts
    innerPair55RoundedFacts leaf1259RoundedFacts (by rfl)

private theorem leaf1259FlatSound : Sound leaf1259Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1259CertificateValid
    leaf1259InnerLogValid leaf1259CoversExact leaf1259LowerChecked

private noncomputable def leaf1260Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1260Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435695/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716838912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (429414575/268435456) }, upper := { exponent := 0, mantissa := (417/256) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435332607/137433677824) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1260InnerLog : WideLogData :=
  innerPair186Data

set_option maxRecDepth 1000000 in
private theorem leaf1260LocalValidity :
    LeafFacts leaf1260Box leaf1260Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1260Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716838912) }) = true
      norm_num [leaf1260Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1260CertificateValid :
    WideCertificateValid leaf1260Box leaf1260Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi118ValidityFacts
    leaf1260LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1260CoverageChecked :
    coverageCheck (innerAD leaf1260Box) leaf1260InnerLog = true := by
  rfl'

private theorem leaf1260InnerLogValid :
    leaf1260InnerLog.Valid 8 (innerAD leaf1260Box) :=
  wideLogDataValid_of_cachedCheck endpoint54PositiveFacts
    endpoint126PositiveFacts.valid leaf1260CoverageChecked

private noncomputable def leaf1260InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629283/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1260InputLogOnePlusV_eq :
    leaf1260InputLogOnePlusV = outerEnclosure 24
      (leaf1260Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1260RoundedFacts : LeafRoundedFacts 8
    leaf1260Certificate.logOnePlusV leaf1260InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1260InputLogOnePlusV_eq }

private noncomputable def leaf1260Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi118InputQChi innerPair186Input
    leaf1260InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1260LowerChecked :
    lowerCheck 24 leaf1260Box leaf1260Inputs = true := by
  rfl'

private theorem leaf1260CoversExact : CoversExact 8
    leaf1260Box leaf1260Certificate leaf1260InnerLog leaf1260Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi118RoundedFacts
    innerPair186RoundedFacts leaf1260RoundedFacts (by rfl)

private theorem leaf1260FlatSound : Sound leaf1260Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1260CertificateValid
    leaf1260InnerLogValid leaf1260CoversExact leaf1260LowerChecked

private noncomputable def leaf1261Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1261Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435691/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717095936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (413097111/268435456) }, upper := { exponent := 0, mantissa := (6421/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435589631/137434191872) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1261InnerLog : WideLogData :=
  innerPair87Data

set_option maxRecDepth 1000000 in
private theorem leaf1261LocalValidity :
    LeafFacts leaf1261Box leaf1261Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1261Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717095936) }) = true
      norm_num [leaf1261Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1261CertificateValid :
    WideCertificateValid leaf1261Box leaf1261Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi115ValidityFacts
    leaf1261LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1261CoverageChecked :
    coverageCheck (innerAD leaf1261Box) leaf1261InnerLog = true := by
  rfl'

private theorem leaf1261InnerLogValid :
    leaf1261InnerLog.Valid 8 (innerAD leaf1261Box) :=
  wideLogDataValid_of_cachedCheck endpoint19PositiveFacts
    endpoint47PositiveFacts.valid leaf1261CoverageChecked

private noncomputable def leaf1261InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1261InputLogOnePlusV_eq :
    leaf1261InputLogOnePlusV = outerEnclosure 24
      (leaf1261Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1261RoundedFacts : LeafRoundedFacts 8
    leaf1261Certificate.logOnePlusV leaf1261InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1261InputLogOnePlusV_eq }

private noncomputable def leaf1261Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi115InputQChi innerPair87Input
    leaf1261InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1261LowerChecked :
    lowerCheck 24 leaf1261Box leaf1261Inputs = true := by
  rfl'

private theorem leaf1261CoversExact : CoversExact 8
    leaf1261Box leaf1261Certificate leaf1261InnerLog leaf1261Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi115RoundedFacts
    innerPair87RoundedFacts leaf1261RoundedFacts (by rfl)

private theorem leaf1261FlatSound : Sound leaf1261Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1261CertificateValid
    leaf1261InnerLogValid leaf1261CoversExact leaf1261LowerChecked

private noncomputable def leaf1262Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1262Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435693/268435456) }, vSqrt := { lower := (32765/32768), upper := (4042264335/4042176512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (419126053/268435456) }, upper := { exponent := 0, mantissa := (3257/2048) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (8084440847/8084353024) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1262InnerLog : WideLogData :=
  innerPair154Data

set_option maxRecDepth 1000000 in
private theorem leaf1262LocalValidity :
    LeafFacts leaf1262Box leaf1262Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1262Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (4042264335/4042176512) }) = true
      norm_num [leaf1262Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1262CertificateValid :
    WideCertificateValid leaf1262Box leaf1262Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi116ValidityFacts
    leaf1262LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1262CoverageChecked :
    coverageCheck (innerAD leaf1262Box) leaf1262InnerLog = true := by
  rfl'

private theorem leaf1262InnerLogValid :
    leaf1262InnerLog.Valid 8 (innerAD leaf1262Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint44PositiveFacts.valid leaf1262CoverageChecked

private noncomputable def leaf1262InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1262InputLogOnePlusV_eq :
    leaf1262InputLogOnePlusV = outerEnclosure 24
      (leaf1262Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1262RoundedFacts : LeafRoundedFacts 8
    leaf1262Certificate.logOnePlusV leaf1262InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1262InputLogOnePlusV_eq }

private noncomputable def leaf1262Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi116InputQChi innerPair154Input
    leaf1262InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1262LowerChecked :
    lowerCheck 24 leaf1262Box leaf1262Inputs = true := by
  rfl'

private theorem leaf1262CoversExact : CoversExact 8
    leaf1262Box leaf1262Certificate leaf1262InnerLog leaf1262Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi116RoundedFacts
    innerPair154RoundedFacts leaf1262RoundedFacts (by rfl)

private theorem leaf1262FlatSound : Sound leaf1262Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1262CertificateValid
    leaf1262InnerLogValid leaf1262CoversExact leaf1262LowerChecked

private noncomputable def leaf1263Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1263Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435693/268435456) }, vSqrt := { lower := (32765/32768), upper := (1347421445/1347393536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (414669877/268435456) }, upper := { exponent := 0, mantissa := (3223/2048) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (2694814981/2694787072) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf1263InnerLog : WideLogData :=
  innerPair184Data

set_option maxRecDepth 1000000 in
private theorem leaf1263LocalValidity :
    LeafFacts leaf1263Box leaf1263Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1263Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (1347421445/1347393536) }) = true
      norm_num [leaf1263Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1263CertificateValid :
    WideCertificateValid leaf1263Box leaf1263Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi115ValidityFacts
    leaf1263LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1263CoverageChecked :
    coverageCheck (innerAD leaf1263Box) leaf1263InnerLog = true := by
  rfl'

private theorem leaf1263InnerLogValid :
    leaf1263InnerLog.Valid 8 (innerAD leaf1263Box) :=
  wideLogDataValid_of_cachedCheck endpoint53PositiveFacts
    endpoint127PositiveFacts.valid leaf1263CoverageChecked

private noncomputable def leaf1263InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1263InputLogOnePlusV_eq :
    leaf1263InputLogOnePlusV = outerEnclosure 24
      (leaf1263Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1263RoundedFacts : LeafRoundedFacts 8
    leaf1263Certificate.logOnePlusV leaf1263InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1263InputLogOnePlusV_eq }

private noncomputable def leaf1263Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi115InputQChi innerPair184Input
    leaf1263InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1263LowerChecked :
    lowerCheck 24 leaf1263Box leaf1263Inputs = true := by
  rfl'

private theorem leaf1263CoversExact : CoversExact 8
    leaf1263Box leaf1263Certificate leaf1263InnerLog leaf1263Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi115RoundedFacts
    innerPair184RoundedFacts leaf1263RoundedFacts (by rfl)

private theorem leaf1263FlatSound : Sound leaf1263Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1263CertificateValid
    leaf1263InnerLogValid leaf1263CoversExact leaf1263LowerChecked

private noncomputable def leaf1264Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1264Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435695/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743394816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (420764351/268435456) }, upper := { exponent := 0, mantissa := (1635/1024) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487093555/27486789632) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf1264InnerLog : WideLogData :=
  innerPair417Data

set_option maxRecDepth 1000000 in
private theorem leaf1264LocalValidity :
    LeafFacts leaf1264Box leaf1264Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1264Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743394816) }) = true
      norm_num [leaf1264Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1264CertificateValid :
    WideCertificateValid leaf1264Box leaf1264Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi116ValidityFacts
    leaf1264LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1264CoverageChecked :
    coverageCheck (innerAD leaf1264Box) leaf1264InnerLog = true := by
  rfl'

private theorem leaf1264InnerLogValid :
    leaf1264InnerLog.Valid 8 (innerAD leaf1264Box) :=
  wideLogDataValid_of_cachedCheck endpoint128PositiveFacts
    endpoint129PositiveFacts.valid leaf1264CoverageChecked

private noncomputable def leaf1264InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814633/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1264InputLogOnePlusV_eq :
    leaf1264InputLogOnePlusV = outerEnclosure 24
      (leaf1264Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1264RoundedFacts : LeafRoundedFacts 8
    leaf1264Certificate.logOnePlusV leaf1264InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1264InputLogOnePlusV_eq }

private noncomputable def leaf1264Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi116InputQChi innerPair417Input
    leaf1264InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1264LowerChecked :
    lowerCheck 24 leaf1264Box leaf1264Inputs = true := by
  rfl'

private theorem leaf1264CoversExact : CoversExact 8
    leaf1264Box leaf1264Certificate leaf1264InnerLog leaf1264Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi116RoundedFacts
    innerPair417RoundedFacts leaf1264RoundedFacts (by rfl)

private theorem leaf1264FlatSound : Sound leaf1264Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1264CertificateValid
    leaf1264InnerLogValid leaf1264CoversExact leaf1264LowerChecked

private noncomputable def leaf1265Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (189/64), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1265Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871339/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137434115072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (832518103/536870912) }, upper := { exponent := 0, mantissa := (12917/8192) } }, logOuter := sk115LogOuterCertificate, logK := sk115LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274871036927/274868230144) } }, logDArg := sk115LogDArgCertificate }

private noncomputable def leaf1265InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf1265LocalValidity :
    LeafFacts leaf1265Box leaf1265Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1265Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137434115072) }) = true
      norm_num [leaf1265Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1265CertificateValid :
    WideCertificateValid leaf1265Box leaf1265Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk115ValidityFacts chi115ValidityFacts
    leaf1265LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1265CoverageChecked :
    coverageCheck (innerAD leaf1265Box) leaf1265InnerLog = true := by
  rfl'

private theorem leaf1265InnerLogValid :
    leaf1265InnerLog.Valid 8 (innerAD leaf1265Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf1265CoverageChecked

private noncomputable def leaf1265InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907313/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1265InputLogOnePlusV_eq :
    leaf1265InputLogOnePlusV = outerEnclosure 24
      (leaf1265Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1265RoundedFacts : LeafRoundedFacts 8
    leaf1265Certificate.logOnePlusV leaf1265InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1265InputLogOnePlusV_eq }

private noncomputable def leaf1265Inputs : Inputs :=
  inputsOfCaches globalInput sk115RoundedInputs
    chi115InputQChi innerPair41Input
    leaf1265InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1265LowerChecked :
    lowerCheck 24 leaf1265Box leaf1265Inputs = true := by
  rfl'

private theorem leaf1265CoversExact : CoversExact 8
    leaf1265Box leaf1265Certificate leaf1265InnerLog leaf1265Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk115RoundedFacts chi115RoundedFacts
    innerPair41RoundedFacts leaf1265RoundedFacts (by rfl)

private theorem leaf1265FlatSound : Sound leaf1265Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1265CertificateValid
    leaf1265InnerLogValid leaf1265CoversExact leaf1265LowerChecked

private noncomputable def leaf1266Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (189/64), kHi := (95/32), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1266Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871341/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137434089472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (834090869/536870912) }, upper := { exponent := 0, mantissa := (6471/4096) } }, logOuter := sk116LogOuterCertificate, logK := sk116LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274871011327/274868178944) } }, logDArg := sk116LogDArgCertificate }

private noncomputable def leaf1266InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf1266LocalValidity :
    LeafFacts leaf1266Box leaf1266Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1266Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137434089472) }) = true
      norm_num [leaf1266Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1266CertificateValid :
    WideCertificateValid leaf1266Box leaf1266Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk116ValidityFacts chi115ValidityFacts
    leaf1266LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1266CoverageChecked :
    coverageCheck (innerAD leaf1266Box) leaf1266InnerLog = true := by
  rfl'

private theorem leaf1266InnerLogValid :
    leaf1266InnerLog.Valid 8 (innerAD leaf1266Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf1266CoverageChecked

private noncomputable def leaf1266InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1266InputLogOnePlusV_eq :
    leaf1266InputLogOnePlusV = outerEnclosure 24
      (leaf1266Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1266RoundedFacts : LeafRoundedFacts 8
    leaf1266Certificate.logOnePlusV leaf1266InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1266InputLogOnePlusV_eq }

private noncomputable def leaf1266Inputs : Inputs :=
  inputsOfCaches globalInput sk116RoundedInputs
    chi115InputQChi innerPair41Input
    leaf1266InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1266LowerChecked :
    lowerCheck 24 leaf1266Box leaf1266Inputs = true := by
  rfl'

private theorem leaf1266CoversExact : CoversExact 8
    leaf1266Box leaf1266Certificate leaf1266InnerLog leaf1266Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk116RoundedFacts chi115RoundedFacts
    innerPair41RoundedFacts leaf1266RoundedFacts (by rfl)

private theorem leaf1266FlatSound : Sound leaf1266Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1266CertificateValid
    leaf1266InnerLogValid leaf1266CoversExact leaf1266LowerChecked

private noncomputable def leaf1267Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (191/64), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1267Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871343/536870912) }, vSqrt := { lower := (32765/32768), upper := (45812307285/45811354624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (835663635/536870912) }, upper := { exponent := 0, mantissa := (12967/8192) } }, logOuter := sk117LogOuterCertificate, logK := sk117LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (91623661909/91622709248) } }, logDArg := sk117LogDArgCertificate }

private noncomputable def leaf1267InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf1267LocalValidity :
    LeafFacts leaf1267Box leaf1267Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1267Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (45812307285/45811354624) }) = true
      norm_num [leaf1267Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1267CertificateValid :
    WideCertificateValid leaf1267Box leaf1267Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk117ValidityFacts chi115ValidityFacts
    leaf1267LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1267CoverageChecked :
    coverageCheck (innerAD leaf1267Box) leaf1267InnerLog = true := by
  rfl'

private theorem leaf1267InnerLogValid :
    leaf1267InnerLog.Valid 8 (innerAD leaf1267Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf1267CoverageChecked

private noncomputable def leaf1267InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1267InputLogOnePlusV_eq :
    leaf1267InputLogOnePlusV = outerEnclosure 24
      (leaf1267Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1267RoundedFacts : LeafRoundedFacts 8
    leaf1267Certificate.logOnePlusV leaf1267InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1267InputLogOnePlusV_eq }

private noncomputable def leaf1267Inputs : Inputs :=
  inputsOfCaches globalInput sk117RoundedInputs
    chi115InputQChi innerPair41Input
    leaf1267InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1267LowerChecked :
    lowerCheck 24 leaf1267Box leaf1267Inputs = true := by
  rfl'

private theorem leaf1267CoversExact : CoversExact 8
    leaf1267Box leaf1267Certificate leaf1267InnerLog leaf1267Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk117RoundedFacts chi115RoundedFacts
    innerPair41RoundedFacts leaf1267RoundedFacts (by rfl)

private theorem leaf1267FlatSound : Sound leaf1267Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1267CertificateValid
    leaf1267InnerLogValid leaf1267CoversExact leaf1267LowerChecked

private noncomputable def leaf1268Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (191/64), kHi := (3), chiLo := (3/16), chiHi := (25/128) }

private noncomputable def leaf1268Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871345/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137434038272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (837236401/536870912) }, upper := { exponent := 0, mantissa := (203/128) } }, logOuter := sk118LogOuterCertificate, logK := sk118LogKCertificate, logChi := chi115LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870960127/274868076544) } }, logDArg := sk118LogDArgCertificate }

private noncomputable def leaf1268InnerLog : WideLogData :=
  innerPair41Data

set_option maxRecDepth 1000000 in
private theorem leaf1268LocalValidity :
    LeafFacts leaf1268Box leaf1268Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1268Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137434038272) }) = true
      norm_num [leaf1268Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1268CertificateValid :
    WideCertificateValid leaf1268Box leaf1268Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk118ValidityFacts chi115ValidityFacts
    leaf1268LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1268CoverageChecked :
    coverageCheck (innerAD leaf1268Box) leaf1268InnerLog = true := by
  rfl'

private theorem leaf1268InnerLogValid :
    leaf1268InnerLog.Valid 8 (innerAD leaf1268Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint14PositiveFacts.valid leaf1268CoverageChecked

private noncomputable def leaf1268InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1268InputLogOnePlusV_eq :
    leaf1268InputLogOnePlusV = outerEnclosure 24
      (leaf1268Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1268RoundedFacts : LeafRoundedFacts 8
    leaf1268Certificate.logOnePlusV leaf1268InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1268InputLogOnePlusV_eq }

private noncomputable def leaf1268Inputs : Inputs :=
  inputsOfCaches globalInput sk118RoundedInputs
    chi115InputQChi innerPair41Input
    leaf1268InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1268LowerChecked :
    lowerCheck 24 leaf1268Box leaf1268Inputs = true := by
  rfl'

private theorem leaf1268CoversExact : CoversExact 8
    leaf1268Box leaf1268Certificate leaf1268InnerLog leaf1268Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk118RoundedFacts chi115RoundedFacts
    innerPair41RoundedFacts leaf1268RoundedFacts (by rfl)

private theorem leaf1268FlatSound : Sound leaf1268Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1268CertificateValid
    leaf1268InnerLogValid leaf1268CoversExact leaf1268LowerChecked

private noncomputable def leaf1269Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (189/64), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1269Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871341/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433921536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (844838117/536870912) }, upper := { exponent := 0, mantissa := (6553/4096) } }, logOuter := sk115LogOuterCertificate, logK := sk115LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274870843391/274867843072) } }, logDArg := sk115LogDArgCertificate }

private noncomputable def leaf1269InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1269LocalValidity :
    LeafFacts leaf1269Box leaf1269Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1269Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433921536) }) = true
      norm_num [leaf1269Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1269CertificateValid :
    WideCertificateValid leaf1269Box leaf1269Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk115ValidityFacts chi116ValidityFacts
    leaf1269LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1269CoverageChecked :
    coverageCheck (innerAD leaf1269Box) leaf1269InnerLog = true := by
  rfl'

private theorem leaf1269InnerLogValid :
    leaf1269InnerLog.Valid 8 (innerAD leaf1269Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1269CoverageChecked

private noncomputable def leaf1269InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726829/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1269InputLogOnePlusV_eq :
    leaf1269InputLogOnePlusV = outerEnclosure 24
      (leaf1269Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1269RoundedFacts : LeafRoundedFacts 8
    leaf1269Certificate.logOnePlusV leaf1269InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1269InputLogOnePlusV_eq }

private noncomputable def leaf1269Inputs : Inputs :=
  inputsOfCaches globalInput sk115RoundedInputs
    chi116InputQChi innerPair50Input
    leaf1269InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1269LowerChecked :
    lowerCheck 24 leaf1269Box leaf1269Inputs = true := by
  rfl'

private theorem leaf1269CoversExact : CoversExact 8
    leaf1269Box leaf1269Certificate leaf1269InnerLog leaf1269Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk115RoundedFacts chi116RoundedFacts
    innerPair50RoundedFacts leaf1269RoundedFacts (by rfl)

private theorem leaf1269FlatSound : Sound leaf1269Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1269CertificateValid
    leaf1269InnerLogValid leaf1269CoversExact leaf1269LowerChecked

private noncomputable def leaf1270Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (189/64), kHi := (95/32), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1270Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871343/536870912) }, vSqrt := { lower := (32765/32768), upper := (5090256365/5090144256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (846476415/536870912) }, upper := { exponent := 0, mantissa := (3283/2048) } }, logOuter := sk116LogOuterCertificate, logK := sk116LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (10180400621/10180288512) } }, logDArg := sk116LogDArgCertificate }

private noncomputable def leaf1270InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1270LocalValidity :
    LeafFacts leaf1270Box leaf1270Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1270Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (5090256365/5090144256) }) = true
      norm_num [leaf1270Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1270CertificateValid :
    WideCertificateValid leaf1270Box leaf1270Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk116ValidityFacts chi116ValidityFacts
    leaf1270LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1270CoverageChecked :
    coverageCheck (innerAD leaf1270Box) leaf1270InnerLog = true := by
  rfl'

private theorem leaf1270InnerLogValid :
    leaf1270InnerLog.Valid 8 (innerAD leaf1270Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1270CoverageChecked

private noncomputable def leaf1270InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1270InputLogOnePlusV_eq :
    leaf1270InputLogOnePlusV = outerEnclosure 24
      (leaf1270Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1270RoundedFacts : LeafRoundedFacts 8
    leaf1270Certificate.logOnePlusV leaf1270InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1270InputLogOnePlusV_eq }

private noncomputable def leaf1270Inputs : Inputs :=
  inputsOfCaches globalInput sk116RoundedInputs
    chi116InputQChi innerPair50Input
    leaf1270InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1270LowerChecked :
    lowerCheck 24 leaf1270Box leaf1270Inputs = true := by
  rfl'

private theorem leaf1270CoversExact : CoversExact 8
    leaf1270Box leaf1270Certificate leaf1270InnerLog leaf1270Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk116RoundedFacts chi116RoundedFacts
    innerPair50RoundedFacts leaf1270RoundedFacts (by rfl)

private theorem leaf1270FlatSound : Sound leaf1270Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1270CertificateValid
    leaf1270InnerLogValid leaf1270CoversExact leaf1270LowerChecked

private noncomputable def leaf1271Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (191/64), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1271Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871345/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433868288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (848114713/536870912) }, upper := { exponent := 0, mantissa := (6579/4096) } }, logOuter := sk117LogOuterCertificate, logK := sk117LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274870790143/274867736576) } }, logDArg := sk117LogDArgCertificate }

private noncomputable def leaf1271InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1271LocalValidity :
    LeafFacts leaf1271Box leaf1271Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1271Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433868288) }) = true
      norm_num [leaf1271Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1271CertificateValid :
    WideCertificateValid leaf1271Box leaf1271Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk117ValidityFacts chi116ValidityFacts
    leaf1271LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1271CoverageChecked :
    coverageCheck (innerAD leaf1271Box) leaf1271InnerLog = true := by
  rfl'

private theorem leaf1271InnerLogValid :
    leaf1271InnerLog.Valid 8 (innerAD leaf1271Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1271CoverageChecked

private noncomputable def leaf1271InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1271InputLogOnePlusV_eq :
    leaf1271InputLogOnePlusV = outerEnclosure 24
      (leaf1271Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1271RoundedFacts : LeafRoundedFacts 8
    leaf1271Certificate.logOnePlusV leaf1271InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1271InputLogOnePlusV_eq }

private noncomputable def leaf1271Inputs : Inputs :=
  inputsOfCaches globalInput sk117RoundedInputs
    chi116InputQChi innerPair50Input
    leaf1271InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1271LowerChecked :
    lowerCheck 24 leaf1271Box leaf1271Inputs = true := by
  rfl'

private theorem leaf1271CoversExact : CoversExact 8
    leaf1271Box leaf1271Certificate leaf1271InnerLog leaf1271Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk117RoundedFacts chi116RoundedFacts
    innerPair50RoundedFacts leaf1271RoundedFacts (by rfl)

private theorem leaf1271FlatSound : Sound leaf1271Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1271CertificateValid
    leaf1271InnerLogValid leaf1271CoversExact leaf1271LowerChecked

private noncomputable def leaf1272Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (191/64), kHi := (3), chiLo := (25/128), chiHi := (13/64) }

private noncomputable def leaf1272Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871347/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433841664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (849753011/536870912) }, upper := { exponent := 0, mantissa := (103/64) } }, logOuter := sk118LogOuterCertificate, logK := sk118LogKCertificate, logChi := chi116LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870763519/274867683328) } }, logDArg := sk118LogDArgCertificate }

private noncomputable def leaf1272InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1272LocalValidity :
    LeafFacts leaf1272Box leaf1272Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1272Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433841664) }) = true
      norm_num [leaf1272Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1272CertificateValid :
    WideCertificateValid leaf1272Box leaf1272Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk118ValidityFacts chi116ValidityFacts
    leaf1272LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1272CoverageChecked :
    coverageCheck (innerAD leaf1272Box) leaf1272InnerLog = true := by
  rfl'

private theorem leaf1272InnerLogValid :
    leaf1272InnerLog.Valid 8 (innerAD leaf1272Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1272CoverageChecked

private noncomputable def leaf1272InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1272InputLogOnePlusV_eq :
    leaf1272InputLogOnePlusV = outerEnclosure 24
      (leaf1272Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1272RoundedFacts : LeafRoundedFacts 8
    leaf1272Certificate.logOnePlusV leaf1272InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1272InputLogOnePlusV_eq }

private noncomputable def leaf1272Inputs : Inputs :=
  inputsOfCaches globalInput sk118RoundedInputs
    chi116InputQChi innerPair50Input
    leaf1272InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1272LowerChecked :
    lowerCheck 24 leaf1272Box leaf1272Inputs = true := by
  rfl'

private theorem leaf1272CoversExact : CoversExact 8
    leaf1272Box leaf1272Certificate leaf1272InnerLog leaf1272Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk118RoundedFacts chi116RoundedFacts
    innerPair50RoundedFacts leaf1272RoundedFacts (by rfl)

private theorem leaf1272FlatSound : Sound leaf1272Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1272CertificateValid
    leaf1272InnerLogValid leaf1272CoversExact leaf1272LowerChecked

private noncomputable def leaf1273Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1273Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435695/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716905472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (425154995/268435456) }, upper := { exponent := 0, mantissa := (6607/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435399167/137433810944) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1273InnerLog : WideLogData :=
  innerPair418Data

set_option maxRecDepth 1000000 in
private theorem leaf1273LocalValidity :
    LeafFacts leaf1273Box leaf1273Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1273Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716905472) }) = true
      norm_num [leaf1273Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1273CertificateValid :
    WideCertificateValid leaf1273Box leaf1273Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi117ValidityFacts
    leaf1273LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1273CoverageChecked :
    coverageCheck (innerAD leaf1273Box) leaf1273InnerLog = true := by
  rfl'

private theorem leaf1273InnerLogValid :
    leaf1273InnerLog.Valid 8 (innerAD leaf1273Box) :=
  wideLogDataValid_of_cachedCheck endpoint130PositiveFacts
    endpoint131PositiveFacts.valid leaf1273CoverageChecked

private noncomputable def leaf1273InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629275/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1273InputLogOnePlusV_eq :
    leaf1273InputLogOnePlusV = outerEnclosure 24
      (leaf1273Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1273RoundedFacts : LeafRoundedFacts 8
    leaf1273Certificate.logOnePlusV leaf1273InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1273InputLogOnePlusV_eq }

private noncomputable def leaf1273Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi117InputQChi innerPair418Input
    leaf1273InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1273LowerChecked :
    lowerCheck 24 leaf1273Box leaf1273Inputs = true := by
  rfl'

private theorem leaf1273CoversExact : CoversExact 8
    leaf1273Box leaf1273Certificate leaf1273InnerLog leaf1273Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi117RoundedFacts
    innerPair418RoundedFacts leaf1273RoundedFacts (by rfl)

private theorem leaf1273FlatSound : Sound leaf1273Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1273CertificateValid
    leaf1273InnerLogValid leaf1273CoversExact leaf1273LowerChecked

private noncomputable def leaf1274Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1274Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435697/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743362048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (431183937/268435456) }, upper := { exponent := 0, mantissa := (1675/1024) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487060787/27486724096) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1274InnerLog : WideLogData :=
  innerPair195Data

set_option maxRecDepth 1000000 in
private theorem leaf1274LocalValidity :
    LeafFacts leaf1274Box leaf1274Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1274Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743362048) }) = true
      norm_num [leaf1274Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1274CertificateValid :
    WideCertificateValid leaf1274Box leaf1274Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi118ValidityFacts
    leaf1274LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1274CoverageChecked :
    coverageCheck (innerAD leaf1274Box) leaf1274InnerLog = true := by
  rfl'

private theorem leaf1274InnerLogValid :
    leaf1274InnerLog.Valid 8 (innerAD leaf1274Box) :=
  wideLogDataValid_of_cachedCheck endpoint57PositiveFacts
    endpoint132PositiveFacts.valid leaf1274CoverageChecked

private noncomputable def leaf1274InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1274InputLogOnePlusV_eq :
    leaf1274InputLogOnePlusV = outerEnclosure 24
      (leaf1274Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1274RoundedFacts : LeafRoundedFacts 8
    leaf1274Certificate.logOnePlusV leaf1274InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1274InputLogOnePlusV_eq }

private noncomputable def leaf1274Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi118InputQChi innerPair195Input
    leaf1274InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1274LowerChecked :
    lowerCheck 24 leaf1274Box leaf1274Inputs = true := by
  rfl'

private theorem leaf1274CoversExact : CoversExact 8
    leaf1274Box leaf1274Certificate leaf1274InnerLog leaf1274Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi118RoundedFacts
    innerPair195RoundedFacts leaf1274RoundedFacts (by rfl)

private theorem leaf1274FlatSound : Sound leaf1274Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1274CertificateValid
    leaf1274InnerLogValid leaf1274CoversExact leaf1274LowerChecked

private noncomputable def leaf1275Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (187/64), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1275Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871339/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433783296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (853750471/536870912) }, upper := { exponent := 0, mantissa := (13241/8192) } }, logOuter := sk119LogOuterCertificate, logK := sk119LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274870705151/274867566592) } }, logDArg := sk119LogDArgCertificate }

private noncomputable def leaf1275InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1275LocalValidity :
    LeafFacts leaf1275Box leaf1275Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1275Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433783296) }) = true
      norm_num [leaf1275Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1275CertificateValid :
    WideCertificateValid leaf1275Box leaf1275Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk119ValidityFacts chi117ValidityFacts
    leaf1275LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1275CoverageChecked :
    coverageCheck (innerAD leaf1275Box) leaf1275InnerLog = true := by
  rfl'

private theorem leaf1275InnerLogValid :
    leaf1275InnerLog.Valid 8 (innerAD leaf1275Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1275CoverageChecked

private noncomputable def leaf1275InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1275InputLogOnePlusV_eq :
    leaf1275InputLogOnePlusV = outerEnclosure 24
      (leaf1275Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1275RoundedFacts : LeafRoundedFacts 8
    leaf1275Certificate.logOnePlusV leaf1275InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1275InputLogOnePlusV_eq }

private noncomputable def leaf1275Inputs : Inputs :=
  inputsOfCaches globalInput sk119RoundedInputs
    chi117InputQChi innerPair50Input
    leaf1275InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1275LowerChecked :
    lowerCheck 24 leaf1275Box leaf1275Inputs = true := by
  rfl'

private theorem leaf1275CoversExact : CoversExact 8
    leaf1275Box leaf1275Certificate leaf1275InnerLog leaf1275Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk119RoundedFacts chi117RoundedFacts
    innerPair50RoundedFacts leaf1275RoundedFacts (by rfl)

private theorem leaf1275FlatSound : Sound leaf1275Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1275CertificateValid
    leaf1275InnerLogValid leaf1275CoversExact leaf1275LowerChecked

private noncomputable def leaf1276Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (187/64), kHi := (47/16), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1276Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871341/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433755648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (855454301/536870912) }, upper := { exponent := 0, mantissa := (3317/2048) } }, logOuter := sk120LogOuterCertificate, logK := sk120LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274870677503/274867511296) } }, logDArg := sk120LogDArgCertificate }

private noncomputable def leaf1276InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1276LocalValidity :
    LeafFacts leaf1276Box leaf1276Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1276Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433755648) }) = true
      norm_num [leaf1276Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1276CertificateValid :
    WideCertificateValid leaf1276Box leaf1276Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk120ValidityFacts chi117ValidityFacts
    leaf1276LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1276CoverageChecked :
    coverageCheck (innerAD leaf1276Box) leaf1276InnerLog = true := by
  rfl'

private theorem leaf1276InnerLogValid :
    leaf1276InnerLog.Valid 8 (innerAD leaf1276Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1276CoverageChecked

private noncomputable def leaf1276InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814637/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1276InputLogOnePlusV_eq :
    leaf1276InputLogOnePlusV = outerEnclosure 24
      (leaf1276Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1276RoundedFacts : LeafRoundedFacts 8
    leaf1276Certificate.logOnePlusV leaf1276InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1276InputLogOnePlusV_eq }

private noncomputable def leaf1276Inputs : Inputs :=
  inputsOfCaches globalInput sk120RoundedInputs
    chi117InputQChi innerPair50Input
    leaf1276InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1276LowerChecked :
    lowerCheck 24 leaf1276Box leaf1276Inputs = true := by
  rfl'

private theorem leaf1276CoversExact : CoversExact 8
    leaf1276Box leaf1276Certificate leaf1276InnerLog leaf1276Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk120RoundedFacts chi117RoundedFacts
    innerPair50RoundedFacts leaf1276RoundedFacts (by rfl)

private theorem leaf1276FlatSound : Sound leaf1276Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1276CertificateValid
    leaf1276InnerLogValid leaf1276CoversExact leaf1276LowerChecked

private noncomputable def leaf1277Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (187/64), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1277Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871341/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433591808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (865939421/536870912) }, upper := { exponent := 0, mantissa := (3357/2048) } }, logOuter := sk119LogOuterCertificate, logK := sk119LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274870513663/274867183616) } }, logDArg := sk119LogDArgCertificate }

private noncomputable def leaf1277InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf1277LocalValidity :
    LeafFacts leaf1277Box leaf1277Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1277Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433591808) }) = true
      norm_num [leaf1277Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1277CertificateValid :
    WideCertificateValid leaf1277Box leaf1277Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk119ValidityFacts chi118ValidityFacts
    leaf1277LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1277CoverageChecked :
    coverageCheck (innerAD leaf1277Box) leaf1277InnerLog = true := by
  rfl'

private theorem leaf1277InnerLogValid :
    leaf1277InnerLog.Valid 8 (innerAD leaf1277Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf1277CoverageChecked

private noncomputable def leaf1277InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1277InputLogOnePlusV_eq :
    leaf1277InputLogOnePlusV = outerEnclosure 24
      (leaf1277Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1277RoundedFacts : LeafRoundedFacts 8
    leaf1277Certificate.logOnePlusV leaf1277InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1277InputLogOnePlusV_eq }

private noncomputable def leaf1277Inputs : Inputs :=
  inputsOfCaches globalInput sk119RoundedInputs
    chi118InputQChi innerPair51Input
    leaf1277InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1277LowerChecked :
    lowerCheck 24 leaf1277Box leaf1277Inputs = true := by
  rfl'

private theorem leaf1277CoversExact : CoversExact 8
    leaf1277Box leaf1277Certificate leaf1277InnerLog leaf1277Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk119RoundedFacts chi118RoundedFacts
    innerPair51RoundedFacts leaf1277RoundedFacts (by rfl)

private theorem leaf1277FlatSound : Sound leaf1277Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1277CertificateValid
    leaf1277InnerLogValid leaf1277CoversExact leaf1277LowerChecked

private noncomputable def leaf1278Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (187/64), kHi := (47/16), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1278Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871343/536870912) }, vSqrt := { lower := (32765/32768), upper := (5090256365/5090131968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (867708783/536870912) }, upper := { exponent := 0, mantissa := (841/512) } }, logOuter := sk120LogOuterCertificate, logK := sk120LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (10180388333/10180263936) } }, logDArg := sk120LogDArgCertificate }

private noncomputable def leaf1278InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf1278LocalValidity :
    LeafFacts leaf1278Box leaf1278Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1278Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (5090256365/5090131968) }) = true
      norm_num [leaf1278Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1278CertificateValid :
    WideCertificateValid leaf1278Box leaf1278Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk120ValidityFacts chi118ValidityFacts
    leaf1278LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1278CoverageChecked :
    coverageCheck (innerAD leaf1278Box) leaf1278InnerLog = true := by
  rfl'

private theorem leaf1278InnerLogValid :
    leaf1278InnerLog.Valid 8 (innerAD leaf1278Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf1278CoverageChecked

private noncomputable def leaf1278InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1278InputLogOnePlusV_eq :
    leaf1278InputLogOnePlusV = outerEnclosure 24
      (leaf1278Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1278RoundedFacts : LeafRoundedFacts 8
    leaf1278Certificate.logOnePlusV leaf1278InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1278InputLogOnePlusV_eq }

private noncomputable def leaf1278Inputs : Inputs :=
  inputsOfCaches globalInput sk120RoundedInputs
    chi118InputQChi innerPair51Input
    leaf1278InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1278LowerChecked :
    lowerCheck 24 leaf1278Box leaf1278Inputs = true := by
  rfl'

private theorem leaf1278CoversExact : CoversExact 8
    leaf1278Box leaf1278Certificate leaf1278InnerLog leaf1278Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk120RoundedFacts chi118RoundedFacts
    innerPair51RoundedFacts leaf1278RoundedFacts (by rfl)

private theorem leaf1278FlatSound : Sound leaf1278Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1278CertificateValid
    leaf1278InnerLogValid leaf1278CoversExact leaf1278LowerChecked

private noncomputable def leaf1279Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (189/64), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1279Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871343/536870912) }, vSqrt := { lower := (32765/32768), upper := (27487384371/27486745600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (857158131/536870912) }, upper := { exponent := 0, mantissa := (13295/8192) } }, logOuter := sk115LogOuterCertificate, logK := sk115LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (54974129971/54973491200) } }, logDArg := sk115LogDArgCertificate }

private noncomputable def leaf1279InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf1279LocalValidity :
    LeafFacts leaf1279Box leaf1279Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1279Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (27487384371/27486745600) }) = true
      norm_num [leaf1279Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1279CertificateValid :
    WideCertificateValid leaf1279Box leaf1279Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk115ValidityFacts chi117ValidityFacts
    leaf1279LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1279CoverageChecked :
    coverageCheck (innerAD leaf1279Box) leaf1279InnerLog = true := by
  rfl'

private theorem leaf1279InnerLogValid :
    leaf1279InnerLog.Valid 8 (innerAD leaf1279Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf1279CoverageChecked

private noncomputable def leaf1279InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1279InputLogOnePlusV_eq :
    leaf1279InputLogOnePlusV = outerEnclosure 24
      (leaf1279Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1279RoundedFacts : LeafRoundedFacts 8
    leaf1279Certificate.logOnePlusV leaf1279InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1279InputLogOnePlusV_eq }

private noncomputable def leaf1279Inputs : Inputs :=
  inputsOfCaches globalInput sk115RoundedInputs
    chi117InputQChi innerPair50Input
    leaf1279InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1279LowerChecked :
    lowerCheck 24 leaf1279Box leaf1279Inputs = true := by
  rfl'

private theorem leaf1279CoversExact : CoversExact 8
    leaf1279Box leaf1279Certificate leaf1279InnerLog leaf1279Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk115RoundedFacts chi117RoundedFacts
    innerPair50RoundedFacts leaf1279RoundedFacts (by rfl)

private theorem leaf1279FlatSound : Sound leaf1279Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1279CertificateValid
    leaf1279InnerLogValid leaf1279CoversExact leaf1279LowerChecked

private noncomputable def leaf1280Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (189/64), kHi := (95/32), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1280Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871345/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433700352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (858861961/536870912) }, upper := { exponent := 0, mantissa := (6661/4096) } }, logOuter := sk116LogOuterCertificate, logK := sk116LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274870622207/274867400704) } }, logDArg := sk116LogDArgCertificate }

private noncomputable def leaf1280InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf1280LocalValidity :
    LeafFacts leaf1280Box leaf1280Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1280Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433700352) }) = true
      norm_num [leaf1280Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1280CertificateValid :
    WideCertificateValid leaf1280Box leaf1280Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk116ValidityFacts chi117ValidityFacts
    leaf1280LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1280CoverageChecked :
    coverageCheck (innerAD leaf1280Box) leaf1280InnerLog = true := by
  rfl'

private theorem leaf1280InnerLogValid :
    leaf1280InnerLog.Valid 8 (innerAD leaf1280Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf1280CoverageChecked

private noncomputable def leaf1280InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1280InputLogOnePlusV_eq :
    leaf1280InputLogOnePlusV = outerEnclosure 24
      (leaf1280Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1280RoundedFacts : LeafRoundedFacts 8
    leaf1280Certificate.logOnePlusV leaf1280InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1280InputLogOnePlusV_eq }

private noncomputable def leaf1280Inputs : Inputs :=
  inputsOfCaches globalInput sk116RoundedInputs
    chi117InputQChi innerPair51Input
    leaf1280InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1280LowerChecked :
    lowerCheck 24 leaf1280Box leaf1280Inputs = true := by
  rfl'

private theorem leaf1280CoversExact : CoversExact 8
    leaf1280Box leaf1280Certificate leaf1280InnerLog leaf1280Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk116RoundedFacts chi117RoundedFacts
    innerPair51RoundedFacts leaf1280RoundedFacts (by rfl)

private theorem leaf1280FlatSound : Sound leaf1280Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1280CertificateValid
    leaf1280InnerLogValid leaf1280CoversExact leaf1280LowerChecked

private noncomputable def leaf1281Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (189/64), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1281Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871345/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433534464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (869478145/536870912) }, upper := { exponent := 0, mantissa := (3371/2048) } }, logOuter := sk115LogOuterCertificate, logK := sk115LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274870456319/274867068928) } }, logDArg := sk115LogDArgCertificate }

private noncomputable def leaf1281InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf1281LocalValidity :
    LeafFacts leaf1281Box leaf1281Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1281Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433534464) }) = true
      norm_num [leaf1281Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1281CertificateValid :
    WideCertificateValid leaf1281Box leaf1281Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk115ValidityFacts chi118ValidityFacts
    leaf1281LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1281CoverageChecked :
    coverageCheck (innerAD leaf1281Box) leaf1281InnerLog = true := by
  rfl'

private theorem leaf1281InnerLogValid :
    leaf1281InnerLog.Valid 8 (innerAD leaf1281Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf1281CoverageChecked

private noncomputable def leaf1281InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453661/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1281InputLogOnePlusV_eq :
    leaf1281InputLogOnePlusV = outerEnclosure 24
      (leaf1281Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1281RoundedFacts : LeafRoundedFacts 8
    leaf1281Certificate.logOnePlusV leaf1281InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1281InputLogOnePlusV_eq }

private noncomputable def leaf1281Inputs : Inputs :=
  inputsOfCaches globalInput sk115RoundedInputs
    chi118InputQChi innerPair51Input
    leaf1281InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1281LowerChecked :
    lowerCheck 24 leaf1281Box leaf1281Inputs = true := by
  rfl'

private theorem leaf1281CoversExact : CoversExact 8
    leaf1281Box leaf1281Certificate leaf1281InnerLog leaf1281Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk115RoundedFacts chi118RoundedFacts
    innerPair51RoundedFacts leaf1281RoundedFacts (by rfl)

private theorem leaf1281FlatSound : Sound leaf1281Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1281CertificateValid
    leaf1281InnerLogValid leaf1281CoversExact leaf1281LowerChecked

private noncomputable def leaf1282Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (189/64), kHi := (95/32), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1282Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871347/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433505792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (871247507/536870912) }, upper := { exponent := 0, mantissa := (1689/1024) } }, logOuter := sk116LogOuterCertificate, logK := sk116LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274870427647/274867011584) } }, logDArg := sk116LogDArgCertificate }

private noncomputable def leaf1282InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf1282LocalValidity :
    LeafFacts leaf1282Box leaf1282Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1282Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433505792) }) = true
      norm_num [leaf1282Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1282CertificateValid :
    WideCertificateValid leaf1282Box leaf1282Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk116ValidityFacts chi118ValidityFacts
    leaf1282LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1282CoverageChecked :
    coverageCheck (innerAD leaf1282Box) leaf1282InnerLog = true := by
  rfl'

private theorem leaf1282InnerLogValid :
    leaf1282InnerLog.Valid 8 (innerAD leaf1282Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf1282CoverageChecked

private noncomputable def leaf1282InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1282InputLogOnePlusV_eq :
    leaf1282InputLogOnePlusV = outerEnclosure 24
      (leaf1282Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1282RoundedFacts : LeafRoundedFacts 8
    leaf1282Certificate.logOnePlusV leaf1282InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1282InputLogOnePlusV_eq }

private noncomputable def leaf1282Inputs : Inputs :=
  inputsOfCaches globalInput sk116RoundedInputs
    chi118InputQChi innerPair51Input
    leaf1282InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1282LowerChecked :
    lowerCheck 24 leaf1282Box leaf1282Inputs = true := by
  rfl'

private theorem leaf1282CoversExact : CoversExact 8
    leaf1282Box leaf1282Certificate leaf1282InnerLog leaf1282Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk116RoundedFacts chi118RoundedFacts
    innerPair51RoundedFacts leaf1282RoundedFacts (by rfl)

private theorem leaf1282FlatSound : Sound leaf1282Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1282CertificateValid
    leaf1282InnerLogValid leaf1282CoversExact leaf1282LowerChecked

private noncomputable def leaf1283Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (191/64), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1283Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871347/536870912) }, vSqrt := { lower := (32765/32768), upper := (137436921855/137433672704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (860565791/536870912) }, upper := { exponent := 0, mantissa := (13349/8192) } }, logOuter := sk117LogOuterCertificate, logK := sk117LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (274870594559/274867345408) } }, logDArg := sk117LogDArgCertificate }

private noncomputable def leaf1283InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf1283LocalValidity :
    LeafFacts leaf1283Box leaf1283Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1283Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (137436921855/137433672704) }) = true
      norm_num [leaf1283Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1283CertificateValid :
    WideCertificateValid leaf1283Box leaf1283Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk117ValidityFacts chi117ValidityFacts
    leaf1283LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1283CoverageChecked :
    coverageCheck (innerAD leaf1283Box) leaf1283InnerLog = true := by
  rfl'

private theorem leaf1283InnerLogValid :
    leaf1283InnerLog.Valid 8 (innerAD leaf1283Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf1283CoverageChecked

private noncomputable def leaf1283InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1283InputLogOnePlusV_eq :
    leaf1283InputLogOnePlusV = outerEnclosure 24
      (leaf1283Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1283RoundedFacts : LeafRoundedFacts 8
    leaf1283Certificate.logOnePlusV leaf1283InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1283InputLogOnePlusV_eq }

private noncomputable def leaf1283Inputs : Inputs :=
  inputsOfCaches globalInput sk117RoundedInputs
    chi117InputQChi innerPair51Input
    leaf1283InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1283LowerChecked :
    lowerCheck 24 leaf1283Box leaf1283Inputs = true := by
  rfl'

private theorem leaf1283CoversExact : CoversExact 8
    leaf1283Box leaf1283Certificate leaf1283InnerLog leaf1283Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk117RoundedFacts chi117RoundedFacts
    innerPair51RoundedFacts leaf1283RoundedFacts (by rfl)

private theorem leaf1283FlatSound : Sound leaf1283Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1283CertificateValid
    leaf1283InnerLogValid leaf1283CoversExact leaf1283LowerChecked

private noncomputable def leaf1284Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (191/64), kHi := (3), chiLo := (13/64), chiHi := (27/128) }

private noncomputable def leaf1284Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871349/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433645056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (862269621/536870912) }, upper := { exponent := 0, mantissa := (209/128) } }, logOuter := sk118LogOuterCertificate, logK := sk118LogKCertificate, logChi := chi117LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870566911/274867290112) } }, logDArg := sk118LogDArgCertificate }

private noncomputable def leaf1284InnerLog : WideLogData :=
  innerPair51Data

set_option maxRecDepth 1000000 in
private theorem leaf1284LocalValidity :
    LeafFacts leaf1284Box leaf1284Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1284Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433645056) }) = true
      norm_num [leaf1284Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1284CertificateValid :
    WideCertificateValid leaf1284Box leaf1284Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk118ValidityFacts chi117ValidityFacts
    leaf1284LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1284CoverageChecked :
    coverageCheck (innerAD leaf1284Box) leaf1284InnerLog = true := by
  rfl'

private theorem leaf1284InnerLogValid :
    leaf1284InnerLog.Valid 8 (innerAD leaf1284Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint15PositiveFacts.valid leaf1284CoverageChecked

private noncomputable def leaf1284InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1284InputLogOnePlusV_eq :
    leaf1284InputLogOnePlusV = outerEnclosure 24
      (leaf1284Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1284RoundedFacts : LeafRoundedFacts 8
    leaf1284Certificate.logOnePlusV leaf1284InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1284InputLogOnePlusV_eq }

private noncomputable def leaf1284Inputs : Inputs :=
  inputsOfCaches globalInput sk118RoundedInputs
    chi117InputQChi innerPair51Input
    leaf1284InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1284LowerChecked :
    lowerCheck 24 leaf1284Box leaf1284Inputs = true := by
  rfl'

private theorem leaf1284CoversExact : CoversExact 8
    leaf1284Box leaf1284Certificate leaf1284InnerLog leaf1284Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk118RoundedFacts chi117RoundedFacts
    innerPair51RoundedFacts leaf1284RoundedFacts (by rfl)

private theorem leaf1284FlatSound : Sound leaf1284Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1284CertificateValid
    leaf1284InnerLogValid leaf1284CoversExact leaf1284LowerChecked

private noncomputable def leaf1285Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (191/64), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1285Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871349/536870912) }, vSqrt := { lower := (32765/32768), upper := (9162461457/9162231808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (873016869/536870912) }, upper := { exponent := 0, mantissa := (3385/2048) } }, logOuter := sk117LogOuterCertificate, logK := sk117LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (18324693265/18324463616) } }, logDArg := sk117LogDArgCertificate }

private noncomputable def leaf1285InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1285LocalValidity :
    LeafFacts leaf1285Box leaf1285Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1285Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (9162461457/9162231808) }) = true
      norm_num [leaf1285Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1285CertificateValid :
    WideCertificateValid leaf1285Box leaf1285Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk117ValidityFacts chi118ValidityFacts
    leaf1285LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1285CoverageChecked :
    coverageCheck (innerAD leaf1285Box) leaf1285InnerLog = true := by
  rfl'

private theorem leaf1285InnerLogValid :
    leaf1285InnerLog.Valid 8 (innerAD leaf1285Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1285CoverageChecked

private noncomputable def leaf1285InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1285InputLogOnePlusV_eq :
    leaf1285InputLogOnePlusV = outerEnclosure 24
      (leaf1285Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1285RoundedFacts : LeafRoundedFacts 8
    leaf1285Certificate.logOnePlusV leaf1285InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1285InputLogOnePlusV_eq }

private noncomputable def leaf1285Inputs : Inputs :=
  inputsOfCaches globalInput sk117RoundedInputs
    chi118InputQChi innerPair56Input
    leaf1285InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1285LowerChecked :
    lowerCheck 24 leaf1285Box leaf1285Inputs = true := by
  rfl'

private theorem leaf1285CoversExact : CoversExact 8
    leaf1285Box leaf1285Certificate leaf1285InnerLog leaf1285Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk117RoundedFacts chi118RoundedFacts
    innerPair56RoundedFacts leaf1285RoundedFacts (by rfl)

private theorem leaf1285FlatSound : Sound leaf1285Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1285CertificateValid
    leaf1285InnerLogValid leaf1285CoversExact leaf1285LowerChecked

private noncomputable def leaf1286Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (191/64), kHi := (3), chiLo := (27/128), chiHi := (7/32) }

private noncomputable def leaf1286Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871351/536870912) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137433448448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (874786231/536870912) }, upper := { exponent := 0, mantissa := (53/32) } }, logOuter := sk118LogOuterCertificate, logK := sk118LogKCertificate, logChi := chi118LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274870370303/274866896896) } }, logDArg := sk118LogDArgCertificate }

private noncomputable def leaf1286InnerLog : WideLogData :=
  innerPair56Data

set_option maxRecDepth 1000000 in
private theorem leaf1286LocalValidity :
    LeafFacts leaf1286Box leaf1286Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1286Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137433448448) }) = true
      norm_num [leaf1286Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1286CertificateValid :
    WideCertificateValid leaf1286Box leaf1286Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk118ValidityFacts chi118ValidityFacts
    leaf1286LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1286CoverageChecked :
    coverageCheck (innerAD leaf1286Box) leaf1286InnerLog = true := by
  rfl'

private theorem leaf1286InnerLogValid :
    leaf1286InnerLog.Valid 8 (innerAD leaf1286Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint15PositiveFacts.valid leaf1286CoverageChecked

private noncomputable def leaf1286InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1286InputLogOnePlusV_eq :
    leaf1286InputLogOnePlusV = outerEnclosure 24
      (leaf1286Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1286RoundedFacts : LeafRoundedFacts 8
    leaf1286Certificate.logOnePlusV leaf1286InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1286InputLogOnePlusV_eq }

private noncomputable def leaf1286Inputs : Inputs :=
  inputsOfCaches globalInput sk118RoundedInputs
    chi118InputQChi innerPair56Input
    leaf1286InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1286LowerChecked :
    lowerCheck 24 leaf1286Box leaf1286Inputs = true := by
  rfl'

private theorem leaf1286CoversExact : CoversExact 8
    leaf1286Box leaf1286Certificate leaf1286InnerLog leaf1286Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk118RoundedFacts chi118RoundedFacts
    innerPair56RoundedFacts leaf1286RoundedFacts (by rfl)

private theorem leaf1286FlatSound : Sound leaf1286Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1286CertificateValid
    leaf1286InnerLogValid leaf1286CoversExact leaf1286LowerChecked

private noncomputable def component29Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component29Node0_sound : Sound component29Node0Box :=
  sound_of_literal_split component29Node0Box leaf1245Box leaf1246Box
    .chi (25/128) (by rfl) (by rfl)
    leaf1245FlatSound leaf1246FlatSound

private noncomputable def component29Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component29Node1_sound : Sound component29Node1Box :=
  sound_of_literal_split component29Node1Box leaf1247Box leaf1248Box
    .chi (25/128) (by rfl) (by rfl)
    leaf1247FlatSound leaf1248FlatSound

private noncomputable def component29Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component29Node2_sound : Sound component29Node2Box :=
  sound_of_literal_split component29Node2Box component29Node0Box component29Node1Box
    .k (89/32) (by rfl) (by rfl)
    component29Node0_sound component29Node1_sound

private noncomputable def component29Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node3_sound : Sound component29Node3Box :=
  sound_of_literal_split component29Node3Box leaf1249Box leaf1250Box
    .chi (27/128) (by rfl) (by rfl)
    leaf1249FlatSound leaf1250FlatSound

private noncomputable def component29Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node4_sound : Sound component29Node4Box :=
  sound_of_literal_split component29Node4Box leaf1251Box leaf1252Box
    .chi (27/128) (by rfl) (by rfl)
    leaf1251FlatSound leaf1252FlatSound

private noncomputable def component29Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node5_sound : Sound component29Node5Box :=
  sound_of_literal_split component29Node5Box component29Node3Box component29Node4Box
    .k (89/32) (by rfl) (by rfl)
    component29Node3_sound component29Node4_sound

private noncomputable def component29Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node6_sound : Sound component29Node6Box :=
  sound_of_literal_split component29Node6Box component29Node2Box component29Node5Box
    .chi (13/64) (by rfl) (by rfl)
    component29Node2_sound component29Node5_sound

private noncomputable def component29Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component29Node7_sound : Sound component29Node7Box :=
  sound_of_literal_split component29Node7Box leaf1253Box leaf1254Box
    .chi (25/128) (by rfl) (by rfl)
    leaf1253FlatSound leaf1254FlatSound

private noncomputable def component29Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component29Node8_sound : Sound component29Node8Box :=
  sound_of_literal_split component29Node8Box leaf1255Box leaf1256Box
    .chi (25/128) (by rfl) (by rfl)
    leaf1255FlatSound leaf1256FlatSound

private noncomputable def component29Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component29Node9_sound : Sound component29Node9Box :=
  sound_of_literal_split component29Node9Box component29Node7Box component29Node8Box
    .k (91/32) (by rfl) (by rfl)
    component29Node7_sound component29Node8_sound

private noncomputable def component29Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node10_sound : Sound component29Node10Box :=
  sound_of_literal_split component29Node10Box leaf1257Box leaf1258Box
    .chi (27/128) (by rfl) (by rfl)
    leaf1257FlatSound leaf1258FlatSound

private noncomputable def component29Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node11_sound : Sound component29Node11Box :=
  sound_of_literal_split component29Node11Box leaf1259Box leaf1260Box
    .chi (27/128) (by rfl) (by rfl)
    leaf1259FlatSound leaf1260FlatSound

private noncomputable def component29Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node12_sound : Sound component29Node12Box :=
  sound_of_literal_split component29Node12Box component29Node10Box component29Node11Box
    .k (91/32) (by rfl) (by rfl)
    component29Node10_sound component29Node11_sound

private noncomputable def component29Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node13_sound : Sound component29Node13Box :=
  sound_of_literal_split component29Node13Box component29Node9Box component29Node12Box
    .chi (13/64) (by rfl) (by rfl)
    component29Node9_sound component29Node12_sound

private noncomputable def component29Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node14_sound : Sound component29Node14Box :=
  sound_of_literal_split component29Node14Box component29Node6Box component29Node13Box
    .k (45/16) (by rfl) (by rfl)
    component29Node6_sound component29Node13_sound

private noncomputable def component29Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component29Node15_sound : Sound component29Node15Box :=
  sound_of_literal_split component29Node15Box leaf1261Box leaf1262Box
    .chi (25/128) (by rfl) (by rfl)
    leaf1261FlatSound leaf1262FlatSound

private noncomputable def component29Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component29Node16_sound : Sound component29Node16Box :=
  sound_of_literal_split component29Node16Box leaf1263Box leaf1264Box
    .chi (25/128) (by rfl) (by rfl)
    leaf1263FlatSound leaf1264FlatSound

private noncomputable def component29Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component29Node17_sound : Sound component29Node17Box :=
  sound_of_literal_split component29Node17Box component29Node15Box component29Node16Box
    .k (93/32) (by rfl) (by rfl)
    component29Node15_sound component29Node16_sound

private noncomputable def component29Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component29Node18_sound : Sound component29Node18Box :=
  sound_of_literal_split component29Node18Box leaf1265Box leaf1266Box
    .k (189/64) (by rfl) (by rfl)
    leaf1265FlatSound leaf1266FlatSound

private noncomputable def component29Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component29Node19_sound : Sound component29Node19Box :=
  sound_of_literal_split component29Node19Box leaf1267Box leaf1268Box
    .k (191/64) (by rfl) (by rfl)
    leaf1267FlatSound leaf1268FlatSound

private noncomputable def component29Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component29Node20_sound : Sound component29Node20Box :=
  sound_of_literal_split component29Node20Box component29Node18Box component29Node19Box
    .k (95/32) (by rfl) (by rfl)
    component29Node18_sound component29Node19_sound

private noncomputable def component29Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component29Node21_sound : Sound component29Node21Box :=
  sound_of_literal_split component29Node21Box leaf1269Box leaf1270Box
    .k (189/64) (by rfl) (by rfl)
    leaf1269FlatSound leaf1270FlatSound

private noncomputable def component29Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component29Node22_sound : Sound component29Node22Box :=
  sound_of_literal_split component29Node22Box leaf1271Box leaf1272Box
    .k (191/64) (by rfl) (by rfl)
    leaf1271FlatSound leaf1272FlatSound

private noncomputable def component29Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component29Node23_sound : Sound component29Node23Box :=
  sound_of_literal_split component29Node23Box component29Node21Box component29Node22Box
    .k (95/32) (by rfl) (by rfl)
    component29Node21_sound component29Node22_sound

private noncomputable def component29Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component29Node24_sound : Sound component29Node24Box :=
  sound_of_literal_split component29Node24Box component29Node20Box component29Node23Box
    .chi (25/128) (by rfl) (by rfl)
    component29Node20_sound component29Node23_sound

private noncomputable def component29Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component29Node25_sound : Sound component29Node25Box :=
  sound_of_literal_split component29Node25Box component29Node17Box component29Node24Box
    .k (47/16) (by rfl) (by rfl)
    component29Node17_sound component29Node24_sound

private noncomputable def component29Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node26_sound : Sound component29Node26Box :=
  sound_of_literal_split component29Node26Box leaf1273Box leaf1274Box
    .chi (27/128) (by rfl) (by rfl)
    leaf1273FlatSound leaf1274FlatSound

private noncomputable def component29Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component29Node27_sound : Sound component29Node27Box :=
  sound_of_literal_split component29Node27Box leaf1275Box leaf1276Box
    .k (187/64) (by rfl) (by rfl)
    leaf1275FlatSound leaf1276FlatSound

private noncomputable def component29Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node28_sound : Sound component29Node28Box :=
  sound_of_literal_split component29Node28Box leaf1277Box leaf1278Box
    .k (187/64) (by rfl) (by rfl)
    leaf1277FlatSound leaf1278FlatSound

private noncomputable def component29Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node29_sound : Sound component29Node29Box :=
  sound_of_literal_split component29Node29Box component29Node27Box component29Node28Box
    .chi (27/128) (by rfl) (by rfl)
    component29Node27_sound component29Node28_sound

private noncomputable def component29Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node30_sound : Sound component29Node30Box :=
  sound_of_literal_split component29Node30Box component29Node26Box component29Node29Box
    .k (93/32) (by rfl) (by rfl)
    component29Node26_sound component29Node29_sound

private noncomputable def component29Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component29Node31_sound : Sound component29Node31Box :=
  sound_of_literal_split component29Node31Box leaf1279Box leaf1280Box
    .k (189/64) (by rfl) (by rfl)
    leaf1279FlatSound leaf1280FlatSound

private noncomputable def component29Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node32_sound : Sound component29Node32Box :=
  sound_of_literal_split component29Node32Box leaf1281Box leaf1282Box
    .k (189/64) (by rfl) (by rfl)
    leaf1281FlatSound leaf1282FlatSound

private noncomputable def component29Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node33_sound : Sound component29Node33Box :=
  sound_of_literal_split component29Node33Box component29Node31Box component29Node32Box
    .chi (27/128) (by rfl) (by rfl)
    component29Node31_sound component29Node32_sound

private noncomputable def component29Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component29Node34_sound : Sound component29Node34Box :=
  sound_of_literal_split component29Node34Box leaf1283Box leaf1284Box
    .k (191/64) (by rfl) (by rfl)
    leaf1283FlatSound leaf1284FlatSound

private noncomputable def component29Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node35_sound : Sound component29Node35Box :=
  sound_of_literal_split component29Node35Box leaf1285Box leaf1286Box
    .k (191/64) (by rfl) (by rfl)
    leaf1285FlatSound leaf1286FlatSound

private noncomputable def component29Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node36_sound : Sound component29Node36Box :=
  sound_of_literal_split component29Node36Box component29Node34Box component29Node35Box
    .chi (27/128) (by rfl) (by rfl)
    component29Node34_sound component29Node35_sound

private noncomputable def component29Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node37_sound : Sound component29Node37Box :=
  sound_of_literal_split component29Node37Box component29Node33Box component29Node36Box
    .k (95/32) (by rfl) (by rfl)
    component29Node33_sound component29Node36_sound

private noncomputable def component29Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node38_sound : Sound component29Node38Box :=
  sound_of_literal_split component29Node38Box component29Node30Box component29Node37Box
    .k (47/16) (by rfl) (by rfl)
    component29Node30_sound component29Node37_sound

private noncomputable def component29Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component29Node39_sound : Sound component29Node39Box :=
  sound_of_literal_split component29Node39Box component29Node25Box component29Node38Box
    .chi (13/64) (by rfl) (by rfl)
    component29Node25_sound component29Node38_sound

noncomputable def component29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
theorem component29_sound : Sound component29Box :=
  sound_of_literal_split component29Box component29Node14Box component29Node39Box
    .k (23/8) (by rfl) (by rfl)
    component29Node14_sound component29Node39_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
