import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch10
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
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

private noncomputable def leaf6217Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (5/8), chiHi := (21/32) }

private noncomputable def leaf6217Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554539/33554432) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178449920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (75462039/67108864) }, upper := { exponent := 1, mantissa := (1205/1024) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi74LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357827583/34356899840) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6217InnerLog : WideLogData :=
  innerPair258Data

set_option maxRecDepth 1000000 in
private theorem leaf6217LocalValidity :
    LeafFacts leaf6217Box leaf6217Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6217Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178449920) }) = true
      norm_num [leaf6217Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6217CertificateValid :
    WideCertificateValid leaf6217Box leaf6217Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi74ValidityFacts
    leaf6217LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6217CoverageChecked :
    coverageCheck (innerAD leaf6217Box) leaf6217InnerLog = true := by
  rfl'

private theorem leaf6217InnerLogValid :
    leaf6217InnerLog.Valid 8 (innerAD leaf6217Box) :=
  wideLogDataValid_of_cachedCheck endpoint74PositiveFacts
    endpoint77PositiveFacts.valid leaf6217CoverageChecked

private noncomputable def leaf6217InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814767/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6217InputLogOnePlusV_eq :
    leaf6217InputLogOnePlusV = outerEnclosure 24
      (leaf6217Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6217RoundedFacts : LeafRoundedFacts 8
    leaf6217Certificate.logOnePlusV leaf6217InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6217InputLogOnePlusV_eq }

private noncomputable def leaf6217Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi74InputQChi innerPair258Input
    leaf6217InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6217LowerChecked :
    lowerCheck 24 leaf6217Box leaf6217Inputs = true := by
  rfl'

private theorem leaf6217CoversExact : CoversExact 8
    leaf6217Box leaf6217Certificate leaf6217InnerLog leaf6217Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi74RoundedFacts
    innerPair258RoundedFacts leaf6217RoundedFacts (by rfl)

private theorem leaf6217FlatSound : Sound leaf6217Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6217CertificateValid
    leaf6217InnerLogValid leaf6217CoversExact leaf6217LowerChecked

private noncomputable def leaf6218Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (5/8), chiHi := (21/32) }

private noncomputable def leaf6218Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554541/33554432) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178406912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (76772677/67108864) }, upper := { exponent := 1, mantissa := (613/512) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi74LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357784575/34356813824) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6218InnerLog : WideLogData :=
  innerPair565Data

set_option maxRecDepth 1000000 in
private theorem leaf6218LocalValidity :
    LeafFacts leaf6218Box leaf6218Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6218Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178406912) }) = true
      norm_num [leaf6218Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6218CertificateValid :
    WideCertificateValid leaf6218Box leaf6218Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi74ValidityFacts
    leaf6218LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6218CoverageChecked :
    coverageCheck (innerAD leaf6218Box) leaf6218InnerLog = true := by
  rfl'

private theorem leaf6218InnerLogValid :
    leaf6218InnerLog.Valid 8 (innerAD leaf6218Box) :=
  wideLogDataValid_of_cachedCheck endpoint295PositiveFacts
    endpoint305PositiveFacts.valid leaf6218CoverageChecked

private noncomputable def leaf6218InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629555/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6218InputLogOnePlusV_eq :
    leaf6218InputLogOnePlusV = outerEnclosure 24
      (leaf6218Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6218RoundedFacts : LeafRoundedFacts 8
    leaf6218Certificate.logOnePlusV leaf6218InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6218InputLogOnePlusV_eq }

private noncomputable def leaf6218Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi74InputQChi innerPair565Input
    leaf6218InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6218LowerChecked :
    lowerCheck 24 leaf6218Box leaf6218Inputs = true := by
  rfl'

private theorem leaf6218CoversExact : CoversExact 8
    leaf6218Box leaf6218Certificate leaf6218InnerLog leaf6218Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi74RoundedFacts
    innerPair565RoundedFacts leaf6218RoundedFacts (by rfl)

private theorem leaf6218FlatSound : Sound leaf6218Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6218CertificateValid
    leaf6218InnerLogValid leaf6218CoversExact leaf6218LowerChecked

private noncomputable def leaf6219Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (21/32), chiHi := (11/16) }

private noncomputable def leaf6219Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554541/33554432) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178382336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (77559061/67108864) }, upper := { exponent := 1, mantissa := (619/512) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi75LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357759999/34356764672) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6219InnerLog : WideLogData :=
  innerPair266Data

set_option maxRecDepth 1000000 in
private theorem leaf6219LocalValidity :
    LeafFacts leaf6219Box leaf6219Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6219Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178382336) }) = true
      norm_num [leaf6219Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6219CertificateValid :
    WideCertificateValid leaf6219Box leaf6219Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi75ValidityFacts
    leaf6219LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6219CoverageChecked :
    coverageCheck (innerAD leaf6219Box) leaf6219InnerLog = true := by
  rfl'

private theorem leaf6219InnerLogValid :
    leaf6219InnerLog.Valid 8 (innerAD leaf6219Box) :=
  wideLogDataValid_of_cachedCheck endpoint75PositiveFacts
    endpoint78PositiveFacts.valid leaf6219CoverageChecked

private noncomputable def leaf6219InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629567/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6219InputLogOnePlusV_eq :
    leaf6219InputLogOnePlusV = outerEnclosure 24
      (leaf6219Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6219RoundedFacts : LeafRoundedFacts 8
    leaf6219Certificate.logOnePlusV leaf6219InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6219InputLogOnePlusV_eq }

private noncomputable def leaf6219Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi75InputQChi innerPair266Input
    leaf6219InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6219LowerChecked :
    lowerCheck 24 leaf6219Box leaf6219Inputs = true := by
  rfl'

private theorem leaf6219CoversExact : CoversExact 8
    leaf6219Box leaf6219Certificate leaf6219InnerLog leaf6219Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi75RoundedFacts
    innerPair266RoundedFacts leaf6219RoundedFacts (by rfl)

private theorem leaf6219FlatSound : Sound leaf6219Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6219CertificateValid
    leaf6219InnerLogValid leaf6219CoversExact leaf6219LowerChecked

private noncomputable def leaf6220Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (21/32), chiHi := (11/16) }

private noncomputable def leaf6220Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554543/33554432) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178337280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (78935231/67108864) }, upper := { exponent := 1, mantissa := (315/256) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi75LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357714943/34356674560) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6220InnerLog : WideLogData :=
  innerPair274Data

set_option maxRecDepth 1000000 in
private theorem leaf6220LocalValidity :
    LeafFacts leaf6220Box leaf6220Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6220Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178337280) }) = true
      norm_num [leaf6220Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6220CertificateValid :
    WideCertificateValid leaf6220Box leaf6220Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi75ValidityFacts
    leaf6220LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6220CoverageChecked :
    coverageCheck (innerAD leaf6220Box) leaf6220InnerLog = true := by
  rfl'

private theorem leaf6220InnerLogValid :
    leaf6220InnerLog.Valid 8 (innerAD leaf6220Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint79PositiveFacts.valid leaf6220CoverageChecked

private noncomputable def leaf6220InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629589/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6220InputLogOnePlusV_eq :
    leaf6220InputLogOnePlusV = outerEnclosure 24
      (leaf6220Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6220RoundedFacts : LeafRoundedFacts 8
    leaf6220Certificate.logOnePlusV leaf6220InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6220InputLogOnePlusV_eq }

private noncomputable def leaf6220Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi75InputQChi innerPair274Input
    leaf6220InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6220LowerChecked :
    lowerCheck 24 leaf6220Box leaf6220Inputs = true := by
  rfl'

private theorem leaf6220CoversExact : CoversExact 8
    leaf6220Box leaf6220Certificate leaf6220InnerLog leaf6220Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi75RoundedFacts
    innerPair274RoundedFacts leaf6220RoundedFacts (by rfl)

private theorem leaf6220FlatSound : Sound leaf6220Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6220CertificateValid
    leaf6220InnerLogValid leaf6220CoversExact leaf6220LowerChecked

private noncomputable def leaf6221Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (5/8), chiHi := (21/32) }

private noncomputable def leaf6221Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554543/33554432) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178363904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (78083315/67108864) }, upper := { exponent := 1, mantissa := (1247/1024) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi74LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357741567/34356727808) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6221InnerLog : WideLogData :=
  innerPair273Data

set_option maxRecDepth 1000000 in
private theorem leaf6221LocalValidity :
    LeafFacts leaf6221Box leaf6221Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6221Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178363904) }) = true
      norm_num [leaf6221Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6221CertificateValid :
    WideCertificateValid leaf6221Box leaf6221Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi74ValidityFacts
    leaf6221LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6221CoverageChecked :
    coverageCheck (innerAD leaf6221Box) leaf6221InnerLog = true := by
  rfl'

private theorem leaf6221InnerLogValid :
    leaf6221InnerLog.Valid 8 (innerAD leaf6221Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint78PositiveFacts.valid leaf6221CoverageChecked

private noncomputable def leaf6221InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453697/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6221InputLogOnePlusV_eq :
    leaf6221InputLogOnePlusV = outerEnclosure 24
      (leaf6221Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6221RoundedFacts : LeafRoundedFacts 8
    leaf6221Certificate.logOnePlusV leaf6221InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6221InputLogOnePlusV_eq }

private noncomputable def leaf6221Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi74InputQChi innerPair273Input
    leaf6221InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6221LowerChecked :
    lowerCheck 24 leaf6221Box leaf6221Inputs = true := by
  rfl'

private theorem leaf6221CoversExact : CoversExact 8
    leaf6221Box leaf6221Certificate leaf6221InnerLog leaf6221Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi74RoundedFacts
    innerPair273RoundedFacts leaf6221RoundedFacts (by rfl)

private theorem leaf6221FlatSound : Sound leaf6221Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6221CertificateValid
    leaf6221InnerLogValid leaf6221CoversExact leaf6221LowerChecked

private noncomputable def leaf6222Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (5/8), chiHi := (41/64) }

private noncomputable def leaf6222Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109017/67108864) }, vSqrt := { lower := (65531/65536), upper := (17179377663/17178357760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (158820745/134217728) }, upper := { exponent := 1, mantissa := (625/512) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi323LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (34357735423/34356715520) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6222InnerLog : WideLogData :=
  innerPair274Data

set_option maxRecDepth 1000000 in
private theorem leaf6222LocalValidity :
    LeafFacts leaf6222Box leaf6222Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6222Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (17179377663/17178357760) }) = true
      norm_num [leaf6222Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6222CertificateValid :
    WideCertificateValid leaf6222Box leaf6222Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi323ValidityFacts
    leaf6222LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6222CoverageChecked :
    coverageCheck (innerAD leaf6222Box) leaf6222InnerLog = true := by
  rfl'

private theorem leaf6222InnerLogValid :
    leaf6222InnerLog.Valid 8 (innerAD leaf6222Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint79PositiveFacts.valid leaf6222CoverageChecked

private noncomputable def leaf6222InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629579/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6222InputLogOnePlusV_eq :
    leaf6222InputLogOnePlusV = outerEnclosure 24
      (leaf6222Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6222RoundedFacts : LeafRoundedFacts 8
    leaf6222Certificate.logOnePlusV leaf6222InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6222InputLogOnePlusV_eq }

private noncomputable def leaf6222Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi323InputQChi innerPair274Input
    leaf6222InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6222LowerChecked :
    lowerCheck 24 leaf6222Box leaf6222Inputs = true := by
  rfl'

private theorem leaf6222CoversExact : CoversExact 8
    leaf6222Box leaf6222Certificate leaf6222InnerLog leaf6222Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi323RoundedFacts
    innerPair274RoundedFacts leaf6222RoundedFacts (by rfl)

private theorem leaf6222FlatSound : Sound leaf6222Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6222CertificateValid
    leaf6222InnerLogValid leaf6222CoversExact leaf6222LowerChecked

private noncomputable def leaf6223Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6223Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109019/67108864) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356641792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (161114363/134217728) }, upper := { exponent := 1, mantissa := (317/256) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714872829/68713283584) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6223InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf6223LocalValidity :
    LeafFacts leaf6223Box leaf6223Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6223Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356641792) }) = true
      norm_num [leaf6223Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6223CertificateValid :
    WideCertificateValid leaf6223Box leaf6223Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi324ValidityFacts
    leaf6223LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6223CoverageChecked :
    coverageCheck (innerAD leaf6223Box) leaf6223InnerLog = true := by
  rfl'

private theorem leaf6223InnerLogValid :
    leaf6223InnerLog.Valid 8 (innerAD leaf6223Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf6223CoverageChecked

private noncomputable def leaf6223InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629469/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6223InputLogOnePlusV_eq :
    leaf6223InputLogOnePlusV = outerEnclosure 24
      (leaf6223Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6223RoundedFacts : LeafRoundedFacts 8
    leaf6223Certificate.logOnePlusV leaf6223InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6223InputLogOnePlusV_eq }

private noncomputable def leaf6223Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi324InputQChi innerPair279Input
    leaf6223InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6223LowerChecked :
    lowerCheck 24 leaf6223Box leaf6223Inputs = true := by
  rfl'

private theorem leaf6223CoversExact : CoversExact 8
    leaf6223Box leaf6223Certificate leaf6223InnerLog leaf6223Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi324RoundedFacts
    innerPair279RoundedFacts leaf6223RoundedFacts (by rfl)

private theorem leaf6223FlatSound : Sound leaf6223Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6223CertificateValid
    leaf6223InnerLogValid leaf6223CoversExact leaf6223LowerChecked

private noncomputable def leaf6224Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (21/32), chiHi := (11/16) }

private noncomputable def leaf6224Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554545/33554432) }, vSqrt := { lower := (65531/65536), upper := (11452743679/11452194816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (80311401/67108864) }, upper := { exponent := 1, mantissa := (641/512) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi75LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (22904938495/22904389632) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6224InnerLog : WideLogData :=
  innerPair587Data

set_option maxRecDepth 1000000 in
private theorem leaf6224LocalValidity :
    LeafFacts leaf6224Box leaf6224Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6224Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (11452743679/11452194816) }) = true
      norm_num [leaf6224Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6224CertificateValid :
    WideCertificateValid leaf6224Box leaf6224Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi75ValidityFacts
    leaf6224LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6224CoverageChecked :
    coverageCheck (innerAD leaf6224Box) leaf6224InnerLog = true := by
  rfl'

private theorem leaf6224InnerLogValid :
    leaf6224InnerLog.Valid 8 (innerAD leaf6224Box) :=
  wideLogDataValid_of_cachedCheck endpoint304PositiveFacts
    endpoint419PositiveFacts.valid leaf6224CoverageChecked

private noncomputable def leaf6224InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629483/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6224InputLogOnePlusV_eq :
    leaf6224InputLogOnePlusV = outerEnclosure 24
      (leaf6224Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6224RoundedFacts : LeafRoundedFacts 8
    leaf6224Certificate.logOnePlusV leaf6224InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6224InputLogOnePlusV_eq }

private noncomputable def leaf6224Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi75InputQChi innerPair587Input
    leaf6224InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6224LowerChecked :
    lowerCheck 24 leaf6224Box leaf6224Inputs = true := by
  rfl'

private theorem leaf6224CoversExact : CoversExact 8
    leaf6224Box leaf6224Certificate leaf6224InnerLog leaf6224Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi75RoundedFacts
    innerPair587RoundedFacts leaf6224RoundedFacts (by rfl)

private theorem leaf6224FlatSound : Sound leaf6224Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6224CertificateValid
    leaf6224InnerLogValid leaf6224CoversExact leaf6224LowerChecked

private noncomputable def leaf6225Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (21/32), chiHi := (11/16) }

private noncomputable def leaf6225Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554547/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356494336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (81687571/67108864) }, upper := { exponent := 1, mantissa := (163/128) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi75LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714725373/68712988672) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6225InnerLog : WideLogData :=
  innerPair280Data

set_option maxRecDepth 1000000 in
private theorem leaf6225LocalValidity :
    LeafFacts leaf6225Box leaf6225Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6225Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356494336) }) = true
      norm_num [leaf6225Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6225CertificateValid :
    WideCertificateValid leaf6225Box leaf6225Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi75ValidityFacts
    leaf6225LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6225CoverageChecked :
    coverageCheck (innerAD leaf6225Box) leaf6225InnerLog = true := by
  rfl'

private theorem leaf6225InnerLogValid :
    leaf6225InnerLog.Valid 8 (innerAD leaf6225Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint90PositiveFacts.valid leaf6225CoverageChecked

private noncomputable def leaf6225InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629505/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6225InputLogOnePlusV_eq :
    leaf6225InputLogOnePlusV = outerEnclosure 24
      (leaf6225Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6225RoundedFacts : LeafRoundedFacts 8
    leaf6225Certificate.logOnePlusV leaf6225InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6225InputLogOnePlusV_eq }

private noncomputable def leaf6225Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi75InputQChi innerPair280Input
    leaf6225InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6225LowerChecked :
    lowerCheck 24 leaf6225Box leaf6225Inputs = true := by
  rfl'

private theorem leaf6225CoversExact : CoversExact 8
    leaf6225Box leaf6225Certificate leaf6225InnerLog leaf6225Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi75RoundedFacts
    innerPair280RoundedFacts leaf6225RoundedFacts (by rfl)

private theorem leaf6225FlatSound : Sound leaf6225Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6225CertificateValid
    leaf6225InnerLogValid leaf6225CoversExact leaf6225LowerChecked

private noncomputable def leaf6226Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (11/16), chiHi := (23/32) }

private noncomputable def leaf6226Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554543/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356629504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (79656083/67108864) }, upper := { exponent := 1, mantissa := (1271/1024) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi80LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714860541/68713259008) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6226InnerLog : WideLogData :=
  innerPair274Data

set_option maxRecDepth 1000000 in
private theorem leaf6226LocalValidity :
    LeafFacts leaf6226Box leaf6226Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6226Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356629504) }) = true
      norm_num [leaf6226Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6226CertificateValid :
    WideCertificateValid leaf6226Box leaf6226Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi80ValidityFacts
    leaf6226LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6226CoverageChecked :
    coverageCheck (innerAD leaf6226Box) leaf6226InnerLog = true := by
  rfl'

private theorem leaf6226InnerLogValid :
    leaf6226InnerLog.Valid 8 (innerAD leaf6226Box) :=
  wideLogDataValid_of_cachedCheck endpoint76PositiveFacts
    endpoint79PositiveFacts.valid leaf6226CoverageChecked

private noncomputable def leaf6226InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (363421/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf6226InputLogOnePlusV_eq :
    leaf6226InputLogOnePlusV = outerEnclosure 24
      (leaf6226Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6226RoundedFacts : LeafRoundedFacts 8
    leaf6226Certificate.logOnePlusV leaf6226InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6226InputLogOnePlusV_eq }

private noncomputable def leaf6226Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi80InputQChi innerPair274Input
    leaf6226InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6226LowerChecked :
    lowerCheck 24 leaf6226Box leaf6226Inputs = true := by
  rfl'

private theorem leaf6226CoversExact : CoversExact 8
    leaf6226Box leaf6226Certificate leaf6226InnerLog leaf6226Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi80RoundedFacts
    innerPair274RoundedFacts leaf6226RoundedFacts (by rfl)

private theorem leaf6226FlatSound : Sound leaf6226Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6226CertificateValid
    leaf6226InnerLogValid leaf6226CoversExact leaf6226LowerChecked

private noncomputable def leaf6227Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (11/16), chiHi := (23/32) }

private noncomputable def leaf6227Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554545/33554432) }, vSqrt := { lower := (65531/65536), upper := (11452743679/11452178432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (81097785/67108864) }, upper := { exponent := 1, mantissa := (647/512) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi80LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (22904922111/22904356864) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6227InnerLog : WideLogData :=
  innerPair280Data

set_option maxRecDepth 1000000 in
private theorem leaf6227LocalValidity :
    LeafFacts leaf6227Box leaf6227Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6227Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (11452743679/11452178432) }) = true
      norm_num [leaf6227Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6227CertificateValid :
    WideCertificateValid leaf6227Box leaf6227Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi80ValidityFacts
    leaf6227LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6227CoverageChecked :
    coverageCheck (innerAD leaf6227Box) leaf6227InnerLog = true := by
  rfl'

private theorem leaf6227InnerLogValid :
    leaf6227InnerLog.Valid 8 (innerAD leaf6227Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint90PositiveFacts.valid leaf6227CoverageChecked

private noncomputable def leaf6227InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629495/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6227InputLogOnePlusV_eq :
    leaf6227InputLogOnePlusV = outerEnclosure 24
      (leaf6227Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6227RoundedFacts : LeafRoundedFacts 8
    leaf6227Certificate.logOnePlusV leaf6227InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6227InputLogOnePlusV_eq }

private noncomputable def leaf6227Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi80InputQChi innerPair280Input
    leaf6227InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6227LowerChecked :
    lowerCheck 24 leaf6227Box leaf6227Inputs = true := by
  rfl'

private theorem leaf6227CoversExact : CoversExact 8
    leaf6227Box leaf6227Certificate leaf6227InnerLog leaf6227Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi80RoundedFacts
    innerPair280RoundedFacts leaf6227RoundedFacts (by rfl)

private theorem leaf6227FlatSound : Sound leaf6227Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6227CertificateValid
    leaf6227InnerLogValid leaf6227CoversExact leaf6227LowerChecked

private noncomputable def leaf6228Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (33/16), chiLo := (23/32), chiHi := (3/4) }

private noncomputable def leaf6228Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554545/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356494336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (81753105/67108864) }, upper := { exponent := 1, mantissa := (163/128) } }, logOuter := sk61LogOuterCertificate, logK := sk61LogKCertificate, logChi := chi81LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714725373/68712988672) } }, logDArg := sk61LogDArgCertificate }

private noncomputable def leaf6228InnerLog : WideLogData :=
  innerPair280Data

set_option maxRecDepth 1000000 in
private theorem leaf6228LocalValidity :
    LeafFacts leaf6228Box leaf6228Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6228Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356494336) }) = true
      norm_num [leaf6228Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6228CertificateValid :
    WideCertificateValid leaf6228Box leaf6228Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk61ValidityFacts chi81ValidityFacts
    leaf6228LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6228CoverageChecked :
    coverageCheck (innerAD leaf6228Box) leaf6228InnerLog = true := by
  rfl'

private theorem leaf6228InnerLogValid :
    leaf6228InnerLog.Valid 8 (innerAD leaf6228Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint90PositiveFacts.valid leaf6228CoverageChecked

private noncomputable def leaf6228InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629505/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6228InputLogOnePlusV_eq :
    leaf6228InputLogOnePlusV = outerEnclosure 24
      (leaf6228Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6228RoundedFacts : LeafRoundedFacts 8
    leaf6228Certificate.logOnePlusV leaf6228InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6228InputLogOnePlusV_eq }

private noncomputable def leaf6228Inputs : Inputs :=
  inputsOfCaches globalInput sk61RoundedInputs
    chi81InputQChi innerPair280Input
    leaf6228InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6228LowerChecked :
    lowerCheck 24 leaf6228Box leaf6228Inputs = true := by
  rfl'

private theorem leaf6228CoversExact : CoversExact 8
    leaf6228Box leaf6228Certificate leaf6228InnerLog leaf6228Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk61RoundedFacts chi81RoundedFacts
    innerPair280RoundedFacts leaf6228RoundedFacts (by rfl)

private theorem leaf6228FlatSound : Sound leaf6228Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6228CertificateValid
    leaf6228InnerLogValid leaf6228CoversExact leaf6228LowerChecked

private noncomputable def leaf6229Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (33/16), kHi := (17/8), chiLo := (23/32), chiHi := (3/4) }

private noncomputable def leaf6229Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554547/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356396032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (83260339/67108864) }, upper := { exponent := 1, mantissa := (83/64) } }, logOuter := sk62LogOuterCertificate, logK := sk62LogKCertificate, logChi := chi81LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714627069/68712792064) } }, logDArg := sk62LogDArgCertificate }

private noncomputable def leaf6229InnerLog : WideLogData :=
  innerPair287Data

set_option maxRecDepth 1000000 in
private theorem leaf6229LocalValidity :
    LeafFacts leaf6229Box leaf6229Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6229Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356396032) }) = true
      norm_num [leaf6229Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6229CertificateValid :
    WideCertificateValid leaf6229Box leaf6229Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk62ValidityFacts chi81ValidityFacts
    leaf6229LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6229CoverageChecked :
    coverageCheck (innerAD leaf6229Box) leaf6229InnerLog = true := by
  rfl'

private theorem leaf6229InnerLogValid :
    leaf6229InnerLog.Valid 8 (innerAD leaf6229Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint91PositiveFacts.valid leaf6229CoverageChecked

private noncomputable def leaf6229InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629529/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6229InputLogOnePlusV_eq :
    leaf6229InputLogOnePlusV = outerEnclosure 24
      (leaf6229Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6229RoundedFacts : LeafRoundedFacts 8
    leaf6229Certificate.logOnePlusV leaf6229InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6229InputLogOnePlusV_eq }

private noncomputable def leaf6229Inputs : Inputs :=
  inputsOfCaches globalInput sk62RoundedInputs
    chi81InputQChi innerPair287Input
    leaf6229InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6229LowerChecked :
    lowerCheck 24 leaf6229Box leaf6229Inputs = true := by
  rfl'

private theorem leaf6229CoversExact : CoversExact 8
    leaf6229Box leaf6229Certificate leaf6229InnerLog leaf6229Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk62RoundedFacts chi81RoundedFacts
    innerPair287RoundedFacts leaf6229RoundedFacts (by rfl)

private theorem leaf6229FlatSound : Sound leaf6229Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6229CertificateValid
    leaf6229InnerLogValid leaf6229CoversExact leaf6229LowerChecked

private noncomputable def leaf6230Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (11/16), chiHi := (23/32) }

private noncomputable def leaf6230Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554547/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356441088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (82539487/67108864) }, upper := { exponent := 1, mantissa := (1317/1024) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi80LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714672125/68712882176) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6230InnerLog : WideLogData :=
  innerPair287Data

set_option maxRecDepth 1000000 in
private theorem leaf6230LocalValidity :
    LeafFacts leaf6230Box leaf6230Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6230Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356441088) }) = true
      norm_num [leaf6230Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6230CertificateValid :
    WideCertificateValid leaf6230Box leaf6230Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi80ValidityFacts
    leaf6230LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6230CoverageChecked :
    coverageCheck (innerAD leaf6230Box) leaf6230InnerLog = true := by
  rfl'

private theorem leaf6230InnerLogValid :
    leaf6230InnerLog.Valid 8 (innerAD leaf6230Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint91PositiveFacts.valid leaf6230CoverageChecked

private noncomputable def leaf6230InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814759/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6230InputLogOnePlusV_eq :
    leaf6230InputLogOnePlusV = outerEnclosure 24
      (leaf6230Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6230RoundedFacts : LeafRoundedFacts 8
    leaf6230Certificate.logOnePlusV leaf6230InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6230InputLogOnePlusV_eq }

private noncomputable def leaf6230Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi80InputQChi innerPair287Input
    leaf6230InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6230LowerChecked :
    lowerCheck 24 leaf6230Box leaf6230Inputs = true := by
  rfl'

private theorem leaf6230CoversExact : CoversExact 8
    leaf6230Box leaf6230Certificate leaf6230InnerLog leaf6230Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi80RoundedFacts
    innerPair287RoundedFacts leaf6230RoundedFacts (by rfl)

private theorem leaf6230FlatSound : Sound leaf6230Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6230CertificateValid
    leaf6230InnerLogValid leaf6230CoversExact leaf6230LowerChecked

private noncomputable def leaf6231Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (11/16), chiHi := (23/32) }

private noncomputable def leaf6231Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554549/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356346880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (83981189/67108864) }, upper := { exponent := 1, mantissa := (335/256) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi80LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714577917/68712693760) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6231InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf6231LocalValidity :
    LeafFacts leaf6231Box leaf6231Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6231Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356346880) }) = true
      norm_num [leaf6231Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6231CertificateValid :
    WideCertificateValid leaf6231Box leaf6231Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi80ValidityFacts
    leaf6231LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6231CoverageChecked :
    coverageCheck (innerAD leaf6231Box) leaf6231InnerLog = true := by
  rfl'

private theorem leaf6231InnerLogValid :
    leaf6231InnerLog.Valid 8 (innerAD leaf6231Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf6231CoverageChecked

private noncomputable def leaf6231InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629541/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6231InputLogOnePlusV_eq :
    leaf6231InputLogOnePlusV = outerEnclosure 24
      (leaf6231Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6231RoundedFacts : LeafRoundedFacts 8
    leaf6231Certificate.logOnePlusV leaf6231InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6231InputLogOnePlusV_eq }

private noncomputable def leaf6231Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi80InputQChi innerPair294Input
    leaf6231InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6231LowerChecked :
    lowerCheck 24 leaf6231Box leaf6231Inputs = true := by
  rfl'

private theorem leaf6231CoversExact : CoversExact 8
    leaf6231Box leaf6231Certificate leaf6231InnerLog leaf6231Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi80RoundedFacts
    innerPair294RoundedFacts leaf6231RoundedFacts (by rfl)

private theorem leaf6231FlatSound : Sound leaf6231Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6231CertificateValid
    leaf6231InnerLogValid leaf6231CoversExact leaf6231LowerChecked

private noncomputable def leaf6232Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (35/16), chiLo := (23/32), chiHi := (3/4) }

private noncomputable def leaf6232Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554549/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356297728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (84767573/67108864) }, upper := { exponent := 1, mantissa := (169/128) } }, logOuter := sk63LogOuterCertificate, logK := sk63LogKCertificate, logChi := chi81LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714528765/68712595456) } }, logDArg := sk63LogDArgCertificate }

private noncomputable def leaf6232InnerLog : WideLogData :=
  innerPair295Data

set_option maxRecDepth 1000000 in
private theorem leaf6232LocalValidity :
    LeafFacts leaf6232Box leaf6232Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6232Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356297728) }) = true
      norm_num [leaf6232Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6232CertificateValid :
    WideCertificateValid leaf6232Box leaf6232Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk63ValidityFacts chi81ValidityFacts
    leaf6232LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6232CoverageChecked :
    coverageCheck (innerAD leaf6232Box) leaf6232InnerLog = true := by
  rfl'

private theorem leaf6232InnerLogValid :
    leaf6232InnerLog.Valid 8 (innerAD leaf6232Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint92PositiveFacts.valid leaf6232CoverageChecked

private noncomputable def leaf6232InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629553/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6232InputLogOnePlusV_eq :
    leaf6232InputLogOnePlusV = outerEnclosure 24
      (leaf6232Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6232RoundedFacts : LeafRoundedFacts 8
    leaf6232Certificate.logOnePlusV leaf6232InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6232InputLogOnePlusV_eq }

private noncomputable def leaf6232Inputs : Inputs :=
  inputsOfCaches globalInput sk63RoundedInputs
    chi81InputQChi innerPair295Input
    leaf6232InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6232LowerChecked :
    lowerCheck 24 leaf6232Box leaf6232Inputs = true := by
  rfl'

private theorem leaf6232CoversExact : CoversExact 8
    leaf6232Box leaf6232Certificate leaf6232InnerLog leaf6232Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk63RoundedFacts chi81RoundedFacts
    innerPair295RoundedFacts leaf6232RoundedFacts (by rfl)

private theorem leaf6232FlatSound : Sound leaf6232Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6232CertificateValid
    leaf6232InnerLogValid leaf6232CoversExact leaf6232LowerChecked

private noncomputable def leaf6233Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (23/32), chiHi := (3/4) }

private noncomputable def leaf6233Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554551/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356199424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (86274807/67108864) }, upper := { exponent := 1, mantissa := (43/32) } }, logOuter := sk64LogOuterCertificate, logK := sk64LogKCertificate, logChi := chi81LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714430461/68712398848) } }, logDArg := sk64LogDArgCertificate }

private noncomputable def leaf6233InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6233LocalValidity :
    LeafFacts leaf6233Box leaf6233Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6233Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356199424) }) = true
      norm_num [leaf6233Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6233CertificateValid :
    WideCertificateValid leaf6233Box leaf6233Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk64ValidityFacts chi81ValidityFacts
    leaf6233LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6233CoverageChecked :
    coverageCheck (innerAD leaf6233Box) leaf6233InnerLog = true := by
  rfl'

private theorem leaf6233InnerLogValid :
    leaf6233InnerLog.Valid 8 (innerAD leaf6233Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6233CoverageChecked

private noncomputable def leaf6233InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629577/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6233InputLogOnePlusV_eq :
    leaf6233InputLogOnePlusV = outerEnclosure 24
      (leaf6233Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6233RoundedFacts : LeafRoundedFacts 8
    leaf6233Certificate.logOnePlusV leaf6233InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6233InputLogOnePlusV_eq }

private noncomputable def leaf6233Inputs : Inputs :=
  inputsOfCaches globalInput sk64RoundedInputs
    chi81InputQChi innerPair340Input
    leaf6233InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6233LowerChecked :
    lowerCheck 24 leaf6233Box leaf6233Inputs = true := by
  rfl'

private theorem leaf6233CoversExact : CoversExact 8
    leaf6233Box leaf6233Certificate leaf6233InnerLog leaf6233Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk64RoundedFacts chi81RoundedFacts
    innerPair340RoundedFacts leaf6233RoundedFacts (by rfl)

private theorem leaf6233FlatSound : Sound leaf6233Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6233CertificateValid
    leaf6233InnerLogValid leaf6233CoversExact leaf6233LowerChecked

private noncomputable def leaf6234Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (5/8), chiHi := (41/64) }

private noncomputable def leaf6234Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (67109019/67108864) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356631552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (161442023/134217728) }, upper := { exponent := 1, mantissa := (2541/2048) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi323LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714862589/68713263104) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6234InnerLog : WideLogData :=
  innerPair279Data

set_option maxRecDepth 1000000 in
private theorem leaf6234LocalValidity :
    LeafFacts leaf6234Box leaf6234Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6234Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356631552) }) = true
      norm_num [leaf6234Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6234CertificateValid :
    WideCertificateValid leaf6234Box leaf6234Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi323ValidityFacts
    leaf6234LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6234CoverageChecked :
    coverageCheck (innerAD leaf6234Box) leaf6234InnerLog = true := by
  rfl'

private theorem leaf6234InnerLogValid :
    leaf6234InnerLog.Valid 8 (innerAD leaf6234Box) :=
  wideLogDataValid_of_cachedCheck endpoint77PositiveFacts
    endpoint79PositiveFacts.valid leaf6234CoverageChecked

private noncomputable def leaf6234InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629471/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6234InputLogOnePlusV_eq :
    leaf6234InputLogOnePlusV = outerEnclosure 24
      (leaf6234Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6234RoundedFacts : LeafRoundedFacts 8
    leaf6234Certificate.logOnePlusV leaf6234InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6234InputLogOnePlusV_eq }

private noncomputable def leaf6234Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi323InputQChi innerPair279Input
    leaf6234InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6234LowerChecked :
    lowerCheck 24 leaf6234Box leaf6234Inputs = true := by
  rfl'

private theorem leaf6234CoversExact : CoversExact 8
    leaf6234Box leaf6234Certificate leaf6234InnerLog leaf6234Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi323RoundedFacts
    innerPair279RoundedFacts leaf6234RoundedFacts (by rfl)

private theorem leaf6234FlatSound : Sound leaf6234Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6234CertificateValid
    leaf6234InnerLogValid leaf6234CoversExact leaf6234LowerChecked

private noncomputable def leaf6235Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6235Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109021/67108864) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356555776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (163801173/134217728) }, upper := { exponent := 1, mantissa := (1289/1024) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714786813/68713111552) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6235InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6235LocalValidity :
    LeafFacts leaf6235Box leaf6235Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6235Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356555776) }) = true
      norm_num [leaf6235Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6235CertificateValid :
    WideCertificateValid leaf6235Box leaf6235Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi324ValidityFacts
    leaf6235LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6235CoverageChecked :
    coverageCheck (innerAD leaf6235Box) leaf6235InnerLog = true := by
  rfl'

private theorem leaf6235InnerLogValid :
    leaf6235InnerLog.Valid 8 (innerAD leaf6235Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6235CoverageChecked

private noncomputable def leaf6235InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814745/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6235InputLogOnePlusV_eq :
    leaf6235InputLogOnePlusV = outerEnclosure 24
      (leaf6235Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6235RoundedFacts : LeafRoundedFacts 8
    leaf6235Certificate.logOnePlusV leaf6235InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6235InputLogOnePlusV_eq }

private noncomputable def leaf6235Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi324InputQChi innerPair286Input
    leaf6235InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6235LowerChecked :
    lowerCheck 24 leaf6235Box leaf6235Inputs = true := by
  rfl'

private theorem leaf6235CoversExact : CoversExact 8
    leaf6235Box leaf6235Certificate leaf6235InnerLog leaf6235Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi324RoundedFacts
    innerPair286RoundedFacts leaf6235RoundedFacts (by rfl)

private theorem leaf6235FlatSound : Sound leaf6235Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6235CertificateValid
    leaf6235InnerLogValid leaf6235CoversExact leaf6235LowerChecked

private noncomputable def leaf6236Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (5/8), chiHi := (41/64) }

private noncomputable def leaf6236Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109021/67108864) }, vSqrt := { lower := (65531/65536), upper := (11452743679/11452182528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (164063301/134217728) }, upper := { exponent := 1, mantissa := (1291/1024) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi323LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (22904926207/22904365056) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6236InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6236LocalValidity :
    LeafFacts leaf6236Box leaf6236Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6236Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (11452743679/11452182528) }) = true
      norm_num [leaf6236Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6236CertificateValid :
    WideCertificateValid leaf6236Box leaf6236Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi323ValidityFacts
    leaf6236LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6236CoverageChecked :
    coverageCheck (innerAD leaf6236Box) leaf6236InnerLog = true := by
  rfl'

private theorem leaf6236InnerLogValid :
    leaf6236InnerLog.Valid 8 (innerAD leaf6236Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6236CoverageChecked

private noncomputable def leaf6236InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907373/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6236InputLogOnePlusV_eq :
    leaf6236InputLogOnePlusV = outerEnclosure 24
      (leaf6236Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6236RoundedFacts : LeafRoundedFacts 8
    leaf6236Certificate.logOnePlusV leaf6236InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6236InputLogOnePlusV_eq }

private noncomputable def leaf6236Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi323InputQChi innerPair286Input
    leaf6236InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6236LowerChecked :
    lowerCheck 24 leaf6236Box leaf6236Inputs = true := by
  rfl'

private theorem leaf6236CoversExact : CoversExact 8
    leaf6236Box leaf6236Certificate leaf6236InnerLog leaf6236Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi323RoundedFacts
    innerPair286RoundedFacts leaf6236RoundedFacts (by rfl)

private theorem leaf6236FlatSound : Sound leaf6236Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6236CertificateValid
    leaf6236InnerLogValid leaf6236CoversExact leaf6236LowerChecked

private noncomputable def leaf6237Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6237Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109023/67108864) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356469760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (166487983/134217728) }, upper := { exponent := 1, mantissa := (655/512) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714700797/68712939520) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6237InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6237LocalValidity :
    LeafFacts leaf6237Box leaf6237Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6237Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356469760) }) = true
      norm_num [leaf6237Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6237CertificateValid :
    WideCertificateValid leaf6237Box leaf6237Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi324ValidityFacts
    leaf6237LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6237CoverageChecked :
    coverageCheck (innerAD leaf6237Box) leaf6237InnerLog = true := by
  rfl'

private theorem leaf6237InnerLogValid :
    leaf6237InnerLog.Valid 8 (innerAD leaf6237Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6237CoverageChecked

private noncomputable def leaf6237InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629511/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6237InputLogOnePlusV_eq :
    leaf6237InputLogOnePlusV = outerEnclosure 24
      (leaf6237Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6237RoundedFacts : LeafRoundedFacts 8
    leaf6237Certificate.logOnePlusV leaf6237InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6237InputLogOnePlusV_eq }

private noncomputable def leaf6237Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi324InputQChi innerPair286Input
    leaf6237InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6237LowerChecked :
    lowerCheck 24 leaf6237Box leaf6237Inputs = true := by
  rfl'

private theorem leaf6237CoversExact : CoversExact 8
    leaf6237Box leaf6237Certificate leaf6237InnerLog leaf6237Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi324RoundedFacts
    innerPair286RoundedFacts leaf6237RoundedFacts (by rfl)

private theorem leaf6237FlatSound : Sound leaf6237Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6237CertificateValid
    leaf6237InnerLogValid leaf6237CoversExact leaf6237LowerChecked

private noncomputable def leaf6238Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (21/32), chiHi := (11/16) }

private noncomputable def leaf6238Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554549/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356404224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (83063741/67108864) }, upper := { exponent := 1, mantissa := (663/512) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi75LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714635261/68712808448) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6238InnerLog : WideLogData :=
  innerPair364Data

set_option maxRecDepth 1000000 in
private theorem leaf6238LocalValidity :
    LeafFacts leaf6238Box leaf6238Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6238Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356404224) }) = true
      norm_num [leaf6238Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6238CertificateValid :
    WideCertificateValid leaf6238Box leaf6238Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi75ValidityFacts
    leaf6238LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6238CoverageChecked :
    coverageCheck (innerAD leaf6238Box) leaf6238InnerLog = true := by
  rfl'

private theorem leaf6238InnerLogValid :
    leaf6238InnerLog.Valid 8 (innerAD leaf6238Box) :=
  wideLogDataValid_of_cachedCheck endpoint94PositiveFacts
    endpoint436PositiveFacts.valid leaf6238CoverageChecked

private noncomputable def leaf6238InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629527/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6238InputLogOnePlusV_eq :
    leaf6238InputLogOnePlusV = outerEnclosure 24
      (leaf6238Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6238RoundedFacts : LeafRoundedFacts 8
    leaf6238Certificate.logOnePlusV leaf6238InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6238InputLogOnePlusV_eq }

private noncomputable def leaf6238Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi75InputQChi innerPair364Input
    leaf6238InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6238LowerChecked :
    lowerCheck 24 leaf6238Box leaf6238Inputs = true := by
  rfl'

private theorem leaf6238CoversExact : CoversExact 8
    leaf6238Box leaf6238Certificate leaf6238InnerLog leaf6238Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi75RoundedFacts
    innerPair364RoundedFacts leaf6238RoundedFacts (by rfl)

private theorem leaf6238FlatSound : Sound leaf6238Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6238CertificateValid
    leaf6238InnerLogValid leaf6238CoversExact leaf6238LowerChecked

private noncomputable def leaf6239Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (21/32), chiHi := (11/16) }

private noncomputable def leaf6239Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554551/33554432) }, vSqrt := { lower := (65531/65536), upper := (11452743679/11452104704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (84439911/67108864) }, upper := { exponent := 1, mantissa := (337/256) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi75LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (22904848383/22904209408) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6239InnerLog : WideLogData :=
  innerPair674Data

set_option maxRecDepth 1000000 in
private theorem leaf6239LocalValidity :
    LeafFacts leaf6239Box leaf6239Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6239Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (11452743679/11452104704) }) = true
      norm_num [leaf6239Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6239CertificateValid :
    WideCertificateValid leaf6239Box leaf6239Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi75ValidityFacts
    leaf6239LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6239CoverageChecked :
    coverageCheck (innerAD leaf6239Box) leaf6239InnerLog = true := by
  rfl'

private theorem leaf6239InnerLogValid :
    leaf6239InnerLog.Valid 8 (innerAD leaf6239Box) :=
  wideLogDataValid_of_cachedCheck endpoint419PositiveFacts
    endpoint473PositiveFacts.valid leaf6239CoverageChecked

private noncomputable def leaf6239InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629549/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6239InputLogOnePlusV_eq :
    leaf6239InputLogOnePlusV = outerEnclosure 24
      (leaf6239Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6239RoundedFacts : LeafRoundedFacts 8
    leaf6239Certificate.logOnePlusV leaf6239InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6239InputLogOnePlusV_eq }

private noncomputable def leaf6239Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi75InputQChi innerPair674Input
    leaf6239InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6239LowerChecked :
    lowerCheck 24 leaf6239Box leaf6239Inputs = true := by
  rfl'

private theorem leaf6239CoversExact : CoversExact 8
    leaf6239Box leaf6239Certificate leaf6239InnerLog leaf6239Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi75RoundedFacts
    innerPair674RoundedFacts leaf6239RoundedFacts (by rfl)

private theorem leaf6239FlatSound : Sound leaf6239Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6239CertificateValid
    leaf6239InnerLogValid leaf6239CoversExact leaf6239LowerChecked

private noncomputable def leaf6240Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (5/8), chiHi := (41/64) }

private noncomputable def leaf6240Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109023/67108864) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356463616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (166684579/134217728) }, upper := { exponent := 1, mantissa := (2623/2048) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi323LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714694653/68712927232) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6240InnerLog : WideLogData :=
  innerPair286Data

set_option maxRecDepth 1000000 in
private theorem leaf6240LocalValidity :
    LeafFacts leaf6240Box leaf6240Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6240Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356463616) }) = true
      norm_num [leaf6240Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6240CertificateValid :
    WideCertificateValid leaf6240Box leaf6240Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi323ValidityFacts
    leaf6240LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6240CoverageChecked :
    coverageCheck (innerAD leaf6240Box) leaf6240InnerLog = true := by
  rfl'

private theorem leaf6240InnerLogValid :
    leaf6240InnerLog.Valid 8 (innerAD leaf6240Box) :=
  wideLogDataValid_of_cachedCheck endpoint78PositiveFacts
    endpoint90PositiveFacts.valid leaf6240CoverageChecked

private noncomputable def leaf6240InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453689/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6240InputLogOnePlusV_eq :
    leaf6240InputLogOnePlusV = outerEnclosure 24
      (leaf6240Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6240RoundedFacts : LeafRoundedFacts 8
    leaf6240Certificate.logOnePlusV leaf6240InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6240InputLogOnePlusV_eq }

private noncomputable def leaf6240Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi323InputQChi innerPair286Input
    leaf6240InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6240LowerChecked :
    lowerCheck 24 leaf6240Box leaf6240Inputs = true := by
  rfl'

private theorem leaf6240CoversExact : CoversExact 8
    leaf6240Box leaf6240Certificate leaf6240InnerLog leaf6240Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi323RoundedFacts
    innerPair286RoundedFacts leaf6240RoundedFacts (by rfl)

private theorem leaf6240FlatSound : Sound leaf6240Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6240CertificateValid
    leaf6240InnerLogValid leaf6240CoversExact leaf6240LowerChecked

private noncomputable def leaf6241Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6241Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109025/67108864) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356383744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (169174793/134217728) }, upper := { exponent := 1, mantissa := (1331/1024) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714614781/68712767488) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6241InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf6241LocalValidity :
    LeafFacts leaf6241Box leaf6241Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6241Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356383744) }) = true
      norm_num [leaf6241Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6241CertificateValid :
    WideCertificateValid leaf6241Box leaf6241Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi324ValidityFacts
    leaf6241LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6241CoverageChecked :
    coverageCheck (innerAD leaf6241Box) leaf6241InnerLog = true := by
  rfl'

private theorem leaf6241InnerLogValid :
    leaf6241InnerLog.Valid 8 (innerAD leaf6241Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf6241CoverageChecked

private noncomputable def leaf6241InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907383/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6241InputLogOnePlusV_eq :
    leaf6241InputLogOnePlusV = outerEnclosure 24
      (leaf6241Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6241RoundedFacts : LeafRoundedFacts 8
    leaf6241Certificate.logOnePlusV leaf6241InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6241InputLogOnePlusV_eq }

private noncomputable def leaf6241Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi324InputQChi innerPair294Input
    leaf6241InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6241LowerChecked :
    lowerCheck 24 leaf6241Box leaf6241Inputs = true := by
  rfl'

private theorem leaf6241CoversExact : CoversExact 8
    leaf6241Box leaf6241Certificate leaf6241InnerLog leaf6241Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi324RoundedFacts
    innerPair294RoundedFacts leaf6241RoundedFacts (by rfl)

private theorem leaf6241FlatSound : Sound leaf6241Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6241CertificateValid
    leaf6241InnerLogValid leaf6241CoversExact leaf6241LowerChecked

private noncomputable def leaf6242Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (5/8), chiHi := (41/64) }

private noncomputable def leaf6242Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109025/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356379648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (169305857/134217728) }, upper := { exponent := 1, mantissa := (333/256) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi323LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714610685/68712759296) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6242InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf6242LocalValidity :
    LeafFacts leaf6242Box leaf6242Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6242Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356379648) }) = true
      norm_num [leaf6242Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6242CertificateValid :
    WideCertificateValid leaf6242Box leaf6242Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi323ValidityFacts
    leaf6242LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6242CoverageChecked :
    coverageCheck (innerAD leaf6242Box) leaf6242InnerLog = true := by
  rfl'

private theorem leaf6242InnerLogValid :
    leaf6242InnerLog.Valid 8 (innerAD leaf6242Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf6242CoverageChecked

private noncomputable def leaf6242InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629533/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6242InputLogOnePlusV_eq :
    leaf6242InputLogOnePlusV = outerEnclosure 24
      (leaf6242Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6242RoundedFacts : LeafRoundedFacts 8
    leaf6242Certificate.logOnePlusV leaf6242InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6242InputLogOnePlusV_eq }

private noncomputable def leaf6242Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi323InputQChi innerPair294Input
    leaf6242InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6242LowerChecked :
    lowerCheck 24 leaf6242Box leaf6242Inputs = true := by
  rfl'

private theorem leaf6242CoversExact : CoversExact 8
    leaf6242Box leaf6242Certificate leaf6242InnerLog leaf6242Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi323RoundedFacts
    innerPair294RoundedFacts leaf6242RoundedFacts (by rfl)

private theorem leaf6242FlatSound : Sound leaf6242Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6242CertificateValid
    leaf6242InnerLogValid leaf6242CoversExact leaf6242LowerChecked

private noncomputable def leaf6243Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6243Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109027/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356297728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (171861603/134217728) }, upper := { exponent := 1, mantissa := (169/128) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714528765/68712595456) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6243InnerLog : WideLogData :=
  innerPair295Data

set_option maxRecDepth 1000000 in
private theorem leaf6243LocalValidity :
    LeafFacts leaf6243Box leaf6243Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6243Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356297728) }) = true
      norm_num [leaf6243Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6243CertificateValid :
    WideCertificateValid leaf6243Box leaf6243Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi324ValidityFacts
    leaf6243LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6243CoverageChecked :
    coverageCheck (innerAD leaf6243Box) leaf6243InnerLog = true := by
  rfl'

private theorem leaf6243InnerLogValid :
    leaf6243InnerLog.Valid 8 (innerAD leaf6243Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint92PositiveFacts.valid leaf6243CoverageChecked

private noncomputable def leaf6243InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629553/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6243InputLogOnePlusV_eq :
    leaf6243InputLogOnePlusV = outerEnclosure 24
      (leaf6243Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6243RoundedFacts : LeafRoundedFacts 8
    leaf6243Certificate.logOnePlusV leaf6243InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6243InputLogOnePlusV_eq }

private noncomputable def leaf6243Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi324InputQChi innerPair295Input
    leaf6243InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6243LowerChecked :
    lowerCheck 24 leaf6243Box leaf6243Inputs = true := by
  rfl'

private theorem leaf6243CoversExact : CoversExact 8
    leaf6243Box leaf6243Certificate leaf6243InnerLog leaf6243Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi324RoundedFacts
    innerPair295RoundedFacts leaf6243RoundedFacts (by rfl)

private theorem leaf6243FlatSound : Sound leaf6243Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6243CertificateValid
    leaf6243InnerLogValid leaf6243CoversExact leaf6243LowerChecked

private noncomputable def leaf6244Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6244Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109027/67108864) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356303872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (171665007/134217728) }, upper := { exponent := 1, mantissa := (2701/2048) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714534909/68712607744) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6244InnerLog : WideLogData :=
  innerPair295Data

set_option maxRecDepth 1000000 in
private theorem leaf6244LocalValidity :
    LeafFacts leaf6244Box leaf6244Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6244Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356303872) }) = true
      norm_num [leaf6244Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6244CertificateValid :
    WideCertificateValid leaf6244Box leaf6244Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi325ValidityFacts
    leaf6244LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6244CoverageChecked :
    coverageCheck (innerAD leaf6244Box) leaf6244InnerLog = true := by
  rfl'

private theorem leaf6244InnerLogValid :
    leaf6244InnerLog.Valid 8 (innerAD leaf6244Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint92PositiveFacts.valid leaf6244CoverageChecked

private noncomputable def leaf6244InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629551/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6244InputLogOnePlusV_eq :
    leaf6244InputLogOnePlusV = outerEnclosure 24
      (leaf6244Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6244RoundedFacts : LeafRoundedFacts 8
    leaf6244Certificate.logOnePlusV leaf6244InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6244InputLogOnePlusV_eq }

private noncomputable def leaf6244Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi325InputQChi innerPair295Input
    leaf6244InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6244LowerChecked :
    lowerCheck 24 leaf6244Box leaf6244Inputs = true := by
  rfl'

private theorem leaf6244CoversExact : CoversExact 8
    leaf6244Box leaf6244Certificate leaf6244InnerLog leaf6244Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi325RoundedFacts
    innerPair295RoundedFacts leaf6244RoundedFacts (by rfl)

private theorem leaf6244FlatSound : Sound leaf6244Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6244CertificateValid
    leaf6244InnerLogValid leaf6244CoversExact leaf6244LowerChecked

private noncomputable def leaf6245Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6245Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109029/67108864) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356224000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (174155221/134217728) }, upper := { exponent := 1, mantissa := (685/512) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714455037/68712448000) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6245InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6245LocalValidity :
    LeafFacts leaf6245Box leaf6245Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6245Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356224000) }) = true
      norm_num [leaf6245Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6245CertificateValid :
    WideCertificateValid leaf6245Box leaf6245Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi326ValidityFacts
    leaf6245LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6245CoverageChecked :
    coverageCheck (innerAD leaf6245Box) leaf6245InnerLog = true := by
  rfl'

private theorem leaf6245InnerLogValid :
    leaf6245InnerLog.Valid 8 (innerAD leaf6245Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6245CoverageChecked

private noncomputable def leaf6245InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629571/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6245InputLogOnePlusV_eq :
    leaf6245InputLogOnePlusV = outerEnclosure 24
      (leaf6245Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6245RoundedFacts : LeafRoundedFacts 8
    leaf6245Certificate.logOnePlusV leaf6245InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6245InputLogOnePlusV_eq }

private noncomputable def leaf6245Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi326InputQChi innerPair340Input
    leaf6245InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6245LowerChecked :
    lowerCheck 24 leaf6245Box leaf6245Inputs = true := by
  rfl'

private theorem leaf6245CoversExact : CoversExact 8
    leaf6245Box leaf6245Certificate leaf6245InnerLog leaf6245Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi326RoundedFacts
    innerPair340RoundedFacts leaf6245RoundedFacts (by rfl)

private theorem leaf6245FlatSound : Sound leaf6245Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6245CertificateValid
    leaf6245InnerLogValid leaf6245CoversExact leaf6245LowerChecked

private noncomputable def leaf6246Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6246Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109029/67108864) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11452071936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (174417349/134217728) }, upper := { exponent := 1, mantissa := (343/256) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904815615/22904143872) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6246InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6246LocalValidity :
    LeafFacts leaf6246Box leaf6246Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6246Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11452071936) }) = true
      norm_num [leaf6246Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6246CertificateValid :
    WideCertificateValid leaf6246Box leaf6246Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi325ValidityFacts
    leaf6246LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6246CoverageChecked :
    coverageCheck (innerAD leaf6246Box) leaf6246InnerLog = true := by
  rfl'

private theorem leaf6246InnerLogValid :
    leaf6246InnerLog.Valid 8 (innerAD leaf6246Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6246CoverageChecked

private noncomputable def leaf6246InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629573/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6246InputLogOnePlusV_eq :
    leaf6246InputLogOnePlusV = outerEnclosure 24
      (leaf6246Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6246RoundedFacts : LeafRoundedFacts 8
    leaf6246Certificate.logOnePlusV leaf6246InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6246InputLogOnePlusV_eq }

private noncomputable def leaf6246Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi325InputQChi innerPair340Input
    leaf6246InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6246LowerChecked :
    lowerCheck 24 leaf6246Box leaf6246Inputs = true := by
  rfl'

private theorem leaf6246CoversExact : CoversExact 8
    leaf6246Box leaf6246Certificate leaf6246InnerLog leaf6246Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi325RoundedFacts
    innerPair340RoundedFacts leaf6246RoundedFacts (by rfl)

private theorem leaf6246FlatSound : Sound leaf6246Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6246CertificateValid
    leaf6246InnerLogValid leaf6246CoversExact leaf6246LowerChecked

private noncomputable def leaf6247Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6247Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109031/67108864) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34356133888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (176973095/134217728) }, upper := { exponent := 1, mantissa := (87/64) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714364925/68712267776) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6247InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6247LocalValidity :
    LeafFacts leaf6247Box leaf6247Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6247Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34356133888) }) = true
      norm_num [leaf6247Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6247CertificateValid :
    WideCertificateValid leaf6247Box leaf6247Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi326ValidityFacts
    leaf6247LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6247CoverageChecked :
    coverageCheck (innerAD leaf6247Box) leaf6247InnerLog = true := by
  rfl'

private theorem leaf6247InnerLogValid :
    leaf6247InnerLog.Valid 8 (innerAD leaf6247Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6247CoverageChecked

private noncomputable def leaf6247InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629593/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6247InputLogOnePlusV_eq :
    leaf6247InputLogOnePlusV = outerEnclosure 24
      (leaf6247Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6247RoundedFacts : LeafRoundedFacts 8
    leaf6247Certificate.logOnePlusV leaf6247InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6247InputLogOnePlusV_eq }

private noncomputable def leaf6247Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi326InputQChi innerPair346Input
    leaf6247InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6247LowerChecked :
    lowerCheck 24 leaf6247Box leaf6247Inputs = true := by
  rfl'

private theorem leaf6247CoversExact : CoversExact 8
    leaf6247Box leaf6247Certificate leaf6247InnerLog leaf6247Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi326RoundedFacts
    innerPair346RoundedFacts leaf6247RoundedFacts (by rfl)

private theorem leaf6247FlatSound : Sound leaf6247Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6247CertificateValid
    leaf6247InnerLogValid leaf6247CoversExact leaf6247LowerChecked

private noncomputable def leaf6248Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (11/16), chiHi := (23/32) }

private noncomputable def leaf6248Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554551/33554432) }, vSqrt := { lower := (65531/65536), upper := (11452743679/11452084224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (85422891/67108864) }, upper := { exponent := 1, mantissa := (1363/1024) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi80LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (22904827903/22904168448) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6248InnerLog : WideLogData :=
  innerPair295Data

set_option maxRecDepth 1000000 in
private theorem leaf6248LocalValidity :
    LeafFacts leaf6248Box leaf6248Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6248Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (11452743679/11452084224) }) = true
      norm_num [leaf6248Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6248CertificateValid :
    WideCertificateValid leaf6248Box leaf6248Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi80ValidityFacts
    leaf6248LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6248CoverageChecked :
    coverageCheck (innerAD leaf6248Box) leaf6248InnerLog = true := by
  rfl'

private theorem leaf6248InnerLogValid :
    leaf6248InnerLog.Valid 8 (innerAD leaf6248Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint92PositiveFacts.valid leaf6248CoverageChecked

private noncomputable def leaf6248InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907391/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6248InputLogOnePlusV_eq :
    leaf6248InputLogOnePlusV = outerEnclosure 24
      (leaf6248Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6248RoundedFacts : LeafRoundedFacts 8
    leaf6248Certificate.logOnePlusV leaf6248InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6248InputLogOnePlusV_eq }

private noncomputable def leaf6248Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi80InputQChi innerPair295Input
    leaf6248InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6248LowerChecked :
    lowerCheck 24 leaf6248Box leaf6248Inputs = true := by
  rfl'

private theorem leaf6248CoversExact : CoversExact 8
    leaf6248Box leaf6248Certificate leaf6248InnerLog leaf6248Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi80RoundedFacts
    innerPair295RoundedFacts leaf6248RoundedFacts (by rfl)

private theorem leaf6248FlatSound : Sound leaf6248Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6248CertificateValid
    leaf6248InnerLogValid leaf6248CoversExact leaf6248LowerChecked

private noncomputable def leaf6249Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (11/16), chiHi := (23/32) }

private noncomputable def leaf6249Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554553/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356158464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (86864593/67108864) }, upper := { exponent := 1, mantissa := (693/512) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi80LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714389501/68712316928) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6249InnerLog : WideLogData :=
  innerPair687Data

set_option maxRecDepth 1000000 in
private theorem leaf6249LocalValidity :
    LeafFacts leaf6249Box leaf6249Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6249Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356158464) }) = true
      norm_num [leaf6249Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6249CertificateValid :
    WideCertificateValid leaf6249Box leaf6249Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi80ValidityFacts
    leaf6249LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6249CoverageChecked :
    coverageCheck (innerAD leaf6249Box) leaf6249InnerLog = true := by
  rfl'

private theorem leaf6249InnerLogValid :
    leaf6249InnerLog.Valid 8 (innerAD leaf6249Box) :=
  wideLogDataValid_of_cachedCheck endpoint435PositiveFacts
    endpoint461PositiveFacts.valid leaf6249CoverageChecked

private noncomputable def leaf6249InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629587/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6249InputLogOnePlusV_eq :
    leaf6249InputLogOnePlusV = outerEnclosure 24
      (leaf6249Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6249RoundedFacts : LeafRoundedFacts 8
    leaf6249Certificate.logOnePlusV leaf6249InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6249InputLogOnePlusV_eq }

private noncomputable def leaf6249Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi80InputQChi innerPair687Input
    leaf6249InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6249LowerChecked :
    lowerCheck 24 leaf6249Box leaf6249Inputs = true := by
  rfl'

private theorem leaf6249CoversExact : CoversExact 8
    leaf6249Box leaf6249Certificate leaf6249InnerLog leaf6249Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi80RoundedFacts
    innerPair687RoundedFacts leaf6249RoundedFacts (by rfl)

private theorem leaf6249FlatSound : Sound leaf6249Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6249CertificateValid
    leaf6249InnerLogValid leaf6249CoversExact leaf6249LowerChecked

private noncomputable def leaf6250Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (23/32), chiHi := (3/4) }

private noncomputable def leaf6250Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554553/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356101120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (87782041/67108864) }, upper := { exponent := 1, mantissa := (175/128) } }, logOuter := sk69LogOuterCertificate, logK := sk69LogKCertificate, logChi := chi81LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714332157/68712202240) } }, logDArg := sk69LogDArgCertificate }

private noncomputable def leaf6250InnerLog : WideLogData :=
  innerPair341Data

set_option maxRecDepth 1000000 in
private theorem leaf6250LocalValidity :
    LeafFacts leaf6250Box leaf6250Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6250Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356101120) }) = true
      norm_num [leaf6250Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6250CertificateValid :
    WideCertificateValid leaf6250Box leaf6250Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk69ValidityFacts chi81ValidityFacts
    leaf6250LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6250CoverageChecked :
    coverageCheck (innerAD leaf6250Box) leaf6250InnerLog = true := by
  rfl'

private theorem leaf6250InnerLogValid :
    leaf6250InnerLog.Valid 8 (innerAD leaf6250Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint93PositiveFacts.valid leaf6250CoverageChecked

private noncomputable def leaf6250InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629601/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6250InputLogOnePlusV_eq :
    leaf6250InputLogOnePlusV = outerEnclosure 24
      (leaf6250Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6250RoundedFacts : LeafRoundedFacts 8
    leaf6250Certificate.logOnePlusV leaf6250InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6250InputLogOnePlusV_eq }

private noncomputable def leaf6250Inputs : Inputs :=
  inputsOfCaches globalInput sk69RoundedInputs
    chi81InputQChi innerPair341Input
    leaf6250InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6250LowerChecked :
    lowerCheck 24 leaf6250Box leaf6250Inputs = true := by
  rfl'

private theorem leaf6250CoversExact : CoversExact 8
    leaf6250Box leaf6250Certificate leaf6250InnerLog leaf6250Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk69RoundedFacts chi81RoundedFacts
    innerPair341RoundedFacts leaf6250RoundedFacts (by rfl)

private theorem leaf6250FlatSound : Sound leaf6250Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6250CertificateValid
    leaf6250InnerLogValid leaf6250CoversExact leaf6250LowerChecked

private noncomputable def leaf6251Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (23/32), chiHi := (3/4) }

private noncomputable def leaf6251Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554555/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356002816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (89289275/67108864) }, upper := { exponent := 1, mantissa := (89/64) } }, logOuter := sk70LogOuterCertificate, logK := sk70LogKCertificate, logChi := chi81LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714233853/68712005632) } }, logDArg := sk70LogDArgCertificate }

private noncomputable def leaf6251InnerLog : WideLogData :=
  innerPair347Data

set_option maxRecDepth 1000000 in
private theorem leaf6251LocalValidity :
    LeafFacts leaf6251Box leaf6251Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6251Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356002816) }) = true
      norm_num [leaf6251Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6251CertificateValid :
    WideCertificateValid leaf6251Box leaf6251Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk70ValidityFacts chi81ValidityFacts
    leaf6251LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6251CoverageChecked :
    coverageCheck (innerAD leaf6251Box) leaf6251InnerLog = true := by
  rfl'

private theorem leaf6251InnerLogValid :
    leaf6251InnerLog.Valid 8 (innerAD leaf6251Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint96PositiveFacts.valid leaf6251CoverageChecked

private noncomputable def leaf6251InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629625/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6251InputLogOnePlusV_eq :
    leaf6251InputLogOnePlusV = outerEnclosure 24
      (leaf6251Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6251RoundedFacts : LeafRoundedFacts 8
    leaf6251Certificate.logOnePlusV leaf6251InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6251InputLogOnePlusV_eq }

private noncomputable def leaf6251Inputs : Inputs :=
  inputsOfCaches globalInput sk70RoundedInputs
    chi81InputQChi innerPair347Input
    leaf6251InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6251LowerChecked :
    lowerCheck 24 leaf6251Box leaf6251Inputs = true := by
  rfl'

private theorem leaf6251CoversExact : CoversExact 8
    leaf6251Box leaf6251Certificate leaf6251InnerLog leaf6251Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk70RoundedFacts chi81RoundedFacts
    innerPair347RoundedFacts leaf6251RoundedFacts (by rfl)

private theorem leaf6251FlatSound : Sound leaf6251Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6251CertificateValid
    leaf6251InnerLogValid leaf6251CoversExact leaf6251LowerChecked

private noncomputable def leaf6252Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (11/16), chiHi := (23/32) }

private noncomputable def leaf6252Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554555/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34356064256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (88306295/67108864) }, upper := { exponent := 1, mantissa := (1409/1024) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi80LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714295293/68712128512) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6252InnerLog : WideLogData :=
  innerPair349Data

set_option maxRecDepth 1000000 in
private theorem leaf6252LocalValidity :
    LeafFacts leaf6252Box leaf6252Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6252Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34356064256) }) = true
      norm_num [leaf6252Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6252CertificateValid :
    WideCertificateValid leaf6252Box leaf6252Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi80ValidityFacts
    leaf6252LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6252CoverageChecked :
    coverageCheck (innerAD leaf6252Box) leaf6252InnerLog = true := by
  rfl'

private theorem leaf6252InnerLogValid :
    leaf6252InnerLog.Valid 8 (innerAD leaf6252Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint460PositiveFacts.valid leaf6252CoverageChecked

private noncomputable def leaf6252InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814805/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6252InputLogOnePlusV_eq :
    leaf6252InputLogOnePlusV = outerEnclosure 24
      (leaf6252Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6252RoundedFacts : LeafRoundedFacts 8
    leaf6252Certificate.logOnePlusV leaf6252InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6252InputLogOnePlusV_eq }

private noncomputable def leaf6252Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi80InputQChi innerPair349Input
    leaf6252InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6252LowerChecked :
    lowerCheck 24 leaf6252Box leaf6252Inputs = true := by
  rfl'

private theorem leaf6252CoversExact : CoversExact 8
    leaf6252Box leaf6252Certificate leaf6252InnerLog leaf6252Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi80RoundedFacts
    innerPair349RoundedFacts leaf6252RoundedFacts (by rfl)

private theorem leaf6252FlatSound : Sound leaf6252Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6252CertificateValid
    leaf6252InnerLogValid leaf6252CoversExact leaf6252LowerChecked

private noncomputable def leaf6253Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (11/16), chiHi := (23/32) }

private noncomputable def leaf6253Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554557/33554432) }, vSqrt := { lower := (32765/32768), upper := (11452743679/11451990016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (89747997/67108864) }, upper := { exponent := 1, mantissa := (179/128) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi80LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (22904733695/22903980032) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6253InnerLog : WideLogData :=
  innerPair706Data

set_option maxRecDepth 1000000 in
private theorem leaf6253LocalValidity :
    LeafFacts leaf6253Box leaf6253Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6253Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (11452743679/11451990016) }) = true
      norm_num [leaf6253Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6253CertificateValid :
    WideCertificateValid leaf6253Box leaf6253Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi80ValidityFacts
    leaf6253LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6253CoverageChecked :
    coverageCheck (innerAD leaf6253Box) leaf6253InnerLog = true := by
  rfl'

private theorem leaf6253InnerLogValid :
    leaf6253InnerLog.Valid 8 (innerAD leaf6253Box) :=
  wideLogDataValid_of_cachedCheck endpoint448PositiveFacts
    endpoint467PositiveFacts.valid leaf6253CoverageChecked

private noncomputable def leaf6253InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629633/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6253InputLogOnePlusV_eq :
    leaf6253InputLogOnePlusV = outerEnclosure 24
      (leaf6253Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6253RoundedFacts : LeafRoundedFacts 8
    leaf6253Certificate.logOnePlusV leaf6253InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6253InputLogOnePlusV_eq }

private noncomputable def leaf6253Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi80InputQChi innerPair706Input
    leaf6253InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6253LowerChecked :
    lowerCheck 24 leaf6253Box leaf6253Inputs = true := by
  rfl'

private theorem leaf6253CoversExact : CoversExact 8
    leaf6253Box leaf6253Certificate leaf6253InnerLog leaf6253Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi80RoundedFacts
    innerPair706RoundedFacts leaf6253RoundedFacts (by rfl)

private theorem leaf6253FlatSound : Sound leaf6253Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6253CertificateValid
    leaf6253InnerLogValid leaf6253CoversExact leaf6253LowerChecked

private noncomputable def leaf6254Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (23/32), chiHi := (3/4) }

private noncomputable def leaf6254Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554557/33554432) }, vSqrt := { lower := (65531/65536), upper := (34358231037/34355904512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (90796509/67108864) }, upper := { exponent := 1, mantissa := (181/128) } }, logOuter := sk67LogOuterCertificate, logK := sk67LogKCertificate, logChi := chi81LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (68714135549/68711809024) } }, logDArg := sk67LogDArgCertificate }

private noncomputable def leaf6254InnerLog : WideLogData :=
  innerPair710Data

set_option maxRecDepth 1000000 in
private theorem leaf6254LocalValidity :
    LeafFacts leaf6254Box leaf6254Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6254Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (34358231037/34355904512) }) = true
      norm_num [leaf6254Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6254CertificateValid :
    WideCertificateValid leaf6254Box leaf6254Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk67ValidityFacts chi81ValidityFacts
    leaf6254LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6254CoverageChecked :
    coverageCheck (innerAD leaf6254Box) leaf6254InnerLog = true := by
  rfl'

private theorem leaf6254InnerLogValid :
    leaf6254InnerLog.Valid 8 (innerAD leaf6254Box) :=
  wideLogDataValid_of_cachedCheck endpoint451PositiveFacts
    endpoint464PositiveFacts.valid leaf6254CoverageChecked

private noncomputable def leaf6254InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629649/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6254InputLogOnePlusV_eq :
    leaf6254InputLogOnePlusV = outerEnclosure 24
      (leaf6254Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6254RoundedFacts : LeafRoundedFacts 8
    leaf6254Certificate.logOnePlusV leaf6254InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6254InputLogOnePlusV_eq }

private noncomputable def leaf6254Inputs : Inputs :=
  inputsOfCaches globalInput sk67RoundedInputs
    chi81InputQChi innerPair710Input
    leaf6254InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6254LowerChecked :
    lowerCheck 24 leaf6254Box leaf6254Inputs = true := by
  rfl'

private theorem leaf6254CoversExact : CoversExact 8
    leaf6254Box leaf6254Certificate leaf6254InnerLog leaf6254Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk67RoundedFacts chi81RoundedFacts
    innerPair710RoundedFacts leaf6254RoundedFacts (by rfl)

private theorem leaf6254FlatSound : Sound leaf6254Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6254CertificateValid
    leaf6254InnerLogValid leaf6254CoversExact leaf6254LowerChecked

private noncomputable def leaf6255Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (23/32), chiHi := (3/4) }

private noncomputable def leaf6255Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (33554559/33554432) }, vSqrt := { lower := (32765/32768), upper := (34358231037/34355806208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (92303743/67108864) }, upper := { exponent := 1, mantissa := (23/16) } }, logOuter := sk68LogOuterCertificate, logK := sk68LogKCertificate, logChi := chi81LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (68714037245/68711612416) } }, logDArg := sk68LogDArgCertificate }

private noncomputable def leaf6255InnerLog : WideLogData :=
  innerPair357Data

set_option maxRecDepth 1000000 in
private theorem leaf6255LocalValidity :
    LeafFacts leaf6255Box leaf6255Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6255Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (34358231037/34355806208) }) = true
      norm_num [leaf6255Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6255CertificateValid :
    WideCertificateValid leaf6255Box leaf6255Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk68ValidityFacts chi81ValidityFacts
    leaf6255LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6255CoverageChecked :
    coverageCheck (innerAD leaf6255Box) leaf6255InnerLog = true := by
  rfl'

private theorem leaf6255InnerLogValid :
    leaf6255InnerLog.Valid 8 (innerAD leaf6255Box) :=
  wideLogDataValid_of_cachedCheck endpoint93PositiveFacts
    endpoint97PositiveFacts.valid leaf6255CoverageChecked

private noncomputable def leaf6255InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629673/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6255InputLogOnePlusV_eq :
    leaf6255InputLogOnePlusV = outerEnclosure 24
      (leaf6255Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6255RoundedFacts : LeafRoundedFacts 8
    leaf6255Certificate.logOnePlusV leaf6255InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6255InputLogOnePlusV_eq }

private noncomputable def leaf6255Inputs : Inputs :=
  inputsOfCaches globalInput sk68RoundedInputs
    chi81InputQChi innerPair357Input
    leaf6255InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6255LowerChecked :
    lowerCheck 24 leaf6255Box leaf6255Inputs = true := by
  rfl'

private theorem leaf6255CoversExact : CoversExact 8
    leaf6255Box leaf6255Certificate leaf6255InnerLog leaf6255Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk68RoundedFacts chi81RoundedFacts
    innerPair357RoundedFacts leaf6255RoundedFacts (by rfl)

private theorem leaf6255FlatSound : Sound leaf6255Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6255CertificateValid
    leaf6255InnerLogValid leaf6255CoversExact leaf6255LowerChecked

private noncomputable def component125Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component125Node0_sound : Sound component125Node0Box :=
  sound_of_literal_split component125Node0Box leaf6217Box leaf6218Box
    .k (33/16) (by rfl) (by rfl)
    leaf6217FlatSound leaf6218FlatSound

private noncomputable def component125Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component125Node1_sound : Sound component125Node1Box :=
  sound_of_literal_split component125Node1Box leaf6219Box leaf6220Box
    .k (33/16) (by rfl) (by rfl)
    leaf6219FlatSound leaf6220FlatSound

private noncomputable def component125Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component125Node2_sound : Sound component125Node2Box :=
  sound_of_literal_split component125Node2Box component125Node0Box component125Node1Box
    .chi (21/32) (by rfl) (by rfl)
    component125Node0_sound component125Node1_sound

private noncomputable def component125Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (35/16), kHi := (9/4), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component125Node3_sound : Sound component125Node3Box :=
  sound_of_literal_split component125Node3Box leaf6222Box leaf6223Box
    .chi (41/64) (by rfl) (by rfl)
    leaf6222FlatSound leaf6223FlatSound

private noncomputable def component125Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component125Node4_sound : Sound component125Node4Box :=
  sound_of_literal_split component125Node4Box leaf6221Box component125Node3Box
    .k (35/16) (by rfl) (by rfl)
    leaf6221FlatSound component125Node3_sound

private noncomputable def component125Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component125Node5_sound : Sound component125Node5Box :=
  sound_of_literal_split component125Node5Box leaf6224Box leaf6225Box
    .k (35/16) (by rfl) (by rfl)
    leaf6224FlatSound leaf6225FlatSound

private noncomputable def component125Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component125Node6_sound : Sound component125Node6Box :=
  sound_of_literal_split component125Node6Box component125Node4Box component125Node5Box
    .chi (21/32) (by rfl) (by rfl)
    component125Node4_sound component125Node5_sound

private noncomputable def component125Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component125Node7_sound : Sound component125Node7Box :=
  sound_of_literal_split component125Node7Box component125Node2Box component125Node6Box
    .k (17/8) (by rfl) (by rfl)
    component125Node2_sound component125Node6_sound

private noncomputable def component125Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component125Node8_sound : Sound component125Node8Box :=
  sound_of_literal_split component125Node8Box leaf6226Box leaf6227Box
    .k (33/16) (by rfl) (by rfl)
    leaf6226FlatSound leaf6227FlatSound

private noncomputable def component125Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component125Node9_sound : Sound component125Node9Box :=
  sound_of_literal_split component125Node9Box leaf6228Box leaf6229Box
    .k (33/16) (by rfl) (by rfl)
    leaf6228FlatSound leaf6229FlatSound

private noncomputable def component125Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (17/8), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component125Node10_sound : Sound component125Node10Box :=
  sound_of_literal_split component125Node10Box component125Node8Box component125Node9Box
    .chi (23/32) (by rfl) (by rfl)
    component125Node8_sound component125Node9_sound

private noncomputable def component125Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component125Node11_sound : Sound component125Node11Box :=
  sound_of_literal_split component125Node11Box leaf6230Box leaf6231Box
    .k (35/16) (by rfl) (by rfl)
    leaf6230FlatSound leaf6231FlatSound

private noncomputable def component125Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component125Node12_sound : Sound component125Node12Box :=
  sound_of_literal_split component125Node12Box leaf6232Box leaf6233Box
    .k (35/16) (by rfl) (by rfl)
    leaf6232FlatSound leaf6233FlatSound

private noncomputable def component125Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/8), kHi := (9/4), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component125Node13_sound : Sound component125Node13Box :=
  sound_of_literal_split component125Node13Box component125Node11Box component125Node12Box
    .chi (23/32) (by rfl) (by rfl)
    component125Node11_sound component125Node12_sound

private noncomputable def component125Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component125Node14_sound : Sound component125Node14Box :=
  sound_of_literal_split component125Node14Box component125Node10Box component125Node13Box
    .k (17/8) (by rfl) (by rfl)
    component125Node10_sound component125Node13_sound

private noncomputable def component125Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (9/4), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component125Node15_sound : Sound component125Node15Box :=
  sound_of_literal_split component125Node15Box component125Node7Box component125Node14Box
    .chi (11/16) (by rfl) (by rfl)
    component125Node7_sound component125Node14_sound

private noncomputable def component125Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component125Node16_sound : Sound component125Node16Box :=
  sound_of_literal_split component125Node16Box leaf6234Box leaf6235Box
    .chi (41/64) (by rfl) (by rfl)
    leaf6234FlatSound leaf6235FlatSound

private noncomputable def component125Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component125Node17_sound : Sound component125Node17Box :=
  sound_of_literal_split component125Node17Box leaf6236Box leaf6237Box
    .chi (41/64) (by rfl) (by rfl)
    leaf6236FlatSound leaf6237FlatSound

private noncomputable def component125Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component125Node18_sound : Sound component125Node18Box :=
  sound_of_literal_split component125Node18Box component125Node16Box component125Node17Box
    .k (37/16) (by rfl) (by rfl)
    component125Node16_sound component125Node17_sound

private noncomputable def component125Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component125Node19_sound : Sound component125Node19Box :=
  sound_of_literal_split component125Node19Box leaf6238Box leaf6239Box
    .k (37/16) (by rfl) (by rfl)
    leaf6238FlatSound leaf6239FlatSound

private noncomputable def component125Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component125Node20_sound : Sound component125Node20Box :=
  sound_of_literal_split component125Node20Box component125Node18Box component125Node19Box
    .chi (21/32) (by rfl) (by rfl)
    component125Node18_sound component125Node19_sound

private noncomputable def component125Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component125Node21_sound : Sound component125Node21Box :=
  sound_of_literal_split component125Node21Box leaf6240Box leaf6241Box
    .chi (41/64) (by rfl) (by rfl)
    leaf6240FlatSound leaf6241FlatSound

private noncomputable def component125Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component125Node22_sound : Sound component125Node22Box :=
  sound_of_literal_split component125Node22Box leaf6242Box leaf6243Box
    .chi (41/64) (by rfl) (by rfl)
    leaf6242FlatSound leaf6243FlatSound

private noncomputable def component125Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component125Node23_sound : Sound component125Node23Box :=
  sound_of_literal_split component125Node23Box component125Node21Box component125Node22Box
    .k (39/16) (by rfl) (by rfl)
    component125Node21_sound component125Node22_sound

private noncomputable def component125Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component125Node24_sound : Sound component125Node24Box :=
  sound_of_literal_split component125Node24Box leaf6244Box leaf6245Box
    .chi (43/64) (by rfl) (by rfl)
    leaf6244FlatSound leaf6245FlatSound

private noncomputable def component125Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component125Node25_sound : Sound component125Node25Box :=
  sound_of_literal_split component125Node25Box leaf6246Box leaf6247Box
    .chi (43/64) (by rfl) (by rfl)
    leaf6246FlatSound leaf6247FlatSound

private noncomputable def component125Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component125Node26_sound : Sound component125Node26Box :=
  sound_of_literal_split component125Node26Box component125Node24Box component125Node25Box
    .k (39/16) (by rfl) (by rfl)
    component125Node24_sound component125Node25_sound

private noncomputable def component125Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component125Node27_sound : Sound component125Node27Box :=
  sound_of_literal_split component125Node27Box component125Node23Box component125Node26Box
    .chi (21/32) (by rfl) (by rfl)
    component125Node23_sound component125Node26_sound

private noncomputable def component125Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component125Node28_sound : Sound component125Node28Box :=
  sound_of_literal_split component125Node28Box component125Node20Box component125Node27Box
    .k (19/8) (by rfl) (by rfl)
    component125Node20_sound component125Node27_sound

private noncomputable def component125Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component125Node29_sound : Sound component125Node29Box :=
  sound_of_literal_split component125Node29Box leaf6248Box leaf6249Box
    .k (37/16) (by rfl) (by rfl)
    leaf6248FlatSound leaf6249FlatSound

private noncomputable def component125Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component125Node30_sound : Sound component125Node30Box :=
  sound_of_literal_split component125Node30Box leaf6250Box leaf6251Box
    .k (37/16) (by rfl) (by rfl)
    leaf6250FlatSound leaf6251FlatSound

private noncomputable def component125Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component125Node31_sound : Sound component125Node31Box :=
  sound_of_literal_split component125Node31Box component125Node29Box component125Node30Box
    .chi (23/32) (by rfl) (by rfl)
    component125Node29_sound component125Node30_sound

private noncomputable def component125Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component125Node32_sound : Sound component125Node32Box :=
  sound_of_literal_split component125Node32Box leaf6252Box leaf6253Box
    .k (39/16) (by rfl) (by rfl)
    leaf6252FlatSound leaf6253FlatSound

private noncomputable def component125Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component125Node33_sound : Sound component125Node33Box :=
  sound_of_literal_split component125Node33Box leaf6254Box leaf6255Box
    .k (39/16) (by rfl) (by rfl)
    leaf6254FlatSound leaf6255FlatSound

private noncomputable def component125Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component125Node34_sound : Sound component125Node34Box :=
  sound_of_literal_split component125Node34Box component125Node32Box component125Node33Box
    .chi (23/32) (by rfl) (by rfl)
    component125Node32_sound component125Node33_sound

private noncomputable def component125Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component125Node35_sound : Sound component125Node35Box :=
  sound_of_literal_split component125Node35Box component125Node31Box component125Node34Box
    .k (19/8) (by rfl) (by rfl)
    component125Node31_sound component125Node34_sound

private noncomputable def component125Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component125Node36_sound : Sound component125Node36Box :=
  sound_of_literal_split component125Node36Box component125Node28Box component125Node35Box
    .chi (11/16) (by rfl) (by rfl)
    component125Node28_sound component125Node35_sound

noncomputable def component125Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (2), kHi := (5/2), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
theorem component125_sound : Sound component125Box :=
  sound_of_literal_split component125Box component125Node15Box component125Node36Box
    .k (9/4) (by rfl) (by rfl)
    component125Node15_sound component125Node36_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
