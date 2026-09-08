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

private noncomputable def leaf1147Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf1147Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435675/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67106995) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (383738791/268435456) }, upper := { exponent := 0, mantissa := (5965/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134215923/134213990) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1147InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1147LocalValidity :
    LeafFacts leaf1147Box leaf1147Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1147Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67106995) }) = true
      norm_num [leaf1147Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1147CertificateValid :
    WideCertificateValid leaf1147Box leaf1147Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi111ValidityFacts
    leaf1147LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1147CoverageChecked :
    coverageCheck (innerAD leaf1147Box) leaf1147InnerLog = true := by
  rfl'

private theorem leaf1147InnerLogValid :
    leaf1147InnerLog.Valid 8 (innerAD leaf1147Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1147CoverageChecked

private noncomputable def leaf1147InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814661/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1147InputLogOnePlusV_eq :
    leaf1147InputLogOnePlusV = outerEnclosure 24
      (leaf1147Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1147RoundedFacts : LeafRoundedFacts 8
    leaf1147Certificate.logOnePlusV leaf1147InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1147InputLogOnePlusV_eq }

private noncomputable def leaf1147Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi111InputQChi innerPair27Input
    leaf1147InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1147LowerChecked :
    lowerCheck 24 leaf1147Box leaf1147Inputs = true := by
  rfl'

private theorem leaf1147CoversExact : CoversExact 8
    leaf1147Box leaf1147Certificate leaf1147InnerLog leaf1147Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi111RoundedFacts
    innerPair27RoundedFacts leaf1147RoundedFacts (by rfl)

private theorem leaf1147FlatSound : Sound leaf1147Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1147CertificateValid
    leaf1147InnerLogValid leaf1147CoversExact leaf1147LowerChecked

private noncomputable def leaf1148Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf1148Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435677/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553487) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (385049429/268435456) }, upper := { exponent := 0, mantissa := (2993/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67107951/67106974) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1148InnerLog : WideLogData :=
  innerPair27Data

set_option maxRecDepth 1000000 in
private theorem leaf1148LocalValidity :
    LeafFacts leaf1148Box leaf1148Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1148Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553487) }) = true
      norm_num [leaf1148Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1148CertificateValid :
    WideCertificateValid leaf1148Box leaf1148Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi111ValidityFacts
    leaf1148LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1148CoverageChecked :
    coverageCheck (innerAD leaf1148Box) leaf1148InnerLog = true := by
  rfl'

private theorem leaf1148InnerLogValid :
    leaf1148InnerLog.Valid 8 (innerAD leaf1148Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint11PositiveFacts.valid leaf1148CoverageChecked

private noncomputable def leaf1148InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629325/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1148InputLogOnePlusV_eq :
    leaf1148InputLogOnePlusV = outerEnclosure 24
      (leaf1148Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1148RoundedFacts : LeafRoundedFacts 8
    leaf1148Certificate.logOnePlusV leaf1148InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1148InputLogOnePlusV_eq }

private noncomputable def leaf1148Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi111InputQChi innerPair27Input
    leaf1148InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1148LowerChecked :
    lowerCheck 24 leaf1148Box leaf1148Inputs = true := by
  rfl'

private theorem leaf1148CoversExact : CoversExact 8
    leaf1148Box leaf1148Certificate leaf1148InnerLog leaf1148Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi111RoundedFacts
    innerPair27RoundedFacts leaf1148RoundedFacts (by rfl)

private theorem leaf1148FlatSound : Sound leaf1148Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1148CertificateValid
    leaf1148InnerLogValid leaf1148CoversExact leaf1148LowerChecked

private noncomputable def leaf1149Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf1149Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435677/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553453) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (389505605/268435456) }, upper := { exponent := 0, mantissa := (3027/2048) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67107917/67106906) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1149InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1149LocalValidity :
    LeafFacts leaf1149Box leaf1149Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1149Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553453) }) = true
      norm_num [leaf1149Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1149CertificateValid :
    WideCertificateValid leaf1149Box leaf1149Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi112ValidityFacts
    leaf1149LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1149CoverageChecked :
    coverageCheck (innerAD leaf1149Box) leaf1149InnerLog = true := by
  rfl'

private theorem leaf1149InnerLogValid :
    leaf1149InnerLog.Valid 8 (innerAD leaf1149Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1149CoverageChecked

private noncomputable def leaf1149InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1149InputLogOnePlusV_eq :
    leaf1149InputLogOnePlusV = outerEnclosure 24
      (leaf1149Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1149RoundedFacts : LeafRoundedFacts 8
    leaf1149Certificate.logOnePlusV leaf1149InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1149InputLogOnePlusV_eq }

private noncomputable def leaf1149Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi112InputQChi innerPair34Input
    leaf1149InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1149LowerChecked :
    lowerCheck 24 leaf1149Box leaf1149Inputs = true := by
  rfl'

private theorem leaf1149CoversExact : CoversExact 8
    leaf1149Box leaf1149Certificate leaf1149InnerLog leaf1149Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi112RoundedFacts
    innerPair34RoundedFacts leaf1149RoundedFacts (by rfl)

private theorem leaf1149FlatSound : Sound leaf1149Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1149CertificateValid
    leaf1149InnerLogValid leaf1149CoversExact leaf1149LowerChecked

private noncomputable def leaf1150Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf1150Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435679/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776721) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (390881775/268435456) }, upper := { exponent := 0, mantissa := (1519/1024) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33553953/33553442) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1150InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1150LocalValidity :
    LeafFacts leaf1150Box leaf1150Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1150Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776721) }) = true
      norm_num [leaf1150Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1150CertificateValid :
    WideCertificateValid leaf1150Box leaf1150Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi112ValidityFacts
    leaf1150LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1150CoverageChecked :
    coverageCheck (innerAD leaf1150Box) leaf1150InnerLog = true := by
  rfl'

private theorem leaf1150InnerLogValid :
    leaf1150InnerLog.Valid 8 (innerAD leaf1150Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1150CoverageChecked

private noncomputable def leaf1150InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1150InputLogOnePlusV_eq :
    leaf1150InputLogOnePlusV = outerEnclosure 24
      (leaf1150Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1150RoundedFacts : LeafRoundedFacts 8
    leaf1150Certificate.logOnePlusV leaf1150InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1150InputLogOnePlusV_eq }

private noncomputable def leaf1150Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi112InputQChi innerPair34Input
    leaf1150InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1150LowerChecked :
    lowerCheck 24 leaf1150Box leaf1150Inputs = true := by
  rfl'

private theorem leaf1150CoversExact : CoversExact 8
    leaf1150Box leaf1150Certificate leaf1150InnerLog leaf1150Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi112RoundedFacts
    innerPair34RoundedFacts leaf1150RoundedFacts (by rfl)

private theorem leaf1150FlatSound : Sound leaf1150Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1150CertificateValid
    leaf1150InnerLogValid leaf1150CoversExact leaf1150LowerChecked

private noncomputable def leaf1151Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf1151Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435679/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67106953) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (386360067/268435456) }, upper := { exponent := 0, mantissa := (6007/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134215881/134213906) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1151InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1151LocalValidity :
    LeafFacts leaf1151Box leaf1151Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1151Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67106953) }) = true
      norm_num [leaf1151Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1151CertificateValid :
    WideCertificateValid leaf1151Box leaf1151Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi111ValidityFacts
    leaf1151LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1151CoverageChecked :
    coverageCheck (innerAD leaf1151Box) leaf1151InnerLog = true := by
  rfl'

private theorem leaf1151InnerLogValid :
    leaf1151InnerLog.Valid 8 (innerAD leaf1151Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1151CoverageChecked

private noncomputable def leaf1151InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (726833/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1151InputLogOnePlusV_eq :
    leaf1151InputLogOnePlusV = outerEnclosure 24
      (leaf1151Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1151RoundedFacts : LeafRoundedFacts 8
    leaf1151Certificate.logOnePlusV leaf1151InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1151InputLogOnePlusV_eq }

private noncomputable def leaf1151Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi111InputQChi innerPair34Input
    leaf1151InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1151LowerChecked :
    lowerCheck 24 leaf1151Box leaf1151Inputs = true := by
  rfl'

private theorem leaf1151CoversExact : CoversExact 8
    leaf1151Box leaf1151Certificate leaf1151InnerLog leaf1151Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi111RoundedFacts
    innerPair34RoundedFacts leaf1151RoundedFacts (by rfl)

private theorem leaf1151FlatSound : Sound leaf1151Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1151CertificateValid
    leaf1151InnerLogValid leaf1151CoversExact leaf1151LowerChecked

private noncomputable def leaf1152Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf1152Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435681/268435456) }, vSqrt := { lower := (32765/32768), upper := (16777232/16776733) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (387670705/268435456) }, upper := { exponent := 0, mantissa := (1507/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (33553965/33553466) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1152InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1152LocalValidity :
    LeafFacts leaf1152Box leaf1152Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1152Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (16777232/16776733) }) = true
      norm_num [leaf1152Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1152CertificateValid :
    WideCertificateValid leaf1152Box leaf1152Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi111ValidityFacts
    leaf1152LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1152CoverageChecked :
    coverageCheck (innerAD leaf1152Box) leaf1152InnerLog = true := by
  rfl'

private theorem leaf1152InnerLogValid :
    leaf1152InnerLog.Valid 8 (innerAD leaf1152Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1152CoverageChecked

private noncomputable def leaf1152InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814665/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1152InputLogOnePlusV_eq :
    leaf1152InputLogOnePlusV = outerEnclosure 24
      (leaf1152Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1152RoundedFacts : LeafRoundedFacts 8
    leaf1152Certificate.logOnePlusV leaf1152InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1152InputLogOnePlusV_eq }

private noncomputable def leaf1152Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi111InputQChi innerPair34Input
    leaf1152InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1152LowerChecked :
    lowerCheck 24 leaf1152Box leaf1152Inputs = true := by
  rfl'

private theorem leaf1152CoversExact : CoversExact 8
    leaf1152Box leaf1152Certificate leaf1152InnerLog leaf1152Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi111RoundedFacts
    innerPair34RoundedFacts leaf1152RoundedFacts (by rfl)

private theorem leaf1152FlatSound : Sound leaf1152Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1152CertificateValid
    leaf1152InnerLogValid leaf1152CoversExact leaf1152LowerChecked

private noncomputable def leaf1153Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf1153Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435681/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905808896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (392257945/268435456) }, upper := { exponent := 0, mantissa := (3049/2048) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811973461/45811617792) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1153InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1153LocalValidity :
    LeafFacts leaf1153Box leaf1153Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1153Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905808896) }) = true
      norm_num [leaf1153Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1153CertificateValid :
    WideCertificateValid leaf1153Box leaf1153Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi112ValidityFacts
    leaf1153LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1153CoverageChecked :
    coverageCheck (innerAD leaf1153Box) leaf1153InnerLog = true := by
  rfl'

private theorem leaf1153InnerLogValid :
    leaf1153InnerLog.Valid 8 (innerAD leaf1153Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1153CoverageChecked

private noncomputable def leaf1153InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1153InputLogOnePlusV_eq :
    leaf1153InputLogOnePlusV = outerEnclosure 24
      (leaf1153Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1153RoundedFacts : LeafRoundedFacts 8
    leaf1153Certificate.logOnePlusV leaf1153InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1153InputLogOnePlusV_eq }

private noncomputable def leaf1153Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi112InputQChi innerPair34Input
    leaf1153InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1153LowerChecked :
    lowerCheck 24 leaf1153Box leaf1153Inputs = true := by
  rfl'

private theorem leaf1153CoversExact : CoversExact 8
    leaf1153Box leaf1153Certificate leaf1153InnerLog leaf1153Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi112RoundedFacts
    innerPair34RoundedFacts leaf1153RoundedFacts (by rfl)

private theorem leaf1153FlatSound : Sound leaf1153Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1153CertificateValid
    leaf1153InnerLogValid leaf1153CoversExact leaf1153LowerChecked

private noncomputable def leaf1154Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf1154Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435683/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743480832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (393634115/268435456) }, upper := { exponent := 0, mantissa := (765/512) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487179571/27486961664) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1154InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1154LocalValidity :
    LeafFacts leaf1154Box leaf1154Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1154Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743480832) }) = true
      norm_num [leaf1154Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1154CertificateValid :
    WideCertificateValid leaf1154Box leaf1154Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi112ValidityFacts
    leaf1154LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1154CoverageChecked :
    coverageCheck (innerAD leaf1154Box) leaf1154InnerLog = true := by
  rfl'

private theorem leaf1154InnerLogValid :
    leaf1154InnerLog.Valid 8 (innerAD leaf1154Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1154CoverageChecked

private noncomputable def leaf1154InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814607/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1154InputLogOnePlusV_eq :
    leaf1154InputLogOnePlusV = outerEnclosure 24
      (leaf1154Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1154RoundedFacts : LeafRoundedFacts 8
    leaf1154Certificate.logOnePlusV leaf1154InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1154InputLogOnePlusV_eq }

private noncomputable def leaf1154Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi112InputQChi innerPair34Input
    leaf1154InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1154LowerChecked :
    lowerCheck 24 leaf1154Box leaf1154Inputs = true := by
  rfl'

private theorem leaf1154CoversExact : CoversExact 8
    leaf1154Box leaf1154Certificate leaf1154InnerLog leaf1154Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi112RoundedFacts
    innerPair34RoundedFacts leaf1154RoundedFacts (by rfl)

private theorem leaf1154FlatSound : Sound leaf1154Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1154CertificateValid
    leaf1154InnerLogValid leaf1154CoversExact leaf1154LowerChecked

private noncomputable def leaf1155Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (11/64), chiHi := (23/128) }

private noncomputable def leaf1155Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435679/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905793536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (395272419/268435456) }, upper := { exponent := 0, mantissa := (6143/4096) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi113LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811958101/45811587072) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1155InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1155LocalValidity :
    LeafFacts leaf1155Box leaf1155Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1155Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905793536) }) = true
      norm_num [leaf1155Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1155CertificateValid :
    WideCertificateValid leaf1155Box leaf1155Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi113ValidityFacts
    leaf1155LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1155CoverageChecked :
    coverageCheck (innerAD leaf1155Box) leaf1155InnerLog = true := by
  rfl'

private theorem leaf1155InnerLogValid :
    leaf1155InnerLog.Valid 8 (innerAD leaf1155Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1155CoverageChecked

private noncomputable def leaf1155InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1155InputLogOnePlusV_eq :
    leaf1155InputLogOnePlusV = outerEnclosure 24
      (leaf1155Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1155RoundedFacts : LeafRoundedFacts 8
    leaf1155Certificate.logOnePlusV leaf1155InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1155InputLogOnePlusV_eq }

private noncomputable def leaf1155Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi113InputQChi innerPair34Input
    leaf1155InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1155LowerChecked :
    lowerCheck 24 leaf1155Box leaf1155Inputs = true := by
  rfl'

private theorem leaf1155CoversExact : CoversExact 8
    leaf1155Box leaf1155Certificate leaf1155InnerLog leaf1155Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi113RoundedFacts
    innerPair34RoundedFacts leaf1155RoundedFacts (by rfl)

private theorem leaf1155FlatSound : Sound leaf1155Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1155CertificateValid
    leaf1155InnerLogValid leaf1155CoversExact leaf1155LowerChecked

private noncomputable def leaf1156Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (11/64), chiHi := (23/128) }

private noncomputable def leaf1156Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435681/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717357056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (396714121/268435456) }, upper := { exponent := 0, mantissa := (3083/2048) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi113LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435850751/137434714112) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1156InnerLog : WideLogData :=
  innerPair153Data

set_option maxRecDepth 1000000 in
private theorem leaf1156LocalValidity :
    LeafFacts leaf1156Box leaf1156Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1156Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717357056) }) = true
      norm_num [leaf1156Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1156CertificateValid :
    WideCertificateValid leaf1156Box leaf1156Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi113ValidityFacts
    leaf1156LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1156CoverageChecked :
    coverageCheck (innerAD leaf1156Box) leaf1156InnerLog = true := by
  rfl'

private theorem leaf1156InnerLogValid :
    leaf1156InnerLog.Valid 8 (innerAD leaf1156Box) :=
  wideLogDataValid_of_cachedCheck endpoint42PositiveFacts
    endpoint49PositiveFacts.valid leaf1156CoverageChecked

private noncomputable def leaf1156InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629219/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1156InputLogOnePlusV_eq :
    leaf1156InputLogOnePlusV = outerEnclosure 24
      (leaf1156Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1156RoundedFacts : LeafRoundedFacts 8
    leaf1156Certificate.logOnePlusV leaf1156InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1156InputLogOnePlusV_eq }

private noncomputable def leaf1156Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi113InputQChi innerPair153Input
    leaf1156InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1156LowerChecked :
    lowerCheck 24 leaf1156Box leaf1156Inputs = true := by
  rfl'

private theorem leaf1156CoversExact : CoversExact 8
    leaf1156Box leaf1156Certificate leaf1156InnerLog leaf1156Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi113RoundedFacts
    innerPair153RoundedFacts leaf1156RoundedFacts (by rfl)

private theorem leaf1156FlatSound : Sound leaf1156Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1156CertificateValid
    leaf1156InnerLogValid leaf1156CoversExact leaf1156LowerChecked

private noncomputable def leaf1157Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (89/32), chiLo := (23/128), chiHi := (3/16) }

private noncomputable def leaf1157Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435681/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717289472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (401039233/268435456) }, upper := { exponent := 0, mantissa := (779/512) } }, logOuter := sk107LogOuterCertificate, logK := sk107LogKCertificate, logChi := chi114LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435783167/137434578944) } }, logDArg := sk107LogDArgCertificate }

private noncomputable def leaf1157InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1157LocalValidity :
    LeafFacts leaf1157Box leaf1157Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1157Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717289472) }) = true
      norm_num [leaf1157Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1157CertificateValid :
    WideCertificateValid leaf1157Box leaf1157Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk107ValidityFacts chi114ValidityFacts
    leaf1157LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1157CoverageChecked :
    coverageCheck (innerAD leaf1157Box) leaf1157InnerLog = true := by
  rfl'

private theorem leaf1157InnerLogValid :
    leaf1157InnerLog.Valid 8 (innerAD leaf1157Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1157CoverageChecked

private noncomputable def leaf1157InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907307/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1157InputLogOnePlusV_eq :
    leaf1157InputLogOnePlusV = outerEnclosure 24
      (leaf1157Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1157RoundedFacts : LeafRoundedFacts 8
    leaf1157Certificate.logOnePlusV leaf1157InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1157InputLogOnePlusV_eq }

private noncomputable def leaf1157Inputs : Inputs :=
  inputsOfCaches globalInput sk107RoundedInputs
    chi114InputQChi innerPair35Input
    leaf1157InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1157LowerChecked :
    lowerCheck 24 leaf1157Box leaf1157Inputs = true := by
  rfl'

private theorem leaf1157CoversExact : CoversExact 8
    leaf1157Box leaf1157Certificate leaf1157InnerLog leaf1157Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk107RoundedFacts chi114RoundedFacts
    innerPair35RoundedFacts leaf1157RoundedFacts (by rfl)

private theorem leaf1157FlatSound : Sound leaf1157Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1157CertificateValid
    leaf1157InnerLogValid leaf1157CoversExact leaf1157LowerChecked

private noncomputable def leaf1158Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (89/32), kHi := (45/16), chiLo := (23/128), chiHi := (3/16) }

private noncomputable def leaf1158Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435683/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717264896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (402546467/268435456) }, upper := { exponent := 0, mantissa := (391/256) } }, logOuter := sk108LogOuterCertificate, logK := sk108LogKCertificate, logChi := chi114LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435758591/137434529792) } }, logDArg := sk108LogDArgCertificate }

private noncomputable def leaf1158InnerLog : WideLogData :=
  innerPair35Data

set_option maxRecDepth 1000000 in
private theorem leaf1158LocalValidity :
    LeafFacts leaf1158Box leaf1158Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1158Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717264896) }) = true
      norm_num [leaf1158Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1158CertificateValid :
    WideCertificateValid leaf1158Box leaf1158Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk108ValidityFacts chi114ValidityFacts
    leaf1158LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1158CoverageChecked :
    coverageCheck (innerAD leaf1158Box) leaf1158InnerLog = true := by
  rfl'

private theorem leaf1158InnerLogValid :
    leaf1158InnerLog.Valid 8 (innerAD leaf1158Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint13PositiveFacts.valid leaf1158CoverageChecked

private noncomputable def leaf1158InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629231/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1158InputLogOnePlusV_eq :
    leaf1158InputLogOnePlusV = outerEnclosure 24
      (leaf1158Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1158RoundedFacts : LeafRoundedFacts 8
    leaf1158Certificate.logOnePlusV leaf1158InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1158InputLogOnePlusV_eq }

private noncomputable def leaf1158Inputs : Inputs :=
  inputsOfCaches globalInput sk108RoundedInputs
    chi114InputQChi innerPair35Input
    leaf1158InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1158LowerChecked :
    lowerCheck 24 leaf1158Box leaf1158Inputs = true := by
  rfl'

private theorem leaf1158CoversExact : CoversExact 8
    leaf1158Box leaf1158Certificate leaf1158InnerLog leaf1158Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk108RoundedFacts chi114RoundedFacts
    innerPair35RoundedFacts leaf1158RoundedFacts (by rfl)

private theorem leaf1158FlatSound : Sound leaf1158Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1158CertificateValid
    leaf1158InnerLogValid leaf1158CoversExact leaf1158LowerChecked

private noncomputable def leaf1159Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (11/64), chiHi := (23/128) }

private noncomputable def leaf1159Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435683/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717333504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (398155823/268435456) }, upper := { exponent := 0, mantissa := (6189/4096) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi113LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435827199/137434667008) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1159InnerLog : WideLogData :=
  innerPair153Data

set_option maxRecDepth 1000000 in
private theorem leaf1159LocalValidity :
    LeafFacts leaf1159Box leaf1159Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1159Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717333504) }) = true
      norm_num [leaf1159Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1159CertificateValid :
    WideCertificateValid leaf1159Box leaf1159Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi113ValidityFacts
    leaf1159LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1159CoverageChecked :
    coverageCheck (innerAD leaf1159Box) leaf1159InnerLog = true := by
  rfl'

private theorem leaf1159InnerLogValid :
    leaf1159InnerLog.Valid 8 (innerAD leaf1159Box) :=
  wideLogDataValid_of_cachedCheck endpoint42PositiveFacts
    endpoint49PositiveFacts.valid leaf1159CoverageChecked

private noncomputable def leaf1159InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814611/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1159InputLogOnePlusV_eq :
    leaf1159InputLogOnePlusV = outerEnclosure 24
      (leaf1159Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1159RoundedFacts : LeafRoundedFacts 8
    leaf1159Certificate.logOnePlusV leaf1159InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1159InputLogOnePlusV_eq }

private noncomputable def leaf1159Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi113InputQChi innerPair153Input
    leaf1159InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1159LowerChecked :
    lowerCheck 24 leaf1159Box leaf1159Inputs = true := by
  rfl'

private theorem leaf1159CoversExact : CoversExact 8
    leaf1159Box leaf1159Certificate leaf1159InnerLog leaf1159Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi113RoundedFacts
    innerPair153RoundedFacts leaf1159RoundedFacts (by rfl)

private theorem leaf1159FlatSound : Sound leaf1159Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1159CertificateValid
    leaf1159InnerLogValid leaf1159CoversExact leaf1159LowerChecked

private noncomputable def leaf1160Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (11/64), chiHi := (23/128) }

private noncomputable def leaf1160Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435685/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905769984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (399597525/268435456) }, upper := { exponent := 0, mantissa := (1553/1024) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi113LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811934549/45811539968) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1160InnerLog : WideLogData :=
  innerPair408Data

set_option maxRecDepth 1000000 in
private theorem leaf1160LocalValidity :
    LeafFacts leaf1160Box leaf1160Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1160Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905769984) }) = true
      norm_num [leaf1160Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1160CertificateValid :
    WideCertificateValid leaf1160Box leaf1160Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi113ValidityFacts
    leaf1160LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1160CoverageChecked :
    coverageCheck (innerAD leaf1160Box) leaf1160InnerLog = true := by
  rfl'

private theorem leaf1160InnerLogValid :
    leaf1160InnerLog.Valid 8 (innerAD leaf1160Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint19PositiveFacts.valid leaf1160CoverageChecked

private noncomputable def leaf1160InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1160InputLogOnePlusV_eq :
    leaf1160InputLogOnePlusV = outerEnclosure 24
      (leaf1160Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1160RoundedFacts : LeafRoundedFacts 8
    leaf1160Certificate.logOnePlusV leaf1160InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1160InputLogOnePlusV_eq }

private noncomputable def leaf1160Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi113InputQChi innerPair408Input
    leaf1160InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1160LowerChecked :
    lowerCheck 24 leaf1160Box leaf1160Inputs = true := by
  rfl'

private theorem leaf1160CoversExact : CoversExact 8
    leaf1160Box leaf1160Certificate leaf1160InnerLog leaf1160Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi113RoundedFacts
    innerPair408RoundedFacts leaf1160RoundedFacts (by rfl)

private theorem leaf1160FlatSound : Sound leaf1160Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1160CertificateValid
    leaf1160InnerLogValid leaf1160CoversExact leaf1160LowerChecked

private noncomputable def leaf1161Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (91/32), chiLo := (23/128), chiHi := (3/16) }

private noncomputable def leaf1161Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435685/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743448064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (404053701/268435456) }, upper := { exponent := 0, mantissa := (785/512) } }, logOuter := sk109LogOuterCertificate, logK := sk109LogKCertificate, logChi := chi114LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487146803/27486896128) } }, logDArg := sk109LogDArgCertificate }

private noncomputable def leaf1161InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1161LocalValidity :
    LeafFacts leaf1161Box leaf1161Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1161Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743448064) }) = true
      norm_num [leaf1161Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1161CertificateValid :
    WideCertificateValid leaf1161Box leaf1161Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk109ValidityFacts chi114ValidityFacts
    leaf1161LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1161CoverageChecked :
    coverageCheck (innerAD leaf1161Box) leaf1161InnerLog = true := by
  rfl'

private theorem leaf1161InnerLogValid :
    leaf1161InnerLog.Valid 8 (innerAD leaf1161Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1161CoverageChecked

private noncomputable def leaf1161InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1161InputLogOnePlusV_eq :
    leaf1161InputLogOnePlusV = outerEnclosure 24
      (leaf1161Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1161RoundedFacts : LeafRoundedFacts 8
    leaf1161Certificate.logOnePlusV leaf1161InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1161InputLogOnePlusV_eq }

private noncomputable def leaf1161Inputs : Inputs :=
  inputsOfCaches globalInput sk109RoundedInputs
    chi114InputQChi innerPair40Input
    leaf1161InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1161LowerChecked :
    lowerCheck 24 leaf1161Box leaf1161Inputs = true := by
  rfl'

private theorem leaf1161CoversExact : CoversExact 8
    leaf1161Box leaf1161Certificate leaf1161InnerLog leaf1161Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk109RoundedFacts chi114RoundedFacts
    innerPair40RoundedFacts leaf1161RoundedFacts (by rfl)

private theorem leaf1161FlatSound : Sound leaf1161Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1161CertificateValid
    leaf1161InnerLogValid leaf1161CoversExact leaf1161LowerChecked

private noncomputable def leaf1162Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (91/32), kHi := (23/8), chiLo := (23/128), chiHi := (3/16) }

private noncomputable def leaf1162Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435687/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717215744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (405560935/268435456) }, upper := { exponent := 0, mantissa := (197/128) } }, logOuter := sk110LogOuterCertificate, logK := sk110LogKCertificate, logChi := chi114LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435709439/137434431488) } }, logDArg := sk110LogDArgCertificate }

private noncomputable def leaf1162InnerLog : WideLogData :=
  innerPair45Data

set_option maxRecDepth 1000000 in
private theorem leaf1162LocalValidity :
    LeafFacts leaf1162Box leaf1162Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1162Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717215744) }) = true
      norm_num [leaf1162Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1162CertificateValid :
    WideCertificateValid leaf1162Box leaf1162Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk110ValidityFacts chi114ValidityFacts
    leaf1162LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1162CoverageChecked :
    coverageCheck (innerAD leaf1162Box) leaf1162InnerLog = true := by
  rfl'

private theorem leaf1162InnerLogValid :
    leaf1162InnerLog.Valid 8 (innerAD leaf1162Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint43PositiveFacts.valid leaf1162CoverageChecked

private noncomputable def leaf1162InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1162InputLogOnePlusV_eq :
    leaf1162InputLogOnePlusV = outerEnclosure 24
      (leaf1162Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1162RoundedFacts : LeafRoundedFacts 8
    leaf1162Certificate.logOnePlusV leaf1162InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1162InputLogOnePlusV_eq }

private noncomputable def leaf1162Inputs : Inputs :=
  inputsOfCaches globalInput sk110RoundedInputs
    chi114InputQChi innerPair45Input
    leaf1162InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1162LowerChecked :
    lowerCheck 24 leaf1162Box leaf1162Inputs = true := by
  rfl'

private theorem leaf1162CoversExact : CoversExact 8
    leaf1162Box leaf1162Certificate leaf1162InnerLog leaf1162Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk110RoundedFacts chi114RoundedFacts
    innerPair45RoundedFacts leaf1162RoundedFacts (by rfl)

private theorem leaf1162FlatSound : Sound leaf1162Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1162CertificateValid
    leaf1162InnerLogValid leaf1162CoversExact leaf1162LowerChecked

private noncomputable def leaf1163Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf1163Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435683/268435456) }, vSqrt := { lower := (32765/32768), upper := (67108928/67106911) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (388981343/268435456) }, upper := { exponent := 0, mantissa := (6049/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (134215839/134213822) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1163InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1163LocalValidity :
    LeafFacts leaf1163Box leaf1163Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1163Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (67108928/67106911) }) = true
      norm_num [leaf1163Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1163CertificateValid :
    WideCertificateValid leaf1163Box leaf1163Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi111ValidityFacts
    leaf1163LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1163CoverageChecked :
    coverageCheck (innerAD leaf1163Box) leaf1163InnerLog = true := by
  rfl'

private theorem leaf1163InnerLogValid :
    leaf1163InnerLog.Valid 8 (innerAD leaf1163Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1163CoverageChecked

private noncomputable def leaf1163InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1163InputLogOnePlusV_eq :
    leaf1163InputLogOnePlusV = outerEnclosure 24
      (leaf1163Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1163RoundedFacts : LeafRoundedFacts 8
    leaf1163Certificate.logOnePlusV leaf1163InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1163InputLogOnePlusV_eq }

private noncomputable def leaf1163Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi111InputQChi innerPair34Input
    leaf1163InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1163LowerChecked :
    lowerCheck 24 leaf1163Box leaf1163Inputs = true := by
  rfl'

private theorem leaf1163CoversExact : CoversExact 8
    leaf1163Box leaf1163Certificate leaf1163InnerLog leaf1163Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi111RoundedFacts
    innerPair34RoundedFacts leaf1163RoundedFacts (by rfl)

private theorem leaf1163FlatSound : Sound leaf1163Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1163CertificateValid
    leaf1163InnerLogValid leaf1163CoversExact leaf1163LowerChecked

private noncomputable def leaf1164Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf1164Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435685/268435456) }, vSqrt := { lower := (32765/32768), upper := (33554464/33553445) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (390291981/268435456) }, upper := { exponent := 0, mantissa := (3035/2048) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (67107909/67106890) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf1164InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1164LocalValidity :
    LeafFacts leaf1164Box leaf1164Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1164Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (33554464/33553445) }) = true
      norm_num [leaf1164Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1164CertificateValid :
    WideCertificateValid leaf1164Box leaf1164Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi111ValidityFacts
    leaf1164LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1164CoverageChecked :
    coverageCheck (innerAD leaf1164Box) leaf1164InnerLog = true := by
  rfl'

private theorem leaf1164InnerLogValid :
    leaf1164InnerLog.Valid 8 (innerAD leaf1164Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1164CoverageChecked

private noncomputable def leaf1164InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1164InputLogOnePlusV_eq :
    leaf1164InputLogOnePlusV = outerEnclosure 24
      (leaf1164Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1164RoundedFacts : LeafRoundedFacts 8
    leaf1164Certificate.logOnePlusV leaf1164InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1164InputLogOnePlusV_eq }

private noncomputable def leaf1164Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi111InputQChi innerPair34Input
    leaf1164InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1164LowerChecked :
    lowerCheck 24 leaf1164Box leaf1164Inputs = true := by
  rfl'

private theorem leaf1164CoversExact : CoversExact 8
    leaf1164Box leaf1164Certificate leaf1164InnerLog leaf1164Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi111RoundedFacts
    innerPair34RoundedFacts leaf1164RoundedFacts (by rfl)

private theorem leaf1164FlatSound : Sound leaf1164Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1164CertificateValid
    leaf1164InnerLogValid leaf1164CoversExact leaf1164LowerChecked

private noncomputable def leaf1165Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf1165Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435685/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717381632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (395010285/268435456) }, upper := { exponent := 0, mantissa := (3071/2048) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435875327/137434763264) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1165InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1165LocalValidity :
    LeafFacts leaf1165Box leaf1165Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1165Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717381632) }) = true
      norm_num [leaf1165Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1165CertificateValid :
    WideCertificateValid leaf1165Box leaf1165Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi112ValidityFacts
    leaf1165LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1165CoverageChecked :
    coverageCheck (innerAD leaf1165Box) leaf1165InnerLog = true := by
  rfl'

private theorem leaf1165InnerLogValid :
    leaf1165InnerLog.Valid 8 (innerAD leaf1165Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1165CoverageChecked

private noncomputable def leaf1165InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (363413/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf1165InputLogOnePlusV_eq :
    leaf1165InputLogOnePlusV = outerEnclosure 24
      (leaf1165Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1165RoundedFacts : LeafRoundedFacts 8
    leaf1165Certificate.logOnePlusV leaf1165InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1165InputLogOnePlusV_eq }

private noncomputable def leaf1165Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi112InputQChi innerPair34Input
    leaf1165InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1165LowerChecked :
    lowerCheck 24 leaf1165Box leaf1165Inputs = true := by
  rfl'

private theorem leaf1165CoversExact : CoversExact 8
    leaf1165Box leaf1165Certificate leaf1165InnerLog leaf1165Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi112RoundedFacts
    innerPair34RoundedFacts leaf1165RoundedFacts (by rfl)

private theorem leaf1165FlatSound : Sound leaf1165Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1165CertificateValid
    leaf1165InnerLogValid leaf1165CoversExact leaf1165LowerChecked

private noncomputable def leaf1166Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf1166Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435687/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905786368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (396386455/268435456) }, upper := { exponent := 0, mantissa := (1541/1024) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811950933/45811572736) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf1166InnerLog : WideLogData :=
  innerPair153Data

set_option maxRecDepth 1000000 in
private theorem leaf1166LocalValidity :
    LeafFacts leaf1166Box leaf1166Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1166Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905786368) }) = true
      norm_num [leaf1166Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1166CertificateValid :
    WideCertificateValid leaf1166Box leaf1166Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi112ValidityFacts
    leaf1166LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1166CoverageChecked :
    coverageCheck (innerAD leaf1166Box) leaf1166InnerLog = true := by
  rfl'

private theorem leaf1166InnerLogValid :
    leaf1166InnerLog.Valid 8 (innerAD leaf1166Box) :=
  wideLogDataValid_of_cachedCheck endpoint42PositiveFacts
    endpoint49PositiveFacts.valid leaf1166CoverageChecked

private noncomputable def leaf1166InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629219/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1166InputLogOnePlusV_eq :
    leaf1166InputLogOnePlusV = outerEnclosure 24
      (leaf1166Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1166RoundedFacts : LeafRoundedFacts 8
    leaf1166Certificate.logOnePlusV leaf1166InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1166InputLogOnePlusV_eq }

private noncomputable def leaf1166Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi112InputQChi innerPair153Input
    leaf1166InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1166LowerChecked :
    lowerCheck 24 leaf1166Box leaf1166Inputs = true := by
  rfl'

private theorem leaf1166CoversExact : CoversExact 8
    leaf1166Box leaf1166Certificate leaf1166InnerLog leaf1166Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi112RoundedFacts
    innerPair153RoundedFacts leaf1166RoundedFacts (by rfl)

private theorem leaf1166FlatSound : Sound leaf1166Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1166CertificateValid
    leaf1166InnerLogValid leaf1166CoversExact leaf1166LowerChecked

private noncomputable def leaf1167Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf1167Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435687/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717433856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (391602619/268435456) }, upper := { exponent := 0, mantissa := (6091/4096) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435927551/137434867712) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf1167InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1167LocalValidity :
    LeafFacts leaf1167Box leaf1167Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1167Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717433856) }) = true
      norm_num [leaf1167Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1167CertificateValid :
    WideCertificateValid leaf1167Box leaf1167Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi111ValidityFacts
    leaf1167LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1167CoverageChecked :
    coverageCheck (innerAD leaf1167Box) leaf1167InnerLog = true := by
  rfl'

private theorem leaf1167InnerLogValid :
    leaf1167InnerLog.Valid 8 (innerAD leaf1167Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1167CoverageChecked

private noncomputable def leaf1167InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814605/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1167InputLogOnePlusV_eq :
    leaf1167InputLogOnePlusV = outerEnclosure 24
      (leaf1167Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1167RoundedFacts : LeafRoundedFacts 8
    leaf1167Certificate.logOnePlusV leaf1167InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1167InputLogOnePlusV_eq }

private noncomputable def leaf1167Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi111InputQChi innerPair34Input
    leaf1167InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1167LowerChecked :
    lowerCheck 24 leaf1167Box leaf1167Inputs = true := by
  rfl'

private theorem leaf1167CoversExact : CoversExact 8
    leaf1167Box leaf1167Certificate leaf1167InnerLog leaf1167Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi111RoundedFacts
    innerPair34RoundedFacts leaf1167RoundedFacts (by rfl)

private theorem leaf1167FlatSound : Sound leaf1167Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1167CertificateValid
    leaf1167InnerLogValid leaf1167CoversExact leaf1167LowerChecked

private noncomputable def leaf1168Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (5/32), chiHi := (21/128) }

private noncomputable def leaf1168Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435689/268435456) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717412352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (392913257/268435456) }, upper := { exponent := 0, mantissa := (191/128) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi111LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435906047/137434824704) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf1168InnerLog : WideLogData :=
  innerPair34Data

set_option maxRecDepth 1000000 in
private theorem leaf1168LocalValidity :
    LeafFacts leaf1168Box leaf1168Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1168Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717412352) }) = true
      norm_num [leaf1168Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1168CertificateValid :
    WideCertificateValid leaf1168Box leaf1168Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi111ValidityFacts
    leaf1168LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1168CoverageChecked :
    coverageCheck (innerAD leaf1168Box) leaf1168InnerLog = true := by
  rfl'

private theorem leaf1168InnerLogValid :
    leaf1168InnerLog.Valid 8 (innerAD leaf1168Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint11PositiveFacts.valid leaf1168CoverageChecked

private noncomputable def leaf1168InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629213/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1168InputLogOnePlusV_eq :
    leaf1168InputLogOnePlusV = outerEnclosure 24
      (leaf1168Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1168RoundedFacts : LeafRoundedFacts 8
    leaf1168Certificate.logOnePlusV leaf1168InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1168InputLogOnePlusV_eq }

private noncomputable def leaf1168Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi111InputQChi innerPair34Input
    leaf1168InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1168LowerChecked :
    lowerCheck 24 leaf1168Box leaf1168Inputs = true := by
  rfl'

private theorem leaf1168CoversExact : CoversExact 8
    leaf1168Box leaf1168Certificate leaf1168InnerLog leaf1168Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi111RoundedFacts
    innerPair34RoundedFacts leaf1168RoundedFacts (by rfl)

private theorem leaf1168FlatSound : Sound leaf1168Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1168CertificateValid
    leaf1168InnerLogValid leaf1168CoversExact leaf1168LowerChecked

private noncomputable def leaf1169Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf1169Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435689/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717336576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (397762625/268435456) }, upper := { exponent := 0, mantissa := (3093/2048) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435830271/137434673152) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf1169InnerLog : WideLogData :=
  innerPair153Data

set_option maxRecDepth 1000000 in
private theorem leaf1169LocalValidity :
    LeafFacts leaf1169Box leaf1169Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1169Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717336576) }) = true
      norm_num [leaf1169Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1169CertificateValid :
    WideCertificateValid leaf1169Box leaf1169Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi112ValidityFacts
    leaf1169LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1169CoverageChecked :
    coverageCheck (innerAD leaf1169Box) leaf1169InnerLog = true := by
  rfl'

private theorem leaf1169InnerLogValid :
    leaf1169InnerLog.Valid 8 (innerAD leaf1169Box) :=
  wideLogDataValid_of_cachedCheck endpoint42PositiveFacts
    endpoint49PositiveFacts.valid leaf1169CoverageChecked

private noncomputable def leaf1169InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814611/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1169InputLogOnePlusV_eq :
    leaf1169InputLogOnePlusV = outerEnclosure 24
      (leaf1169Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1169RoundedFacts : LeafRoundedFacts 8
    leaf1169Certificate.logOnePlusV leaf1169InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1169InputLogOnePlusV_eq }

private noncomputable def leaf1169Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi112InputQChi innerPair153Input
    leaf1169InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1169LowerChecked :
    lowerCheck 24 leaf1169Box leaf1169Inputs = true := by
  rfl'

private theorem leaf1169CoversExact : CoversExact 8
    leaf1169Box leaf1169Certificate leaf1169InnerLog leaf1169Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi112RoundedFacts
    innerPair153RoundedFacts leaf1169RoundedFacts (by rfl)

private theorem leaf1169FlatSound : Sound leaf1169Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1169CertificateValid
    leaf1169InnerLogValid leaf1169CoversExact leaf1169LowerChecked

private noncomputable def leaf1170Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (21/128), chiHi := (11/64) }

private noncomputable def leaf1170Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435691/268435456) }, vSqrt := { lower := (65529/65536), upper := (4042264335/4042194944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (399138795/268435456) }, upper := { exponent := 0, mantissa := (97/64) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi112LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8084459279/8084389888) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf1170InnerLog : WideLogData :=
  innerPair409Data

set_option maxRecDepth 1000000 in
private theorem leaf1170LocalValidity :
    LeafFacts leaf1170Box leaf1170Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1170Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4042264335/4042194944) }) = true
      norm_num [leaf1170Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1170CertificateValid :
    WideCertificateValid leaf1170Box leaf1170Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi112ValidityFacts
    leaf1170LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1170CoverageChecked :
    coverageCheck (innerAD leaf1170Box) leaf1170InnerLog = true := by
  rfl'

private theorem leaf1170InnerLogValid :
    leaf1170InnerLog.Valid 8 (innerAD leaf1170Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint49PositiveFacts.valid leaf1170CoverageChecked

private noncomputable def leaf1170InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1170InputLogOnePlusV_eq :
    leaf1170InputLogOnePlusV = outerEnclosure 24
      (leaf1170Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1170RoundedFacts : LeafRoundedFacts 8
    leaf1170Certificate.logOnePlusV leaf1170InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1170InputLogOnePlusV_eq }

private noncomputable def leaf1170Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi112InputQChi innerPair409Input
    leaf1170InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1170LowerChecked :
    lowerCheck 24 leaf1170Box leaf1170Inputs = true := by
  rfl'

private theorem leaf1170CoversExact : CoversExact 8
    leaf1170Box leaf1170Certificate leaf1170InnerLog leaf1170Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi112RoundedFacts
    innerPair409RoundedFacts leaf1170RoundedFacts (by rfl)

private theorem leaf1170FlatSound : Sound leaf1170Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1170CertificateValid
    leaf1170InnerLogValid leaf1170CoversExact leaf1170LowerChecked

private noncomputable def leaf1171Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (11/64), chiHi := (23/128) }

private noncomputable def leaf1171Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435687/268435456) }, vSqrt := { lower := (32765/32768), upper := (13743698739/13743457280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (401039227/268435456) }, upper := { exponent := 0, mantissa := (6235/4096) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi113LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (27487156019/27486914560) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1171InnerLog : WideLogData :=
  innerPair408Data

set_option maxRecDepth 1000000 in
private theorem leaf1171LocalValidity :
    LeafFacts leaf1171Box leaf1171Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1171Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (13743698739/13743457280) }) = true
      norm_num [leaf1171Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1171CertificateValid :
    WideCertificateValid leaf1171Box leaf1171Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi113ValidityFacts
    leaf1171LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1171CoverageChecked :
    coverageCheck (innerAD leaf1171Box) leaf1171InnerLog = true := by
  rfl'

private theorem leaf1171InnerLogValid :
    leaf1171InnerLog.Valid 8 (innerAD leaf1171Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint19PositiveFacts.valid leaf1171CoverageChecked

private noncomputable def leaf1171InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (2907307/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1171InputLogOnePlusV_eq :
    leaf1171InputLogOnePlusV = outerEnclosure 24
      (leaf1171Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1171RoundedFacts : LeafRoundedFacts 8
    leaf1171Certificate.logOnePlusV leaf1171InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1171InputLogOnePlusV_eq }

private noncomputable def leaf1171Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi113InputQChi innerPair408Input
    leaf1171InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1171LowerChecked :
    lowerCheck 24 leaf1171Box leaf1171Inputs = true := by
  rfl'

private theorem leaf1171CoversExact : CoversExact 8
    leaf1171Box leaf1171Certificate leaf1171InnerLog leaf1171Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi113RoundedFacts
    innerPair408RoundedFacts leaf1171RoundedFacts (by rfl)

private theorem leaf1171FlatSound : Sound leaf1171Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1171CertificateValid
    leaf1171InnerLogValid leaf1171CoversExact leaf1171LowerChecked

private noncomputable def leaf1172Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (11/64), chiHi := (23/128) }

private noncomputable def leaf1172Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435689/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717262848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (402480929/268435456) }, upper := { exponent := 0, mantissa := (3129/2048) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi113LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435756543/137434525696) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf1172InnerLog : WideLogData :=
  innerPair408Data

set_option maxRecDepth 1000000 in
private theorem leaf1172LocalValidity :
    LeafFacts leaf1172Box leaf1172Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1172Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717262848) }) = true
      norm_num [leaf1172Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1172CertificateValid :
    WideCertificateValid leaf1172Box leaf1172Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi113ValidityFacts
    leaf1172LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1172CoverageChecked :
    coverageCheck (innerAD leaf1172Box) leaf1172InnerLog = true := by
  rfl'

private theorem leaf1172InnerLogValid :
    leaf1172InnerLog.Valid 8 (innerAD leaf1172Box) :=
  wideLogDataValid_of_cachedCheck endpoint120PositiveFacts
    endpoint19PositiveFacts.valid leaf1172CoverageChecked

private noncomputable def leaf1172InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629231/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1172InputLogOnePlusV_eq :
    leaf1172InputLogOnePlusV = outerEnclosure 24
      (leaf1172Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1172RoundedFacts : LeafRoundedFacts 8
    leaf1172Certificate.logOnePlusV leaf1172InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1172InputLogOnePlusV_eq }

private noncomputable def leaf1172Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi113InputQChi innerPair408Input
    leaf1172InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1172LowerChecked :
    lowerCheck 24 leaf1172Box leaf1172Inputs = true := by
  rfl'

private theorem leaf1172CoversExact : CoversExact 8
    leaf1172Box leaf1172Certificate leaf1172InnerLog leaf1172Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi113RoundedFacts
    innerPair408RoundedFacts leaf1172RoundedFacts (by rfl)

private theorem leaf1172FlatSound : Sound leaf1172Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1172CertificateValid
    leaf1172InnerLogValid leaf1172CoversExact leaf1172LowerChecked

private noncomputable def leaf1173Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (93/32), chiLo := (23/128), chiHi := (3/16) }

private noncomputable def leaf1173Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435689/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717191168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (407068169/268435456) }, upper := { exponent := 0, mantissa := (791/512) } }, logOuter := sk111LogOuterCertificate, logK := sk111LogKCertificate, logChi := chi114LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435684863/137434382336) } }, logDArg := sk111LogDArgCertificate }

private noncomputable def leaf1173InnerLog : WideLogData :=
  innerPair177Data

set_option maxRecDepth 1000000 in
private theorem leaf1173LocalValidity :
    LeafFacts leaf1173Box leaf1173Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1173Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717191168) }) = true
      norm_num [leaf1173Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1173CertificateValid :
    WideCertificateValid leaf1173Box leaf1173Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk111ValidityFacts chi114ValidityFacts
    leaf1173LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1173CoverageChecked :
    coverageCheck (innerAD leaf1173Box) leaf1173InnerLog = true := by
  rfl'

private theorem leaf1173InnerLogValid :
    leaf1173InnerLog.Valid 8 (innerAD leaf1173Box) :=
  wideLogDataValid_of_cachedCheck endpoint49PositiveFacts
    endpoint43PositiveFacts.valid leaf1173CoverageChecked

private noncomputable def leaf1173InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1173InputLogOnePlusV_eq :
    leaf1173InputLogOnePlusV = outerEnclosure 24
      (leaf1173Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1173RoundedFacts : LeafRoundedFacts 8
    leaf1173Certificate.logOnePlusV leaf1173InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1173InputLogOnePlusV_eq }

private noncomputable def leaf1173Inputs : Inputs :=
  inputsOfCaches globalInput sk111RoundedInputs
    chi114InputQChi innerPair177Input
    leaf1173InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1173LowerChecked :
    lowerCheck 24 leaf1173Box leaf1173Inputs = true := by
  rfl'

private theorem leaf1173CoversExact : CoversExact 8
    leaf1173Box leaf1173Certificate leaf1173InnerLog leaf1173Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk111RoundedFacts chi114RoundedFacts
    innerPair177RoundedFacts leaf1173RoundedFacts (by rfl)

private theorem leaf1173FlatSound : Sound leaf1173Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1173CertificateValid
    leaf1173InnerLogValid leaf1173CoversExact leaf1173LowerChecked

private noncomputable def leaf1174Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (93/32), kHi := (47/16), chiLo := (23/128), chiHi := (3/16) }

private noncomputable def leaf1174Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435691/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717166592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (408575403/268435456) }, upper := { exponent := 0, mantissa := (397/256) } }, logOuter := sk112LogOuterCertificate, logK := sk112LogKCertificate, logChi := chi114LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435660287/137434333184) } }, logDArg := sk112LogDArgCertificate }

private noncomputable def leaf1174InnerLog : WideLogData :=
  innerPair410Data

set_option maxRecDepth 1000000 in
private theorem leaf1174LocalValidity :
    LeafFacts leaf1174Box leaf1174Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1174Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717166592) }) = true
      norm_num [leaf1174Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1174CertificateValid :
    WideCertificateValid leaf1174Box leaf1174Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk112ValidityFacts chi114ValidityFacts
    leaf1174LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1174CoverageChecked :
    coverageCheck (innerAD leaf1174Box) leaf1174InnerLog = true := by
  rfl'

private theorem leaf1174InnerLogValid :
    leaf1174InnerLog.Valid 8 (innerAD leaf1174Box) :=
  wideLogDataValid_of_cachedCheck endpoint121PositiveFacts
    endpoint122PositiveFacts.valid leaf1174CoverageChecked

private noncomputable def leaf1174InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629243/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1174InputLogOnePlusV_eq :
    leaf1174InputLogOnePlusV = outerEnclosure 24
      (leaf1174Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1174RoundedFacts : LeafRoundedFacts 8
    leaf1174Certificate.logOnePlusV leaf1174InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1174InputLogOnePlusV_eq }

private noncomputable def leaf1174Inputs : Inputs :=
  inputsOfCaches globalInput sk112RoundedInputs
    chi114InputQChi innerPair410Input
    leaf1174InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1174LowerChecked :
    lowerCheck 24 leaf1174Box leaf1174Inputs = true := by
  rfl'

private theorem leaf1174CoversExact : CoversExact 8
    leaf1174Box leaf1174Certificate leaf1174InnerLog leaf1174Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk112RoundedFacts chi114RoundedFacts
    innerPair410RoundedFacts leaf1174RoundedFacts (by rfl)

private theorem leaf1174FlatSound : Sound leaf1174Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1174CertificateValid
    leaf1174InnerLogValid leaf1174CoversExact leaf1174LowerChecked

private noncomputable def leaf1175Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (11/64), chiHi := (23/128) }

private noncomputable def leaf1175Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435691/268435456) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905746432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (403922631/268435456) }, upper := { exponent := 0, mantissa := (6281/4096) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi113LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811910997/45811492864) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf1175InnerLog : WideLogData :=
  innerPair414Data

set_option maxRecDepth 1000000 in
private theorem leaf1175LocalValidity :
    LeafFacts leaf1175Box leaf1175Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1175Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905746432) }) = true
      norm_num [leaf1175Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1175CertificateValid :
    WideCertificateValid leaf1175Box leaf1175Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi113ValidityFacts
    leaf1175LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1175CoverageChecked :
    coverageCheck (innerAD leaf1175Box) leaf1175InnerLog = true := by
  rfl'

private theorem leaf1175InnerLogValid :
    leaf1175InnerLog.Valid 8 (innerAD leaf1175Box) :=
  wideLogDataValid_of_cachedCheck endpoint123PositiveFacts
    endpoint124PositiveFacts.valid leaf1175CoverageChecked

private noncomputable def leaf1175InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1175InputLogOnePlusV_eq :
    leaf1175InputLogOnePlusV = outerEnclosure 24
      (leaf1175Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1175RoundedFacts : LeafRoundedFacts 8
    leaf1175Certificate.logOnePlusV leaf1175InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1175InputLogOnePlusV_eq }

private noncomputable def leaf1175Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi113InputQChi innerPair414Input
    leaf1175InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1175LowerChecked :
    lowerCheck 24 leaf1175Box leaf1175Inputs = true := by
  rfl'

private theorem leaf1175CoversExact : CoversExact 8
    leaf1175Box leaf1175Certificate leaf1175InnerLog leaf1175Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi113RoundedFacts
    innerPair414RoundedFacts leaf1175RoundedFacts (by rfl)

private theorem leaf1175FlatSound : Sound leaf1175Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1175CertificateValid
    leaf1175InnerLogValid leaf1175CoversExact leaf1175LowerChecked

private noncomputable def leaf1176Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (11/64), chiHi := (45/256) }

private noncomputable def leaf1176Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871193/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717264896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (810761625/536870912) }, upper := { exponent := 0, mantissa := (391/256) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi133LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435758591/137434529792) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf1176InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1176LocalValidity :
    LeafFacts leaf1176Box leaf1176Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1176Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717264896) }) = true
      norm_num [leaf1176Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1176CertificateValid :
    WideCertificateValid leaf1176Box leaf1176Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi133ValidityFacts
    leaf1176LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1176CoverageChecked :
    coverageCheck (innerAD leaf1176Box) leaf1176InnerLog = true := by
  rfl'

private theorem leaf1176InnerLogValid :
    leaf1176InnerLog.Valid 8 (innerAD leaf1176Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1176CoverageChecked

private noncomputable def leaf1176InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629231/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1176InputLogOnePlusV_eq :
    leaf1176InputLogOnePlusV = outerEnclosure 24
      (leaf1176Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1176RoundedFacts : LeafRoundedFacts 8
    leaf1176Certificate.logOnePlusV leaf1176InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1176InputLogOnePlusV_eq }

private noncomputable def leaf1176Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi133InputQChi innerPair40Input
    leaf1176InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1176LowerChecked :
    lowerCheck 24 leaf1176Box leaf1176Inputs = true := by
  rfl'

private theorem leaf1176CoversExact : CoversExact 8
    leaf1176Box leaf1176Certificate leaf1176InnerLog leaf1176Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi133RoundedFacts
    innerPair40RoundedFacts leaf1176RoundedFacts (by rfl)

private theorem leaf1176FlatSound : Sound leaf1176Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1176CertificateValid
    leaf1176InnerLogValid leaf1176CoversExact leaf1176LowerChecked

private noncomputable def leaf1177Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (45/256), chiHi := (23/128) }

private noncomputable def leaf1177Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871195/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717215744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (816987163/536870912) }, upper := { exponent := 0, mantissa := (197/128) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi134LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435709439/137434431488) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf1177InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1177LocalValidity :
    LeafFacts leaf1177Box leaf1177Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1177Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717215744) }) = true
      norm_num [leaf1177Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1177CertificateValid :
    WideCertificateValid leaf1177Box leaf1177Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi134ValidityFacts
    leaf1177LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1177CoverageChecked :
    coverageCheck (innerAD leaf1177Box) leaf1177InnerLog = true := by
  rfl'

private theorem leaf1177InnerLogValid :
    leaf1177InnerLog.Valid 8 (innerAD leaf1177Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1177CoverageChecked

private noncomputable def leaf1177InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1177InputLogOnePlusV_eq :
    leaf1177InputLogOnePlusV = outerEnclosure 24
      (leaf1177Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1177RoundedFacts : LeafRoundedFacts 8
    leaf1177Certificate.logOnePlusV leaf1177InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1177InputLogOnePlusV_eq }

private noncomputable def leaf1177Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi134InputQChi innerPair40Input
    leaf1177InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1177LowerChecked :
    lowerCheck 24 leaf1177Box leaf1177Inputs = true := by
  rfl'

private theorem leaf1177CoversExact : CoversExact 8
    leaf1177Box leaf1177Certificate leaf1177InnerLog leaf1177Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi134RoundedFacts
    innerPair40RoundedFacts leaf1177RoundedFacts (by rfl)

private theorem leaf1177FlatSound : Sound leaf1177Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1177CertificateValid
    leaf1177InnerLogValid leaf1177CoversExact leaf1177LowerChecked

private noncomputable def leaf1178Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (95/32), chiLo := (23/128), chiHi := (3/16) }

private noncomputable def leaf1178Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (268435693/268435456) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68717142016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (410082637/268435456) }, upper := { exponent := 0, mantissa := (797/512) } }, logOuter := sk113LogOuterCertificate, logK := sk113LogKCertificate, logChi := chi114LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137435635711/137434284032) } }, logDArg := sk113LogDArgCertificate }

private noncomputable def leaf1178InnerLog : WideLogData :=
  innerPair400Data

set_option maxRecDepth 1000000 in
private theorem leaf1178LocalValidity :
    LeafFacts leaf1178Box leaf1178Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1178Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68717142016) }) = true
      norm_num [leaf1178Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1178CertificateValid :
    WideCertificateValid leaf1178Box leaf1178Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk113ValidityFacts chi114ValidityFacts
    leaf1178LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1178CoverageChecked :
    coverageCheck (innerAD leaf1178Box) leaf1178InnerLog = true := by
  rfl'

private theorem leaf1178InnerLogValid :
    leaf1178InnerLog.Valid 8 (innerAD leaf1178Box) :=
  wideLogDataValid_of_cachedCheck endpoint112PositiveFacts
    endpoint125PositiveFacts.valid leaf1178CoverageChecked

private noncomputable def leaf1178InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (5814623/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1178InputLogOnePlusV_eq :
    leaf1178InputLogOnePlusV = outerEnclosure 24
      (leaf1178Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1178RoundedFacts : LeafRoundedFacts 8
    leaf1178Certificate.logOnePlusV leaf1178InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1178InputLogOnePlusV_eq }

private noncomputable def leaf1178Inputs : Inputs :=
  inputsOfCaches globalInput sk113RoundedInputs
    chi114InputQChi innerPair400Input
    leaf1178InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1178LowerChecked :
    lowerCheck 24 leaf1178Box leaf1178Inputs = true := by
  rfl'

private theorem leaf1178CoversExact : CoversExact 8
    leaf1178Box leaf1178Certificate leaf1178InnerLog leaf1178Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk113RoundedFacts chi114RoundedFacts
    innerPair400RoundedFacts leaf1178RoundedFacts (by rfl)

private theorem leaf1178FlatSound : Sound leaf1178Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1178CertificateValid
    leaf1178InnerLogValid leaf1178CoversExact leaf1178LowerChecked

private noncomputable def leaf1179Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (23/128), chiHi := (47/256) }

private noncomputable def leaf1179Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871197/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68717166592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (823212701/536870912) }, upper := { exponent := 0, mantissa := (397/256) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi135LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137435660287/137434333184) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf1179InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1179LocalValidity :
    LeafFacts leaf1179Box leaf1179Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1179Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68717166592) }) = true
      norm_num [leaf1179Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1179CertificateValid :
    WideCertificateValid leaf1179Box leaf1179Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi135ValidityFacts
    leaf1179LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1179CoverageChecked :
    coverageCheck (innerAD leaf1179Box) leaf1179InnerLog = true := by
  rfl'

private theorem leaf1179InnerLogValid :
    leaf1179InnerLog.Valid 8 (innerAD leaf1179Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1179CoverageChecked

private noncomputable def leaf1179InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629243/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1179InputLogOnePlusV_eq :
    leaf1179InputLogOnePlusV = outerEnclosure 24
      (leaf1179Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1179RoundedFacts : LeafRoundedFacts 8
    leaf1179Certificate.logOnePlusV leaf1179InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1179InputLogOnePlusV_eq }

private noncomputable def leaf1179Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi135InputQChi innerPair40Input
    leaf1179InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1179LowerChecked :
    lowerCheck 24 leaf1179Box leaf1179Inputs = true := by
  rfl'

private theorem leaf1179CoversExact : CoversExact 8
    leaf1179Box leaf1179Certificate leaf1179InnerLog leaf1179Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi135RoundedFacts
    innerPair40RoundedFacts leaf1179RoundedFacts (by rfl)

private theorem leaf1179FlatSound : Sound leaf1179Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1179CertificateValid
    leaf1179InnerLogValid leaf1179CoversExact leaf1179LowerChecked

private noncomputable def leaf1180Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (47/256), chiHi := (3/16) }

private noncomputable def leaf1180Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871199/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743423488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (829438239/536870912) }, upper := { exponent := 0, mantissa := (25/16) } }, logOuter := sk114LogOuterCertificate, logK := sk114LogKCertificate, logChi := chi136LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27487122227/27486846976) } }, logDArg := sk114LogDArgCertificate }

private noncomputable def leaf1180InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf1180LocalValidity :
    LeafFacts leaf1180Box leaf1180Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1180Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743423488) }) = true
      norm_num [leaf1180Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1180CertificateValid :
    WideCertificateValid leaf1180Box leaf1180Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk114ValidityFacts chi136ValidityFacts
    leaf1180LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1180CoverageChecked :
    coverageCheck (innerAD leaf1180Box) leaf1180InnerLog = true := by
  rfl'

private theorem leaf1180InnerLogValid :
    leaf1180InnerLog.Valid 8 (innerAD leaf1180Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf1180CoverageChecked

private noncomputable def leaf1180InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1180InputLogOnePlusV_eq :
    leaf1180InputLogOnePlusV = outerEnclosure 24
      (leaf1180Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1180RoundedFacts : LeafRoundedFacts 8
    leaf1180Certificate.logOnePlusV leaf1180InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1180InputLogOnePlusV_eq }

private noncomputable def leaf1180Inputs : Inputs :=
  inputsOfCaches globalInput sk114RoundedInputs
    chi136InputQChi innerPair40Input
    leaf1180InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1180LowerChecked :
    lowerCheck 24 leaf1180Box leaf1180Inputs = true := by
  rfl'

private theorem leaf1180CoversExact : CoversExact 8
    leaf1180Box leaf1180Certificate leaf1180InnerLog leaf1180Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk114RoundedFacts chi136RoundedFacts
    innerPair40RoundedFacts leaf1180RoundedFacts (by rfl)

private theorem leaf1180FlatSound : Sound leaf1180Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1180CertificateValid
    leaf1180InnerLogValid leaf1180CoversExact leaf1180LowerChecked

private noncomputable def component27Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component27Node0_sound : Sound component27Node0Box :=
  sound_of_literal_split component27Node0Box leaf1147Box leaf1148Box
    .k (89/32) (by rfl) (by rfl)
    leaf1147FlatSound leaf1148FlatSound

private noncomputable def component27Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component27Node1_sound : Sound component27Node1Box :=
  sound_of_literal_split component27Node1Box leaf1149Box leaf1150Box
    .k (89/32) (by rfl) (by rfl)
    leaf1149FlatSound leaf1150FlatSound

private noncomputable def component27Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component27Node2_sound : Sound component27Node2Box :=
  sound_of_literal_split component27Node2Box component27Node0Box component27Node1Box
    .chi (21/128) (by rfl) (by rfl)
    component27Node0_sound component27Node1_sound

private noncomputable def component27Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component27Node3_sound : Sound component27Node3Box :=
  sound_of_literal_split component27Node3Box leaf1151Box leaf1152Box
    .k (91/32) (by rfl) (by rfl)
    leaf1151FlatSound leaf1152FlatSound

private noncomputable def component27Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component27Node4_sound : Sound component27Node4Box :=
  sound_of_literal_split component27Node4Box leaf1153Box leaf1154Box
    .k (91/32) (by rfl) (by rfl)
    leaf1153FlatSound leaf1154FlatSound

private noncomputable def component27Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component27Node5_sound : Sound component27Node5Box :=
  sound_of_literal_split component27Node5Box component27Node3Box component27Node4Box
    .chi (21/128) (by rfl) (by rfl)
    component27Node3_sound component27Node4_sound

private noncomputable def component27Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component27Node6_sound : Sound component27Node6Box :=
  sound_of_literal_split component27Node6Box component27Node2Box component27Node5Box
    .k (45/16) (by rfl) (by rfl)
    component27Node2_sound component27Node5_sound

private noncomputable def component27Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component27Node7_sound : Sound component27Node7Box :=
  sound_of_literal_split component27Node7Box leaf1155Box leaf1156Box
    .k (89/32) (by rfl) (by rfl)
    leaf1155FlatSound leaf1156FlatSound

private noncomputable def component27Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component27Node8_sound : Sound component27Node8Box :=
  sound_of_literal_split component27Node8Box leaf1157Box leaf1158Box
    .k (89/32) (by rfl) (by rfl)
    leaf1157FlatSound leaf1158FlatSound

private noncomputable def component27Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (45/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component27Node9_sound : Sound component27Node9Box :=
  sound_of_literal_split component27Node9Box component27Node7Box component27Node8Box
    .chi (23/128) (by rfl) (by rfl)
    component27Node7_sound component27Node8_sound

private noncomputable def component27Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component27Node10_sound : Sound component27Node10Box :=
  sound_of_literal_split component27Node10Box leaf1159Box leaf1160Box
    .k (91/32) (by rfl) (by rfl)
    leaf1159FlatSound leaf1160FlatSound

private noncomputable def component27Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component27Node11_sound : Sound component27Node11Box :=
  sound_of_literal_split component27Node11Box leaf1161Box leaf1162Box
    .k (91/32) (by rfl) (by rfl)
    leaf1161FlatSound leaf1162FlatSound

private noncomputable def component27Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (45/16), kHi := (23/8), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component27Node12_sound : Sound component27Node12Box :=
  sound_of_literal_split component27Node12Box component27Node10Box component27Node11Box
    .chi (23/128) (by rfl) (by rfl)
    component27Node10_sound component27Node11_sound

private noncomputable def component27Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component27Node13_sound : Sound component27Node13Box :=
  sound_of_literal_split component27Node13Box component27Node9Box component27Node12Box
    .k (45/16) (by rfl) (by rfl)
    component27Node9_sound component27Node12_sound

private noncomputable def component27Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (23/8), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component27Node14_sound : Sound component27Node14Box :=
  sound_of_literal_split component27Node14Box component27Node6Box component27Node13Box
    .chi (11/64) (by rfl) (by rfl)
    component27Node6_sound component27Node13_sound

private noncomputable def component27Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component27Node15_sound : Sound component27Node15Box :=
  sound_of_literal_split component27Node15Box leaf1163Box leaf1164Box
    .k (93/32) (by rfl) (by rfl)
    leaf1163FlatSound leaf1164FlatSound

private noncomputable def component27Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component27Node16_sound : Sound component27Node16Box :=
  sound_of_literal_split component27Node16Box leaf1165Box leaf1166Box
    .k (93/32) (by rfl) (by rfl)
    leaf1165FlatSound leaf1166FlatSound

private noncomputable def component27Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component27Node17_sound : Sound component27Node17Box :=
  sound_of_literal_split component27Node17Box component27Node15Box component27Node16Box
    .chi (21/128) (by rfl) (by rfl)
    component27Node15_sound component27Node16_sound

private noncomputable def component27Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (5/32), chiHi := (21/128) }

set_option maxRecDepth 1000000 in
private theorem component27Node18_sound : Sound component27Node18Box :=
  sound_of_literal_split component27Node18Box leaf1167Box leaf1168Box
    .k (95/32) (by rfl) (by rfl)
    leaf1167FlatSound leaf1168FlatSound

private noncomputable def component27Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (21/128), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component27Node19_sound : Sound component27Node19Box :=
  sound_of_literal_split component27Node19Box leaf1169Box leaf1170Box
    .k (95/32) (by rfl) (by rfl)
    leaf1169FlatSound leaf1170FlatSound

private noncomputable def component27Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component27Node20_sound : Sound component27Node20Box :=
  sound_of_literal_split component27Node20Box component27Node18Box component27Node19Box
    .chi (21/128) (by rfl) (by rfl)
    component27Node18_sound component27Node19_sound

private noncomputable def component27Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (5/32), chiHi := (11/64) }

set_option maxRecDepth 1000000 in
private theorem component27Node21_sound : Sound component27Node21Box :=
  sound_of_literal_split component27Node21Box component27Node17Box component27Node20Box
    .k (47/16) (by rfl) (by rfl)
    component27Node17_sound component27Node20_sound

private noncomputable def component27Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component27Node22_sound : Sound component27Node22Box :=
  sound_of_literal_split component27Node22Box leaf1171Box leaf1172Box
    .k (93/32) (by rfl) (by rfl)
    leaf1171FlatSound leaf1172FlatSound

private noncomputable def component27Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component27Node23_sound : Sound component27Node23Box :=
  sound_of_literal_split component27Node23Box leaf1173Box leaf1174Box
    .k (93/32) (by rfl) (by rfl)
    leaf1173FlatSound leaf1174FlatSound

private noncomputable def component27Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (47/16), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component27Node24_sound : Sound component27Node24Box :=
  sound_of_literal_split component27Node24Box component27Node22Box component27Node23Box
    .chi (23/128) (by rfl) (by rfl)
    component27Node22_sound component27Node23_sound

private noncomputable def component27Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component27Node25_sound : Sound component27Node25Box :=
  sound_of_literal_split component27Node25Box leaf1176Box leaf1177Box
    .chi (45/256) (by rfl) (by rfl)
    leaf1176FlatSound leaf1177FlatSound

private noncomputable def component27Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (11/64), chiHi := (23/128) }

set_option maxRecDepth 1000000 in
private theorem component27Node26_sound : Sound component27Node26Box :=
  sound_of_literal_split component27Node26Box leaf1175Box component27Node25Box
    .k (95/32) (by rfl) (by rfl)
    leaf1175FlatSound component27Node25_sound

private noncomputable def component27Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (95/32), kHi := (3), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component27Node27_sound : Sound component27Node27Box :=
  sound_of_literal_split component27Node27Box leaf1179Box leaf1180Box
    .chi (47/256) (by rfl) (by rfl)
    leaf1179FlatSound leaf1180FlatSound

private noncomputable def component27Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (23/128), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component27Node28_sound : Sound component27Node28Box :=
  sound_of_literal_split component27Node28Box leaf1178Box component27Node27Box
    .k (95/32) (by rfl) (by rfl)
    leaf1178FlatSound component27Node27_sound

private noncomputable def component27Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (47/16), kHi := (3), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component27Node29_sound : Sound component27Node29Box :=
  sound_of_literal_split component27Node29Box component27Node26Box component27Node28Box
    .chi (23/128) (by rfl) (by rfl)
    component27Node26_sound component27Node28_sound

private noncomputable def component27Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (11/64), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component27Node30_sound : Sound component27Node30Box :=
  sound_of_literal_split component27Node30Box component27Node24Box component27Node29Box
    .k (47/16) (by rfl) (by rfl)
    component27Node24_sound component27Node29_sound

private noncomputable def component27Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/8), kHi := (3), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component27Node31_sound : Sound component27Node31Box :=
  sound_of_literal_split component27Node31Box component27Node21Box component27Node30Box
    .chi (11/64) (by rfl) (by rfl)
    component27Node21_sound component27Node30_sound

noncomputable def component27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/4), kHi := (3), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
theorem component27_sound : Sound component27Box :=
  sound_of_literal_split component27Box component27Node14Box component27Node31Box
    .k (23/8) (by rfl) (by rfl)
    component27Node14_sound component27Node31_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
