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
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
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

private noncomputable def leaf6837Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6837Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217987/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588869376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (398409727/268435456) }, upper := { exponent := 1, mantissa := (6209/4096) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178296063/17177738752) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf6837InnerLog : WideLogData :=
  innerPair850Data

set_option maxRecDepth 1000000 in
private theorem leaf6837LocalValidity :
    LeafFacts leaf6837Box leaf6837Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6837Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588869376) }) = true
      norm_num [leaf6837Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6837CertificateValid :
    WideCertificateValid leaf6837Box leaf6837Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi335ValidityFacts
    leaf6837LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6837CoverageChecked :
    coverageCheck (innerAD leaf6837Box) leaf6837InnerLog = true := by
  rfl'

private theorem leaf6837InnerLogValid :
    leaf6837InnerLog.Valid 8 (innerAD leaf6837Box) :=
  wideLogDataValid_of_cachedCheck endpoint545PositiveFacts
    endpoint546PositiveFacts.valid leaf6837CoverageChecked

private noncomputable def leaf6837InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629625/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6837InputLogOnePlusV_eq :
    leaf6837InputLogOnePlusV = outerEnclosure 24
      (leaf6837Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6837RoundedFacts : LeafRoundedFacts 8
    leaf6837Certificate.logOnePlusV leaf6837InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6837InputLogOnePlusV_eq }

private noncomputable def leaf6837Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi335InputQChi innerPair850Input
    leaf6837InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6837LowerChecked :
    lowerCheck 24 leaf6837Box leaf6837Inputs = true := by
  rfl'

private theorem leaf6837CoversExact : CoversExact 8
    leaf6837Box leaf6837Certificate leaf6837InnerLog leaf6837Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi335RoundedFacts
    innerPair850RoundedFacts leaf6837RoundedFacts (by rfl)

private theorem leaf6837FlatSound : Sound leaf6837Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6837CertificateValid
    leaf6837InnerLogValid leaf6837CoversExact leaf6837LowerChecked

private noncomputable def leaf6838Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6838Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217989/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588854784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (402079517/268435456) }, upper := { exponent := 1, mantissa := (3133/2048) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178281471/17177709568) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf6838InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6838LocalValidity :
    LeafFacts leaf6838Box leaf6838Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6838Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588854784) }) = true
      norm_num [leaf6838Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6838CertificateValid :
    WideCertificateValid leaf6838Box leaf6838Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi336ValidityFacts
    leaf6838LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6838CoverageChecked :
    coverageCheck (innerAD leaf6838Box) leaf6838InnerLog = true := by
  rfl'

private theorem leaf6838InnerLogValid :
    leaf6838InnerLog.Valid 8 (innerAD leaf6838Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6838CoverageChecked

private noncomputable def leaf6838InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629639/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6838InputLogOnePlusV_eq :
    leaf6838InputLogOnePlusV = outerEnclosure 24
      (leaf6838Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6838RoundedFacts : LeafRoundedFacts 8
    leaf6838Certificate.logOnePlusV leaf6838InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6838InputLogOnePlusV_eq }

private noncomputable def leaf6838Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi336InputQChi innerPair376Input
    leaf6838InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6838LowerChecked :
    lowerCheck 24 leaf6838Box leaf6838Inputs = true := by
  rfl'

private theorem leaf6838CoversExact : CoversExact 8
    leaf6838Box leaf6838Certificate leaf6838InnerLog leaf6838Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi336RoundedFacts
    innerPair376RoundedFacts leaf6838RoundedFacts (by rfl)

private theorem leaf6838FlatSound : Sound leaf6838Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6838CertificateValid
    leaf6838InnerLogValid leaf6838CoversExact leaf6838LowerChecked

private noncomputable def leaf6839Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6839Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217989/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588850688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (403128029/268435456) }, upper := { exponent := 1, mantissa := (3141/2048) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178277375/17177701376) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf6839InnerLog : WideLogData :=
  innerPair387Data

set_option maxRecDepth 1000000 in
private theorem leaf6839LocalValidity :
    LeafFacts leaf6839Box leaf6839Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6839Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588850688) }) = true
      norm_num [leaf6839Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6839CertificateValid :
    WideCertificateValid leaf6839Box leaf6839Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi335ValidityFacts
    leaf6839LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6839CoverageChecked :
    coverageCheck (innerAD leaf6839Box) leaf6839InnerLog = true := by
  rfl'

private theorem leaf6839InnerLogValid :
    leaf6839InnerLog.Valid 8 (innerAD leaf6839Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint547PositiveFacts.valid leaf6839CoverageChecked

private noncomputable def leaf6839InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629643/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6839InputLogOnePlusV_eq :
    leaf6839InputLogOnePlusV = outerEnclosure 24
      (leaf6839Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6839RoundedFacts : LeafRoundedFacts 8
    leaf6839Certificate.logOnePlusV leaf6839InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6839InputLogOnePlusV_eq }

private noncomputable def leaf6839Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi335InputQChi innerPair387Input
    leaf6839InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6839LowerChecked :
    lowerCheck 24 leaf6839Box leaf6839Inputs = true := by
  rfl'

private theorem leaf6839CoversExact : CoversExact 8
    leaf6839Box leaf6839Certificate leaf6839InnerLog leaf6839Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi335RoundedFacts
    innerPair387RoundedFacts leaf6839RoundedFacts (by rfl)

private theorem leaf6839FlatSound : Sound leaf6839Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6839CertificateValid
    leaf6839InnerLogValid leaf6839CoversExact leaf6839LowerChecked

private noncomputable def leaf6840Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6840Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217991/134217728) }, vSqrt := { lower := (8191/8192), upper := (2863142229/2862945280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (406863351/268435456) }, upper := { exponent := 1, mantissa := (1585/1024) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5726087509/5725890560) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf6840InnerLog : WideLogData :=
  innerPair831Data

set_option maxRecDepth 1000000 in
private theorem leaf6840LocalValidity :
    LeafFacts leaf6840Box leaf6840Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6840Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2863142229/2862945280) }) = true
      norm_num [leaf6840Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6840CertificateValid :
    WideCertificateValid leaf6840Box leaf6840Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi336ValidityFacts
    leaf6840LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6840CoverageChecked :
    coverageCheck (innerAD leaf6840Box) leaf6840InnerLog = true := by
  rfl'

private theorem leaf6840InnerLogValid :
    leaf6840InnerLog.Valid 8 (innerAD leaf6840Box) :=
  wideLogDataValid_of_cachedCheck endpoint526PositiveFacts
    endpoint548PositiveFacts.valid leaf6840CoverageChecked

private noncomputable def leaf6840InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814829/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6840InputLogOnePlusV_eq :
    leaf6840InputLogOnePlusV = outerEnclosure 24
      (leaf6840Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6840RoundedFacts : LeafRoundedFacts 8
    leaf6840Certificate.logOnePlusV leaf6840InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6840InputLogOnePlusV_eq }

private noncomputable def leaf6840Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi336InputQChi innerPair831Input
    leaf6840InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6840LowerChecked :
    lowerCheck 24 leaf6840Box leaf6840Inputs = true := by
  rfl'

private theorem leaf6840CoversExact : CoversExact 8
    leaf6840Box leaf6840Certificate leaf6840InnerLog leaf6840Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi336RoundedFacts
    innerPair831RoundedFacts leaf6840RoundedFacts (by rfl)

private theorem leaf6840FlatSound : Sound leaf6840Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6840CertificateValid
    leaf6840InnerLogValid leaf6840CoversExact leaf6840LowerChecked

private noncomputable def leaf6841Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6841Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217991/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588840192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (405749307/268435456) }, upper := { exponent := 1, mantissa := (6323/4096) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178266879/17177680384) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf6841InnerLog : WideLogData :=
  innerPair783Data

set_option maxRecDepth 1000000 in
private theorem leaf6841LocalValidity :
    LeafFacts leaf6841Box leaf6841Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6841Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588840192) }) = true
      norm_num [leaf6841Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6841CertificateValid :
    WideCertificateValid leaf6841Box leaf6841Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi337ValidityFacts
    leaf6841LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6841CoverageChecked :
    coverageCheck (innerAD leaf6841Box) leaf6841InnerLog = true := by
  rfl'

private theorem leaf6841InnerLogValid :
    leaf6841InnerLog.Valid 8 (innerAD leaf6841Box) :=
  wideLogDataValid_of_cachedCheck endpoint491PositiveFacts
    endpoint530PositiveFacts.valid leaf6841CoverageChecked

private noncomputable def leaf6841InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814827/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6841InputLogOnePlusV_eq :
    leaf6841InputLogOnePlusV = outerEnclosure 24
      (leaf6841Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6841RoundedFacts : LeafRoundedFacts 8
    leaf6841Certificate.logOnePlusV leaf6841InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6841InputLogOnePlusV_eq }

private noncomputable def leaf6841Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi337InputQChi innerPair783Input
    leaf6841InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6841LowerChecked :
    lowerCheck 24 leaf6841Box leaf6841Inputs = true := by
  rfl'

private theorem leaf6841CoversExact : CoversExact 8
    leaf6841Box leaf6841Certificate leaf6841InnerLog leaf6841Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi337RoundedFacts
    innerPair783RoundedFacts leaf6841RoundedFacts (by rfl)

private theorem leaf6841FlatSound : Sound leaf6841Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6841CertificateValid
    leaf6841InnerLogValid leaf6841CoversExact leaf6841LowerChecked

private noncomputable def leaf6842Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6842Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217993/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588825600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (409419097/268435456) }, upper := { exponent := 1, mantissa := (1595/1024) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178252287/17177651200) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf6842InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6842LocalValidity :
    LeafFacts leaf6842Box leaf6842Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6842Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588825600) }) = true
      norm_num [leaf6842Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6842CertificateValid :
    WideCertificateValid leaf6842Box leaf6842Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi338ValidityFacts
    leaf6842LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6842CoverageChecked :
    coverageCheck (innerAD leaf6842Box) leaf6842InnerLog = true := by
  rfl'

private theorem leaf6842InnerLogValid :
    leaf6842InnerLog.Valid 8 (innerAD leaf6842Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6842CoverageChecked

private noncomputable def leaf6842InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907417/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6842InputLogOnePlusV_eq :
    leaf6842InputLogOnePlusV = outerEnclosure 24
      (leaf6842Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6842RoundedFacts : LeafRoundedFacts 8
    leaf6842Certificate.logOnePlusV leaf6842InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6842InputLogOnePlusV_eq }

private noncomputable def leaf6842Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi338InputQChi innerPair382Input
    leaf6842InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6842LowerChecked :
    lowerCheck 24 leaf6842Box leaf6842Inputs = true := by
  rfl'

private theorem leaf6842CoversExact : CoversExact 8
    leaf6842Box leaf6842Certificate leaf6842InnerLog leaf6842Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi338RoundedFacts
    innerPair382RoundedFacts leaf6842RoundedFacts (by rfl)

private theorem leaf6842FlatSound : Sound leaf6842Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6842CertificateValid
    leaf6842InnerLogValid leaf6842CoversExact leaf6842LowerChecked

private noncomputable def leaf6843Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6843Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217993/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588820992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (410598673/268435456) }, upper := { exponent := 1, mantissa := (3199/2048) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178247679/17177641984) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf6843InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6843LocalValidity :
    LeafFacts leaf6843Box leaf6843Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6843Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588820992) }) = true
      norm_num [leaf6843Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6843CertificateValid :
    WideCertificateValid leaf6843Box leaf6843Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi337ValidityFacts
    leaf6843LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6843CoverageChecked :
    coverageCheck (innerAD leaf6843Box) leaf6843InnerLog = true := by
  rfl'

private theorem leaf6843InnerLogValid :
    leaf6843InnerLog.Valid 8 (innerAD leaf6843Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6843CoverageChecked

private noncomputable def leaf6843InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453709/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6843InputLogOnePlusV_eq :
    leaf6843InputLogOnePlusV = outerEnclosure 24
      (leaf6843Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6843RoundedFacts : LeafRoundedFacts 8
    leaf6843Certificate.logOnePlusV leaf6843InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6843InputLogOnePlusV_eq }

private noncomputable def leaf6843Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi337InputQChi innerPair382Input
    leaf6843InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6843LowerChecked :
    lowerCheck 24 leaf6843Box leaf6843Inputs = true := by
  rfl'

private theorem leaf6843CoversExact : CoversExact 8
    leaf6843Box leaf6843Certificate leaf6843InnerLog leaf6843Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi337RoundedFacts
    innerPair382RoundedFacts leaf6843RoundedFacts (by rfl)

private theorem leaf6843FlatSound : Sound leaf6843Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6843CertificateValid
    leaf6843InnerLogValid leaf6843CoversExact leaf6843LowerChecked

private noncomputable def leaf6844Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6844Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217995/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588806144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (414333995/268435456) }, upper := { exponent := 1, mantissa := (807/512) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178232831/17177612288) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf6844InnerLog : WideLogData :=
  innerPair832Data

set_option maxRecDepth 1000000 in
private theorem leaf6844LocalValidity :
    LeafFacts leaf6844Box leaf6844Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6844Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588806144) }) = true
      norm_num [leaf6844Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6844CertificateValid :
    WideCertificateValid leaf6844Box leaf6844Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi338ValidityFacts
    leaf6844LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6844CoverageChecked :
    coverageCheck (innerAD leaf6844Box) leaf6844InnerLog = true := by
  rfl'

private theorem leaf6844InnerLogValid :
    leaf6844InnerLog.Valid 8 (innerAD leaf6844Box) :=
  wideLogDataValid_of_cachedCheck endpoint527PositiveFacts
    endpoint492PositiveFacts.valid leaf6844CoverageChecked

private noncomputable def leaf6844InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629687/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6844InputLogOnePlusV_eq :
    leaf6844InputLogOnePlusV = outerEnclosure 24
      (leaf6844Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6844RoundedFacts : LeafRoundedFacts 8
    leaf6844Certificate.logOnePlusV leaf6844InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6844InputLogOnePlusV_eq }

private noncomputable def leaf6844Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi338InputQChi innerPair832Input
    leaf6844InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6844LowerChecked :
    lowerCheck 24 leaf6844Box leaf6844Inputs = true := by
  rfl'

private theorem leaf6844CoversExact : CoversExact 8
    leaf6844Box leaf6844Certificate leaf6844InnerLog leaf6844Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi338RoundedFacts
    innerPair832RoundedFacts leaf6844RoundedFacts (by rfl)

private theorem leaf6844FlatSound : Sound leaf6844Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6844CertificateValid
    leaf6844InnerLogValid leaf6844CoversExact leaf6844LowerChecked

private noncomputable def leaf6845Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6845Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217991/134217728) }, vSqrt := { lower := (8191/8192), upper := (2863142229/2862944000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (407846331/268435456) }, upper := { exponent := 1, mantissa := (6355/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5726086229/5725888000) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf6845InnerLog : WideLogData :=
  innerPair851Data

set_option maxRecDepth 1000000 in
private theorem leaf6845LocalValidity :
    LeafFacts leaf6845Box leaf6845Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6845Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2863142229/2862944000) }) = true
      norm_num [leaf6845Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6845CertificateValid :
    WideCertificateValid leaf6845Box leaf6845Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi335ValidityFacts
    leaf6845LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6845CoverageChecked :
    coverageCheck (innerAD leaf6845Box) leaf6845InnerLog = true := by
  rfl'

private theorem leaf6845InnerLogValid :
    leaf6845InnerLog.Valid 8 (innerAD leaf6845Box) :=
  wideLogDataValid_of_cachedCheck endpoint549PositiveFacts
    endpoint550PositiveFacts.valid leaf6845CoverageChecked

private noncomputable def leaf6845InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814831/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6845InputLogOnePlusV_eq :
    leaf6845InputLogOnePlusV = outerEnclosure 24
      (leaf6845Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6845RoundedFacts : LeafRoundedFacts 8
    leaf6845Certificate.logOnePlusV leaf6845InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6845InputLogOnePlusV_eq }

private noncomputable def leaf6845Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi335InputQChi innerPair851Input
    leaf6845InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6845LowerChecked :
    lowerCheck 24 leaf6845Box leaf6845Inputs = true := by
  rfl'

private theorem leaf6845CoversExact : CoversExact 8
    leaf6845Box leaf6845Certificate leaf6845InnerLog leaf6845Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi335RoundedFacts
    innerPair851RoundedFacts leaf6845RoundedFacts (by rfl)

private theorem leaf6845FlatSound : Sound leaf6845Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6845CertificateValid
    leaf6845InnerLogValid leaf6845CoversExact leaf6845LowerChecked

private noncomputable def leaf6846Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6846Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217993/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588816896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (411647185/268435456) }, upper := { exponent := 1, mantissa := (3207/2048) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178243583/17177633792) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf6846InnerLog : WideLogData :=
  innerPair852Data

set_option maxRecDepth 1000000 in
private theorem leaf6846LocalValidity :
    LeafFacts leaf6846Box leaf6846Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6846Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588816896) }) = true
      norm_num [leaf6846Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6846CertificateValid :
    WideCertificateValid leaf6846Box leaf6846Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi336ValidityFacts
    leaf6846LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6846CoverageChecked :
    coverageCheck (innerAD leaf6846Box) leaf6846InnerLog = true := by
  rfl'

private theorem leaf6846InnerLogValid :
    leaf6846InnerLog.Valid 8 (innerAD leaf6846Box) :=
  wideLogDataValid_of_cachedCheck endpoint551PositiveFacts
    endpoint552PositiveFacts.valid leaf6846CoverageChecked

private noncomputable def leaf6846InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907419/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6846InputLogOnePlusV_eq :
    leaf6846InputLogOnePlusV = outerEnclosure 24
      (leaf6846Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6846RoundedFacts : LeafRoundedFacts 8
    leaf6846Certificate.logOnePlusV leaf6846InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6846InputLogOnePlusV_eq }

private noncomputable def leaf6846Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi336InputQChi innerPair852Input
    leaf6846InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6846LowerChecked :
    lowerCheck 24 leaf6846Box leaf6846Inputs = true := by
  rfl'

private theorem leaf6846CoversExact : CoversExact 8
    leaf6846Box leaf6846Certificate leaf6846InnerLog leaf6846Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi336RoundedFacts
    innerPair852RoundedFacts leaf6846RoundedFacts (by rfl)

private theorem leaf6846FlatSound : Sound leaf6846Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6846CertificateValid
    leaf6846InnerLogValid leaf6846CoversExact leaf6846LowerChecked

private noncomputable def leaf6847Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6847Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435839/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177645312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (825162179/536870912) }, upper := { exponent := 1, mantissa := (12783/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356482303/34355290624) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf6847InnerLog : WideLogData :=
  innerPair743Data

set_option maxRecDepth 1000000 in
private theorem leaf6847LocalValidity :
    LeafFacts leaf6847Box leaf6847Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6847Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177645312) }) = true
      norm_num [leaf6847Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6847CertificateValid :
    WideCertificateValid leaf6847Box leaf6847Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi335ValidityFacts
    leaf6847LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6847CoverageChecked :
    coverageCheck (innerAD leaf6847Box) leaf6847InnerLog = true := by
  rfl'

private theorem leaf6847InnerLogValid :
    leaf6847InnerLog.Valid 8 (innerAD leaf6847Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint483PositiveFacts.valid leaf6847CoverageChecked

private noncomputable def leaf6847InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629663/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6847InputLogOnePlusV_eq :
    leaf6847InputLogOnePlusV = outerEnclosure 24
      (leaf6847Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6847RoundedFacts : LeafRoundedFacts 8
    leaf6847Certificate.logOnePlusV leaf6847InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6847InputLogOnePlusV_eq }

private noncomputable def leaf6847Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi335InputQChi innerPair743Input
    leaf6847InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6847LowerChecked :
    lowerCheck 24 leaf6847Box leaf6847Inputs = true := by
  rfl'

private theorem leaf6847CoversExact : CoversExact 8
    leaf6847Box leaf6847Certificate leaf6847InnerLog leaf6847Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi335RoundedFacts
    innerPair743RoundedFacts leaf6847RoundedFacts (by rfl)

private theorem leaf6847FlatSound : Sound leaf6847Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6847CertificateValid
    leaf6847InnerLogValid leaf6847CoversExact leaf6847LowerChecked

private noncomputable def leaf6848Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (9/16), chiHi := (73/128) }

private noncomputable def leaf6848Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (268435841/268435456) }, vSqrt := { lower := (8191/8192), upper := (17178836991/17177626624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (829880481/536870912) }, upper := { exponent := 1, mantissa := (1607/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi335LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34356463615/34355253248) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf6848InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6848LocalValidity :
    LeafFacts leaf6848Box leaf6848Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6848Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178836991/17177626624) }) = true
      norm_num [leaf6848Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6848CertificateValid :
    WideCertificateValid leaf6848Box leaf6848Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi335ValidityFacts
    leaf6848LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6848CoverageChecked :
    coverageCheck (innerAD leaf6848Box) leaf6848InnerLog = true := by
  rfl'

private theorem leaf6848InnerLogValid :
    leaf6848InnerLog.Valid 8 (innerAD leaf6848Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6848CoverageChecked

private noncomputable def leaf6848InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453709/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6848InputLogOnePlusV_eq :
    leaf6848InputLogOnePlusV = outerEnclosure 24
      (leaf6848Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6848RoundedFacts : LeafRoundedFacts 8
    leaf6848Certificate.logOnePlusV leaf6848InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6848InputLogOnePlusV_eq }

private noncomputable def leaf6848Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi335InputQChi innerPair744Input
    leaf6848InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6848LowerChecked :
    lowerCheck 24 leaf6848Box leaf6848Inputs = true := by
  rfl'

private theorem leaf6848CoversExact : CoversExact 8
    leaf6848Box leaf6848Certificate leaf6848InnerLog leaf6848Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi335RoundedFacts
    innerPair744RoundedFacts leaf6848RoundedFacts (by rfl)

private theorem leaf6848FlatSound : Sound leaf6848Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6848CertificateValid
    leaf6848InnerLogValid leaf6848CoversExact leaf6848LowerChecked

private noncomputable def leaf6849Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (73/128), chiHi := (37/64) }

private noncomputable def leaf6849Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217995/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588797952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (416431019/268435456) }, upper := { exponent := 1, mantissa := (811/512) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi336LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178224639/17177595904) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf6849InnerLog : WideLogData :=
  innerPair836Data

set_option maxRecDepth 1000000 in
private theorem leaf6849LocalValidity :
    LeafFacts leaf6849Box leaf6849Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6849Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588797952) }) = true
      norm_num [leaf6849Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6849CertificateValid :
    WideCertificateValid leaf6849Box leaf6849Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi336ValidityFacts
    leaf6849LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6849CoverageChecked :
    coverageCheck (innerAD leaf6849Box) leaf6849InnerLog = true := by
  rfl'

private theorem leaf6849InnerLogValid :
    leaf6849InnerLog.Valid 8 (innerAD leaf6849Box) :=
  wideLogDataValid_of_cachedCheck endpoint530PositiveFacts
    endpoint532PositiveFacts.valid leaf6849CoverageChecked

private noncomputable def leaf6849InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629695/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6849InputLogOnePlusV_eq :
    leaf6849InputLogOnePlusV = outerEnclosure 24
      (leaf6849Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6849RoundedFacts : LeafRoundedFacts 8
    leaf6849Certificate.logOnePlusV leaf6849InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6849InputLogOnePlusV_eq }

private noncomputable def leaf6849Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi336InputQChi innerPair836Input
    leaf6849InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6849LowerChecked :
    lowerCheck 24 leaf6849Box leaf6849Inputs = true := by
  rfl'

private theorem leaf6849CoversExact : CoversExact 8
    leaf6849Box leaf6849Certificate leaf6849InnerLog leaf6849Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi336RoundedFacts
    innerPair836RoundedFacts leaf6849RoundedFacts (by rfl)

private theorem leaf6849FlatSound : Sound leaf6849Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6849CertificateValid
    leaf6849InnerLogValid leaf6849CoversExact leaf6849LowerChecked

private noncomputable def leaf6850Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6850Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217995/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588801792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (415448039/268435456) }, upper := { exponent := 1, mantissa := (6473/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178228479/17177603584) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf6850InnerLog : WideLogData :=
  innerPair836Data

set_option maxRecDepth 1000000 in
private theorem leaf6850LocalValidity :
    LeafFacts leaf6850Box leaf6850Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6850Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588801792) }) = true
      norm_num [leaf6850Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6850CertificateValid :
    WideCertificateValid leaf6850Box leaf6850Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi337ValidityFacts
    leaf6850LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6850CoverageChecked :
    coverageCheck (innerAD leaf6850Box) leaf6850InnerLog = true := by
  rfl'

private theorem leaf6850InnerLogValid :
    leaf6850InnerLog.Valid 8 (innerAD leaf6850Box) :=
  wideLogDataValid_of_cachedCheck endpoint530PositiveFacts
    endpoint532PositiveFacts.valid leaf6850CoverageChecked

private noncomputable def leaf6850InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629691/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6850InputLogOnePlusV_eq :
    leaf6850InputLogOnePlusV = outerEnclosure 24
      (leaf6850Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6850RoundedFacts : LeafRoundedFacts 8
    leaf6850Certificate.logOnePlusV leaf6850InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6850InputLogOnePlusV_eq }

private noncomputable def leaf6850Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi337InputQChi innerPair836Input
    leaf6850InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6850LowerChecked :
    lowerCheck 24 leaf6850Box leaf6850Inputs = true := by
  rfl'

private theorem leaf6850CoversExact : CoversExact 8
    leaf6850Box leaf6850Certificate leaf6850InnerLog leaf6850Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi337RoundedFacts
    innerPair836RoundedFacts leaf6850RoundedFacts (by rfl)

private theorem leaf6850FlatSound : Sound leaf6850Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6850CertificateValid
    leaf6850InnerLogValid leaf6850CoversExact leaf6850LowerChecked

private noncomputable def leaf6851Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6851Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217997/134217728) }, vSqrt := { lower := (8191/8192), upper := (954380743/954309632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (419248893/268435456) }, upper := { exponent := 1, mantissa := (1633/1024) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1908690375/1908619264) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf6851InnerLog : WideLogData :=
  innerPair853Data

set_option maxRecDepth 1000000 in
private theorem leaf6851LocalValidity :
    LeafFacts leaf6851Box leaf6851Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6851Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (954380743/954309632) }) = true
      norm_num [leaf6851Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6851CertificateValid :
    WideCertificateValid leaf6851Box leaf6851Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi338ValidityFacts
    leaf6851LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6851CoverageChecked :
    coverageCheck (innerAD leaf6851Box) leaf6851InnerLog = true := by
  rfl'

private theorem leaf6851InnerLogValid :
    leaf6851InnerLog.Valid 8 (innerAD leaf6851Box) :=
  wideLogDataValid_of_cachedCheck endpoint553PositiveFacts
    endpoint494PositiveFacts.valid leaf6851CoverageChecked

private noncomputable def leaf6851InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814853/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6851InputLogOnePlusV_eq :
    leaf6851InputLogOnePlusV = outerEnclosure 24
      (leaf6851Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6851RoundedFacts : LeafRoundedFacts 8
    leaf6851Certificate.logOnePlusV leaf6851InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6851InputLogOnePlusV_eq }

private noncomputable def leaf6851Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi338InputQChi innerPair853Input
    leaf6851InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6851LowerChecked :
    lowerCheck 24 leaf6851Box leaf6851Inputs = true := by
  rfl'

private theorem leaf6851CoversExact : CoversExact 8
    leaf6851Box leaf6851Certificate leaf6851InnerLog leaf6851Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi338RoundedFacts
    innerPair853RoundedFacts leaf6851RoundedFacts (by rfl)

private theorem leaf6851FlatSound : Sound leaf6851Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6851CertificateValid
    leaf6851InnerLogValid leaf6851CoversExact leaf6851LowerChecked

private noncomputable def leaf6852Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (37/64), chiHi := (75/128) }

private noncomputable def leaf6852Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217997/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588782592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (420297405/268435456) }, upper := { exponent := 1, mantissa := (1637/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi337LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178209279/17177565184) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf6852InnerLog : WideLogData :=
  innerPair752Data

set_option maxRecDepth 1000000 in
private theorem leaf6852LocalValidity :
    LeafFacts leaf6852Box leaf6852Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6852Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588782592) }) = true
      norm_num [leaf6852Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6852CertificateValid :
    WideCertificateValid leaf6852Box leaf6852Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi337ValidityFacts
    leaf6852LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6852CoverageChecked :
    coverageCheck (innerAD leaf6852Box) leaf6852InnerLog = true := by
  rfl'

private theorem leaf6852InnerLogValid :
    leaf6852InnerLog.Valid 8 (innerAD leaf6852Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint494PositiveFacts.valid leaf6852CoverageChecked

private noncomputable def leaf6852InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814855/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6852InputLogOnePlusV_eq :
    leaf6852InputLogOnePlusV = outerEnclosure 24
      (leaf6852Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6852RoundedFacts : LeafRoundedFacts 8
    leaf6852Certificate.logOnePlusV leaf6852InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6852InputLogOnePlusV_eq }

private noncomputable def leaf6852Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi337InputQChi innerPair752Input
    leaf6852InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6852LowerChecked :
    lowerCheck 24 leaf6852Box leaf6852Inputs = true := by
  rfl'

private theorem leaf6852CoversExact : CoversExact 8
    leaf6852Box leaf6852Certificate leaf6852InnerLog leaf6852Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi337RoundedFacts
    innerPair752RoundedFacts leaf6852RoundedFacts (by rfl)

private theorem leaf6852FlatSound : Sound leaf6852Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6852CertificateValid
    leaf6852InnerLogValid leaf6852CoversExact leaf6852LowerChecked

private noncomputable def leaf6853Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (75/128), chiHi := (19/32) }

private noncomputable def leaf6853Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217999/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588767232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (424163791/268435456) }, upper := { exponent := 1, mantissa := (413/256) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi338LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178193919/17177534464) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf6853InnerLog : WideLogData :=
  innerPair784Data

set_option maxRecDepth 1000000 in
private theorem leaf6853LocalValidity :
    LeafFacts leaf6853Box leaf6853Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6853Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588767232) }) = true
      norm_num [leaf6853Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6853CertificateValid :
    WideCertificateValid leaf6853Box leaf6853Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi338ValidityFacts
    leaf6853LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6853CoverageChecked :
    coverageCheck (innerAD leaf6853Box) leaf6853InnerLog = true := by
  rfl'

private theorem leaf6853InnerLogValid :
    leaf6853InnerLog.Valid 8 (innerAD leaf6853Box) :=
  wideLogDataValid_of_cachedCheck endpoint492PositiveFacts
    endpoint496PositiveFacts.valid leaf6853CoverageChecked

private noncomputable def leaf6853InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629725/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6853InputLogOnePlusV_eq :
    leaf6853InputLogOnePlusV = outerEnclosure 24
      (leaf6853Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6853RoundedFacts : LeafRoundedFacts 8
    leaf6853Certificate.logOnePlusV leaf6853InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6853InputLogOnePlusV_eq }

private noncomputable def leaf6853Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi338InputQChi innerPair784Input
    leaf6853InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6853LowerChecked :
    lowerCheck 24 leaf6853Box leaf6853Inputs = true := by
  rfl'

private theorem leaf6853CoversExact : CoversExact 8
    leaf6853Box leaf6853Certificate leaf6853InnerLog leaf6853Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi338RoundedFacts
    innerPair784RoundedFacts leaf6853RoundedFacts (by rfl)

private theorem leaf6853FlatSound : Sound leaf6853Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6853CertificateValid
    leaf6853InnerLogValid leaf6853CoversExact leaf6853LowerChecked

private noncomputable def leaf6854Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (19/32), chiHi := (77/128) }

private noncomputable def leaf6854Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217995/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588811008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (413088887/268435456) }, upper := { exponent := 1, mantissa := (6437/4096) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi339LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178237695/17177622016) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf6854InnerLog : WideLogData :=
  innerPair746Data

set_option maxRecDepth 1000000 in
private theorem leaf6854LocalValidity :
    LeafFacts leaf6854Box leaf6854Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6854Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588811008) }) = true
      norm_num [leaf6854Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6854CertificateValid :
    WideCertificateValid leaf6854Box leaf6854Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi339ValidityFacts
    leaf6854LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6854CoverageChecked :
    coverageCheck (innerAD leaf6854Box) leaf6854InnerLog = true := by
  rfl'

private theorem leaf6854InnerLogValid :
    leaf6854InnerLog.Valid 8 (innerAD leaf6854Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint492PositiveFacts.valid leaf6854CoverageChecked

private noncomputable def leaf6854InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814841/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6854InputLogOnePlusV_eq :
    leaf6854InputLogOnePlusV = outerEnclosure 24
      (leaf6854Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6854RoundedFacts : LeafRoundedFacts 8
    leaf6854Certificate.logOnePlusV leaf6854InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6854InputLogOnePlusV_eq }

private noncomputable def leaf6854Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi339InputQChi innerPair746Input
    leaf6854InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6854LowerChecked :
    lowerCheck 24 leaf6854Box leaf6854Inputs = true := by
  rfl'

private theorem leaf6854CoversExact : CoversExact 8
    leaf6854Box leaf6854Certificate leaf6854InnerLog leaf6854Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi339RoundedFacts
    innerPair746RoundedFacts leaf6854RoundedFacts (by rfl)

private theorem leaf6854FlatSound : Sound leaf6854Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6854CertificateValid
    leaf6854InnerLogValid leaf6854CoversExact leaf6854LowerChecked

private noncomputable def leaf6855Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (77/128), chiHi := (39/64) }

private noncomputable def leaf6855Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217997/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588796416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (416758677/268435456) }, upper := { exponent := 1, mantissa := (3247/2048) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi340LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178223103/17177592832) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf6855InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6855LocalValidity :
    LeafFacts leaf6855Box leaf6855Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6855Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588796416) }) = true
      norm_num [leaf6855Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6855CertificateValid :
    WideCertificateValid leaf6855Box leaf6855Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi340ValidityFacts
    leaf6855LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6855CoverageChecked :
    coverageCheck (innerAD leaf6855Box) leaf6855InnerLog = true := by
  rfl'

private theorem leaf6855InnerLogValid :
    leaf6855InnerLog.Valid 8 (innerAD leaf6855Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6855CoverageChecked

private noncomputable def leaf6855InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (90857/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf6855InputLogOnePlusV_eq :
    leaf6855InputLogOnePlusV = outerEnclosure 24
      (leaf6855Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6855RoundedFacts : LeafRoundedFacts 8
    leaf6855Certificate.logOnePlusV leaf6855InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6855InputLogOnePlusV_eq }

private noncomputable def leaf6855Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi340InputQChi innerPair744Input
    leaf6855InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6855LowerChecked :
    lowerCheck 24 leaf6855Box leaf6855Inputs = true := by
  rfl'

private theorem leaf6855CoversExact : CoversExact 8
    leaf6855Box leaf6855Certificate leaf6855InnerLog leaf6855Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi340RoundedFacts
    innerPair744RoundedFacts leaf6855RoundedFacts (by rfl)

private theorem leaf6855FlatSound : Sound leaf6855Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6855CertificateValid
    leaf6855InnerLogValid leaf6855CoversExact leaf6855LowerChecked

private noncomputable def leaf6856Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (19/32), chiHi := (77/128) }

private noncomputable def leaf6856Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217997/134217728) }, vSqrt := { lower := (8191/8192), upper := (954380743/954310144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (418069317/268435456) }, upper := { exponent := 1, mantissa := (3257/2048) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi339LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1908690887/1908620288) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf6856InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6856LocalValidity :
    LeafFacts leaf6856Box leaf6856Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6856Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (954380743/954310144) }) = true
      norm_num [leaf6856Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6856CertificateValid :
    WideCertificateValid leaf6856Box leaf6856Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi339ValidityFacts
    leaf6856LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6856CoverageChecked :
    coverageCheck (innerAD leaf6856Box) leaf6856InnerLog = true := by
  rfl'

private theorem leaf6856InnerLogValid :
    leaf6856InnerLog.Valid 8 (innerAD leaf6856Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6856CoverageChecked

private noncomputable def leaf6856InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629701/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6856InputLogOnePlusV_eq :
    leaf6856InputLogOnePlusV = outerEnclosure 24
      (leaf6856Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6856RoundedFacts : LeafRoundedFacts 8
    leaf6856Certificate.logOnePlusV leaf6856InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6856InputLogOnePlusV_eq }

private noncomputable def leaf6856Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi339InputQChi innerPair744Input
    leaf6856InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6856LowerChecked :
    lowerCheck 24 leaf6856Box leaf6856Inputs = true := by
  rfl'

private theorem leaf6856CoversExact : CoversExact 8
    leaf6856Box leaf6856Certificate leaf6856InnerLog leaf6856Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi339RoundedFacts
    innerPair744RoundedFacts leaf6856RoundedFacts (by rfl)

private theorem leaf6856FlatSound : Sound leaf6856Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6856CertificateValid
    leaf6856InnerLogValid leaf6856CoversExact leaf6856LowerChecked

private noncomputable def leaf6857Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (77/128), chiHi := (39/64) }

private noncomputable def leaf6857Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217999/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588776448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (421804639/268435456) }, upper := { exponent := 1, mantissa := (1643/1024) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi340LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178203135/17177552896) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf6857InnerLog : WideLogData :=
  innerPair834Data

set_option maxRecDepth 1000000 in
private theorem leaf6857LocalValidity :
    LeafFacts leaf6857Box leaf6857Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6857Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588776448) }) = true
      norm_num [leaf6857Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6857CertificateValid :
    WideCertificateValid leaf6857Box leaf6857Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi340ValidityFacts
    leaf6857LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6857CoverageChecked :
    coverageCheck (innerAD leaf6857Box) leaf6857InnerLog = true := by
  rfl'

private theorem leaf6857InnerLogValid :
    leaf6857InnerLog.Valid 8 (innerAD leaf6857Box) :=
  wideLogDataValid_of_cachedCheck endpoint528PositiveFacts
    endpoint535PositiveFacts.valid leaf6857CoverageChecked

private noncomputable def leaf6857InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907429/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6857InputLogOnePlusV_eq :
    leaf6857InputLogOnePlusV = outerEnclosure 24
      (leaf6857Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6857RoundedFacts : LeafRoundedFacts 8
    leaf6857Certificate.logOnePlusV leaf6857InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6857InputLogOnePlusV_eq }

private noncomputable def leaf6857Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi340InputQChi innerPair834Input
    leaf6857InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6857LowerChecked :
    lowerCheck 24 leaf6857Box leaf6857Inputs = true := by
  rfl'

private theorem leaf6857CoversExact : CoversExact 8
    leaf6857Box leaf6857Certificate leaf6857InnerLog leaf6857Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi340RoundedFacts
    innerPair834RoundedFacts leaf6857RoundedFacts (by rfl)

private theorem leaf6857FlatSound : Sound leaf6857Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6857CertificateValid
    leaf6857InnerLogValid leaf6857CoversExact leaf6857LowerChecked

private noncomputable def leaf6858Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (39/64), chiHi := (79/128) }

private noncomputable def leaf6858Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217999/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588781824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (420428467/268435456) }, upper := { exponent := 1, mantissa := (6551/4096) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi347LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178208511/17177563648) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf6858InnerLog : WideLogData :=
  innerPair752Data

set_option maxRecDepth 1000000 in
private theorem leaf6858LocalValidity :
    LeafFacts leaf6858Box leaf6858Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6858Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588781824) }) = true
      norm_num [leaf6858Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6858CertificateValid :
    WideCertificateValid leaf6858Box leaf6858Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi347ValidityFacts
    leaf6858LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6858CoverageChecked :
    coverageCheck (innerAD leaf6858Box) leaf6858InnerLog = true := by
  rfl'

private theorem leaf6858InnerLogValid :
    leaf6858InnerLog.Valid 8 (innerAD leaf6858Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint494PositiveFacts.valid leaf6858CoverageChecked

private noncomputable def leaf6858InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629711/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6858InputLogOnePlusV_eq :
    leaf6858InputLogOnePlusV = outerEnclosure 24
      (leaf6858Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6858RoundedFacts : LeafRoundedFacts 8
    leaf6858Certificate.logOnePlusV leaf6858InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6858InputLogOnePlusV_eq }

private noncomputable def leaf6858Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi347InputQChi innerPair752Input
    leaf6858InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6858LowerChecked :
    lowerCheck 24 leaf6858Box leaf6858Inputs = true := by
  rfl'

private theorem leaf6858CoversExact : CoversExact 8
    leaf6858Box leaf6858Certificate leaf6858InnerLog leaf6858Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi347RoundedFacts
    innerPair752RoundedFacts leaf6858RoundedFacts (by rfl)

private theorem leaf6858FlatSound : Sound leaf6858Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6858CertificateValid
    leaf6858InnerLogValid leaf6858CoversExact leaf6858LowerChecked

private noncomputable def leaf6859Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (79/128), chiHi := (5/8) }

private noncomputable def leaf6859Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218001/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588767232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (424098257/268435456) }, upper := { exponent := 1, mantissa := (413/256) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi348LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178193919/17177534464) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf6859InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6859LocalValidity :
    LeafFacts leaf6859Box leaf6859Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6859Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588767232) }) = true
      norm_num [leaf6859Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6859CertificateValid :
    WideCertificateValid leaf6859Box leaf6859Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi348ValidityFacts
    leaf6859LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6859CoverageChecked :
    coverageCheck (innerAD leaf6859Box) leaf6859InnerLog = true := by
  rfl'

private theorem leaf6859InnerLogValid :
    leaf6859InnerLog.Valid 8 (innerAD leaf6859Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6859CoverageChecked

private noncomputable def leaf6859InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629725/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6859InputLogOnePlusV_eq :
    leaf6859InputLogOnePlusV = outerEnclosure 24
      (leaf6859Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6859RoundedFacts : LeafRoundedFacts 8
    leaf6859Certificate.logOnePlusV leaf6859InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6859InputLogOnePlusV_eq }

private noncomputable def leaf6859Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi348InputQChi innerPair749Input
    leaf6859InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6859LowerChecked :
    lowerCheck 24 leaf6859Box leaf6859Inputs = true := by
  rfl'

private theorem leaf6859CoversExact : CoversExact 8
    leaf6859Box leaf6859Certificate leaf6859InnerLog leaf6859Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi348RoundedFacts
    innerPair749RoundedFacts leaf6859RoundedFacts (by rfl)

private theorem leaf6859FlatSound : Sound leaf6859Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6859CertificateValid
    leaf6859InnerLogValid leaf6859CoversExact leaf6859LowerChecked

private noncomputable def leaf6860Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (39/64), chiHi := (79/128) }

private noncomputable def leaf6860Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218001/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588761600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (425539961/268435456) }, upper := { exponent := 1, mantissa := (3315/2048) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi347LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178188287/17177523200) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf6860InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6860LocalValidity :
    LeafFacts leaf6860Box leaf6860Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6860Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588761600) }) = true
      norm_num [leaf6860Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6860CertificateValid :
    WideCertificateValid leaf6860Box leaf6860Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi347ValidityFacts
    leaf6860LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6860CoverageChecked :
    coverageCheck (innerAD leaf6860Box) leaf6860InnerLog = true := by
  rfl'

private theorem leaf6860InnerLogValid :
    leaf6860InnerLog.Valid 8 (innerAD leaf6860Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6860CoverageChecked

private noncomputable def leaf6860InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814865/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6860InputLogOnePlusV_eq :
    leaf6860InputLogOnePlusV = outerEnclosure 24
      (leaf6860Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6860RoundedFacts : LeafRoundedFacts 8
    leaf6860Certificate.logOnePlusV leaf6860InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6860InputLogOnePlusV_eq }

private noncomputable def leaf6860Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi347InputQChi innerPair749Input
    leaf6860InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6860LowerChecked :
    lowerCheck 24 leaf6860Box leaf6860Inputs = true := by
  rfl'

private theorem leaf6860CoversExact : CoversExact 8
    leaf6860Box leaf6860Certificate leaf6860InnerLog leaf6860Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi347RoundedFacts
    innerPair749RoundedFacts leaf6860RoundedFacts (by rfl)

private theorem leaf6860FlatSound : Sound leaf6860Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6860CertificateValid
    leaf6860InnerLogValid leaf6860CoversExact leaf6860LowerChecked

private noncomputable def leaf6861Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (79/128), chiHi := (5/8) }

private noncomputable def leaf6861Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218003/134217728) }, vSqrt := { lower := (8191/8192), upper := (2863142229/2862915584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (429275283/268435456) }, upper := { exponent := 1, mantissa := (209/128) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi348LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5726057813/5725831168) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf6861InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6861LocalValidity :
    LeafFacts leaf6861Box leaf6861Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6861Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2863142229/2862915584) }) = true
      norm_num [leaf6861Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6861CertificateValid :
    WideCertificateValid leaf6861Box leaf6861Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi348ValidityFacts
    leaf6861LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6861CoverageChecked :
    coverageCheck (innerAD leaf6861Box) leaf6861InnerLog = true := by
  rfl'

private theorem leaf6861InnerLogValid :
    leaf6861InnerLog.Valid 8 (innerAD leaf6861Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6861CoverageChecked

private noncomputable def leaf6861InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629745/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6861InputLogOnePlusV_eq :
    leaf6861InputLogOnePlusV = outerEnclosure 24
      (leaf6861Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6861RoundedFacts : LeafRoundedFacts 8
    leaf6861Certificate.logOnePlusV leaf6861InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6861InputLogOnePlusV_eq }

private noncomputable def leaf6861Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi348InputQChi innerPair755Input
    leaf6861InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6861LowerChecked :
    lowerCheck 24 leaf6861Box leaf6861Inputs = true := by
  rfl'

private theorem leaf6861CoversExact : CoversExact 8
    leaf6861Box leaf6861Certificate leaf6861InnerLog leaf6861Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi348RoundedFacts
    innerPair755RoundedFacts leaf6861RoundedFacts (by rfl)

private theorem leaf6861FlatSound : Sound leaf6861Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6861CertificateValid
    leaf6861InnerLogValid leaf6861CoversExact leaf6861LowerChecked

private noncomputable def leaf6862Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (19/32), chiHi := (77/128) }

private noncomputable def leaf6862Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217999/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588771584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (423049747/268435456) }, upper := { exponent := 1, mantissa := (6591/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi339LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178198271/17177543168) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf6862InnerLog : WideLogData :=
  innerPair834Data

set_option maxRecDepth 1000000 in
private theorem leaf6862LocalValidity :
    LeafFacts leaf6862Box leaf6862Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6862Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588771584) }) = true
      norm_num [leaf6862Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6862CertificateValid :
    WideCertificateValid leaf6862Box leaf6862Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi339ValidityFacts
    leaf6862LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6862CoverageChecked :
    coverageCheck (innerAD leaf6862Box) leaf6862InnerLog = true := by
  rfl'

private theorem leaf6862InnerLogValid :
    leaf6862InnerLog.Valid 8 (innerAD leaf6862Box) :=
  wideLogDataValid_of_cachedCheck endpoint528PositiveFacts
    endpoint535PositiveFacts.valid leaf6862CoverageChecked

private noncomputable def leaf6862InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629721/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6862InputLogOnePlusV_eq :
    leaf6862InputLogOnePlusV = outerEnclosure 24
      (leaf6862Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6862RoundedFacts : LeafRoundedFacts 8
    leaf6862Certificate.logOnePlusV leaf6862InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6862InputLogOnePlusV_eq }

private noncomputable def leaf6862Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi339InputQChi innerPair834Input
    leaf6862InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6862LowerChecked :
    lowerCheck 24 leaf6862Box leaf6862Inputs = true := by
  rfl'

private theorem leaf6862CoversExact : CoversExact 8
    leaf6862Box leaf6862Certificate leaf6862InnerLog leaf6862Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi339RoundedFacts
    innerPair834RoundedFacts leaf6862RoundedFacts (by rfl)

private theorem leaf6862FlatSound : Sound leaf6862Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6862CertificateValid
    leaf6862InnerLogValid leaf6862CoversExact leaf6862LowerChecked

private noncomputable def leaf6863Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (77/128), chiHi := (39/64) }

private noncomputable def leaf6863Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218001/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588756480) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (426850601/268435456) }, upper := { exponent := 1, mantissa := (3325/2048) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi340LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178183167/17177512960) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf6863InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6863LocalValidity :
    LeafFacts leaf6863Box leaf6863Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6863Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588756480) }) = true
      norm_num [leaf6863Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6863CertificateValid :
    WideCertificateValid leaf6863Box leaf6863Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi340ValidityFacts
    leaf6863LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6863CoverageChecked :
    coverageCheck (innerAD leaf6863Box) leaf6863InnerLog = true := by
  rfl'

private theorem leaf6863InnerLogValid :
    leaf6863InnerLog.Valid 8 (innerAD leaf6863Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6863CoverageChecked

private noncomputable def leaf6863InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629735/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6863InputLogOnePlusV_eq :
    leaf6863InputLogOnePlusV = outerEnclosure 24
      (leaf6863Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6863RoundedFacts : LeafRoundedFacts 8
    leaf6863Certificate.logOnePlusV leaf6863InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6863InputLogOnePlusV_eq }

private noncomputable def leaf6863Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi340InputQChi innerPair749Input
    leaf6863InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6863LowerChecked :
    lowerCheck 24 leaf6863Box leaf6863Inputs = true := by
  rfl'

private theorem leaf6863CoversExact : CoversExact 8
    leaf6863Box leaf6863Certificate leaf6863InnerLog leaf6863Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi340RoundedFacts
    innerPair749RoundedFacts leaf6863RoundedFacts (by rfl)

private theorem leaf6863FlatSound : Sound leaf6863Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6863CertificateValid
    leaf6863InnerLogValid leaf6863CoversExact leaf6863LowerChecked

private noncomputable def leaf6864Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (19/32), chiHi := (77/128) }

private noncomputable def leaf6864Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218001/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588751872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (428030177/268435456) }, upper := { exponent := 1, mantissa := (1667/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi339LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178178559/17177503744) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf6864InnerLog : WideLogData :=
  innerPair759Data

set_option maxRecDepth 1000000 in
private theorem leaf6864LocalValidity :
    LeafFacts leaf6864Box leaf6864Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6864Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588751872) }) = true
      norm_num [leaf6864Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6864CertificateValid :
    WideCertificateValid leaf6864Box leaf6864Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi339ValidityFacts
    leaf6864LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6864CoverageChecked :
    coverageCheck (innerAD leaf6864Box) leaf6864InnerLog = true := by
  rfl'

private theorem leaf6864InnerLogValid :
    leaf6864InnerLog.Valid 8 (innerAD leaf6864Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint554PositiveFacts.valid leaf6864CoverageChecked

private noncomputable def leaf6864InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907435/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6864InputLogOnePlusV_eq :
    leaf6864InputLogOnePlusV = outerEnclosure 24
      (leaf6864Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6864RoundedFacts : LeafRoundedFacts 8
    leaf6864Certificate.logOnePlusV leaf6864InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6864InputLogOnePlusV_eq }

private noncomputable def leaf6864Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi339InputQChi innerPair759Input
    leaf6864InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6864LowerChecked :
    lowerCheck 24 leaf6864Box leaf6864Inputs = true := by
  rfl'

private theorem leaf6864CoversExact : CoversExact 8
    leaf6864Box leaf6864Certificate leaf6864InnerLog leaf6864Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi339RoundedFacts
    innerPair759RoundedFacts leaf6864RoundedFacts (by rfl)

private theorem leaf6864FlatSound : Sound leaf6864Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6864CertificateValid
    leaf6864InnerLogValid leaf6864CoversExact leaf6864LowerChecked

private noncomputable def leaf6865Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (77/128), chiHi := (39/64) }

private noncomputable def leaf6865Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218003/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588736512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (431896563/268435456) }, upper := { exponent := 1, mantissa := (841/512) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi340LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178163199/17177473024) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf6865InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6865LocalValidity :
    LeafFacts leaf6865Box leaf6865Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6865Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588736512) }) = true
      norm_num [leaf6865Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6865CertificateValid :
    WideCertificateValid leaf6865Box leaf6865Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi340ValidityFacts
    leaf6865LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6865CoverageChecked :
    coverageCheck (innerAD leaf6865Box) leaf6865InnerLog = true := by
  rfl'

private theorem leaf6865InnerLogValid :
    leaf6865InnerLog.Valid 8 (innerAD leaf6865Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6865CoverageChecked

private noncomputable def leaf6865InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629755/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6865InputLogOnePlusV_eq :
    leaf6865InputLogOnePlusV = outerEnclosure 24
      (leaf6865Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6865RoundedFacts : LeafRoundedFacts 8
    leaf6865Certificate.logOnePlusV leaf6865InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6865InputLogOnePlusV_eq }

private noncomputable def leaf6865Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi340InputQChi innerPair755Input
    leaf6865InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6865LowerChecked :
    lowerCheck 24 leaf6865Box leaf6865Inputs = true := by
  rfl'

private theorem leaf6865CoversExact : CoversExact 8
    leaf6865Box leaf6865Certificate leaf6865InnerLog leaf6865Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi340RoundedFacts
    innerPair755RoundedFacts leaf6865RoundedFacts (by rfl)

private theorem leaf6865FlatSound : Sound leaf6865Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6865CertificateValid
    leaf6865InnerLogValid leaf6865CoversExact leaf6865LowerChecked

private noncomputable def leaf6866Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (39/64), chiHi := (79/128) }

private noncomputable def leaf6866Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218003/134217728) }, vSqrt := { lower := (8191/8192), upper := (2863142229/2862913792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (430651455/268435456) }, upper := { exponent := 1, mantissa := (6709/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi347LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5726056021/5725827584) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf6866InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6866LocalValidity :
    LeafFacts leaf6866Box leaf6866Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6866Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2863142229/2862913792) }) = true
      norm_num [leaf6866Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6866CertificateValid :
    WideCertificateValid leaf6866Box leaf6866Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi347ValidityFacts
    leaf6866LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6866CoverageChecked :
    coverageCheck (innerAD leaf6866Box) leaf6866InnerLog = true := by
  rfl'

private theorem leaf6866InnerLogValid :
    leaf6866InnerLog.Valid 8 (innerAD leaf6866Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6866CoverageChecked

private noncomputable def leaf6866InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814875/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6866InputLogOnePlusV_eq :
    leaf6866InputLogOnePlusV = outerEnclosure 24
      (leaf6866Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6866RoundedFacts : LeafRoundedFacts 8
    leaf6866Certificate.logOnePlusV leaf6866InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6866InputLogOnePlusV_eq }

private noncomputable def leaf6866Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi347InputQChi innerPair755Input
    leaf6866InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6866LowerChecked :
    lowerCheck 24 leaf6866Box leaf6866Inputs = true := by
  rfl'

private theorem leaf6866CoversExact : CoversExact 8
    leaf6866Box leaf6866Certificate leaf6866InnerLog leaf6866Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi347RoundedFacts
    innerPair755RoundedFacts leaf6866RoundedFacts (by rfl)

private theorem leaf6866FlatSound : Sound leaf6866Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6866CertificateValid
    leaf6866InnerLogValid leaf6866CoversExact leaf6866LowerChecked

private noncomputable def leaf6867Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (79/128), chiHi := (5/8) }

private noncomputable def leaf6867Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218005/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588726272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (434452309/268435456) }, upper := { exponent := 1, mantissa := (423/256) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi348LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178152959/17177452544) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf6867InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6867LocalValidity :
    LeafFacts leaf6867Box leaf6867Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6867Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588726272) }) = true
      norm_num [leaf6867Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6867CertificateValid :
    WideCertificateValid leaf6867Box leaf6867Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi348ValidityFacts
    leaf6867LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6867CoverageChecked :
    coverageCheck (innerAD leaf6867Box) leaf6867InnerLog = true := by
  rfl'

private theorem leaf6867InnerLogValid :
    leaf6867InnerLog.Valid 8 (innerAD leaf6867Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6867CoverageChecked

private noncomputable def leaf6867InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629765/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6867InputLogOnePlusV_eq :
    leaf6867InputLogOnePlusV = outerEnclosure 24
      (leaf6867Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6867RoundedFacts : LeafRoundedFacts 8
    leaf6867Certificate.logOnePlusV leaf6867InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6867InputLogOnePlusV_eq }

private noncomputable def leaf6867Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi348InputQChi innerPair755Input
    leaf6867InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6867LowerChecked :
    lowerCheck 24 leaf6867Box leaf6867Inputs = true := by
  rfl'

private theorem leaf6867CoversExact : CoversExact 8
    leaf6867Box leaf6867Certificate leaf6867InnerLog leaf6867Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi348RoundedFacts
    innerPair755RoundedFacts leaf6867RoundedFacts (by rfl)

private theorem leaf6867FlatSound : Sound leaf6867Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6867CertificateValid
    leaf6867InnerLogValid leaf6867CoversExact leaf6867LowerChecked

private noncomputable def leaf6868Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (39/64), chiHi := (79/128) }

private noncomputable def leaf6868Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218005/134217728) }, vSqrt := { lower := (8191/8192), upper := (8589426687/8588721152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (435762949/268435456) }, upper := { exponent := 1, mantissa := (1697/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi347LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (17178147839/17177442304) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf6868InnerLog : WideLogData :=
  innerPair790Data

set_option maxRecDepth 1000000 in
private theorem leaf6868LocalValidity :
    LeafFacts leaf6868Box leaf6868Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6868Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8589426687/8588721152) }) = true
      norm_num [leaf6868Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6868CertificateValid :
    WideCertificateValid leaf6868Box leaf6868Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi347ValidityFacts
    leaf6868LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6868CoverageChecked :
    coverageCheck (innerAD leaf6868Box) leaf6868InnerLog = true := by
  rfl'

private theorem leaf6868InnerLogValid :
    leaf6868InnerLog.Valid 8 (innerAD leaf6868Box) :=
  wideLogDataValid_of_cachedCheck endpoint496PositiveFacts
    endpoint536PositiveFacts.valid leaf6868CoverageChecked

private noncomputable def leaf6868InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814885/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6868InputLogOnePlusV_eq :
    leaf6868InputLogOnePlusV = outerEnclosure 24
      (leaf6868Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6868RoundedFacts : LeafRoundedFacts 8
    leaf6868Certificate.logOnePlusV leaf6868InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6868InputLogOnePlusV_eq }

private noncomputable def leaf6868Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi347InputQChi innerPair790Input
    leaf6868InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6868LowerChecked :
    lowerCheck 24 leaf6868Box leaf6868Inputs = true := by
  rfl'

private theorem leaf6868CoversExact : CoversExact 8
    leaf6868Box leaf6868Certificate leaf6868InnerLog leaf6868Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi347RoundedFacts
    innerPair790RoundedFacts leaf6868RoundedFacts (by rfl)

private theorem leaf6868FlatSound : Sound leaf6868Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6868CertificateValid
    leaf6868InnerLogValid leaf6868CoversExact leaf6868LowerChecked

private noncomputable def leaf6869Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (79/128), chiHi := (5/8) }

private noncomputable def leaf6869Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134218007/134217728) }, vSqrt := { lower := (8191/8192), upper := (199754109/199737344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (439629335/268435456) }, upper := { exponent := 1, mantissa := (107/64) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi348LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (399491453/399474688) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf6869InnerLog : WideLogData :=
  innerPair761Data

set_option maxRecDepth 1000000 in
private theorem leaf6869LocalValidity :
    LeafFacts leaf6869Box leaf6869Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6869Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (199754109/199737344) }) = true
      norm_num [leaf6869Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6869CertificateValid :
    WideCertificateValid leaf6869Box leaf6869Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi348ValidityFacts
    leaf6869LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6869CoverageChecked :
    coverageCheck (innerAD leaf6869Box) leaf6869InnerLog = true := by
  rfl'

private theorem leaf6869InnerLogValid :
    leaf6869InnerLog.Valid 8 (innerAD leaf6869Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint487PositiveFacts.valid leaf6869CoverageChecked

private noncomputable def leaf6869InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629785/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6869InputLogOnePlusV_eq :
    leaf6869InputLogOnePlusV = outerEnclosure 24
      (leaf6869Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6869RoundedFacts : LeafRoundedFacts 8
    leaf6869Certificate.logOnePlusV leaf6869InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6869InputLogOnePlusV_eq }

private noncomputable def leaf6869Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi348InputQChi innerPair761Input
    leaf6869InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6869LowerChecked :
    lowerCheck 24 leaf6869Box leaf6869Inputs = true := by
  rfl'

private theorem leaf6869CoversExact : CoversExact 8
    leaf6869Box leaf6869Certificate leaf6869InnerLog leaf6869Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi348RoundedFacts
    innerPair761RoundedFacts leaf6869RoundedFacts (by rfl)

private theorem leaf6869FlatSound : Sound leaf6869Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6869CertificateValid
    leaf6869InnerLogValid leaf6869CoversExact leaf6869LowerChecked

private noncomputable def component139Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component139Node0_sound : Sound component139Node0Box :=
  sound_of_literal_split component139Node0Box leaf6837Box leaf6838Box
    .chi (73/128) (by rfl) (by rfl)
    leaf6837FlatSound leaf6838FlatSound

private noncomputable def component139Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component139Node1_sound : Sound component139Node1Box :=
  sound_of_literal_split component139Node1Box leaf6839Box leaf6840Box
    .chi (73/128) (by rfl) (by rfl)
    leaf6839FlatSound leaf6840FlatSound

private noncomputable def component139Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component139Node2_sound : Sound component139Node2Box :=
  sound_of_literal_split component139Node2Box component139Node0Box component139Node1Box
    .k (57/16) (by rfl) (by rfl)
    component139Node0_sound component139Node1_sound

private noncomputable def component139Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component139Node3_sound : Sound component139Node3Box :=
  sound_of_literal_split component139Node3Box leaf6841Box leaf6842Box
    .chi (75/128) (by rfl) (by rfl)
    leaf6841FlatSound leaf6842FlatSound

private noncomputable def component139Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component139Node4_sound : Sound component139Node4Box :=
  sound_of_literal_split component139Node4Box leaf6843Box leaf6844Box
    .chi (75/128) (by rfl) (by rfl)
    leaf6843FlatSound leaf6844FlatSound

private noncomputable def component139Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component139Node5_sound : Sound component139Node5Box :=
  sound_of_literal_split component139Node5Box component139Node3Box component139Node4Box
    .k (57/16) (by rfl) (by rfl)
    component139Node3_sound component139Node4_sound

private noncomputable def component139Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component139Node6_sound : Sound component139Node6Box :=
  sound_of_literal_split component139Node6Box component139Node2Box component139Node5Box
    .chi (37/64) (by rfl) (by rfl)
    component139Node2_sound component139Node5_sound

private noncomputable def component139Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component139Node7_sound : Sound component139Node7Box :=
  sound_of_literal_split component139Node7Box leaf6845Box leaf6846Box
    .chi (73/128) (by rfl) (by rfl)
    leaf6845FlatSound leaf6846FlatSound

private noncomputable def component139Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (9/16), chiHi := (73/128) }

set_option maxRecDepth 1000000 in
private theorem component139Node8_sound : Sound component139Node8Box :=
  sound_of_literal_split component139Node8Box leaf6847Box leaf6848Box
    .k (119/32) (by rfl) (by rfl)
    leaf6847FlatSound leaf6848FlatSound

private noncomputable def component139Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component139Node9_sound : Sound component139Node9Box :=
  sound_of_literal_split component139Node9Box component139Node8Box leaf6849Box
    .chi (73/128) (by rfl) (by rfl)
    component139Node8_sound leaf6849FlatSound

private noncomputable def component139Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (9/16), chiHi := (37/64) }

set_option maxRecDepth 1000000 in
private theorem component139Node10_sound : Sound component139Node10Box :=
  sound_of_literal_split component139Node10Box component139Node7Box component139Node9Box
    .k (59/16) (by rfl) (by rfl)
    component139Node7_sound component139Node9_sound

private noncomputable def component139Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component139Node11_sound : Sound component139Node11Box :=
  sound_of_literal_split component139Node11Box leaf6850Box leaf6851Box
    .chi (75/128) (by rfl) (by rfl)
    leaf6850FlatSound leaf6851FlatSound

private noncomputable def component139Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component139Node12_sound : Sound component139Node12Box :=
  sound_of_literal_split component139Node12Box leaf6852Box leaf6853Box
    .chi (75/128) (by rfl) (by rfl)
    leaf6852FlatSound leaf6853FlatSound

private noncomputable def component139Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (37/64), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component139Node13_sound : Sound component139Node13Box :=
  sound_of_literal_split component139Node13Box component139Node11Box component139Node12Box
    .k (59/16) (by rfl) (by rfl)
    component139Node11_sound component139Node12_sound

private noncomputable def component139Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component139Node14_sound : Sound component139Node14Box :=
  sound_of_literal_split component139Node14Box component139Node10Box component139Node13Box
    .chi (37/64) (by rfl) (by rfl)
    component139Node10_sound component139Node13_sound

private noncomputable def component139Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (9/16), chiHi := (19/32) }

set_option maxRecDepth 1000000 in
private theorem component139Node15_sound : Sound component139Node15Box :=
  sound_of_literal_split component139Node15Box component139Node6Box component139Node14Box
    .k (29/8) (by rfl) (by rfl)
    component139Node6_sound component139Node14_sound

private noncomputable def component139Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component139Node16_sound : Sound component139Node16Box :=
  sound_of_literal_split component139Node16Box leaf6854Box leaf6855Box
    .chi (77/128) (by rfl) (by rfl)
    leaf6854FlatSound leaf6855FlatSound

private noncomputable def component139Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component139Node17_sound : Sound component139Node17Box :=
  sound_of_literal_split component139Node17Box leaf6856Box leaf6857Box
    .chi (77/128) (by rfl) (by rfl)
    leaf6856FlatSound leaf6857FlatSound

private noncomputable def component139Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component139Node18_sound : Sound component139Node18Box :=
  sound_of_literal_split component139Node18Box component139Node16Box component139Node17Box
    .k (57/16) (by rfl) (by rfl)
    component139Node16_sound component139Node17_sound

private noncomputable def component139Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component139Node19_sound : Sound component139Node19Box :=
  sound_of_literal_split component139Node19Box leaf6858Box leaf6859Box
    .chi (79/128) (by rfl) (by rfl)
    leaf6858FlatSound leaf6859FlatSound

private noncomputable def component139Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component139Node20_sound : Sound component139Node20Box :=
  sound_of_literal_split component139Node20Box leaf6860Box leaf6861Box
    .chi (79/128) (by rfl) (by rfl)
    leaf6860FlatSound leaf6861FlatSound

private noncomputable def component139Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component139Node21_sound : Sound component139Node21Box :=
  sound_of_literal_split component139Node21Box component139Node19Box component139Node20Box
    .k (57/16) (by rfl) (by rfl)
    component139Node19_sound component139Node20_sound

private noncomputable def component139Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component139Node22_sound : Sound component139Node22Box :=
  sound_of_literal_split component139Node22Box component139Node18Box component139Node21Box
    .chi (39/64) (by rfl) (by rfl)
    component139Node18_sound component139Node21_sound

private noncomputable def component139Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component139Node23_sound : Sound component139Node23Box :=
  sound_of_literal_split component139Node23Box leaf6862Box leaf6863Box
    .chi (77/128) (by rfl) (by rfl)
    leaf6862FlatSound leaf6863FlatSound

private noncomputable def component139Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component139Node24_sound : Sound component139Node24Box :=
  sound_of_literal_split component139Node24Box leaf6864Box leaf6865Box
    .chi (77/128) (by rfl) (by rfl)
    leaf6864FlatSound leaf6865FlatSound

private noncomputable def component139Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (19/32), chiHi := (39/64) }

set_option maxRecDepth 1000000 in
private theorem component139Node25_sound : Sound component139Node25Box :=
  sound_of_literal_split component139Node25Box component139Node23Box component139Node24Box
    .k (59/16) (by rfl) (by rfl)
    component139Node23_sound component139Node24_sound

private noncomputable def component139Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component139Node26_sound : Sound component139Node26Box :=
  sound_of_literal_split component139Node26Box leaf6866Box leaf6867Box
    .chi (79/128) (by rfl) (by rfl)
    leaf6866FlatSound leaf6867FlatSound

private noncomputable def component139Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component139Node27_sound : Sound component139Node27Box :=
  sound_of_literal_split component139Node27Box leaf6868Box leaf6869Box
    .chi (79/128) (by rfl) (by rfl)
    leaf6868FlatSound leaf6869FlatSound

private noncomputable def component139Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (39/64), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component139Node28_sound : Sound component139Node28Box :=
  sound_of_literal_split component139Node28Box component139Node26Box component139Node27Box
    .k (59/16) (by rfl) (by rfl)
    component139Node26_sound component139Node27_sound

private noncomputable def component139Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component139Node29_sound : Sound component139Node29Box :=
  sound_of_literal_split component139Node29Box component139Node25Box component139Node28Box
    .chi (39/64) (by rfl) (by rfl)
    component139Node25_sound component139Node28_sound

private noncomputable def component139Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (19/32), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component139Node30_sound : Sound component139Node30Box :=
  sound_of_literal_split component139Node30Box component139Node22Box component139Node29Box
    .k (29/8) (by rfl) (by rfl)
    component139Node22_sound component139Node29_sound

noncomputable def component139Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
theorem component139_sound : Sound component139Box :=
  sound_of_literal_split component139Box component139Node15Box component139Node30Box
    .chi (19/32) (by rfl) (by rfl)
    component139Node15_sound component139Node30_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
