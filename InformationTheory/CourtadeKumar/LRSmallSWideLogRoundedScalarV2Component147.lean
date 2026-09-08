import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch9
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch12
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch13
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch14
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

private noncomputable def leaf7228Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (7/8), chiHi := (57/64) }

private noncomputable def leaf7228Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109091/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176542208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (272584223/268435456) }, upper := { exponent := 2, mantissa := (4273/4096) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi367LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354871293/34353084416) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf7228InnerLog : WideLogData :=
  innerPair818Data

set_option maxRecDepth 1000000 in
private theorem leaf7228LocalValidity :
    LeafFacts leaf7228Box leaf7228Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7228Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176542208) }) = true
      norm_num [leaf7228Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7228CertificateValid :
    WideCertificateValid leaf7228Box leaf7228Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi367ValidityFacts
    leaf7228LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7228CoverageChecked :
    coverageCheck (innerAD leaf7228Box) leaf7228InnerLog = true := by
  rfl'

private theorem leaf7228InnerLogValid :
    leaf7228InnerLog.Valid 8 (innerAD leaf7228Box) :=
  wideLogDataValid_of_cachedCheck endpoint506PositiveFacts
    endpoint584PositiveFacts.valid leaf7228CoverageChecked

private noncomputable def leaf7228InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629953/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7228InputLogOnePlusV_eq :
    leaf7228InputLogOnePlusV = outerEnclosure 24
      (leaf7228Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7228RoundedFacts : LeafRoundedFacts 8
    leaf7228Certificate.logOnePlusV leaf7228InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7228InputLogOnePlusV_eq }

private noncomputable def leaf7228Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi367InputQChi innerPair818Input
    leaf7228InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7228LowerChecked :
    lowerCheck 24 leaf7228Box leaf7228Inputs = true := by
  rfl'

private theorem leaf7228CoversExact : CoversExact 8
    leaf7228Box leaf7228Certificate leaf7228InnerLog leaf7228Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi367RoundedFacts
    innerPair818RoundedFacts leaf7228RoundedFacts (by rfl)

private theorem leaf7228FlatSound : Sound leaf7228Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7228CertificateValid
    leaf7228InnerLogValid leaf7228CoversExact leaf7228LowerChecked

private noncomputable def leaf7229Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (7/8), chiHi := (57/64) }

private noncomputable def leaf7229Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109093/67108864) }, vSqrt := { lower := (8191/8192), upper := (3435665817/3435296768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (276254013/268435456) }, upper := { exponent := 2, mantissa := (2165/2048) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi367LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6870962585/6870593536) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf7229InnerLog : WideLogData :=
  innerPair869Data

set_option maxRecDepth 1000000 in
private theorem leaf7229LocalValidity :
    LeafFacts leaf7229Box leaf7229Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7229Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3435665817/3435296768) }) = true
      norm_num [leaf7229Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7229CertificateValid :
    WideCertificateValid leaf7229Box leaf7229Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi367ValidityFacts
    leaf7229LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7229CoverageChecked :
    coverageCheck (innerAD leaf7229Box) leaf7229InnerLog = true := by
  rfl'

private theorem leaf7229InnerLogValid :
    leaf7229InnerLog.Valid 8 (innerAD leaf7229Box) :=
  wideLogDataValid_of_cachedCheck endpoint582PositiveFacts
    endpoint585PositiveFacts.valid leaf7229CoverageChecked

private noncomputable def leaf7229InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814991/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7229InputLogOnePlusV_eq :
    leaf7229InputLogOnePlusV = outerEnclosure 24
      (leaf7229Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7229RoundedFacts : LeafRoundedFacts 8
    leaf7229Certificate.logOnePlusV leaf7229InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7229InputLogOnePlusV_eq }

private noncomputable def leaf7229Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi367InputQChi innerPair869Input
    leaf7229InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7229LowerChecked :
    lowerCheck 24 leaf7229Box leaf7229Inputs = true := by
  rfl'

private theorem leaf7229CoversExact : CoversExact 8
    leaf7229Box leaf7229Certificate leaf7229InnerLog leaf7229Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi367RoundedFacts
    innerPair869RoundedFacts leaf7229RoundedFacts (by rfl)

private theorem leaf7229FlatSound : Sound leaf7229Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7229CertificateValid
    leaf7229InnerLogValid leaf7229CoversExact leaf7229LowerChecked

private noncomputable def leaf7230Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (57/64), chiHi := (29/32) }

private noncomputable def leaf7230Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109093/67108864) }, vSqrt := { lower := (8191/8192), upper := (3435665817/3435296768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (276254013/268435456) }, upper := { exponent := 2, mantissa := (2165/2048) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi368LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6870962585/6870593536) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf7230InnerLog : WideLogData :=
  innerPair869Data

set_option maxRecDepth 1000000 in
private theorem leaf7230LocalValidity :
    LeafFacts leaf7230Box leaf7230Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7230Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3435665817/3435296768) }) = true
      norm_num [leaf7230Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7230CertificateValid :
    WideCertificateValid leaf7230Box leaf7230Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi368ValidityFacts
    leaf7230LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7230CoverageChecked :
    coverageCheck (innerAD leaf7230Box) leaf7230InnerLog = true := by
  rfl'

private theorem leaf7230InnerLogValid :
    leaf7230InnerLog.Valid 8 (innerAD leaf7230Box) :=
  wideLogDataValid_of_cachedCheck endpoint582PositiveFacts
    endpoint585PositiveFacts.valid leaf7230CoverageChecked

private noncomputable def leaf7230InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814991/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7230InputLogOnePlusV_eq :
    leaf7230InputLogOnePlusV = outerEnclosure 24
      (leaf7230Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7230RoundedFacts : LeafRoundedFacts 8
    leaf7230Certificate.logOnePlusV leaf7230InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7230InputLogOnePlusV_eq }

private noncomputable def leaf7230Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi368InputQChi innerPair869Input
    leaf7230InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7230LowerChecked :
    lowerCheck 24 leaf7230Box leaf7230Inputs = true := by
  rfl'

private theorem leaf7230CoversExact : CoversExact 8
    leaf7230Box leaf7230Certificate leaf7230InnerLog leaf7230Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi368RoundedFacts
    innerPair869RoundedFacts leaf7230RoundedFacts (by rfl)

private theorem leaf7230FlatSound : Sound leaf7230Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7230CertificateValid
    leaf7230InnerLogValid leaf7230CoversExact leaf7230LowerChecked

private noncomputable def leaf7231Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (57/64), chiHi := (29/32) }

private noncomputable def leaf7231Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109095/67108864) }, vSqrt := { lower := (8191/8192), upper := (5726109695/5725474816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (279989335/268435456) }, upper := { exponent := 2, mantissa := (1097/1024) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi368LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11451584511/11450949632) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf7231InnerLog : WideLogData :=
  innerPair872Data

set_option maxRecDepth 1000000 in
private theorem leaf7231LocalValidity :
    LeafFacts leaf7231Box leaf7231Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7231Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726109695/5725474816) }) = true
      norm_num [leaf7231Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7231CertificateValid :
    WideCertificateValid leaf7231Box leaf7231Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi368ValidityFacts
    leaf7231LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7231CoverageChecked :
    coverageCheck (innerAD leaf7231Box) leaf7231InnerLog = true := by
  rfl'

private theorem leaf7231InnerLogValid :
    leaf7231InnerLog.Valid 8 (innerAD leaf7231Box) :=
  wideLogDataValid_of_cachedCheck endpoint583PositiveFacts
    endpoint589PositiveFacts.valid leaf7231CoverageChecked

private noncomputable def leaf7231InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630011/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7231InputLogOnePlusV_eq :
    leaf7231InputLogOnePlusV = outerEnclosure 24
      (leaf7231Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7231RoundedFacts : LeafRoundedFacts 8
    leaf7231Certificate.logOnePlusV leaf7231InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7231InputLogOnePlusV_eq }

private noncomputable def leaf7231Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi368InputQChi innerPair872Input
    leaf7231InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7231LowerChecked :
    lowerCheck 24 leaf7231Box leaf7231Inputs = true := by
  rfl'

private theorem leaf7231CoversExact : CoversExact 8
    leaf7231Box leaf7231Certificate leaf7231InnerLog leaf7231Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi368RoundedFacts
    innerPair872RoundedFacts leaf7231RoundedFacts (by rfl)

private theorem leaf7231FlatSound : Sound leaf7231Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7231CertificateValid
    leaf7231InnerLogValid leaf7231CoversExact leaf7231LowerChecked

private noncomputable def leaf7232Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf7232Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554605/33554432) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176367104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (139945461/134217728) }, upper := { exponent := 2, mantissa := (1111/1024) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354696189/34352734208) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf7232InnerLog : WideLogData :=
  innerPair890Data

set_option maxRecDepth 1000000 in
private theorem leaf7232LocalValidity :
    LeafFacts leaf7232Box leaf7232Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7232Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176367104) }) = true
      norm_num [leaf7232Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7232CertificateValid :
    WideCertificateValid leaf7232Box leaf7232Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi93ValidityFacts
    leaf7232LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7232CoverageChecked :
    coverageCheck (innerAD leaf7232Box) leaf7232InnerLog = true := by
  rfl'

private theorem leaf7232InnerLogValid :
    leaf7232InnerLog.Valid 8 (innerAD leaf7232Box) :=
  wideLogDataValid_of_cachedCheck endpoint594PositiveFacts
    endpoint595PositiveFacts.valid leaf7232CoverageChecked

private noncomputable def leaf7232InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630039/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7232InputLogOnePlusV_eq :
    leaf7232InputLogOnePlusV = outerEnclosure 24
      (leaf7232Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7232RoundedFacts : LeafRoundedFacts 8
    leaf7232Certificate.logOnePlusV leaf7232InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7232InputLogOnePlusV_eq }

private noncomputable def leaf7232Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi93InputQChi innerPair890Input
    leaf7232InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7232LowerChecked :
    lowerCheck 24 leaf7232Box leaf7232Inputs = true := by
  rfl'

private theorem leaf7232CoversExact : CoversExact 8
    leaf7232Box leaf7232Certificate leaf7232InnerLog leaf7232Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi93RoundedFacts
    innerPair890RoundedFacts leaf7232RoundedFacts (by rfl)

private theorem leaf7232FlatSound : Sound leaf7232Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7232CertificateValid
    leaf7232InnerLogValid leaf7232CoversExact leaf7232LowerChecked

private noncomputable def leaf7233Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (29/32), chiHi := (15/16) }

private noncomputable def leaf7233Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554607/33554432) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176305664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (141845887/134217728) }, upper := { exponent := 2, mantissa := (563/512) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi93LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354634749/34352611328) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf7233InnerLog : WideLogData :=
  innerPair891Data

set_option maxRecDepth 1000000 in
private theorem leaf7233LocalValidity :
    LeafFacts leaf7233Box leaf7233Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7233Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176305664) }) = true
      norm_num [leaf7233Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7233CertificateValid :
    WideCertificateValid leaf7233Box leaf7233Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi93ValidityFacts
    leaf7233LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7233CoverageChecked :
    coverageCheck (innerAD leaf7233Box) leaf7233InnerLog = true := by
  rfl'

private theorem leaf7233InnerLogValid :
    leaf7233InnerLog.Valid 8 (innerAD leaf7233Box) :=
  wideLogDataValid_of_cachedCheck endpoint596PositiveFacts
    endpoint597PositiveFacts.valid leaf7233CoverageChecked

private noncomputable def leaf7233InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630069/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7233InputLogOnePlusV_eq :
    leaf7233InputLogOnePlusV = outerEnclosure 24
      (leaf7233Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7233RoundedFacts : LeafRoundedFacts 8
    leaf7233Certificate.logOnePlusV leaf7233InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7233InputLogOnePlusV_eq }

private noncomputable def leaf7233Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi93InputQChi innerPair891Input
    leaf7233InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7233LowerChecked :
    lowerCheck 24 leaf7233Box leaf7233Inputs = true := by
  rfl'

private theorem leaf7233CoversExact : CoversExact 8
    leaf7233Box leaf7233Certificate leaf7233InnerLog leaf7233Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi93RoundedFacts
    innerPair891RoundedFacts leaf7233RoundedFacts (by rfl)

private theorem leaf7233FlatSound : Sound leaf7233Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7233CertificateValid
    leaf7233InnerLogValid leaf7233CoversExact leaf7233LowerChecked

private noncomputable def leaf7234Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (7/8), chiHi := (57/64) }

private noncomputable def leaf7234Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109095/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176425472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (279923803/268435456) }, upper := { exponent := 2, mantissa := (4387/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi367LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354754557/34352850944) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7234InnerLog : WideLogData :=
  innerPair872Data

set_option maxRecDepth 1000000 in
private theorem leaf7234LocalValidity :
    LeafFacts leaf7234Box leaf7234Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7234Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176425472) }) = true
      norm_num [leaf7234Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7234CertificateValid :
    WideCertificateValid leaf7234Box leaf7234Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi367ValidityFacts
    leaf7234LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7234CoverageChecked :
    coverageCheck (innerAD leaf7234Box) leaf7234InnerLog = true := by
  rfl'

private theorem leaf7234InnerLogValid :
    leaf7234InnerLog.Valid 8 (innerAD leaf7234Box) :=
  wideLogDataValid_of_cachedCheck endpoint583PositiveFacts
    endpoint589PositiveFacts.valid leaf7234CoverageChecked

private noncomputable def leaf7234InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5815005/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7234InputLogOnePlusV_eq :
    leaf7234InputLogOnePlusV = outerEnclosure 24
      (leaf7234Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7234RoundedFacts : LeafRoundedFacts 8
    leaf7234Certificate.logOnePlusV leaf7234InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7234InputLogOnePlusV_eq }

private noncomputable def leaf7234Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi367InputQChi innerPair872Input
    leaf7234InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7234LowerChecked :
    lowerCheck 24 leaf7234Box leaf7234Inputs = true := by
  rfl'

private theorem leaf7234CoversExact : CoversExact 8
    leaf7234Box leaf7234Certificate leaf7234InnerLog leaf7234Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi367RoundedFacts
    innerPair872RoundedFacts leaf7234RoundedFacts (by rfl)

private theorem leaf7234FlatSound : Sound leaf7234Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7234CertificateValid
    leaf7234InnerLogValid leaf7234CoversExact leaf7234LowerChecked

private noncomputable def leaf7235Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (7/8), chiHi := (57/64) }

private noncomputable def leaf7235Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109097/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176367104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (283593593/268435456) }, upper := { exponent := 2, mantissa := (1111/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi367LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354696189/34352734208) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7235InnerLog : WideLogData :=
  innerPair875Data

set_option maxRecDepth 1000000 in
private theorem leaf7235LocalValidity :
    LeafFacts leaf7235Box leaf7235Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7235Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176367104) }) = true
      norm_num [leaf7235Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7235CertificateValid :
    WideCertificateValid leaf7235Box leaf7235Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi367ValidityFacts
    leaf7235LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7235CoverageChecked :
    coverageCheck (innerAD leaf7235Box) leaf7235InnerLog = true := by
  rfl'

private theorem leaf7235InnerLogValid :
    leaf7235InnerLog.Valid 8 (innerAD leaf7235Box) :=
  wideLogDataValid_of_cachedCheck endpoint584PositiveFacts
    endpoint590PositiveFacts.valid leaf7235CoverageChecked

private noncomputable def leaf7235InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630039/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7235InputLogOnePlusV_eq :
    leaf7235InputLogOnePlusV = outerEnclosure 24
      (leaf7235Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7235RoundedFacts : LeafRoundedFacts 8
    leaf7235Certificate.logOnePlusV leaf7235InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7235InputLogOnePlusV_eq }

private noncomputable def leaf7235Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi367InputQChi innerPair875Input
    leaf7235InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7235LowerChecked :
    lowerCheck 24 leaf7235Box leaf7235Inputs = true := by
  rfl'

private theorem leaf7235CoversExact : CoversExact 8
    leaf7235Box leaf7235Certificate leaf7235InnerLog leaf7235Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi367RoundedFacts
    innerPair875RoundedFacts leaf7235RoundedFacts (by rfl)

private theorem leaf7235FlatSound : Sound leaf7235Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7235CertificateValid
    leaf7235InnerLogValid leaf7235CoversExact leaf7235LowerChecked

private noncomputable def leaf7236Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (57/64), chiHi := (29/32) }

private noncomputable def leaf7236Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109097/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176365056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (283724657/268435456) }, upper := { exponent := 2, mantissa := (2223/2048) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi368LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354694141/34352730112) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7236InnerLog : WideLogData :=
  innerPair875Data

set_option maxRecDepth 1000000 in
private theorem leaf7236LocalValidity :
    LeafFacts leaf7236Box leaf7236Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7236Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176365056) }) = true
      norm_num [leaf7236Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7236CertificateValid :
    WideCertificateValid leaf7236Box leaf7236Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi368ValidityFacts
    leaf7236LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7236CoverageChecked :
    coverageCheck (innerAD leaf7236Box) leaf7236InnerLog = true := by
  rfl'

private theorem leaf7236InnerLogValid :
    leaf7236InnerLog.Valid 8 (innerAD leaf7236Box) :=
  wideLogDataValid_of_cachedCheck endpoint584PositiveFacts
    endpoint590PositiveFacts.valid leaf7236CoverageChecked

private noncomputable def leaf7236InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453755/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf7236InputLogOnePlusV_eq :
    leaf7236InputLogOnePlusV = outerEnclosure 24
      (leaf7236Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7236RoundedFacts : LeafRoundedFacts 8
    leaf7236Certificate.logOnePlusV leaf7236InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7236InputLogOnePlusV_eq }

private noncomputable def leaf7236Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi368InputQChi innerPair875Input
    leaf7236InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7236LowerChecked :
    lowerCheck 24 leaf7236Box leaf7236Inputs = true := by
  rfl'

private theorem leaf7236CoversExact : CoversExact 8
    leaf7236Box leaf7236Certificate leaf7236InnerLog leaf7236Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi368RoundedFacts
    innerPair875RoundedFacts leaf7236RoundedFacts (by rfl)

private theorem leaf7236FlatSound : Sound leaf7236Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7236CertificateValid
    leaf7236InnerLogValid leaf7236CoversExact leaf7236LowerChecked

private noncomputable def leaf7237Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (57/64), chiHi := (29/32) }

private noncomputable def leaf7237Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109099/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176305664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (287459979/268435456) }, upper := { exponent := 2, mantissa := (563/512) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi368LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354634749/34352611328) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7237InnerLog : WideLogData :=
  innerPair878Data

set_option maxRecDepth 1000000 in
private theorem leaf7237LocalValidity :
    LeafFacts leaf7237Box leaf7237Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7237Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176305664) }) = true
      norm_num [leaf7237Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7237CertificateValid :
    WideCertificateValid leaf7237Box leaf7237Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi368ValidityFacts
    leaf7237LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7237CoverageChecked :
    coverageCheck (innerAD leaf7237Box) leaf7237InnerLog = true := by
  rfl'

private theorem leaf7237InnerLogValid :
    leaf7237InnerLog.Valid 8 (innerAD leaf7237Box) :=
  wideLogDataValid_of_cachedCheck endpoint585PositiveFacts
    endpoint591PositiveFacts.valid leaf7237CoverageChecked

private noncomputable def leaf7237InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630069/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7237InputLogOnePlusV_eq :
    leaf7237InputLogOnePlusV = outerEnclosure 24
      (leaf7237Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7237RoundedFacts : LeafRoundedFacts 8
    leaf7237Certificate.logOnePlusV leaf7237InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7237InputLogOnePlusV_eq }

private noncomputable def leaf7237Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi368InputQChi innerPair878Input
    leaf7237InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7237LowerChecked :
    lowerCheck 24 leaf7237Box leaf7237Inputs = true := by
  rfl'

private theorem leaf7237CoversExact : CoversExact 8
    leaf7237Box leaf7237Certificate leaf7237InnerLog leaf7237Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi368RoundedFacts
    innerPair878RoundedFacts leaf7237RoundedFacts (by rfl)

private theorem leaf7237FlatSound : Sound leaf7237Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7237CertificateValid
    leaf7237InnerLogValid leaf7237CoversExact leaf7237LowerChecked

private noncomputable def leaf7238Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (29/32), chiHi := (59/64) }

private noncomputable def leaf7238Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109099/67108864) }, vSqrt := { lower := (8191/8192), upper := (1145221939/1145086976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (287525511/268435456) }, upper := { exponent := 2, mantissa := (4505/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi369LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2290308915/2290173952) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7238InnerLog : WideLogData :=
  innerPair878Data

set_option maxRecDepth 1000000 in
private theorem leaf7238LocalValidity :
    LeafFacts leaf7238Box leaf7238Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7238Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1145221939/1145086976) }) = true
      norm_num [leaf7238Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7238CertificateValid :
    WideCertificateValid leaf7238Box leaf7238Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi369ValidityFacts
    leaf7238LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7238CoverageChecked :
    coverageCheck (innerAD leaf7238Box) leaf7238InnerLog = true := by
  rfl'

private theorem leaf7238InnerLogValid :
    leaf7238InnerLog.Valid 8 (innerAD leaf7238Box) :=
  wideLogDataValid_of_cachedCheck endpoint585PositiveFacts
    endpoint591PositiveFacts.valid leaf7238CoverageChecked

private noncomputable def leaf7238InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630069/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7238InputLogOnePlusV_eq :
    leaf7238InputLogOnePlusV = outerEnclosure 24
      (leaf7238Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7238RoundedFacts : LeafRoundedFacts 8
    leaf7238Certificate.logOnePlusV leaf7238InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7238InputLogOnePlusV_eq }

private noncomputable def leaf7238Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi369InputQChi innerPair878Input
    leaf7238InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7238LowerChecked :
    lowerCheck 24 leaf7238Box leaf7238Inputs = true := by
  rfl'

private theorem leaf7238CoversExact : CoversExact 8
    leaf7238Box leaf7238Certificate leaf7238InnerLog leaf7238Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi369RoundedFacts
    innerPair878RoundedFacts leaf7238RoundedFacts (by rfl)

private theorem leaf7238FlatSound : Sound leaf7238Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7238CertificateValid
    leaf7238InnerLogValid leaf7238CoversExact leaf7238LowerChecked

private noncomputable def leaf7239Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (29/32), chiHi := (59/64) }

private noncomputable def leaf7239Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109101/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176244224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (291326365/268435456) }, upper := { exponent := 2, mantissa := (1141/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi369LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354573309/34352488448) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7239InnerLog : WideLogData :=
  innerPair882Data

set_option maxRecDepth 1000000 in
private theorem leaf7239LocalValidity :
    LeafFacts leaf7239Box leaf7239Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7239Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176244224) }) = true
      norm_num [leaf7239Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7239CertificateValid :
    WideCertificateValid leaf7239Box leaf7239Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi369ValidityFacts
    leaf7239LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7239CoverageChecked :
    coverageCheck (innerAD leaf7239Box) leaf7239InnerLog = true := by
  rfl'

private theorem leaf7239InnerLogValid :
    leaf7239InnerLog.Valid 8 (innerAD leaf7239Box) :=
  wideLogDataValid_of_cachedCheck endpoint589PositiveFacts
    endpoint592PositiveFacts.valid leaf7239CoverageChecked

private noncomputable def leaf7239InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630099/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7239InputLogOnePlusV_eq :
    leaf7239InputLogOnePlusV = outerEnclosure 24
      (leaf7239Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7239RoundedFacts : LeafRoundedFacts 8
    leaf7239Certificate.logOnePlusV leaf7239InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7239InputLogOnePlusV_eq }

private noncomputable def leaf7239Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi369InputQChi innerPair882Input
    leaf7239InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7239LowerChecked :
    lowerCheck 24 leaf7239Box leaf7239Inputs = true := by
  rfl'

private theorem leaf7239CoversExact : CoversExact 8
    leaf7239Box leaf7239Certificate leaf7239InnerLog leaf7239Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi369RoundedFacts
    innerPair882RoundedFacts leaf7239RoundedFacts (by rfl)

private theorem leaf7239FlatSound : Sound leaf7239Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7239CertificateValid
    leaf7239InnerLogValid leaf7239CoversExact leaf7239LowerChecked

private noncomputable def leaf7240Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (59/64), chiHi := (15/16) }

private noncomputable def leaf7240Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109101/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176244224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (291326365/268435456) }, upper := { exponent := 2, mantissa := (1141/1024) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi370LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354573309/34352488448) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7240InnerLog : WideLogData :=
  innerPair882Data

set_option maxRecDepth 1000000 in
private theorem leaf7240LocalValidity :
    LeafFacts leaf7240Box leaf7240Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7240Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176244224) }) = true
      norm_num [leaf7240Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7240CertificateValid :
    WideCertificateValid leaf7240Box leaf7240Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi370ValidityFacts
    leaf7240LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7240CoverageChecked :
    coverageCheck (innerAD leaf7240Box) leaf7240InnerLog = true := by
  rfl'

private theorem leaf7240InnerLogValid :
    leaf7240InnerLog.Valid 8 (innerAD leaf7240Box) :=
  wideLogDataValid_of_cachedCheck endpoint589PositiveFacts
    endpoint592PositiveFacts.valid leaf7240CoverageChecked

private noncomputable def leaf7240InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630099/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7240InputLogOnePlusV_eq :
    leaf7240InputLogOnePlusV = outerEnclosure 24
      (leaf7240Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7240RoundedFacts : LeafRoundedFacts 8
    leaf7240Certificate.logOnePlusV leaf7240InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7240InputLogOnePlusV_eq }

private noncomputable def leaf7240Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi370InputQChi innerPair882Input
    leaf7240InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7240LowerChecked :
    lowerCheck 24 leaf7240Box leaf7240Inputs = true := by
  rfl'

private theorem leaf7240CoversExact : CoversExact 8
    leaf7240Box leaf7240Certificate leaf7240InnerLog leaf7240Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi370RoundedFacts
    innerPair882RoundedFacts leaf7240RoundedFacts (by rfl)

private theorem leaf7240FlatSound : Sound leaf7240Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7240CertificateValid
    leaf7240InnerLogValid leaf7240CoversExact leaf7240LowerChecked

private noncomputable def leaf7241Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (59/64), chiHi := (15/16) }

private noncomputable def leaf7241Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109103/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34352365568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (295192751/268435456) }, upper := { exponent := 2, mantissa := (289/256) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi370LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708499449/68704731136) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7241InnerLog : WideLogData :=
  innerPair884Data

set_option maxRecDepth 1000000 in
private theorem leaf7241LocalValidity :
    LeafFacts leaf7241Box leaf7241Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7241Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34352365568) }) = true
      norm_num [leaf7241Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7241CertificateValid :
    WideCertificateValid leaf7241Box leaf7241Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi370ValidityFacts
    leaf7241LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7241CoverageChecked :
    coverageCheck (innerAD leaf7241Box) leaf7241InnerLog = true := by
  rfl'

private theorem leaf7241InnerLogValid :
    leaf7241InnerLog.Valid 8 (innerAD leaf7241Box) :=
  wideLogDataValid_of_cachedCheck endpoint590PositiveFacts
    endpoint598PositiveFacts.valid leaf7241CoverageChecked

private noncomputable def leaf7241InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630001/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7241InputLogOnePlusV_eq :
    leaf7241InputLogOnePlusV = outerEnclosure 24
      (leaf7241Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7241RoundedFacts : LeafRoundedFacts 8
    leaf7241Certificate.logOnePlusV leaf7241InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7241InputLogOnePlusV_eq }

private noncomputable def leaf7241Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi370InputQChi innerPair884Input
    leaf7241InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7241LowerChecked :
    lowerCheck 24 leaf7241Box leaf7241Inputs = true := by
  rfl'

private theorem leaf7241CoversExact : CoversExact 8
    leaf7241Box leaf7241Certificate leaf7241InnerLog leaf7241Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi370RoundedFacts
    innerPair884RoundedFacts leaf7241RoundedFacts (by rfl)

private theorem leaf7241FlatSound : Sound leaf7241Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7241CertificateValid
    leaf7241InnerLogValid leaf7241CoversExact leaf7241LowerChecked

private noncomputable def leaf7242Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf7242Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (33554607/33554432) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176250368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (143615251/134217728) }, upper := { exponent := 2, mantissa := (2279/2048) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354579453/34352500736) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf7242InnerLog : WideLogData :=
  innerPair879Data

set_option maxRecDepth 1000000 in
private theorem leaf7242LocalValidity :
    LeafFacts leaf7242Box leaf7242Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7242Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176250368) }) = true
      norm_num [leaf7242Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7242CertificateValid :
    WideCertificateValid leaf7242Box leaf7242Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi94ValidityFacts
    leaf7242LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7242CoverageChecked :
    coverageCheck (innerAD leaf7242Box) leaf7242InnerLog = true := by
  rfl'

private theorem leaf7242InnerLogValid :
    leaf7242InnerLog.Valid 8 (innerAD leaf7242Box) :=
  wideLogDataValid_of_cachedCheck endpoint585PositiveFacts
    endpoint592PositiveFacts.valid leaf7242CoverageChecked

private noncomputable def leaf7242InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726881/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf7242InputLogOnePlusV_eq :
    leaf7242InputLogOnePlusV = outerEnclosure 24
      (leaf7242Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7242RoundedFacts : LeafRoundedFacts 8
    leaf7242Certificate.logOnePlusV leaf7242InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7242InputLogOnePlusV_eq }

private noncomputable def leaf7242Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi94InputQChi innerPair879Input
    leaf7242InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7242LowerChecked :
    lowerCheck 24 leaf7242Box leaf7242Inputs = true := by
  rfl'

private theorem leaf7242CoversExact : CoversExact 8
    leaf7242Box leaf7242Certificate leaf7242InnerLog leaf7242Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi94RoundedFacts
    innerPair879RoundedFacts leaf7242RoundedFacts (by rfl)

private theorem leaf7242FlatSound : Sound leaf7242Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7242CertificateValid
    leaf7242InnerLogValid leaf7242CoversExact leaf7242LowerChecked

private noncomputable def leaf7243Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (15/16), chiHi := (31/32) }

private noncomputable def leaf7243Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (33554609/33554432) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34352373760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (145581209/134217728) }, upper := { exponent := 2, mantissa := (1155/1024) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi94LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708507641/68704747520) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf7243InnerLog : WideLogData :=
  innerPair894Data

set_option maxRecDepth 1000000 in
private theorem leaf7243LocalValidity :
    LeafFacts leaf7243Box leaf7243Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7243Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34352373760) }) = true
      norm_num [leaf7243Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7243CertificateValid :
    WideCertificateValid leaf7243Box leaf7243Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi94ValidityFacts
    leaf7243LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7243CoverageChecked :
    coverageCheck (innerAD leaf7243Box) leaf7243InnerLog = true := by
  rfl'

private theorem leaf7243InnerLogValid :
    leaf7243InnerLog.Valid 8 (innerAD leaf7243Box) :=
  wideLogDataValid_of_cachedCheck endpoint599PositiveFacts
    endpoint600PositiveFacts.valid leaf7243CoverageChecked

private noncomputable def leaf7243InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629999/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7243InputLogOnePlusV_eq :
    leaf7243InputLogOnePlusV = outerEnclosure 24
      (leaf7243Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7243RoundedFacts : LeafRoundedFacts 8
    leaf7243Certificate.logOnePlusV leaf7243InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7243InputLogOnePlusV_eq }

private noncomputable def leaf7243Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi94InputQChi innerPair894Input
    leaf7243InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7243LowerChecked :
    lowerCheck 24 leaf7243Box leaf7243Inputs = true := by
  rfl'

private theorem leaf7243CoversExact : CoversExact 8
    leaf7243Box leaf7243Certificate leaf7243InnerLog leaf7243Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi94RoundedFacts
    innerPair894RoundedFacts leaf7243RoundedFacts (by rfl)

private theorem leaf7243FlatSound : Sound leaf7243Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7243CertificateValid
    leaf7243InnerLogValid leaf7243CoversExact leaf7243LowerChecked

private noncomputable def leaf7244Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf7244Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (33554609/33554432) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34352267264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (147285041/134217728) }, upper := { exponent := 2, mantissa := (73/64) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708401145/68704534528) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf7244InnerLog : WideLogData :=
  innerPair884Data

set_option maxRecDepth 1000000 in
private theorem leaf7244LocalValidity :
    LeafFacts leaf7244Box leaf7244Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7244Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34352267264) }) = true
      norm_num [leaf7244Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7244CertificateValid :
    WideCertificateValid leaf7244Box leaf7244Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi95ValidityFacts
    leaf7244LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7244CoverageChecked :
    coverageCheck (innerAD leaf7244Box) leaf7244InnerLog = true := by
  rfl'

private theorem leaf7244InnerLogValid :
    leaf7244InnerLog.Valid 8 (innerAD leaf7244Box) :=
  wideLogDataValid_of_cachedCheck endpoint590PositiveFacts
    endpoint598PositiveFacts.valid leaf7244CoverageChecked

private noncomputable def leaf7244InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630025/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7244InputLogOnePlusV_eq :
    leaf7244InputLogOnePlusV = outerEnclosure 24
      (leaf7244Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7244RoundedFacts : LeafRoundedFacts 8
    leaf7244Certificate.logOnePlusV leaf7244InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7244InputLogOnePlusV_eq }

private noncomputable def leaf7244Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi95InputQChi innerPair884Input
    leaf7244InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7244LowerChecked :
    lowerCheck 24 leaf7244Box leaf7244Inputs = true := by
  rfl'

private theorem leaf7244CoversExact : CoversExact 8
    leaf7244Box leaf7244Certificate leaf7244InnerLog leaf7244Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi95RoundedFacts
    innerPair884RoundedFacts leaf7244RoundedFacts (by rfl)

private theorem leaf7244FlatSound : Sound leaf7244Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7244CertificateValid
    leaf7244InnerLogValid leaf7244CoversExact leaf7244LowerChecked

private noncomputable def leaf7245Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (31/32), chiHi := (1) }

private noncomputable def leaf7245Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (33554611/33554432) }, vSqrt := { lower := (8191/8192), upper := (11452044627/11450712064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (149316531/134217728) }, upper := { exponent := 2, mantissa := (37/32) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi95LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22902756691/22901424128) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf7245InnerLog : WideLogData :=
  innerPair886Data

set_option maxRecDepth 1000000 in
private theorem leaf7245LocalValidity :
    LeafFacts leaf7245Box leaf7245Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7245Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452044627/11450712064) }) = true
      norm_num [leaf7245Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7245CertificateValid :
    WideCertificateValid leaf7245Box leaf7245Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi95ValidityFacts
    leaf7245LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7245CoverageChecked :
    coverageCheck (innerAD leaf7245Box) leaf7245InnerLog = true := by
  rfl'

private theorem leaf7245InnerLogValid :
    leaf7245InnerLog.Valid 8 (innerAD leaf7245Box) :=
  wideLogDataValid_of_cachedCheck endpoint591PositiveFacts
    endpoint601PositiveFacts.valid leaf7245CoverageChecked

private noncomputable def leaf7245InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630057/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7245InputLogOnePlusV_eq :
    leaf7245InputLogOnePlusV = outerEnclosure 24
      (leaf7245Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7245RoundedFacts : LeafRoundedFacts 8
    leaf7245Certificate.logOnePlusV leaf7245InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7245InputLogOnePlusV_eq }

private noncomputable def leaf7245Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi95InputQChi innerPair886Input
    leaf7245InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7245LowerChecked :
    lowerCheck 24 leaf7245Box leaf7245Inputs = true := by
  rfl'

private theorem leaf7245CoversExact : CoversExact 8
    leaf7245Box leaf7245Certificate leaf7245InnerLog leaf7245Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi95RoundedFacts
    innerPair886RoundedFacts leaf7245RoundedFacts (by rfl)

private theorem leaf7245FlatSound : Sound leaf7245Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7245CertificateValid
    leaf7245InnerLogValid leaf7245CoversExact leaf7245LowerChecked

private noncomputable def leaf7246Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (15/16), chiHi := (61/64) }

private noncomputable def leaf7246Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109103/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34352367616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (295127219/268435456) }, upper := { exponent := 2, mantissa := (4623/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi371LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708501497/68704735232) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7246InnerLog : WideLogData :=
  innerPair884Data

set_option maxRecDepth 1000000 in
private theorem leaf7246LocalValidity :
    LeafFacts leaf7246Box leaf7246Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7246Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34352367616) }) = true
      norm_num [leaf7246Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7246CertificateValid :
    WideCertificateValid leaf7246Box leaf7246Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi371ValidityFacts
    leaf7246LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7246CoverageChecked :
    coverageCheck (innerAD leaf7246Box) leaf7246InnerLog = true := by
  rfl'

private theorem leaf7246InnerLogValid :
    leaf7246InnerLog.Valid 8 (innerAD leaf7246Box) :=
  wideLogDataValid_of_cachedCheck endpoint590PositiveFacts
    endpoint598PositiveFacts.valid leaf7246CoverageChecked

private noncomputable def leaf7246InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726875/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf7246InputLogOnePlusV_eq :
    leaf7246InputLogOnePlusV = outerEnclosure 24
      (leaf7246Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7246RoundedFacts : LeafRoundedFacts 8
    leaf7246Certificate.logOnePlusV leaf7246InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7246InputLogOnePlusV_eq }

private noncomputable def leaf7246Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi371InputQChi innerPair884Input
    leaf7246InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7246LowerChecked :
    lowerCheck 24 leaf7246Box leaf7246Inputs = true := by
  rfl'

private theorem leaf7246CoversExact : CoversExact 8
    leaf7246Box leaf7246Certificate leaf7246InnerLog leaf7246Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi371RoundedFacts
    innerPair884RoundedFacts leaf7246RoundedFacts (by rfl)

private theorem leaf7246FlatSound : Sound leaf7246Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7246CertificateValid
    leaf7246InnerLogValid leaf7246CoversExact leaf7246LowerChecked

private noncomputable def leaf7247Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (15/16), chiHi := (61/64) }

private noncomputable def leaf7247Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109105/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34352242688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (299059137/268435456) }, upper := { exponent := 2, mantissa := (1171/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi371LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708376569/68704485376) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7247InnerLog : WideLogData :=
  innerPair886Data

set_option maxRecDepth 1000000 in
private theorem leaf7247LocalValidity :
    LeafFacts leaf7247Box leaf7247Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7247Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34352242688) }) = true
      norm_num [leaf7247Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7247CertificateValid :
    WideCertificateValid leaf7247Box leaf7247Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi371ValidityFacts
    leaf7247LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7247CoverageChecked :
    coverageCheck (innerAD leaf7247Box) leaf7247InnerLog = true := by
  rfl'

private theorem leaf7247InnerLogValid :
    leaf7247InnerLog.Valid 8 (innerAD leaf7247Box) :=
  wideLogDataValid_of_cachedCheck endpoint591PositiveFacts
    endpoint601PositiveFacts.valid leaf7247CoverageChecked

private noncomputable def leaf7247InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630031/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7247InputLogOnePlusV_eq :
    leaf7247InputLogOnePlusV = outerEnclosure 24
      (leaf7247Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7247RoundedFacts : LeafRoundedFacts 8
    leaf7247Certificate.logOnePlusV leaf7247InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7247InputLogOnePlusV_eq }

private noncomputable def leaf7247Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi371InputQChi innerPair886Input
    leaf7247InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7247LowerChecked :
    lowerCheck 24 leaf7247Box leaf7247Inputs = true := by
  rfl'

private theorem leaf7247CoversExact : CoversExact 8
    leaf7247Box leaf7247Certificate leaf7247InnerLog leaf7247Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi371RoundedFacts
    innerPair886RoundedFacts leaf7247RoundedFacts (by rfl)

private theorem leaf7247FlatSound : Sound leaf7247Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7247CertificateValid
    leaf7247InnerLogValid leaf7247CoversExact leaf7247LowerChecked

private noncomputable def leaf7248Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (61/64), chiHi := (31/32) }

private noncomputable def leaf7248Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109105/67108864) }, vSqrt := { lower := (8191/8192), upper := (11452044627/11450748928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (298928073/268435456) }, upper := { exponent := 2, mantissa := (2341/2048) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi372LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22902793555/22901497856) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7248InnerLog : WideLogData :=
  innerPair886Data

set_option maxRecDepth 1000000 in
private theorem leaf7248LocalValidity :
    LeafFacts leaf7248Box leaf7248Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7248Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452044627/11450748928) }) = true
      norm_num [leaf7248Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7248CertificateValid :
    WideCertificateValid leaf7248Box leaf7248Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi372ValidityFacts
    leaf7248LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7248CoverageChecked :
    coverageCheck (innerAD leaf7248Box) leaf7248InnerLog = true := by
  rfl'

private theorem leaf7248InnerLogValid :
    leaf7248InnerLog.Valid 8 (innerAD leaf7248Box) :=
  wideLogDataValid_of_cachedCheck endpoint591PositiveFacts
    endpoint601PositiveFacts.valid leaf7248CoverageChecked

private noncomputable def leaf7248InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5815015/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7248InputLogOnePlusV_eq :
    leaf7248InputLogOnePlusV = outerEnclosure 24
      (leaf7248Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7248RoundedFacts : LeafRoundedFacts 8
    leaf7248Certificate.logOnePlusV leaf7248InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7248InputLogOnePlusV_eq }

private noncomputable def leaf7248Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi372InputQChi innerPair886Input
    leaf7248InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7248LowerChecked :
    lowerCheck 24 leaf7248Box leaf7248Inputs = true := by
  rfl'

private theorem leaf7248CoversExact : CoversExact 8
    leaf7248Box leaf7248Certificate leaf7248InnerLog leaf7248Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi372RoundedFacts
    innerPair886RoundedFacts leaf7248RoundedFacts (by rfl)

private theorem leaf7248FlatSound : Sound leaf7248Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7248CertificateValid
    leaf7248InnerLogValid leaf7248CoversExact leaf7248LowerChecked

private noncomputable def leaf7249Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (61/64), chiHi := (31/32) }

private noncomputable def leaf7249Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109107/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34352119808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (302925523/268435456) }, upper := { exponent := 2, mantissa := (593/512) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi372LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708253689/68704239616) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7249InnerLog : WideLogData :=
  innerPair888Data

set_option maxRecDepth 1000000 in
private theorem leaf7249LocalValidity :
    LeafFacts leaf7249Box leaf7249Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7249Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34352119808) }) = true
      norm_num [leaf7249Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7249CertificateValid :
    WideCertificateValid leaf7249Box leaf7249Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi372ValidityFacts
    leaf7249LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7249CoverageChecked :
    coverageCheck (innerAD leaf7249Box) leaf7249InnerLog = true := by
  rfl'

private theorem leaf7249InnerLogValid :
    leaf7249InnerLog.Valid 8 (innerAD leaf7249Box) :=
  wideLogDataValid_of_cachedCheck endpoint592PositiveFacts
    endpoint602PositiveFacts.valid leaf7249CoverageChecked

private noncomputable def leaf7249InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630061/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7249InputLogOnePlusV_eq :
    leaf7249InputLogOnePlusV = outerEnclosure 24
      (leaf7249Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7249RoundedFacts : LeafRoundedFacts 8
    leaf7249Certificate.logOnePlusV leaf7249InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7249InputLogOnePlusV_eq }

private noncomputable def leaf7249Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi372InputQChi innerPair888Input
    leaf7249InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7249LowerChecked :
    lowerCheck 24 leaf7249Box leaf7249Inputs = true := by
  rfl'

private theorem leaf7249CoversExact : CoversExact 8
    leaf7249Box leaf7249Certificate leaf7249InnerLog leaf7249Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi372RoundedFacts
    innerPair888RoundedFacts leaf7249RoundedFacts (by rfl)

private theorem leaf7249FlatSound : Sound leaf7249Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7249CertificateValid
    leaf7249InnerLogValid leaf7249CoversExact leaf7249LowerChecked

private noncomputable def leaf7250Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (31/32), chiHi := (63/64) }

private noncomputable def leaf7250Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109107/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34352125952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (302728927/268435456) }, upper := { exponent := 2, mantissa := (4741/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi373LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708259833/68704251904) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7250InnerLog : WideLogData :=
  innerPair888Data

set_option maxRecDepth 1000000 in
private theorem leaf7250LocalValidity :
    LeafFacts leaf7250Box leaf7250Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7250Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34352125952) }) = true
      norm_num [leaf7250Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7250CertificateValid :
    WideCertificateValid leaf7250Box leaf7250Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi373ValidityFacts
    leaf7250LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7250CoverageChecked :
    coverageCheck (innerAD leaf7250Box) leaf7250InnerLog = true := by
  rfl'

private theorem leaf7250InnerLogValid :
    leaf7250InnerLog.Valid 8 (innerAD leaf7250Box) :=
  wideLogDataValid_of_cachedCheck endpoint592PositiveFacts
    endpoint602PositiveFacts.valid leaf7250CoverageChecked

private noncomputable def leaf7250InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630059/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7250InputLogOnePlusV_eq :
    leaf7250InputLogOnePlusV = outerEnclosure 24
      (leaf7250Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7250RoundedFacts : LeafRoundedFacts 8
    leaf7250Certificate.logOnePlusV leaf7250InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7250InputLogOnePlusV_eq }

private noncomputable def leaf7250Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi373InputQChi innerPair888Input
    leaf7250InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7250LowerChecked :
    lowerCheck 24 leaf7250Box leaf7250Inputs = true := by
  rfl'

private theorem leaf7250CoversExact : CoversExact 8
    leaf7250Box leaf7250Certificate leaf7250InnerLog leaf7250Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi373RoundedFacts
    innerPair888RoundedFacts leaf7250RoundedFacts (by rfl)

private theorem leaf7250FlatSound : Sound leaf7250Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7250CertificateValid
    leaf7250InnerLogValid leaf7250CoversExact leaf7250LowerChecked

private noncomputable def leaf7251Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (31/32), chiHi := (63/64) }

private noncomputable def leaf7251Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109109/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34351996928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (306791909/268435456) }, upper := { exponent := 2, mantissa := (1201/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi373LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708130809/68703993856) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7251InnerLog : WideLogData :=
  innerPair893Data

set_option maxRecDepth 1000000 in
private theorem leaf7251LocalValidity :
    LeafFacts leaf7251Box leaf7251Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7251Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34351996928) }) = true
      norm_num [leaf7251Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7251CertificateValid :
    WideCertificateValid leaf7251Box leaf7251Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi373ValidityFacts
    leaf7251LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7251CoverageChecked :
    coverageCheck (innerAD leaf7251Box) leaf7251InnerLog = true := by
  rfl'

private theorem leaf7251InnerLogValid :
    leaf7251InnerLog.Valid 8 (innerAD leaf7251Box) :=
  wideLogDataValid_of_cachedCheck endpoint598PositiveFacts
    endpoint603PositiveFacts.valid leaf7251CoverageChecked

private noncomputable def leaf7251InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630091/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7251InputLogOnePlusV_eq :
    leaf7251InputLogOnePlusV = outerEnclosure 24
      (leaf7251Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7251RoundedFacts : LeafRoundedFacts 8
    leaf7251Certificate.logOnePlusV leaf7251InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7251InputLogOnePlusV_eq }

private noncomputable def leaf7251Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi373InputQChi innerPair893Input
    leaf7251InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7251LowerChecked :
    lowerCheck 24 leaf7251Box leaf7251Inputs = true := by
  rfl'

private theorem leaf7251CoversExact : CoversExact 8
    leaf7251Box leaf7251Certificate leaf7251InnerLog leaf7251Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi373RoundedFacts
    innerPair893RoundedFacts leaf7251RoundedFacts (by rfl)

private theorem leaf7251FlatSound : Sound leaf7251Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7251CertificateValid
    leaf7251InnerLogValid leaf7251CoversExact leaf7251LowerChecked

private noncomputable def leaf7252Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (63/64), chiHi := (1) }

private noncomputable def leaf7252Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109109/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34352005120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (306529781/268435456) }, upper := { exponent := 2, mantissa := (75/64) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi374LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708139001/68704010240) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf7252InnerLog : WideLogData :=
  innerPair892Data

set_option maxRecDepth 1000000 in
private theorem leaf7252LocalValidity :
    LeafFacts leaf7252Box leaf7252Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7252Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34352005120) }) = true
      norm_num [leaf7252Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7252CertificateValid :
    WideCertificateValid leaf7252Box leaf7252Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi374ValidityFacts
    leaf7252LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7252CoverageChecked :
    coverageCheck (innerAD leaf7252Box) leaf7252InnerLog = true := by
  rfl'

private theorem leaf7252InnerLogValid :
    leaf7252InnerLog.Valid 8 (innerAD leaf7252Box) :=
  wideLogDataValid_of_cachedCheck endpoint598PositiveFacts
    endpoint602PositiveFacts.valid leaf7252CoverageChecked

private noncomputable def leaf7252InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630089/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7252InputLogOnePlusV_eq :
    leaf7252InputLogOnePlusV = outerEnclosure 24
      (leaf7252Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7252RoundedFacts : LeafRoundedFacts 8
    leaf7252Certificate.logOnePlusV leaf7252InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7252InputLogOnePlusV_eq }

private noncomputable def leaf7252Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi374InputQChi innerPair892Input
    leaf7252InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7252LowerChecked :
    lowerCheck 24 leaf7252Box leaf7252Inputs = true := by
  rfl'

private theorem leaf7252CoversExact : CoversExact 8
    leaf7252Box leaf7252Certificate leaf7252InnerLog leaf7252Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi374RoundedFacts
    innerPair892RoundedFacts leaf7252RoundedFacts (by rfl)

private theorem leaf7252FlatSound : Sound leaf7252Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7252CertificateValid
    leaf7252InnerLogValid leaf7252CoversExact leaf7252LowerChecked

private noncomputable def leaf7253Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (63/64), chiHi := (1) }

private noncomputable def leaf7253Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109111/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34351874048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (310658295/268435456) }, upper := { exponent := 2, mantissa := (19/16) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi374LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708007929/68703748096) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf7253InnerLog : WideLogData :=
  innerPair895Data

set_option maxRecDepth 1000000 in
private theorem leaf7253LocalValidity :
    LeafFacts leaf7253Box leaf7253Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7253Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34351874048) }) = true
      norm_num [leaf7253Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7253CertificateValid :
    WideCertificateValid leaf7253Box leaf7253Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi374ValidityFacts
    leaf7253LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7253CoverageChecked :
    coverageCheck (innerAD leaf7253Box) leaf7253InnerLog = true := by
  rfl'

private theorem leaf7253InnerLogValid :
    leaf7253InnerLog.Valid 8 (innerAD leaf7253Box) :=
  wideLogDataValid_of_cachedCheck endpoint601PositiveFacts
    endpoint603PositiveFacts.valid leaf7253CoverageChecked

private noncomputable def leaf7253InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630121/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7253InputLogOnePlusV_eq :
    leaf7253InputLogOnePlusV = outerEnclosure 24
      (leaf7253Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7253RoundedFacts : LeafRoundedFacts 8
    leaf7253Certificate.logOnePlusV leaf7253InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7253InputLogOnePlusV_eq }

private noncomputable def leaf7253Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi374InputQChi innerPair895Input
    leaf7253InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7253LowerChecked :
    lowerCheck 24 leaf7253Box leaf7253Inputs = true := by
  rfl'

private theorem leaf7253CoversExact : CoversExact 8
    leaf7253Box leaf7253Certificate leaf7253InnerLog leaf7253Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi374RoundedFacts
    innerPair895RoundedFacts leaf7253RoundedFacts (by rfl)

private theorem leaf7253FlatSound : Sound leaf7253Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7253CertificateValid
    leaf7253InnerLogValid leaf7253CoversExact leaf7253LowerChecked

private noncomputable def leaf7254Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (7/8), chiHi := (57/64) }

private noncomputable def leaf7254Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109099/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176308736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (287263383/268435456) }, upper := { exponent := 2, mantissa := (4501/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi367LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354637821/34352617472) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7254InnerLog : WideLogData :=
  innerPair878Data

set_option maxRecDepth 1000000 in
private theorem leaf7254LocalValidity :
    LeafFacts leaf7254Box leaf7254Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7254Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176308736) }) = true
      norm_num [leaf7254Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7254CertificateValid :
    WideCertificateValid leaf7254Box leaf7254Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi367ValidityFacts
    leaf7254LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7254CoverageChecked :
    coverageCheck (innerAD leaf7254Box) leaf7254InnerLog = true := by
  rfl'

private theorem leaf7254InnerLogValid :
    leaf7254InnerLog.Valid 8 (innerAD leaf7254Box) :=
  wideLogDataValid_of_cachedCheck endpoint585PositiveFacts
    endpoint591PositiveFacts.valid leaf7254CoverageChecked

private noncomputable def leaf7254InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630067/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7254InputLogOnePlusV_eq :
    leaf7254InputLogOnePlusV = outerEnclosure 24
      (leaf7254Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7254RoundedFacts : LeafRoundedFacts 8
    leaf7254Certificate.logOnePlusV leaf7254InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7254InputLogOnePlusV_eq }

private noncomputable def leaf7254Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi367InputQChi innerPair878Input
    leaf7254InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7254LowerChecked :
    lowerCheck 24 leaf7254Box leaf7254Inputs = true := by
  rfl'

private theorem leaf7254CoversExact : CoversExact 8
    leaf7254Box leaf7254Certificate leaf7254InnerLog leaf7254Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi367RoundedFacts
    innerPair878RoundedFacts leaf7254RoundedFacts (by rfl)

private theorem leaf7254FlatSound : Sound leaf7254Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7254CertificateValid
    leaf7254InnerLogValid leaf7254CoversExact leaf7254LowerChecked

private noncomputable def leaf7255Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (7/8), chiHi := (57/64) }

private noncomputable def leaf7255Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109101/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176250368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (290933173/268435456) }, upper := { exponent := 2, mantissa := (2279/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi367LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34354579453/34352500736) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7255InnerLog : WideLogData :=
  innerPair882Data

set_option maxRecDepth 1000000 in
private theorem leaf7255LocalValidity :
    LeafFacts leaf7255Box leaf7255Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7255Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176250368) }) = true
      norm_num [leaf7255Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7255CertificateValid :
    WideCertificateValid leaf7255Box leaf7255Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi367ValidityFacts
    leaf7255LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7255CoverageChecked :
    coverageCheck (innerAD leaf7255Box) leaf7255InnerLog = true := by
  rfl'

private theorem leaf7255InnerLogValid :
    leaf7255InnerLog.Valid 8 (innerAD leaf7255Box) :=
  wideLogDataValid_of_cachedCheck endpoint589PositiveFacts
    endpoint592PositiveFacts.valid leaf7255CoverageChecked

private noncomputable def leaf7255InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726881/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf7255InputLogOnePlusV_eq :
    leaf7255InputLogOnePlusV = outerEnclosure 24
      (leaf7255Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7255RoundedFacts : LeafRoundedFacts 8
    leaf7255Certificate.logOnePlusV leaf7255InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7255InputLogOnePlusV_eq }

private noncomputable def leaf7255Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi367InputQChi innerPair882Input
    leaf7255InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7255LowerChecked :
    lowerCheck 24 leaf7255Box leaf7255Inputs = true := by
  rfl'

private theorem leaf7255CoversExact : CoversExact 8
    leaf7255Box leaf7255Certificate leaf7255InnerLog leaf7255Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi367RoundedFacts
    innerPair882RoundedFacts leaf7255RoundedFacts (by rfl)

private theorem leaf7255FlatSound : Sound leaf7255Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7255CertificateValid
    leaf7255InnerLogValid leaf7255CoversExact leaf7255LowerChecked

private noncomputable def leaf7256Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (57/64), chiHi := (29/32) }

private noncomputable def leaf7256Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109101/67108864) }, vSqrt := { lower := (8191/8192), upper := (5726109695/5725415424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (291195301/268435456) }, upper := { exponent := 2, mantissa := (2281/2048) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi368LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (11451525119/11450830848) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7256InnerLog : WideLogData :=
  innerPair882Data

set_option maxRecDepth 1000000 in
private theorem leaf7256LocalValidity :
    LeafFacts leaf7256Box leaf7256Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7256Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5726109695/5725415424) }) = true
      norm_num [leaf7256Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7256CertificateValid :
    WideCertificateValid leaf7256Box leaf7256Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi368ValidityFacts
    leaf7256LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7256CoverageChecked :
    coverageCheck (innerAD leaf7256Box) leaf7256InnerLog = true := by
  rfl'

private theorem leaf7256InnerLogValid :
    leaf7256InnerLog.Valid 8 (innerAD leaf7256Box) :=
  wideLogDataValid_of_cachedCheck endpoint589PositiveFacts
    endpoint592PositiveFacts.valid leaf7256CoverageChecked

private noncomputable def leaf7256InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5815049/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7256InputLogOnePlusV_eq :
    leaf7256InputLogOnePlusV = outerEnclosure 24
      (leaf7256Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7256RoundedFacts : LeafRoundedFacts 8
    leaf7256Certificate.logOnePlusV leaf7256InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7256InputLogOnePlusV_eq }

private noncomputable def leaf7256Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi368InputQChi innerPair882Input
    leaf7256InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7256LowerChecked :
    lowerCheck 24 leaf7256Box leaf7256Inputs = true := by
  rfl'

private theorem leaf7256CoversExact : CoversExact 8
    leaf7256Box leaf7256Certificate leaf7256InnerLog leaf7256Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi368RoundedFacts
    innerPair882RoundedFacts leaf7256RoundedFacts (by rfl)

private theorem leaf7256FlatSound : Sound leaf7256Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7256CertificateValid
    leaf7256InnerLogValid leaf7256CoversExact leaf7256LowerChecked

private noncomputable def leaf7257Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (57/64), chiHi := (29/32) }

private noncomputable def leaf7257Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109103/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34352373760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (294930623/268435456) }, upper := { exponent := 2, mantissa := (1155/1024) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi368LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708507641/68704747520) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7257InnerLog : WideLogData :=
  innerPair884Data

set_option maxRecDepth 1000000 in
private theorem leaf7257LocalValidity :
    LeafFacts leaf7257Box leaf7257Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7257Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34352373760) }) = true
      norm_num [leaf7257Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7257CertificateValid :
    WideCertificateValid leaf7257Box leaf7257Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi368ValidityFacts
    leaf7257LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7257CoverageChecked :
    coverageCheck (innerAD leaf7257Box) leaf7257InnerLog = true := by
  rfl'

private theorem leaf7257InnerLogValid :
    leaf7257InnerLog.Valid 8 (innerAD leaf7257Box) :=
  wideLogDataValid_of_cachedCheck endpoint590PositiveFacts
    endpoint598PositiveFacts.valid leaf7257CoverageChecked

private noncomputable def leaf7257InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629999/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7257InputLogOnePlusV_eq :
    leaf7257InputLogOnePlusV = outerEnclosure 24
      (leaf7257Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7257RoundedFacts : LeafRoundedFacts 8
    leaf7257Certificate.logOnePlusV leaf7257InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7257InputLogOnePlusV_eq }

private noncomputable def leaf7257Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi368InputQChi innerPair884Input
    leaf7257InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7257LowerChecked :
    lowerCheck 24 leaf7257Box leaf7257Inputs = true := by
  rfl'

private theorem leaf7257CoversExact : CoversExact 8
    leaf7257Box leaf7257Certificate leaf7257InnerLog leaf7257Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi368RoundedFacts
    innerPair884RoundedFacts leaf7257RoundedFacts (by rfl)

private theorem leaf7257FlatSound : Sound leaf7257Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7257CertificateValid
    leaf7257InnerLogValid leaf7257CoversExact leaf7257LowerChecked

private noncomputable def leaf7258Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (29/32), chiHi := (59/64) }

private noncomputable def leaf7258Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109103/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34352367616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (295127219/268435456) }, upper := { exponent := 2, mantissa := (4623/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi369LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708501497/68704735232) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7258InnerLog : WideLogData :=
  innerPair884Data

set_option maxRecDepth 1000000 in
private theorem leaf7258LocalValidity :
    LeafFacts leaf7258Box leaf7258Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7258Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34352367616) }) = true
      norm_num [leaf7258Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7258CertificateValid :
    WideCertificateValid leaf7258Box leaf7258Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi369ValidityFacts
    leaf7258LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7258CoverageChecked :
    coverageCheck (innerAD leaf7258Box) leaf7258InnerLog = true := by
  rfl'

private theorem leaf7258InnerLogValid :
    leaf7258InnerLog.Valid 8 (innerAD leaf7258Box) :=
  wideLogDataValid_of_cachedCheck endpoint590PositiveFacts
    endpoint598PositiveFacts.valid leaf7258CoverageChecked

private noncomputable def leaf7258InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726875/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf7258InputLogOnePlusV_eq :
    leaf7258InputLogOnePlusV = outerEnclosure 24
      (leaf7258Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7258RoundedFacts : LeafRoundedFacts 8
    leaf7258Certificate.logOnePlusV leaf7258InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7258InputLogOnePlusV_eq }

private noncomputable def leaf7258Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi369InputQChi innerPair884Input
    leaf7258InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7258LowerChecked :
    lowerCheck 24 leaf7258Box leaf7258Inputs = true := by
  rfl'

private theorem leaf7258CoversExact : CoversExact 8
    leaf7258Box leaf7258Certificate leaf7258InnerLog leaf7258Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi369RoundedFacts
    innerPair884RoundedFacts leaf7258RoundedFacts (by rfl)

private theorem leaf7258FlatSound : Sound leaf7258Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7258CertificateValid
    leaf7258InnerLogValid leaf7258CoversExact leaf7258LowerChecked

private noncomputable def leaf7259Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (29/32), chiHi := (59/64) }

private noncomputable def leaf7259Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109105/67108864) }, vSqrt := { lower := (8191/8192), upper := (11452044627/11450748928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (298928073/268435456) }, upper := { exponent := 2, mantissa := (2341/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi369LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22902793555/22901497856) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7259InnerLog : WideLogData :=
  innerPair886Data

set_option maxRecDepth 1000000 in
private theorem leaf7259LocalValidity :
    LeafFacts leaf7259Box leaf7259Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7259Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452044627/11450748928) }) = true
      norm_num [leaf7259Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7259CertificateValid :
    WideCertificateValid leaf7259Box leaf7259Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi369ValidityFacts
    leaf7259LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7259CoverageChecked :
    coverageCheck (innerAD leaf7259Box) leaf7259InnerLog = true := by
  rfl'

private theorem leaf7259InnerLogValid :
    leaf7259InnerLog.Valid 8 (innerAD leaf7259Box) :=
  wideLogDataValid_of_cachedCheck endpoint591PositiveFacts
    endpoint601PositiveFacts.valid leaf7259CoverageChecked

private noncomputable def leaf7259InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5815015/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7259InputLogOnePlusV_eq :
    leaf7259InputLogOnePlusV = outerEnclosure 24
      (leaf7259Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7259RoundedFacts : LeafRoundedFacts 8
    leaf7259Certificate.logOnePlusV leaf7259InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7259InputLogOnePlusV_eq }

private noncomputable def leaf7259Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi369InputQChi innerPair886Input
    leaf7259InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7259LowerChecked :
    lowerCheck 24 leaf7259Box leaf7259Inputs = true := by
  rfl'

private theorem leaf7259CoversExact : CoversExact 8
    leaf7259Box leaf7259Certificate leaf7259InnerLog leaf7259Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi369RoundedFacts
    innerPair886RoundedFacts leaf7259RoundedFacts (by rfl)

private theorem leaf7259FlatSound : Sound leaf7259Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7259CertificateValid
    leaf7259InnerLogValid leaf7259CoversExact leaf7259LowerChecked

private noncomputable def leaf7260Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (59/64), chiHi := (15/16) }

private noncomputable def leaf7260Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109105/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34352242688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (299059137/268435456) }, upper := { exponent := 2, mantissa := (1171/1024) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi370LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708376569/68704485376) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7260InnerLog : WideLogData :=
  innerPair886Data

set_option maxRecDepth 1000000 in
private theorem leaf7260LocalValidity :
    LeafFacts leaf7260Box leaf7260Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7260Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34352242688) }) = true
      norm_num [leaf7260Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7260CertificateValid :
    WideCertificateValid leaf7260Box leaf7260Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi370ValidityFacts
    leaf7260LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7260CoverageChecked :
    coverageCheck (innerAD leaf7260Box) leaf7260InnerLog = true := by
  rfl'

private theorem leaf7260InnerLogValid :
    leaf7260InnerLog.Valid 8 (innerAD leaf7260Box) :=
  wideLogDataValid_of_cachedCheck endpoint591PositiveFacts
    endpoint601PositiveFacts.valid leaf7260CoverageChecked

private noncomputable def leaf7260InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630031/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7260InputLogOnePlusV_eq :
    leaf7260InputLogOnePlusV = outerEnclosure 24
      (leaf7260Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7260RoundedFacts : LeafRoundedFacts 8
    leaf7260Certificate.logOnePlusV leaf7260InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7260InputLogOnePlusV_eq }

private noncomputable def leaf7260Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi370InputQChi innerPair886Input
    leaf7260InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7260LowerChecked :
    lowerCheck 24 leaf7260Box leaf7260Inputs = true := by
  rfl'

private theorem leaf7260CoversExact : CoversExact 8
    leaf7260Box leaf7260Certificate leaf7260InnerLog leaf7260Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi370RoundedFacts
    innerPair886RoundedFacts leaf7260RoundedFacts (by rfl)

private theorem leaf7260FlatSound : Sound leaf7260Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7260CertificateValid
    leaf7260InnerLogValid leaf7260CoversExact leaf7260LowerChecked

private noncomputable def leaf7261Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (59/64), chiHi := (15/16) }

private noncomputable def leaf7261Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109107/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34352119808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (302925523/268435456) }, upper := { exponent := 2, mantissa := (593/512) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi370LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708253689/68704239616) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7261InnerLog : WideLogData :=
  innerPair888Data

set_option maxRecDepth 1000000 in
private theorem leaf7261LocalValidity :
    LeafFacts leaf7261Box leaf7261Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7261Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34352119808) }) = true
      norm_num [leaf7261Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7261CertificateValid :
    WideCertificateValid leaf7261Box leaf7261Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi370ValidityFacts
    leaf7261LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7261CoverageChecked :
    coverageCheck (innerAD leaf7261Box) leaf7261InnerLog = true := by
  rfl'

private theorem leaf7261InnerLogValid :
    leaf7261InnerLog.Valid 8 (innerAD leaf7261Box) :=
  wideLogDataValid_of_cachedCheck endpoint592PositiveFacts
    endpoint602PositiveFacts.valid leaf7261CoverageChecked

private noncomputable def leaf7261InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630061/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7261InputLogOnePlusV_eq :
    leaf7261InputLogOnePlusV = outerEnclosure 24
      (leaf7261Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7261RoundedFacts : LeafRoundedFacts 8
    leaf7261Certificate.logOnePlusV leaf7261InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7261InputLogOnePlusV_eq }

private noncomputable def leaf7261Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi370InputQChi innerPair888Input
    leaf7261InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7261LowerChecked :
    lowerCheck 24 leaf7261Box leaf7261Inputs = true := by
  rfl'

private theorem leaf7261CoversExact : CoversExact 8
    leaf7261Box leaf7261Certificate leaf7261InnerLog leaf7261Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi370RoundedFacts
    innerPair888RoundedFacts leaf7261RoundedFacts (by rfl)

private theorem leaf7261FlatSound : Sound leaf7261Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7261CertificateValid
    leaf7261InnerLogValid leaf7261CoversExact leaf7261LowerChecked

private noncomputable def leaf7262Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (7/8), chiHi := (57/64) }

private noncomputable def leaf7262Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109103/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34352384000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (294602963/268435456) }, upper := { exponent := 2, mantissa := (4615/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi367LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708517881/68704768000) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7262InnerLog : WideLogData :=
  innerPair884Data

set_option maxRecDepth 1000000 in
private theorem leaf7262LocalValidity :
    LeafFacts leaf7262Box leaf7262Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7262Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34352384000) }) = true
      norm_num [leaf7262Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7262CertificateValid :
    WideCertificateValid leaf7262Box leaf7262Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi367ValidityFacts
    leaf7262LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7262CoverageChecked :
    coverageCheck (innerAD leaf7262Box) leaf7262InnerLog = true := by
  rfl'

private theorem leaf7262InnerLogValid :
    leaf7262InnerLog.Valid 8 (innerAD leaf7262Box) :=
  wideLogDataValid_of_cachedCheck endpoint590PositiveFacts
    endpoint598PositiveFacts.valid leaf7262CoverageChecked

private noncomputable def leaf7262InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907499/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7262InputLogOnePlusV_eq :
    leaf7262InputLogOnePlusV = outerEnclosure 24
      (leaf7262Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7262RoundedFacts : LeafRoundedFacts 8
    leaf7262Certificate.logOnePlusV leaf7262InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7262InputLogOnePlusV_eq }

private noncomputable def leaf7262Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi367InputQChi innerPair884Input
    leaf7262InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7262LowerChecked :
    lowerCheck 24 leaf7262Box leaf7262Inputs = true := by
  rfl'

private theorem leaf7262CoversExact : CoversExact 8
    leaf7262Box leaf7262Certificate leaf7262InnerLog leaf7262Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi367RoundedFacts
    innerPair884RoundedFacts leaf7262RoundedFacts (by rfl)

private theorem leaf7262FlatSound : Sound leaf7262Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7262CertificateValid
    leaf7262InnerLogValid leaf7262CoversExact leaf7262LowerChecked

private noncomputable def leaf7263Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (7/8), chiHi := (57/64) }

private noncomputable def leaf7263Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109105/67108864) }, vSqrt := { lower := (65527/65536), upper := (34356133881/34352267264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (298272753/268435456) }, upper := { exponent := 2, mantissa := (73/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi367LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68708401145/68704534528) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7263InnerLog : WideLogData :=
  innerPair885Data

set_option maxRecDepth 1000000 in
private theorem leaf7263LocalValidity :
    LeafFacts leaf7263Box leaf7263Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7263Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34356133881/34352267264) }) = true
      norm_num [leaf7263Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7263CertificateValid :
    WideCertificateValid leaf7263Box leaf7263Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi367ValidityFacts
    leaf7263LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7263CoverageChecked :
    coverageCheck (innerAD leaf7263Box) leaf7263InnerLog = true := by
  rfl'

private theorem leaf7263InnerLogValid :
    leaf7263InnerLog.Valid 8 (innerAD leaf7263Box) :=
  wideLogDataValid_of_cachedCheck endpoint591PositiveFacts
    endpoint598PositiveFacts.valid leaf7263CoverageChecked

private noncomputable def leaf7263InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11630025/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7263InputLogOnePlusV_eq :
    leaf7263InputLogOnePlusV = outerEnclosure 24
      (leaf7263Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7263RoundedFacts : LeafRoundedFacts 8
    leaf7263Certificate.logOnePlusV leaf7263InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7263InputLogOnePlusV_eq }

private noncomputable def leaf7263Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi367InputQChi innerPair885Input
    leaf7263InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7263LowerChecked :
    lowerCheck 24 leaf7263Box leaf7263Inputs = true := by
  rfl'

private theorem leaf7263CoversExact : CoversExact 8
    leaf7263Box leaf7263Certificate leaf7263InnerLog leaf7263Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi367RoundedFacts
    innerPair885RoundedFacts leaf7263RoundedFacts (by rfl)

private theorem leaf7263FlatSound : Sound leaf7263Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7263CertificateValid
    leaf7263InnerLogValid leaf7263CoversExact leaf7263LowerChecked

private noncomputable def leaf7264Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (57/64), chiHi := (29/32) }

private noncomputable def leaf7264Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109105/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34352254976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (298665945/268435456) }, upper := { exponent := 2, mantissa := (2339/2048) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi368LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708388857/68704509952) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7264InnerLog : WideLogData :=
  innerPair886Data

set_option maxRecDepth 1000000 in
private theorem leaf7264LocalValidity :
    LeafFacts leaf7264Box leaf7264Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7264Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34352254976) }) = true
      norm_num [leaf7264Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7264CertificateValid :
    WideCertificateValid leaf7264Box leaf7264Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi368ValidityFacts
    leaf7264LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7264CoverageChecked :
    coverageCheck (innerAD leaf7264Box) leaf7264InnerLog = true := by
  rfl'

private theorem leaf7264InnerLogValid :
    leaf7264InnerLog.Valid 8 (innerAD leaf7264Box) :=
  wideLogDataValid_of_cachedCheck endpoint591PositiveFacts
    endpoint601PositiveFacts.valid leaf7264CoverageChecked

private noncomputable def leaf7264InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907507/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7264InputLogOnePlusV_eq :
    leaf7264InputLogOnePlusV = outerEnclosure 24
      (leaf7264Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7264RoundedFacts : LeafRoundedFacts 8
    leaf7264Certificate.logOnePlusV leaf7264InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7264InputLogOnePlusV_eq }

private noncomputable def leaf7264Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi368InputQChi innerPair886Input
    leaf7264InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7264LowerChecked :
    lowerCheck 24 leaf7264Box leaf7264Inputs = true := by
  rfl'

private theorem leaf7264CoversExact : CoversExact 8
    leaf7264Box leaf7264Certificate leaf7264InnerLog leaf7264Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi368RoundedFacts
    innerPair886RoundedFacts leaf7264RoundedFacts (by rfl)

private theorem leaf7264FlatSound : Sound leaf7264Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7264CertificateValid
    leaf7264InnerLogValid leaf7264CoversExact leaf7264LowerChecked

private noncomputable def leaf7265Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (57/64), chiHi := (29/32) }

private noncomputable def leaf7265Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109107/67108864) }, vSqrt := { lower := (65527/65536), upper := (11452044627/11450712064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (302401267/268435456) }, upper := { exponent := 2, mantissa := (37/32) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi368LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (22902756691/22901424128) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7265InnerLog : WideLogData :=
  innerPair887Data

set_option maxRecDepth 1000000 in
private theorem leaf7265LocalValidity :
    LeafFacts leaf7265Box leaf7265Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7265Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (11452044627/11450712064) }) = true
      norm_num [leaf7265Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7265CertificateValid :
    WideCertificateValid leaf7265Box leaf7265Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi368ValidityFacts
    leaf7265LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7265CoverageChecked :
    coverageCheck (innerAD leaf7265Box) leaf7265InnerLog = true := by
  rfl'

private theorem leaf7265InnerLogValid :
    leaf7265InnerLog.Valid 8 (innerAD leaf7265Box) :=
  wideLogDataValid_of_cachedCheck endpoint592PositiveFacts
    endpoint601PositiveFacts.valid leaf7265CoverageChecked

private noncomputable def leaf7265InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11630057/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7265InputLogOnePlusV_eq :
    leaf7265InputLogOnePlusV = outerEnclosure 24
      (leaf7265Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7265RoundedFacts : LeafRoundedFacts 8
    leaf7265Certificate.logOnePlusV leaf7265InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7265InputLogOnePlusV_eq }

private noncomputable def leaf7265Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi368InputQChi innerPair887Input
    leaf7265InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7265LowerChecked :
    lowerCheck 24 leaf7265Box leaf7265Inputs = true := by
  rfl'

private theorem leaf7265CoversExact : CoversExact 8
    leaf7265Box leaf7265Certificate leaf7265InnerLog leaf7265Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi368RoundedFacts
    innerPair887RoundedFacts leaf7265RoundedFacts (by rfl)

private theorem leaf7265FlatSound : Sound leaf7265Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7265CertificateValid
    leaf7265InnerLogValid leaf7265CoversExact leaf7265LowerChecked

private noncomputable def leaf7266Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (29/32), chiHi := (59/64) }

private noncomputable def leaf7266Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109107/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34352125952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (302728927/268435456) }, upper := { exponent := 2, mantissa := (4741/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi369LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708259833/68704251904) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7266InnerLog : WideLogData :=
  innerPair888Data

set_option maxRecDepth 1000000 in
private theorem leaf7266LocalValidity :
    LeafFacts leaf7266Box leaf7266Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7266Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34352125952) }) = true
      norm_num [leaf7266Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7266CertificateValid :
    WideCertificateValid leaf7266Box leaf7266Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi369ValidityFacts
    leaf7266LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7266CoverageChecked :
    coverageCheck (innerAD leaf7266Box) leaf7266InnerLog = true := by
  rfl'

private theorem leaf7266InnerLogValid :
    leaf7266InnerLog.Valid 8 (innerAD leaf7266Box) :=
  wideLogDataValid_of_cachedCheck endpoint592PositiveFacts
    endpoint602PositiveFacts.valid leaf7266CoverageChecked

private noncomputable def leaf7266InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630059/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7266InputLogOnePlusV_eq :
    leaf7266InputLogOnePlusV = outerEnclosure 24
      (leaf7266Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7266RoundedFacts : LeafRoundedFacts 8
    leaf7266Certificate.logOnePlusV leaf7266InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7266InputLogOnePlusV_eq }

private noncomputable def leaf7266Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi369InputQChi innerPair888Input
    leaf7266InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7266LowerChecked :
    lowerCheck 24 leaf7266Box leaf7266Inputs = true := by
  rfl'

private theorem leaf7266CoversExact : CoversExact 8
    leaf7266Box leaf7266Certificate leaf7266InnerLog leaf7266Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi369RoundedFacts
    innerPair888RoundedFacts leaf7266RoundedFacts (by rfl)

private theorem leaf7266FlatSound : Sound leaf7266Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7266CertificateValid
    leaf7266InnerLogValid leaf7266CoversExact leaf7266LowerChecked

private noncomputable def leaf7267Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (29/32), chiHi := (59/64) }

private noncomputable def leaf7267Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109109/67108864) }, vSqrt := { lower := (65527/65536), upper := (34356133881/34352005120) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (306529781/268435456) }, upper := { exponent := 2, mantissa := (75/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi369LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68708139001/68704010240) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7267InnerLog : WideLogData :=
  innerPair892Data

set_option maxRecDepth 1000000 in
private theorem leaf7267LocalValidity :
    LeafFacts leaf7267Box leaf7267Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7267Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34356133881/34352005120) }) = true
      norm_num [leaf7267Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7267CertificateValid :
    WideCertificateValid leaf7267Box leaf7267Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi369ValidityFacts
    leaf7267LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7267CoverageChecked :
    coverageCheck (innerAD leaf7267Box) leaf7267InnerLog = true := by
  rfl'

private theorem leaf7267InnerLogValid :
    leaf7267InnerLog.Valid 8 (innerAD leaf7267Box) :=
  wideLogDataValid_of_cachedCheck endpoint598PositiveFacts
    endpoint602PositiveFacts.valid leaf7267CoverageChecked

private noncomputable def leaf7267InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11630089/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7267InputLogOnePlusV_eq :
    leaf7267InputLogOnePlusV = outerEnclosure 24
      (leaf7267Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7267RoundedFacts : LeafRoundedFacts 8
    leaf7267Certificate.logOnePlusV leaf7267InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7267InputLogOnePlusV_eq }

private noncomputable def leaf7267Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi369InputQChi innerPair892Input
    leaf7267InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7267LowerChecked :
    lowerCheck 24 leaf7267Box leaf7267Inputs = true := by
  rfl'

private theorem leaf7267CoversExact : CoversExact 8
    leaf7267Box leaf7267Certificate leaf7267InnerLog leaf7267Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi369RoundedFacts
    innerPair892RoundedFacts leaf7267RoundedFacts (by rfl)

private theorem leaf7267FlatSound : Sound leaf7267Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7267CertificateValid
    leaf7267InnerLogValid leaf7267CoversExact leaf7267LowerChecked

private noncomputable def leaf7268Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (59/64), chiHi := (15/16) }

private noncomputable def leaf7268Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109109/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34351996928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (306791909/268435456) }, upper := { exponent := 2, mantissa := (1201/1024) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi370LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708130809/68703993856) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7268InnerLog : WideLogData :=
  innerPair893Data

set_option maxRecDepth 1000000 in
private theorem leaf7268LocalValidity :
    LeafFacts leaf7268Box leaf7268Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7268Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34351996928) }) = true
      norm_num [leaf7268Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7268CertificateValid :
    WideCertificateValid leaf7268Box leaf7268Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi370ValidityFacts
    leaf7268LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7268CoverageChecked :
    coverageCheck (innerAD leaf7268Box) leaf7268InnerLog = true := by
  rfl'

private theorem leaf7268InnerLogValid :
    leaf7268InnerLog.Valid 8 (innerAD leaf7268Box) :=
  wideLogDataValid_of_cachedCheck endpoint598PositiveFacts
    endpoint603PositiveFacts.valid leaf7268CoverageChecked

private noncomputable def leaf7268InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630091/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7268InputLogOnePlusV_eq :
    leaf7268InputLogOnePlusV = outerEnclosure 24
      (leaf7268Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7268RoundedFacts : LeafRoundedFacts 8
    leaf7268Certificate.logOnePlusV leaf7268InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7268InputLogOnePlusV_eq }

private noncomputable def leaf7268Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi370InputQChi innerPair893Input
    leaf7268InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7268LowerChecked :
    lowerCheck 24 leaf7268Box leaf7268Inputs = true := by
  rfl'

private theorem leaf7268CoversExact : CoversExact 8
    leaf7268Box leaf7268Certificate leaf7268InnerLog leaf7268Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi370RoundedFacts
    innerPair893RoundedFacts leaf7268RoundedFacts (by rfl)

private theorem leaf7268FlatSound : Sound leaf7268Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7268CertificateValid
    leaf7268InnerLogValid leaf7268CoversExact leaf7268LowerChecked

private noncomputable def leaf7269Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (59/64), chiHi := (15/16) }

private noncomputable def leaf7269Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109111/67108864) }, vSqrt := { lower := (65527/65536), upper := (34356133881/34351874048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (310658295/268435456) }, upper := { exponent := 2, mantissa := (19/16) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi370LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68708007929/68703748096) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7269InnerLog : WideLogData :=
  innerPair895Data

set_option maxRecDepth 1000000 in
private theorem leaf7269LocalValidity :
    LeafFacts leaf7269Box leaf7269Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7269Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34356133881/34351874048) }) = true
      norm_num [leaf7269Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7269CertificateValid :
    WideCertificateValid leaf7269Box leaf7269Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi370ValidityFacts
    leaf7269LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7269CoverageChecked :
    coverageCheck (innerAD leaf7269Box) leaf7269InnerLog = true := by
  rfl'

private theorem leaf7269InnerLogValid :
    leaf7269InnerLog.Valid 8 (innerAD leaf7269Box) :=
  wideLogDataValid_of_cachedCheck endpoint601PositiveFacts
    endpoint603PositiveFacts.valid leaf7269CoverageChecked

private noncomputable def leaf7269InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11630121/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7269InputLogOnePlusV_eq :
    leaf7269InputLogOnePlusV = outerEnclosure 24
      (leaf7269Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7269RoundedFacts : LeafRoundedFacts 8
    leaf7269Certificate.logOnePlusV leaf7269InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7269InputLogOnePlusV_eq }

private noncomputable def leaf7269Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi370InputQChi innerPair895Input
    leaf7269InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7269LowerChecked :
    lowerCheck 24 leaf7269Box leaf7269Inputs = true := by
  rfl'

private theorem leaf7269CoversExact : CoversExact 8
    leaf7269Box leaf7269Certificate leaf7269InnerLog leaf7269Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi370RoundedFacts
    innerPair895RoundedFacts leaf7269RoundedFacts (by rfl)

private theorem leaf7269FlatSound : Sound leaf7269Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7269CertificateValid
    leaf7269InnerLogValid leaf7269CoversExact leaf7269LowerChecked

private noncomputable def leaf7270Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (15/16), chiHi := (61/64) }

private noncomputable def leaf7270Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109107/67108864) }, vSqrt := { lower := (8191/8192), upper := (11452044627/11450705920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (302991055/268435456) }, upper := { exponent := 2, mantissa := (4745/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi371LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22902750547/22901411840) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7270InnerLog : WideLogData :=
  innerPair888Data

set_option maxRecDepth 1000000 in
private theorem leaf7270LocalValidity :
    LeafFacts leaf7270Box leaf7270Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7270Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452044627/11450705920) }) = true
      norm_num [leaf7270Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7270CertificateValid :
    WideCertificateValid leaf7270Box leaf7270Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi371ValidityFacts
    leaf7270LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7270CoverageChecked :
    coverageCheck (innerAD leaf7270Box) leaf7270InnerLog = true := by
  rfl'

private theorem leaf7270InnerLogValid :
    leaf7270InnerLog.Valid 8 (innerAD leaf7270Box) :=
  wideLogDataValid_of_cachedCheck endpoint592PositiveFacts
    endpoint602PositiveFacts.valid leaf7270CoverageChecked

private noncomputable def leaf7270InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630061/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7270InputLogOnePlusV_eq :
    leaf7270InputLogOnePlusV = outerEnclosure 24
      (leaf7270Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7270RoundedFacts : LeafRoundedFacts 8
    leaf7270Certificate.logOnePlusV leaf7270InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7270InputLogOnePlusV_eq }

private noncomputable def leaf7270Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi371InputQChi innerPair888Input
    leaf7270InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7270LowerChecked :
    lowerCheck 24 leaf7270Box leaf7270Inputs = true := by
  rfl'

private theorem leaf7270CoversExact : CoversExact 8
    leaf7270Box leaf7270Certificate leaf7270InnerLog leaf7270Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi371RoundedFacts
    innerPair888RoundedFacts leaf7270RoundedFacts (by rfl)

private theorem leaf7270FlatSound : Sound leaf7270Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7270CertificateValid
    leaf7270InnerLogValid leaf7270CoversExact leaf7270LowerChecked

private noncomputable def leaf7271Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (15/16), chiHi := (61/64) }

private noncomputable def leaf7271Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109109/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34351992832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (306922973/268435456) }, upper := { exponent := 2, mantissa := (2403/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi371LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708126713/68703985664) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7271InnerLog : WideLogData :=
  innerPair893Data

set_option maxRecDepth 1000000 in
private theorem leaf7271LocalValidity :
    LeafFacts leaf7271Box leaf7271Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7271Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34351992832) }) = true
      norm_num [leaf7271Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7271CertificateValid :
    WideCertificateValid leaf7271Box leaf7271Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi371ValidityFacts
    leaf7271LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7271CoverageChecked :
    coverageCheck (innerAD leaf7271Box) leaf7271InnerLog = true := by
  rfl'

private theorem leaf7271InnerLogValid :
    leaf7271InnerLog.Valid 8 (innerAD leaf7271Box) :=
  wideLogDataValid_of_cachedCheck endpoint598PositiveFacts
    endpoint603PositiveFacts.valid leaf7271CoverageChecked

private noncomputable def leaf7271InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907523/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7271InputLogOnePlusV_eq :
    leaf7271InputLogOnePlusV = outerEnclosure 24
      (leaf7271Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7271RoundedFacts : LeafRoundedFacts 8
    leaf7271Certificate.logOnePlusV leaf7271InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7271InputLogOnePlusV_eq }

private noncomputable def leaf7271Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi371InputQChi innerPair893Input
    leaf7271InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7271LowerChecked :
    lowerCheck 24 leaf7271Box leaf7271Inputs = true := by
  rfl'

private theorem leaf7271CoversExact : CoversExact 8
    leaf7271Box leaf7271Certificate leaf7271InnerLog leaf7271Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi371RoundedFacts
    innerPair893RoundedFacts leaf7271RoundedFacts (by rfl)

private theorem leaf7271FlatSound : Sound leaf7271Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7271CertificateValid
    leaf7271InnerLogValid leaf7271CoversExact leaf7271LowerChecked

private noncomputable def leaf7272Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (61/64), chiHi := (31/32) }

private noncomputable def leaf7272Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109109/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34351992832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (306922973/268435456) }, upper := { exponent := 2, mantissa := (2403/2048) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi372LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708126713/68703985664) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7272InnerLog : WideLogData :=
  innerPair893Data

set_option maxRecDepth 1000000 in
private theorem leaf7272LocalValidity :
    LeafFacts leaf7272Box leaf7272Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7272Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34351992832) }) = true
      norm_num [leaf7272Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7272CertificateValid :
    WideCertificateValid leaf7272Box leaf7272Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi372ValidityFacts
    leaf7272LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7272CoverageChecked :
    coverageCheck (innerAD leaf7272Box) leaf7272InnerLog = true := by
  rfl'

private theorem leaf7272InnerLogValid :
    leaf7272InnerLog.Valid 8 (innerAD leaf7272Box) :=
  wideLogDataValid_of_cachedCheck endpoint598PositiveFacts
    endpoint603PositiveFacts.valid leaf7272CoverageChecked

private noncomputable def leaf7272InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907523/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7272InputLogOnePlusV_eq :
    leaf7272InputLogOnePlusV = outerEnclosure 24
      (leaf7272Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7272RoundedFacts : LeafRoundedFacts 8
    leaf7272Certificate.logOnePlusV leaf7272InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7272InputLogOnePlusV_eq }

private noncomputable def leaf7272Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi372InputQChi innerPair893Input
    leaf7272InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7272LowerChecked :
    lowerCheck 24 leaf7272Box leaf7272Inputs = true := by
  rfl'

private theorem leaf7272CoversExact : CoversExact 8
    leaf7272Box leaf7272Certificate leaf7272InnerLog leaf7272Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi372RoundedFacts
    innerPair893RoundedFacts leaf7272RoundedFacts (by rfl)

private theorem leaf7272FlatSound : Sound leaf7272Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7272CertificateValid
    leaf7272InnerLogValid leaf7272CoversExact leaf7272LowerChecked

private noncomputable def leaf7273Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (61/64), chiHi := (31/32) }

private noncomputable def leaf7273Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109111/67108864) }, vSqrt := { lower := (8191/8192), upper := (1272449403/1272291328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (310920423/268435456) }, upper := { exponent := 2, mantissa := (1217/1024) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi372LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2544740731/2544582656) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7273InnerLog : WideLogData :=
  innerPair896Data

set_option maxRecDepth 1000000 in
private theorem leaf7273LocalValidity :
    LeafFacts leaf7273Box leaf7273Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7273Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1272449403/1272291328) }) = true
      norm_num [leaf7273Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7273CertificateValid :
    WideCertificateValid leaf7273Box leaf7273Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi372ValidityFacts
    leaf7273LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7273CoverageChecked :
    coverageCheck (innerAD leaf7273Box) leaf7273InnerLog = true := by
  rfl'

private theorem leaf7273InnerLogValid :
    leaf7273InnerLog.Valid 8 (innerAD leaf7273Box) :=
  wideLogDataValid_of_cachedCheck endpoint601PositiveFacts
    endpoint604PositiveFacts.valid leaf7273CoverageChecked

private noncomputable def leaf7273InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630123/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7273InputLogOnePlusV_eq :
    leaf7273InputLogOnePlusV = outerEnclosure 24
      (leaf7273Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7273RoundedFacts : LeafRoundedFacts 8
    leaf7273Certificate.logOnePlusV leaf7273InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7273InputLogOnePlusV_eq }

private noncomputable def leaf7273Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi372InputQChi innerPair896Input
    leaf7273InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7273LowerChecked :
    lowerCheck 24 leaf7273Box leaf7273Inputs = true := by
  rfl'

private theorem leaf7273CoversExact : CoversExact 8
    leaf7273Box leaf7273Certificate leaf7273InnerLog leaf7273Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi372RoundedFacts
    innerPair896RoundedFacts leaf7273RoundedFacts (by rfl)

private theorem leaf7273FlatSound : Sound leaf7273Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7273CertificateValid
    leaf7273InnerLogValid leaf7273CoversExact leaf7273LowerChecked

private noncomputable def leaf7274Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (31/32), chiHi := (63/64) }

private noncomputable def leaf7274Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109111/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34351867904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (310854891/268435456) }, upper := { exponent := 2, mantissa := (4867/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi373LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708001785/68703735808) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7274InnerLog : WideLogData :=
  innerPair896Data

set_option maxRecDepth 1000000 in
private theorem leaf7274LocalValidity :
    LeafFacts leaf7274Box leaf7274Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7274Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34351867904) }) = true
      norm_num [leaf7274Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7274CertificateValid :
    WideCertificateValid leaf7274Box leaf7274Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi373ValidityFacts
    leaf7274LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7274CoverageChecked :
    coverageCheck (innerAD leaf7274Box) leaf7274InnerLog = true := by
  rfl'

private theorem leaf7274InnerLogValid :
    leaf7274InnerLog.Valid 8 (innerAD leaf7274Box) :=
  wideLogDataValid_of_cachedCheck endpoint601PositiveFacts
    endpoint604PositiveFacts.valid leaf7274CoverageChecked

private noncomputable def leaf7274InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5815061/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7274InputLogOnePlusV_eq :
    leaf7274InputLogOnePlusV = outerEnclosure 24
      (leaf7274Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7274RoundedFacts : LeafRoundedFacts 8
    leaf7274Certificate.logOnePlusV leaf7274InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7274InputLogOnePlusV_eq }

private noncomputable def leaf7274Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi373InputQChi innerPair896Input
    leaf7274InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7274LowerChecked :
    lowerCheck 24 leaf7274Box leaf7274Inputs = true := by
  rfl'

private theorem leaf7274CoversExact : CoversExact 8
    leaf7274Box leaf7274Certificate leaf7274InnerLog leaf7274Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi373RoundedFacts
    innerPair896RoundedFacts leaf7274RoundedFacts (by rfl)

private theorem leaf7274FlatSound : Sound leaf7274Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7274CertificateValid
    leaf7274InnerLogValid leaf7274CoversExact leaf7274LowerChecked

private noncomputable def leaf7275Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (31/32), chiHi := (63/64) }

private noncomputable def leaf7275Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109113/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34351738880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (314917873/268435456) }, upper := { exponent := 2, mantissa := (2465/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi373LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68707872761/68703477760) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7275InnerLog : WideLogData :=
  innerPair898Data

set_option maxRecDepth 1000000 in
private theorem leaf7275LocalValidity :
    LeafFacts leaf7275Box leaf7275Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7275Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34351738880) }) = true
      norm_num [leaf7275Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7275CertificateValid :
    WideCertificateValid leaf7275Box leaf7275Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi373ValidityFacts
    leaf7275LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7275CoverageChecked :
    coverageCheck (innerAD leaf7275Box) leaf7275InnerLog = true := by
  rfl'

private theorem leaf7275InnerLogValid :
    leaf7275InnerLog.Valid 8 (innerAD leaf7275Box) :=
  wideLogDataValid_of_cachedCheck endpoint602PositiveFacts
    endpoint605PositiveFacts.valid leaf7275CoverageChecked

private noncomputable def leaf7275InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5815077/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7275InputLogOnePlusV_eq :
    leaf7275InputLogOnePlusV = outerEnclosure 24
      (leaf7275Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7275RoundedFacts : LeafRoundedFacts 8
    leaf7275Certificate.logOnePlusV leaf7275InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7275InputLogOnePlusV_eq }

private noncomputable def leaf7275Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi373InputQChi innerPair898Input
    leaf7275InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7275LowerChecked :
    lowerCheck 24 leaf7275Box leaf7275Inputs = true := by
  rfl'

private theorem leaf7275CoversExact : CoversExact 8
    leaf7275Box leaf7275Certificate leaf7275InnerLog leaf7275Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi373RoundedFacts
    innerPair898RoundedFacts leaf7275RoundedFacts (by rfl)

private theorem leaf7275FlatSound : Sound leaf7275Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7275CertificateValid
    leaf7275InnerLogValid leaf7275CoversExact leaf7275LowerChecked

private noncomputable def leaf7276Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (63/64), chiHi := (1) }

private noncomputable def leaf7276Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109113/67108864) }, vSqrt := { lower := (8191/8192), upper := (11452044627/11450580992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (314786809/268435456) }, upper := { exponent := 2, mantissa := (77/64) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi374LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22902625619/22901161984) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf7276InnerLog : WideLogData :=
  innerPair897Data

set_option maxRecDepth 1000000 in
private theorem leaf7276LocalValidity :
    LeafFacts leaf7276Box leaf7276Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7276Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452044627/11450580992) }) = true
      norm_num [leaf7276Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7276CertificateValid :
    WideCertificateValid leaf7276Box leaf7276Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi374ValidityFacts
    leaf7276LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7276CoverageChecked :
    coverageCheck (innerAD leaf7276Box) leaf7276InnerLog = true := by
  rfl'

private theorem leaf7276InnerLogValid :
    leaf7276InnerLog.Valid 8 (innerAD leaf7276Box) :=
  wideLogDataValid_of_cachedCheck endpoint602PositiveFacts
    endpoint604PositiveFacts.valid leaf7276CoverageChecked

private noncomputable def leaf7276InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630153/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7276InputLogOnePlusV_eq :
    leaf7276InputLogOnePlusV = outerEnclosure 24
      (leaf7276Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7276RoundedFacts : LeafRoundedFacts 8
    leaf7276Certificate.logOnePlusV leaf7276InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7276InputLogOnePlusV_eq }

private noncomputable def leaf7276Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi374InputQChi innerPair897Input
    leaf7276InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7276LowerChecked :
    lowerCheck 24 leaf7276Box leaf7276Inputs = true := by
  rfl'

private theorem leaf7276CoversExact : CoversExact 8
    leaf7276Box leaf7276Certificate leaf7276InnerLog leaf7276Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi374RoundedFacts
    innerPair897RoundedFacts leaf7276RoundedFacts (by rfl)

private theorem leaf7276FlatSound : Sound leaf7276Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7276CertificateValid
    leaf7276InnerLogValid leaf7276CoversExact leaf7276LowerChecked

private noncomputable def leaf7277Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (63/64), chiHi := (1) }

private noncomputable def leaf7277Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109115/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34351611904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (318915323/268435456) }, upper := { exponent := 2, mantissa := (39/32) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi374LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68707745785/68703223808) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf7277InnerLog : WideLogData :=
  innerPair899Data

set_option maxRecDepth 1000000 in
private theorem leaf7277LocalValidity :
    LeafFacts leaf7277Box leaf7277Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7277Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34351611904) }) = true
      norm_num [leaf7277Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7277CertificateValid :
    WideCertificateValid leaf7277Box leaf7277Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi374ValidityFacts
    leaf7277LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7277CoverageChecked :
    coverageCheck (innerAD leaf7277Box) leaf7277InnerLog = true := by
  rfl'

private theorem leaf7277InnerLogValid :
    leaf7277InnerLog.Valid 8 (innerAD leaf7277Box) :=
  wideLogDataValid_of_cachedCheck endpoint603PositiveFacts
    endpoint605PositiveFacts.valid leaf7277CoverageChecked

private noncomputable def leaf7277InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630185/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7277InputLogOnePlusV_eq :
    leaf7277InputLogOnePlusV = outerEnclosure 24
      (leaf7277Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7277RoundedFacts : LeafRoundedFacts 8
    leaf7277Certificate.logOnePlusV leaf7277InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7277InputLogOnePlusV_eq }

private noncomputable def leaf7277Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi374InputQChi innerPair899Input
    leaf7277InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7277LowerChecked :
    lowerCheck 24 leaf7277Box leaf7277Inputs = true := by
  rfl'

private theorem leaf7277CoversExact : CoversExact 8
    leaf7277Box leaf7277Certificate leaf7277InnerLog leaf7277Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi374RoundedFacts
    innerPair899RoundedFacts leaf7277RoundedFacts (by rfl)

private theorem leaf7277FlatSound : Sound leaf7277Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7277CertificateValid
    leaf7277InnerLogValid leaf7277CoversExact leaf7277LowerChecked

private noncomputable def leaf7278Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (15/16), chiHi := (61/64) }

private noncomputable def leaf7278Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109111/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34351867904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (310854891/268435456) }, upper := { exponent := 2, mantissa := (4867/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi371LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68708001785/68703735808) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7278InnerLog : WideLogData :=
  innerPair896Data

set_option maxRecDepth 1000000 in
private theorem leaf7278LocalValidity :
    LeafFacts leaf7278Box leaf7278Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7278Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34351867904) }) = true
      norm_num [leaf7278Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7278CertificateValid :
    WideCertificateValid leaf7278Box leaf7278Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi371ValidityFacts
    leaf7278LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7278CoverageChecked :
    coverageCheck (innerAD leaf7278Box) leaf7278InnerLog = true := by
  rfl'

private theorem leaf7278InnerLogValid :
    leaf7278InnerLog.Valid 8 (innerAD leaf7278Box) :=
  wideLogDataValid_of_cachedCheck endpoint601PositiveFacts
    endpoint604PositiveFacts.valid leaf7278CoverageChecked

private noncomputable def leaf7278InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5815061/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7278InputLogOnePlusV_eq :
    leaf7278InputLogOnePlusV = outerEnclosure 24
      (leaf7278Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7278RoundedFacts : LeafRoundedFacts 8
    leaf7278Certificate.logOnePlusV leaf7278InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7278InputLogOnePlusV_eq }

private noncomputable def leaf7278Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi371InputQChi innerPair896Input
    leaf7278InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7278LowerChecked :
    lowerCheck 24 leaf7278Box leaf7278Inputs = true := by
  rfl'

private theorem leaf7278CoversExact : CoversExact 8
    leaf7278Box leaf7278Certificate leaf7278InnerLog leaf7278Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi371RoundedFacts
    innerPair896RoundedFacts leaf7278RoundedFacts (by rfl)

private theorem leaf7278FlatSound : Sound leaf7278Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7278CertificateValid
    leaf7278InnerLogValid leaf7278CoversExact leaf7278LowerChecked

private noncomputable def leaf7279Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (15/16), chiHi := (61/64) }

private noncomputable def leaf7279Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109113/67108864) }, vSqrt := { lower := (65527/65536), upper := (11452044627/11450580992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (314786809/268435456) }, upper := { exponent := 2, mantissa := (77/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi371LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (22902625619/22901161984) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7279InnerLog : WideLogData :=
  innerPair897Data

set_option maxRecDepth 1000000 in
private theorem leaf7279LocalValidity :
    LeafFacts leaf7279Box leaf7279Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7279Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (11452044627/11450580992) }) = true
      norm_num [leaf7279Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7279CertificateValid :
    WideCertificateValid leaf7279Box leaf7279Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi371ValidityFacts
    leaf7279LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7279CoverageChecked :
    coverageCheck (innerAD leaf7279Box) leaf7279InnerLog = true := by
  rfl'

private theorem leaf7279InnerLogValid :
    leaf7279InnerLog.Valid 8 (innerAD leaf7279Box) :=
  wideLogDataValid_of_cachedCheck endpoint602PositiveFacts
    endpoint604PositiveFacts.valid leaf7279CoverageChecked

private noncomputable def leaf7279InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11630153/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7279InputLogOnePlusV_eq :
    leaf7279InputLogOnePlusV = outerEnclosure 24
      (leaf7279Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7279RoundedFacts : LeafRoundedFacts 8
    leaf7279Certificate.logOnePlusV leaf7279InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7279InputLogOnePlusV_eq }

private noncomputable def leaf7279Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi371InputQChi innerPair897Input
    leaf7279InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7279LowerChecked :
    lowerCheck 24 leaf7279Box leaf7279Inputs = true := by
  rfl'

private theorem leaf7279CoversExact : CoversExact 8
    leaf7279Box leaf7279Certificate leaf7279InnerLog leaf7279Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi371RoundedFacts
    innerPair897RoundedFacts leaf7279RoundedFacts (by rfl)

private theorem leaf7279FlatSound : Sound leaf7279Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7279CertificateValid
    leaf7279InnerLogValid leaf7279CoversExact leaf7279LowerChecked

private noncomputable def leaf7280Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (61/64), chiHi := (31/32) }

private noncomputable def leaf7280Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109113/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34351738880) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (314917873/268435456) }, upper := { exponent := 2, mantissa := (2465/2048) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi372LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68707872761/68703477760) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7280InnerLog : WideLogData :=
  innerPair898Data

set_option maxRecDepth 1000000 in
private theorem leaf7280LocalValidity :
    LeafFacts leaf7280Box leaf7280Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7280Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34351738880) }) = true
      norm_num [leaf7280Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7280CertificateValid :
    WideCertificateValid leaf7280Box leaf7280Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi372ValidityFacts
    leaf7280LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7280CoverageChecked :
    coverageCheck (innerAD leaf7280Box) leaf7280InnerLog = true := by
  rfl'

private theorem leaf7280InnerLogValid :
    leaf7280InnerLog.Valid 8 (innerAD leaf7280Box) :=
  wideLogDataValid_of_cachedCheck endpoint602PositiveFacts
    endpoint605PositiveFacts.valid leaf7280CoverageChecked

private noncomputable def leaf7280InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5815077/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7280InputLogOnePlusV_eq :
    leaf7280InputLogOnePlusV = outerEnclosure 24
      (leaf7280Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7280RoundedFacts : LeafRoundedFacts 8
    leaf7280Certificate.logOnePlusV leaf7280InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7280InputLogOnePlusV_eq }

private noncomputable def leaf7280Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi372InputQChi innerPair898Input
    leaf7280InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7280LowerChecked :
    lowerCheck 24 leaf7280Box leaf7280Inputs = true := by
  rfl'

private theorem leaf7280CoversExact : CoversExact 8
    leaf7280Box leaf7280Certificate leaf7280InnerLog leaf7280Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi372RoundedFacts
    innerPair898RoundedFacts leaf7280RoundedFacts (by rfl)

private theorem leaf7280FlatSound : Sound leaf7280Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7280CertificateValid
    leaf7280InnerLogValid leaf7280CoversExact leaf7280LowerChecked

private noncomputable def leaf7281Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (61/64), chiHi := (31/32) }

private noncomputable def leaf7281Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109115/67108864) }, vSqrt := { lower := (65527/65536), upper := (34356133881/34351611904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (318915323/268435456) }, upper := { exponent := 2, mantissa := (39/32) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi372LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68707745785/68703223808) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7281InnerLog : WideLogData :=
  innerPair899Data

set_option maxRecDepth 1000000 in
private theorem leaf7281LocalValidity :
    LeafFacts leaf7281Box leaf7281Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7281Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34356133881/34351611904) }) = true
      norm_num [leaf7281Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7281CertificateValid :
    WideCertificateValid leaf7281Box leaf7281Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi372ValidityFacts
    leaf7281LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7281CoverageChecked :
    coverageCheck (innerAD leaf7281Box) leaf7281InnerLog = true := by
  rfl'

private theorem leaf7281InnerLogValid :
    leaf7281InnerLog.Valid 8 (innerAD leaf7281Box) :=
  wideLogDataValid_of_cachedCheck endpoint603PositiveFacts
    endpoint605PositiveFacts.valid leaf7281CoverageChecked

private noncomputable def leaf7281InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11630185/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7281InputLogOnePlusV_eq :
    leaf7281InputLogOnePlusV = outerEnclosure 24
      (leaf7281Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7281RoundedFacts : LeafRoundedFacts 8
    leaf7281Certificate.logOnePlusV leaf7281InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7281InputLogOnePlusV_eq }

private noncomputable def leaf7281Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi372InputQChi innerPair899Input
    leaf7281InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7281LowerChecked :
    lowerCheck 24 leaf7281Box leaf7281Inputs = true := by
  rfl'

private theorem leaf7281CoversExact : CoversExact 8
    leaf7281Box leaf7281Certificate leaf7281InnerLog leaf7281Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi372RoundedFacts
    innerPair899RoundedFacts leaf7281RoundedFacts (by rfl)

private theorem leaf7281FlatSound : Sound leaf7281Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7281CertificateValid
    leaf7281InnerLogValid leaf7281CoversExact leaf7281LowerChecked

private noncomputable def leaf7282Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (31/32), chiHi := (63/64) }

private noncomputable def leaf7282Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109115/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34351609856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (318980855/268435456) }, upper := { exponent := 2, mantissa := (4993/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi373LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68707743737/68703219712) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7282InnerLog : WideLogData :=
  innerPair900Data

set_option maxRecDepth 1000000 in
private theorem leaf7282LocalValidity :
    LeafFacts leaf7282Box leaf7282Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7282Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34351609856) }) = true
      norm_num [leaf7282Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7282CertificateValid :
    WideCertificateValid leaf7282Box leaf7282Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi373ValidityFacts
    leaf7282LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7282CoverageChecked :
    coverageCheck (innerAD leaf7282Box) leaf7282InnerLog = true := by
  rfl'

private theorem leaf7282InnerLogValid :
    leaf7282InnerLog.Valid 8 (innerAD leaf7282Box) :=
  wideLogDataValid_of_cachedCheck endpoint603PositiveFacts
    endpoint606PositiveFacts.valid leaf7282CoverageChecked

private noncomputable def leaf7282InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630185/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7282InputLogOnePlusV_eq :
    leaf7282InputLogOnePlusV = outerEnclosure 24
      (leaf7282Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7282RoundedFacts : LeafRoundedFacts 8
    leaf7282Certificate.logOnePlusV leaf7282InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7282InputLogOnePlusV_eq }

private noncomputable def leaf7282Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi373InputQChi innerPair900Input
    leaf7282InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7282LowerChecked :
    lowerCheck 24 leaf7282Box leaf7282Inputs = true := by
  rfl'

private theorem leaf7282CoversExact : CoversExact 8
    leaf7282Box leaf7282Certificate leaf7282InnerLog leaf7282Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi373RoundedFacts
    innerPair900RoundedFacts leaf7282RoundedFacts (by rfl)

private theorem leaf7282FlatSound : Sound leaf7282Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7282CertificateValid
    leaf7282InnerLogValid leaf7282CoversExact leaf7282LowerChecked

private noncomputable def leaf7283Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (31/32), chiHi := (63/64) }

private noncomputable def leaf7283Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109117/67108864) }, vSqrt := { lower := (65527/65536), upper := (34356133881/34351480832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (323043837/268435456) }, upper := { exponent := 2, mantissa := (79/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi373LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (68707614713/68702961664) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7283InnerLog : WideLogData :=
  innerPair901Data

set_option maxRecDepth 1000000 in
private theorem leaf7283LocalValidity :
    LeafFacts leaf7283Box leaf7283Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7283Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (34356133881/34351480832) }) = true
      norm_num [leaf7283Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7283CertificateValid :
    WideCertificateValid leaf7283Box leaf7283Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi373ValidityFacts
    leaf7283LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7283CoverageChecked :
    coverageCheck (innerAD leaf7283Box) leaf7283InnerLog = true := by
  rfl'

private theorem leaf7283InnerLogValid :
    leaf7283InnerLog.Valid 8 (innerAD leaf7283Box) :=
  wideLogDataValid_of_cachedCheck endpoint604PositiveFacts
    endpoint606PositiveFacts.valid leaf7283CoverageChecked

private noncomputable def leaf7283InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11630217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7283InputLogOnePlusV_eq :
    leaf7283InputLogOnePlusV = outerEnclosure 24
      (leaf7283Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7283RoundedFacts : LeafRoundedFacts 8
    leaf7283Certificate.logOnePlusV leaf7283InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7283InputLogOnePlusV_eq }

private noncomputable def leaf7283Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi373InputQChi innerPair901Input
    leaf7283InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7283LowerChecked :
    lowerCheck 24 leaf7283Box leaf7283Inputs = true := by
  rfl'

private theorem leaf7283CoversExact : CoversExact 8
    leaf7283Box leaf7283Certificate leaf7283InnerLog leaf7283Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi373RoundedFacts
    innerPair901RoundedFacts leaf7283RoundedFacts (by rfl)

private theorem leaf7283FlatSound : Sound leaf7283Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7283CertificateValid
    leaf7283InnerLogValid leaf7283CoversExact leaf7283LowerChecked

private noncomputable def leaf7284Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (63/64), chiHi := (1) }

private noncomputable def leaf7284Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (8191/8192), upper := (67109117/67108864) }, vSqrt := { lower := (8191/8192), upper := (34356133881/34351480832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (323043837/268435456) }, upper := { exponent := 2, mantissa := (79/64) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi374LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68707614713/68702961664) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf7284InnerLog : WideLogData :=
  innerPair901Data

set_option maxRecDepth 1000000 in
private theorem leaf7284LocalValidity :
    LeafFacts leaf7284Box leaf7284Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7284Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34356133881/34351480832) }) = true
      norm_num [leaf7284Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7284CertificateValid :
    WideCertificateValid leaf7284Box leaf7284Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi374ValidityFacts
    leaf7284LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7284CoverageChecked :
    coverageCheck (innerAD leaf7284Box) leaf7284InnerLog = true := by
  rfl'

private theorem leaf7284InnerLogValid :
    leaf7284InnerLog.Valid 8 (innerAD leaf7284Box) :=
  wideLogDataValid_of_cachedCheck endpoint604PositiveFacts
    endpoint606PositiveFacts.valid leaf7284CoverageChecked

private noncomputable def leaf7284InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11630217/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7284InputLogOnePlusV_eq :
    leaf7284InputLogOnePlusV = outerEnclosure 24
      (leaf7284Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7284RoundedFacts : LeafRoundedFacts 8
    leaf7284Certificate.logOnePlusV leaf7284InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7284InputLogOnePlusV_eq }

private noncomputable def leaf7284Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi374InputQChi innerPair901Input
    leaf7284InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7284LowerChecked :
    lowerCheck 24 leaf7284Box leaf7284Inputs = true := by
  rfl'

private theorem leaf7284CoversExact : CoversExact 8
    leaf7284Box leaf7284Certificate leaf7284InnerLog leaf7284Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi374RoundedFacts
    innerPair901RoundedFacts leaf7284RoundedFacts (by rfl)

private theorem leaf7284FlatSound : Sound leaf7284Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7284CertificateValid
    leaf7284InnerLogValid leaf7284CoversExact leaf7284LowerChecked

private noncomputable def leaf7285Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (63/64), chiHi := (1) }

private noncomputable def leaf7285Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65527/65536), upper := (67109119/67108864) }, vSqrt := { lower := (65527/65536), upper := (1431483733/1431306240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 2, mantissa := (327172351/268435456) }, upper := { exponent := 2, mantissa := (5/4) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi374LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (2862789973/2862612480) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf7285InnerLog : WideLogData :=
  innerPair902Data

set_option maxRecDepth 1000000 in
private theorem leaf7285LocalValidity :
    LeafFacts leaf7285Box leaf7285Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7285Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1431483733/1431306240) }) = true
      norm_num [leaf7285Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7285CertificateValid :
    WideCertificateValid leaf7285Box leaf7285Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi374ValidityFacts
    leaf7285LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7285CoverageChecked :
    coverageCheck (innerAD leaf7285Box) leaf7285InnerLog = true := by
  rfl'

private theorem leaf7285InnerLogValid :
    leaf7285InnerLog.Valid 8 (innerAD leaf7285Box) :=
  wideLogDataValid_of_cachedCheck endpoint605PositiveFacts
    endpoint607PositiveFacts.valid leaf7285CoverageChecked

private noncomputable def leaf7285InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11630121/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7285InputLogOnePlusV_eq :
    leaf7285InputLogOnePlusV = outerEnclosure 24
      (leaf7285Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7285RoundedFacts : LeafRoundedFacts 8
    leaf7285Certificate.logOnePlusV leaf7285InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7285InputLogOnePlusV_eq }

private noncomputable def leaf7285Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi374InputQChi innerPair902Input
    leaf7285InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7285LowerChecked :
    lowerCheck 24 leaf7285Box leaf7285Inputs = true := by
  rfl'

private theorem leaf7285CoversExact : CoversExact 8
    leaf7285Box leaf7285Certificate leaf7285InnerLog leaf7285Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi374RoundedFacts
    innerPair902RoundedFacts leaf7285RoundedFacts (by rfl)

private theorem leaf7285FlatSound : Sound leaf7285Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7285CertificateValid
    leaf7285InnerLogValid leaf7285CoversExact leaf7285LowerChecked

private noncomputable def component147Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (7/8), chiHi := (57/64) }

set_option maxRecDepth 1000000 in
private theorem component147Node0_sound : Sound component147Node0Box :=
  sound_of_literal_split component147Node0Box leaf7228Box leaf7229Box
    .k (57/16) (by rfl) (by rfl)
    leaf7228FlatSound leaf7229FlatSound

private noncomputable def component147Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (57/64), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component147Node1_sound : Sound component147Node1Box :=
  sound_of_literal_split component147Node1Box leaf7230Box leaf7231Box
    .k (57/16) (by rfl) (by rfl)
    leaf7230FlatSound leaf7231FlatSound

private noncomputable def component147Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (7/8), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component147Node2_sound : Sound component147Node2Box :=
  sound_of_literal_split component147Node2Box component147Node0Box component147Node1Box
    .chi (57/64) (by rfl) (by rfl)
    component147Node0_sound component147Node1_sound

private noncomputable def component147Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (29/32), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component147Node3_sound : Sound component147Node3Box :=
  sound_of_literal_split component147Node3Box leaf7232Box leaf7233Box
    .k (57/16) (by rfl) (by rfl)
    leaf7232FlatSound leaf7233FlatSound

private noncomputable def component147Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component147Node4_sound : Sound component147Node4Box :=
  sound_of_literal_split component147Node4Box component147Node2Box component147Node3Box
    .chi (29/32) (by rfl) (by rfl)
    component147Node2_sound component147Node3_sound

private noncomputable def component147Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (7/8), chiHi := (57/64) }

set_option maxRecDepth 1000000 in
private theorem component147Node5_sound : Sound component147Node5Box :=
  sound_of_literal_split component147Node5Box leaf7234Box leaf7235Box
    .k (59/16) (by rfl) (by rfl)
    leaf7234FlatSound leaf7235FlatSound

private noncomputable def component147Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (57/64), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component147Node6_sound : Sound component147Node6Box :=
  sound_of_literal_split component147Node6Box leaf7236Box leaf7237Box
    .k (59/16) (by rfl) (by rfl)
    leaf7236FlatSound leaf7237FlatSound

private noncomputable def component147Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (7/8), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component147Node7_sound : Sound component147Node7Box :=
  sound_of_literal_split component147Node7Box component147Node5Box component147Node6Box
    .chi (57/64) (by rfl) (by rfl)
    component147Node5_sound component147Node6_sound

private noncomputable def component147Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (29/32), chiHi := (59/64) }

set_option maxRecDepth 1000000 in
private theorem component147Node8_sound : Sound component147Node8Box :=
  sound_of_literal_split component147Node8Box leaf7238Box leaf7239Box
    .k (59/16) (by rfl) (by rfl)
    leaf7238FlatSound leaf7239FlatSound

private noncomputable def component147Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (59/64), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component147Node9_sound : Sound component147Node9Box :=
  sound_of_literal_split component147Node9Box leaf7240Box leaf7241Box
    .k (59/16) (by rfl) (by rfl)
    leaf7240FlatSound leaf7241FlatSound

private noncomputable def component147Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (29/32), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component147Node10_sound : Sound component147Node10Box :=
  sound_of_literal_split component147Node10Box component147Node8Box component147Node9Box
    .chi (59/64) (by rfl) (by rfl)
    component147Node8_sound component147Node9_sound

private noncomputable def component147Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component147Node11_sound : Sound component147Node11Box :=
  sound_of_literal_split component147Node11Box component147Node7Box component147Node10Box
    .chi (29/32) (by rfl) (by rfl)
    component147Node7_sound component147Node10_sound

private noncomputable def component147Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component147Node12_sound : Sound component147Node12Box :=
  sound_of_literal_split component147Node12Box component147Node4Box component147Node11Box
    .k (29/8) (by rfl) (by rfl)
    component147Node4_sound component147Node11_sound

private noncomputable def component147Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (15/16), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component147Node13_sound : Sound component147Node13Box :=
  sound_of_literal_split component147Node13Box leaf7242Box leaf7243Box
    .k (57/16) (by rfl) (by rfl)
    leaf7242FlatSound leaf7243FlatSound

private noncomputable def component147Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (31/32), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component147Node14_sound : Sound component147Node14Box :=
  sound_of_literal_split component147Node14Box leaf7244Box leaf7245Box
    .k (57/16) (by rfl) (by rfl)
    leaf7244FlatSound leaf7245FlatSound

private noncomputable def component147Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component147Node15_sound : Sound component147Node15Box :=
  sound_of_literal_split component147Node15Box component147Node13Box component147Node14Box
    .chi (31/32) (by rfl) (by rfl)
    component147Node13_sound component147Node14_sound

private noncomputable def component147Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (15/16), chiHi := (61/64) }

set_option maxRecDepth 1000000 in
private theorem component147Node16_sound : Sound component147Node16Box :=
  sound_of_literal_split component147Node16Box leaf7246Box leaf7247Box
    .k (59/16) (by rfl) (by rfl)
    leaf7246FlatSound leaf7247FlatSound

private noncomputable def component147Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (61/64), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component147Node17_sound : Sound component147Node17Box :=
  sound_of_literal_split component147Node17Box leaf7248Box leaf7249Box
    .k (59/16) (by rfl) (by rfl)
    leaf7248FlatSound leaf7249FlatSound

private noncomputable def component147Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (15/16), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component147Node18_sound : Sound component147Node18Box :=
  sound_of_literal_split component147Node18Box component147Node16Box component147Node17Box
    .chi (61/64) (by rfl) (by rfl)
    component147Node16_sound component147Node17_sound

private noncomputable def component147Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (31/32), chiHi := (63/64) }

set_option maxRecDepth 1000000 in
private theorem component147Node19_sound : Sound component147Node19Box :=
  sound_of_literal_split component147Node19Box leaf7250Box leaf7251Box
    .k (59/16) (by rfl) (by rfl)
    leaf7250FlatSound leaf7251FlatSound

private noncomputable def component147Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (63/64), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component147Node20_sound : Sound component147Node20Box :=
  sound_of_literal_split component147Node20Box leaf7252Box leaf7253Box
    .k (59/16) (by rfl) (by rfl)
    leaf7252FlatSound leaf7253FlatSound

private noncomputable def component147Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (31/32), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component147Node21_sound : Sound component147Node21Box :=
  sound_of_literal_split component147Node21Box component147Node19Box component147Node20Box
    .chi (63/64) (by rfl) (by rfl)
    component147Node19_sound component147Node20_sound

private noncomputable def component147Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component147Node22_sound : Sound component147Node22Box :=
  sound_of_literal_split component147Node22Box component147Node18Box component147Node21Box
    .chi (31/32) (by rfl) (by rfl)
    component147Node18_sound component147Node21_sound

private noncomputable def component147Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component147Node23_sound : Sound component147Node23Box :=
  sound_of_literal_split component147Node23Box component147Node15Box component147Node22Box
    .k (29/8) (by rfl) (by rfl)
    component147Node15_sound component147Node22_sound

private noncomputable def component147Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component147Node24_sound : Sound component147Node24Box :=
  sound_of_literal_split component147Node24Box component147Node12Box component147Node23Box
    .chi (15/16) (by rfl) (by rfl)
    component147Node12_sound component147Node23_sound

private noncomputable def component147Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (7/8), chiHi := (57/64) }

set_option maxRecDepth 1000000 in
private theorem component147Node25_sound : Sound component147Node25Box :=
  sound_of_literal_split component147Node25Box leaf7254Box leaf7255Box
    .k (61/16) (by rfl) (by rfl)
    leaf7254FlatSound leaf7255FlatSound

private noncomputable def component147Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (57/64), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component147Node26_sound : Sound component147Node26Box :=
  sound_of_literal_split component147Node26Box leaf7256Box leaf7257Box
    .k (61/16) (by rfl) (by rfl)
    leaf7256FlatSound leaf7257FlatSound

private noncomputable def component147Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (7/8), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component147Node27_sound : Sound component147Node27Box :=
  sound_of_literal_split component147Node27Box component147Node25Box component147Node26Box
    .chi (57/64) (by rfl) (by rfl)
    component147Node25_sound component147Node26_sound

private noncomputable def component147Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (29/32), chiHi := (59/64) }

set_option maxRecDepth 1000000 in
private theorem component147Node28_sound : Sound component147Node28Box :=
  sound_of_literal_split component147Node28Box leaf7258Box leaf7259Box
    .k (61/16) (by rfl) (by rfl)
    leaf7258FlatSound leaf7259FlatSound

private noncomputable def component147Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (59/64), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component147Node29_sound : Sound component147Node29Box :=
  sound_of_literal_split component147Node29Box leaf7260Box leaf7261Box
    .k (61/16) (by rfl) (by rfl)
    leaf7260FlatSound leaf7261FlatSound

private noncomputable def component147Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (29/32), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component147Node30_sound : Sound component147Node30Box :=
  sound_of_literal_split component147Node30Box component147Node28Box component147Node29Box
    .chi (59/64) (by rfl) (by rfl)
    component147Node28_sound component147Node29_sound

private noncomputable def component147Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component147Node31_sound : Sound component147Node31Box :=
  sound_of_literal_split component147Node31Box component147Node27Box component147Node30Box
    .chi (29/32) (by rfl) (by rfl)
    component147Node27_sound component147Node30_sound

private noncomputable def component147Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (7/8), chiHi := (57/64) }

set_option maxRecDepth 1000000 in
private theorem component147Node32_sound : Sound component147Node32Box :=
  sound_of_literal_split component147Node32Box leaf7262Box leaf7263Box
    .k (63/16) (by rfl) (by rfl)
    leaf7262FlatSound leaf7263FlatSound

private noncomputable def component147Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (57/64), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component147Node33_sound : Sound component147Node33Box :=
  sound_of_literal_split component147Node33Box leaf7264Box leaf7265Box
    .k (63/16) (by rfl) (by rfl)
    leaf7264FlatSound leaf7265FlatSound

private noncomputable def component147Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (7/8), chiHi := (29/32) }

set_option maxRecDepth 1000000 in
private theorem component147Node34_sound : Sound component147Node34Box :=
  sound_of_literal_split component147Node34Box component147Node32Box component147Node33Box
    .chi (57/64) (by rfl) (by rfl)
    component147Node32_sound component147Node33_sound

private noncomputable def component147Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (29/32), chiHi := (59/64) }

set_option maxRecDepth 1000000 in
private theorem component147Node35_sound : Sound component147Node35Box :=
  sound_of_literal_split component147Node35Box leaf7266Box leaf7267Box
    .k (63/16) (by rfl) (by rfl)
    leaf7266FlatSound leaf7267FlatSound

private noncomputable def component147Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (59/64), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component147Node36_sound : Sound component147Node36Box :=
  sound_of_literal_split component147Node36Box leaf7268Box leaf7269Box
    .k (63/16) (by rfl) (by rfl)
    leaf7268FlatSound leaf7269FlatSound

private noncomputable def component147Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (29/32), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component147Node37_sound : Sound component147Node37Box :=
  sound_of_literal_split component147Node37Box component147Node35Box component147Node36Box
    .chi (59/64) (by rfl) (by rfl)
    component147Node35_sound component147Node36_sound

private noncomputable def component147Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component147Node38_sound : Sound component147Node38Box :=
  sound_of_literal_split component147Node38Box component147Node34Box component147Node37Box
    .chi (29/32) (by rfl) (by rfl)
    component147Node34_sound component147Node37_sound

private noncomputable def component147Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (7/8), chiHi := (15/16) }

set_option maxRecDepth 1000000 in
private theorem component147Node39_sound : Sound component147Node39Box :=
  sound_of_literal_split component147Node39Box component147Node31Box component147Node38Box
    .k (31/8) (by rfl) (by rfl)
    component147Node31_sound component147Node38_sound

private noncomputable def component147Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (15/16), chiHi := (61/64) }

set_option maxRecDepth 1000000 in
private theorem component147Node40_sound : Sound component147Node40Box :=
  sound_of_literal_split component147Node40Box leaf7270Box leaf7271Box
    .k (61/16) (by rfl) (by rfl)
    leaf7270FlatSound leaf7271FlatSound

private noncomputable def component147Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (61/64), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component147Node41_sound : Sound component147Node41Box :=
  sound_of_literal_split component147Node41Box leaf7272Box leaf7273Box
    .k (61/16) (by rfl) (by rfl)
    leaf7272FlatSound leaf7273FlatSound

private noncomputable def component147Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (15/16), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component147Node42_sound : Sound component147Node42Box :=
  sound_of_literal_split component147Node42Box component147Node40Box component147Node41Box
    .chi (61/64) (by rfl) (by rfl)
    component147Node40_sound component147Node41_sound

private noncomputable def component147Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (31/32), chiHi := (63/64) }

set_option maxRecDepth 1000000 in
private theorem component147Node43_sound : Sound component147Node43Box :=
  sound_of_literal_split component147Node43Box leaf7274Box leaf7275Box
    .k (61/16) (by rfl) (by rfl)
    leaf7274FlatSound leaf7275FlatSound

private noncomputable def component147Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (63/64), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component147Node44_sound : Sound component147Node44Box :=
  sound_of_literal_split component147Node44Box leaf7276Box leaf7277Box
    .k (61/16) (by rfl) (by rfl)
    leaf7276FlatSound leaf7277FlatSound

private noncomputable def component147Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (31/32), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component147Node45_sound : Sound component147Node45Box :=
  sound_of_literal_split component147Node45Box component147Node43Box component147Node44Box
    .chi (63/64) (by rfl) (by rfl)
    component147Node43_sound component147Node44_sound

private noncomputable def component147Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component147Node46_sound : Sound component147Node46Box :=
  sound_of_literal_split component147Node46Box component147Node42Box component147Node45Box
    .chi (31/32) (by rfl) (by rfl)
    component147Node42_sound component147Node45_sound

private noncomputable def component147Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (15/16), chiHi := (61/64) }

set_option maxRecDepth 1000000 in
private theorem component147Node47_sound : Sound component147Node47Box :=
  sound_of_literal_split component147Node47Box leaf7278Box leaf7279Box
    .k (63/16) (by rfl) (by rfl)
    leaf7278FlatSound leaf7279FlatSound

private noncomputable def component147Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (61/64), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component147Node48_sound : Sound component147Node48Box :=
  sound_of_literal_split component147Node48Box leaf7280Box leaf7281Box
    .k (63/16) (by rfl) (by rfl)
    leaf7280FlatSound leaf7281FlatSound

private noncomputable def component147Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (15/16), chiHi := (31/32) }

set_option maxRecDepth 1000000 in
private theorem component147Node49_sound : Sound component147Node49Box :=
  sound_of_literal_split component147Node49Box component147Node47Box component147Node48Box
    .chi (61/64) (by rfl) (by rfl)
    component147Node47_sound component147Node48_sound

private noncomputable def component147Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (31/32), chiHi := (63/64) }

set_option maxRecDepth 1000000 in
private theorem component147Node50_sound : Sound component147Node50Box :=
  sound_of_literal_split component147Node50Box leaf7282Box leaf7283Box
    .k (63/16) (by rfl) (by rfl)
    leaf7282FlatSound leaf7283FlatSound

private noncomputable def component147Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (63/64), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component147Node51_sound : Sound component147Node51Box :=
  sound_of_literal_split component147Node51Box leaf7284Box leaf7285Box
    .k (63/16) (by rfl) (by rfl)
    leaf7284FlatSound leaf7285FlatSound

private noncomputable def component147Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (31/32), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component147Node52_sound : Sound component147Node52Box :=
  sound_of_literal_split component147Node52Box component147Node50Box component147Node51Box
    .chi (63/64) (by rfl) (by rfl)
    component147Node50_sound component147Node51_sound

private noncomputable def component147Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component147Node53_sound : Sound component147Node53Box :=
  sound_of_literal_split component147Node53Box component147Node49Box component147Node52Box
    .chi (31/32) (by rfl) (by rfl)
    component147Node49_sound component147Node52_sound

private noncomputable def component147Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (15/16), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component147Node54_sound : Sound component147Node54Box :=
  sound_of_literal_split component147Node54Box component147Node46Box component147Node53Box
    .k (31/8) (by rfl) (by rfl)
    component147Node46_sound component147Node53_sound

private noncomputable def component147Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
private theorem component147Node55_sound : Sound component147Node55Box :=
  sound_of_literal_split component147Node55Box component147Node39Box component147Node54Box
    .chi (15/16) (by rfl) (by rfl)
    component147Node39_sound component147Node54_sound

noncomputable def component147Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (4), chiLo := (7/8), chiHi := (1) }

set_option maxRecDepth 1000000 in
theorem component147_sound : Sound component147Box :=
  sound_of_literal_split component147Box component147Node24Box component147Node55Box
    .k (15/4) (by rfl) (by rfl)
    component147Node24_sound component147Node55_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
