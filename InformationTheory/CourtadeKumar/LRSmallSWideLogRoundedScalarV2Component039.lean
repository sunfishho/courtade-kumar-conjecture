import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
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

private noncomputable def leaf1710Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (1/16), chiHi := (17/256) }

private noncomputable def leaf1710Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435611/268435456) }, vSqrt := { lower := (8191/8192), upper := (67108992/67107827) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (331313255/268435456) }, upper := { exponent := 0, mantissa := (5133/4096) } }, logOuter := sk157LogOuterCertificate, logK := sk157LogKCertificate, logChi := chi151LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216819/134215654) } }, logDArg := sk157LogDArgCertificate }

private noncomputable def leaf1710InnerLog : WideLogData :=
  innerPair128Data

set_option maxRecDepth 1000000 in
private theorem leaf1710LocalValidity :
    LeafFacts leaf1710Box leaf1710Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1710Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108992/67107827) }) = true
      norm_num [leaf1710Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1710CertificateValid :
    WideCertificateValid leaf1710Box leaf1710Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk157ValidityFacts chi151ValidityFacts
    leaf1710LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1710CoverageChecked :
    coverageCheck (innerAD leaf1710Box) leaf1710InnerLog = true := by
  rfl'

private theorem leaf1710InnerLogValid :
    leaf1710InnerLog.Valid 8 (innerAD leaf1710Box) :=
  wideLogDataValid_of_cachedCheck endpoint27PositiveFacts
    endpoint100PositiveFacts.valid leaf1710CoverageChecked

private noncomputable def leaf1710InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814613/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1710InputLogOnePlusV_eq :
    leaf1710InputLogOnePlusV = outerEnclosure 24
      (leaf1710Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1710RoundedFacts : LeafRoundedFacts 8
    leaf1710Certificate.logOnePlusV leaf1710InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1710InputLogOnePlusV_eq }

private noncomputable def leaf1710Inputs : Inputs :=
  inputsOfCaches globalInput sk157RoundedInputs
    chi151InputQChi innerPair128Input
    leaf1710InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1710LowerChecked :
    lowerCheck 24 leaf1710Box leaf1710Inputs = true := by
  rfl'

private theorem leaf1710CoversExact : CoversExact 8
    leaf1710Box leaf1710Certificate leaf1710InnerLog leaf1710Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk157RoundedFacts chi151RoundedFacts
    innerPair128RoundedFacts leaf1710RoundedFacts (by rfl)

private theorem leaf1710FlatSound : Sound leaf1710Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1710CertificateValid
    leaf1710InnerLogValid leaf1710CoversExact leaf1710LowerChecked

private noncomputable def leaf1711Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (17/256), chiHi := (9/128) }

private noncomputable def leaf1711Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107775) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (670523149/536870912) }, upper := { exponent := 0, mantissa := (5185/4096) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi152LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216703/134215550) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf1711InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1711LocalValidity :
    LeafFacts leaf1711Box leaf1711Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1711Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107775) }) = true
      norm_num [leaf1711Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1711CertificateValid :
    WideCertificateValid leaf1711Box leaf1711Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi152ValidityFacts
    leaf1711LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1711CoverageChecked :
    coverageCheck (innerAD leaf1711Box) leaf1711InnerLog = true := by
  rfl'

private theorem leaf1711InnerLogValid :
    leaf1711InnerLog.Valid 8 (innerAD leaf1711Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1711CoverageChecked

private noncomputable def leaf1711InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1711InputLogOnePlusV_eq :
    leaf1711InputLogOnePlusV = outerEnclosure 24
      (leaf1711Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1711RoundedFacts : LeafRoundedFacts 8
    leaf1711Certificate.logOnePlusV leaf1711InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1711InputLogOnePlusV_eq }

private noncomputable def leaf1711Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi152InputQChi innerPair13Input
    leaf1711InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1711LowerChecked :
    lowerCheck 24 leaf1711Box leaf1711Inputs = true := by
  rfl'

private theorem leaf1711CoversExact : CoversExact 8
    leaf1711Box leaf1711Certificate leaf1711InnerLog leaf1711Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi152RoundedFacts
    innerPair13RoundedFacts leaf1711RoundedFacts (by rfl)

private theorem leaf1711FlatSound : Sound leaf1711Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1711CertificateValid
    leaf1711InnerLogValid leaf1711CoversExact leaf1711LowerChecked

private noncomputable def leaf1712Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (17/256), chiHi := (9/128) }

private noncomputable def leaf1712Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553883) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (671637191/536870912) }, upper := { exponent := 0, mantissa := (2597/2048) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi152LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108347/67107766) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf1712InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1712LocalValidity :
    LeafFacts leaf1712Box leaf1712Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1712Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553883) }) = true
      norm_num [leaf1712Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1712CertificateValid :
    WideCertificateValid leaf1712Box leaf1712Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi152ValidityFacts
    leaf1712LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1712CoverageChecked :
    coverageCheck (innerAD leaf1712Box) leaf1712InnerLog = true := by
  rfl'

private theorem leaf1712InnerLogValid :
    leaf1712InnerLog.Valid 8 (innerAD leaf1712Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1712CoverageChecked

private noncomputable def leaf1712InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814613/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1712InputLogOnePlusV_eq :
    leaf1712InputLogOnePlusV = outerEnclosure 24
      (leaf1712Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1712RoundedFacts : LeafRoundedFacts 8
    leaf1712Certificate.logOnePlusV leaf1712InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1712InputLogOnePlusV_eq }

private noncomputable def leaf1712Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi152InputQChi innerPair16Input
    leaf1712InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1712LowerChecked :
    lowerCheck 24 leaf1712Box leaf1712Inputs = true := by
  rfl'

private theorem leaf1712CoversExact : CoversExact 8
    leaf1712Box leaf1712Certificate leaf1712InnerLog leaf1712Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi152RoundedFacts
    innerPair16RoundedFacts leaf1712RoundedFacts (by rfl)

private theorem leaf1712FlatSound : Sound leaf1712Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1712CertificateValid
    leaf1712InnerLogValid leaf1712CoversExact leaf1712LowerChecked

private noncomputable def leaf1713Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (1/16), chiHi := (17/256) }

private noncomputable def leaf1713Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435613/268435456) }, vSqrt := { lower := (8191/8192), upper := (11184832/11184635) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (332361765/268435456) }, upper := { exponent := 0, mantissa := (2575/2048) } }, logOuter := sk158LogOuterCertificate, logK := sk158LogKCertificate, logChi := chi151LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22369467/22369270) } }, logDArg := sk158LogDArgCertificate }

private noncomputable def leaf1713InnerLog : WideLogData :=
  innerPair403Data

set_option maxRecDepth 1000000 in
private theorem leaf1713LocalValidity :
    LeafFacts leaf1713Box leaf1713Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1713Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11184832/11184635) }) = true
      norm_num [leaf1713Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1713CertificateValid :
    WideCertificateValid leaf1713Box leaf1713Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk158ValidityFacts chi151ValidityFacts
    leaf1713LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1713CoverageChecked :
    coverageCheck (innerAD leaf1713Box) leaf1713InnerLog = true := by
  rfl'

private theorem leaf1713InnerLogValid :
    leaf1713InnerLog.Valid 8 (innerAD leaf1713Box) :=
  wideLogDataValid_of_cachedCheck endpoint116PositiveFacts
    endpoint154PositiveFacts.valid leaf1713CoverageChecked

private noncomputable def leaf1713InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907307/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1713InputLogOnePlusV_eq :
    leaf1713InputLogOnePlusV = outerEnclosure 24
      (leaf1713Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1713RoundedFacts : LeafRoundedFacts 8
    leaf1713Certificate.logOnePlusV leaf1713InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1713InputLogOnePlusV_eq }

private noncomputable def leaf1713Inputs : Inputs :=
  inputsOfCaches globalInput sk158RoundedInputs
    chi151InputQChi innerPair403Input
    leaf1713InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1713LowerChecked :
    lowerCheck 24 leaf1713Box leaf1713Inputs = true := by
  rfl'

private theorem leaf1713CoversExact : CoversExact 8
    leaf1713Box leaf1713Certificate leaf1713InnerLog leaf1713Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk158RoundedFacts chi151RoundedFacts
    innerPair403RoundedFacts leaf1713RoundedFacts (by rfl)

private theorem leaf1713FlatSound : Sound leaf1713Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1713CertificateValid
    leaf1713InnerLogValid leaf1713CoversExact leaf1713LowerChecked

private noncomputable def leaf1714Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (17/256), chiHi := (9/128) }

private noncomputable def leaf1714Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107757) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (672751233/536870912) }, upper := { exponent := 0, mantissa := (5203/4096) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi152LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216685/134215514) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf1714InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1714LocalValidity :
    LeafFacts leaf1714Box leaf1714Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1714Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107757) }) = true
      norm_num [leaf1714Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1714CertificateValid :
    WideCertificateValid leaf1714Box leaf1714Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi152ValidityFacts
    leaf1714LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1714CoverageChecked :
    coverageCheck (innerAD leaf1714Box) leaf1714InnerLog = true := by
  rfl'

private theorem leaf1714InnerLogValid :
    leaf1714InnerLog.Valid 8 (innerAD leaf1714Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1714CoverageChecked

private noncomputable def leaf1714InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1714InputLogOnePlusV_eq :
    leaf1714InputLogOnePlusV = outerEnclosure 24
      (leaf1714Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1714RoundedFacts : LeafRoundedFacts 8
    leaf1714Certificate.logOnePlusV leaf1714InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1714InputLogOnePlusV_eq }

private noncomputable def leaf1714Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi152InputQChi innerPair16Input
    leaf1714InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1714LowerChecked :
    lowerCheck 24 leaf1714Box leaf1714Inputs = true := by
  rfl'

private theorem leaf1714CoversExact : CoversExact 8
    leaf1714Box leaf1714Certificate leaf1714InnerLog leaf1714Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi152RoundedFacts
    innerPair16RoundedFacts leaf1714RoundedFacts (by rfl)

private theorem leaf1714FlatSound : Sound leaf1714Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1714CertificateValid
    leaf1714InnerLogValid leaf1714CoversExact leaf1714LowerChecked

private noncomputable def leaf1715Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (17/256), chiHi := (9/128) }

private noncomputable def leaf1715Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776937) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (673865275/536870912) }, upper := { exponent := 0, mantissa := (1303/1024) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi152LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554169/33553874) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1715InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1715LocalValidity :
    LeafFacts leaf1715Box leaf1715Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1715Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776937) }) = true
      norm_num [leaf1715Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1715CertificateValid :
    WideCertificateValid leaf1715Box leaf1715Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi152ValidityFacts
    leaf1715LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1715CoverageChecked :
    coverageCheck (innerAD leaf1715Box) leaf1715InnerLog = true := by
  rfl'

private theorem leaf1715InnerLogValid :
    leaf1715InnerLog.Valid 8 (innerAD leaf1715Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1715CoverageChecked

private noncomputable def leaf1715InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907307/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1715InputLogOnePlusV_eq :
    leaf1715InputLogOnePlusV = outerEnclosure 24
      (leaf1715Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1715RoundedFacts : LeafRoundedFacts 8
    leaf1715Certificate.logOnePlusV leaf1715InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1715InputLogOnePlusV_eq }

private noncomputable def leaf1715Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi152InputQChi innerPair16Input
    leaf1715InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1715LowerChecked :
    lowerCheck 24 leaf1715Box leaf1715Inputs = true := by
  rfl'

private theorem leaf1715CoversExact : CoversExact 8
    leaf1715Box leaf1715Certificate leaf1715InnerLog leaf1715Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi152RoundedFacts
    innerPair16RoundedFacts leaf1715RoundedFacts (by rfl)

private theorem leaf1715FlatSound : Sound leaf1715Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1715CertificateValid
    leaf1715InnerLogValid leaf1715CoversExact leaf1715LowerChecked

private noncomputable def leaf1716Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1716Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134215429) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (678386987/536870912) }, upper := { exponent := 0, mantissa := (10491/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268433285/268430858) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf1716InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1716LocalValidity :
    LeafFacts leaf1716Box leaf1716Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1716Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134215429) }) = true
      norm_num [leaf1716Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1716CertificateValid :
    WideCertificateValid leaf1716Box leaf1716Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi147ValidityFacts
    leaf1716LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1716CoverageChecked :
    coverageCheck (innerAD leaf1716Box) leaf1716InnerLog = true := by
  rfl'

private theorem leaf1716InnerLogValid :
    leaf1716InnerLog.Valid 8 (innerAD leaf1716Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1716CoverageChecked

private noncomputable def leaf1716InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1716InputLogOnePlusV_eq :
    leaf1716InputLogOnePlusV = outerEnclosure 24
      (leaf1716Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1716RoundedFacts : LeafRoundedFacts 8
    leaf1716Certificate.logOnePlusV leaf1716InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1716InputLogOnePlusV_eq }

private noncomputable def leaf1716Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi147InputQChi innerPair16Input
    leaf1716InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1716LowerChecked :
    lowerCheck 24 leaf1716Box leaf1716Inputs = true := by
  rfl'

private theorem leaf1716CoversExact : CoversExact 8
    leaf1716Box leaf1716Certificate leaf1716InnerLog leaf1716Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi147RoundedFacts
    innerPair16RoundedFacts leaf1716RoundedFacts (by rfl)

private theorem leaf1716FlatSound : Sound leaf1716Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1716CertificateValid
    leaf1716InnerLogValid leaf1716CoversExact leaf1716LowerChecked

private noncomputable def leaf1717Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1717Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107705) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (679566561/536870912) }, upper := { exponent := 0, mantissa := (5255/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216633/134215410) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf1717InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1717LocalValidity :
    LeafFacts leaf1717Box leaf1717Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1717Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107705) }) = true
      norm_num [leaf1717Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1717CertificateValid :
    WideCertificateValid leaf1717Box leaf1717Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi147ValidityFacts
    leaf1717LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1717CoverageChecked :
    coverageCheck (innerAD leaf1717Box) leaf1717InnerLog = true := by
  rfl'

private theorem leaf1717InnerLogValid :
    leaf1717InnerLog.Valid 8 (innerAD leaf1717Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1717CoverageChecked

private noncomputable def leaf1717InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1717InputLogOnePlusV_eq :
    leaf1717InputLogOnePlusV = outerEnclosure 24
      (leaf1717Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1717RoundedFacts : LeafRoundedFacts 8
    leaf1717Certificate.logOnePlusV leaf1717InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1717InputLogOnePlusV_eq }

private noncomputable def leaf1717Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi147InputQChi innerPair16Input
    leaf1717InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1717LowerChecked :
    lowerCheck 24 leaf1717Box leaf1717Inputs = true := by
  rfl'

private theorem leaf1717CoversExact : CoversExact 8
    leaf1717Box leaf1717Certificate leaf1717InnerLog leaf1717Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi147RoundedFacts
    innerPair16RoundedFacts leaf1717RoundedFacts (by rfl)

private theorem leaf1717FlatSound : Sound leaf1717Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1717CertificateValid
    leaf1717InnerLogValid leaf1717CoversExact leaf1717LowerChecked

private noncomputable def leaf1718Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1718Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553827) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (686250825/536870912) }, upper := { exponent := 0, mantissa := (2653/2048) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108291/67107654) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf1718InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1718LocalValidity :
    LeafFacts leaf1718Box leaf1718Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1718Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553827) }) = true
      norm_num [leaf1718Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1718CertificateValid :
    WideCertificateValid leaf1718Box leaf1718Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi148ValidityFacts
    leaf1718LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1718CoverageChecked :
    coverageCheck (innerAD leaf1718Box) leaf1718InnerLog = true := by
  rfl'

private theorem leaf1718InnerLogValid :
    leaf1718InnerLog.Valid 8 (innerAD leaf1718Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1718CoverageChecked

private noncomputable def leaf1718InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1718InputLogOnePlusV_eq :
    leaf1718InputLogOnePlusV = outerEnclosure 24
      (leaf1718Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1718RoundedFacts : LeafRoundedFacts 8
    leaf1718Certificate.logOnePlusV leaf1718InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1718InputLogOnePlusV_eq }

private noncomputable def leaf1718Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi148InputQChi innerPair16Input
    leaf1718InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1718LowerChecked :
    lowerCheck 24 leaf1718Box leaf1718Inputs = true := by
  rfl'

private theorem leaf1718CoversExact : CoversExact 8
    leaf1718Box leaf1718Certificate leaf1718InnerLog leaf1718Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi148RoundedFacts
    innerPair16RoundedFacts leaf1718RoundedFacts (by rfl)

private theorem leaf1718FlatSound : Sound leaf1718Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1718CertificateValid
    leaf1718InnerLogValid leaf1718CoversExact leaf1718LowerChecked

private noncomputable def leaf1719Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1719Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776911) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (687495931/536870912) }, upper := { exponent := 0, mantissa := (1329/1024) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554143/33553822) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf1719InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1719LocalValidity :
    LeafFacts leaf1719Box leaf1719Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1719Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776911) }) = true
      norm_num [leaf1719Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1719CertificateValid :
    WideCertificateValid leaf1719Box leaf1719Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi148ValidityFacts
    leaf1719LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1719CoverageChecked :
    coverageCheck (innerAD leaf1719Box) leaf1719InnerLog = true := by
  rfl'

private theorem leaf1719InnerLogValid :
    leaf1719InnerLog.Valid 8 (innerAD leaf1719Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1719CoverageChecked

private noncomputable def leaf1719InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1719InputLogOnePlusV_eq :
    leaf1719InputLogOnePlusV = outerEnclosure 24
      (leaf1719Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1719RoundedFacts : LeafRoundedFacts 8
    leaf1719Certificate.logOnePlusV leaf1719InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1719InputLogOnePlusV_eq }

private noncomputable def leaf1719Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi148InputQChi innerPair16Input
    leaf1719InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1719LowerChecked :
    lowerCheck 24 leaf1719Box leaf1719Inputs = true := by
  rfl'

private theorem leaf1719CoversExact : CoversExact 8
    leaf1719Box leaf1719Certificate leaf1719InnerLog leaf1719Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi148RoundedFacts
    innerPair16RoundedFacts leaf1719RoundedFacts (by rfl)

private theorem leaf1719FlatSound : Sound leaf1719Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1719CertificateValid
    leaf1719InnerLogValid leaf1719CoversExact leaf1719LowerChecked

private noncomputable def leaf1720Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1720Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (8191/8192), upper := (7895168/7895023) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (680746135/536870912) }, upper := { exponent := 0, mantissa := (10529/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15790191/15790046) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf1720InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1720LocalValidity :
    LeafFacts leaf1720Box leaf1720Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1720Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7895168/7895023) }) = true
      norm_num [leaf1720Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1720CertificateValid :
    WideCertificateValid leaf1720Box leaf1720Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi147ValidityFacts
    leaf1720LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1720CoverageChecked :
    coverageCheck (innerAD leaf1720Box) leaf1720InnerLog = true := by
  rfl'

private theorem leaf1720InnerLogValid :
    leaf1720InnerLog.Valid 8 (innerAD leaf1720Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1720CoverageChecked

private noncomputable def leaf1720InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1720InputLogOnePlusV_eq :
    leaf1720InputLogOnePlusV = outerEnclosure 24
      (leaf1720Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1720RoundedFacts : LeafRoundedFacts 8
    leaf1720Certificate.logOnePlusV leaf1720InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1720InputLogOnePlusV_eq }

private noncomputable def leaf1720Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi147InputQChi innerPair16Input
    leaf1720InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1720LowerChecked :
    lowerCheck 24 leaf1720Box leaf1720Inputs = true := by
  rfl'

private theorem leaf1720CoversExact : CoversExact 8
    leaf1720Box leaf1720Certificate leaf1720InnerLog leaf1720Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi147RoundedFacts
    innerPair16RoundedFacts leaf1720RoundedFacts (by rfl)

private theorem leaf1720FlatSound : Sound leaf1720Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1720CertificateValid
    leaf1720InnerLogValid leaf1720CoversExact leaf1720LowerChecked

private noncomputable def leaf1721Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1721Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553843) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (681925709/536870912) }, upper := { exponent := 0, mantissa := (2637/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108307/67107686) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1721InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1721LocalValidity :
    LeafFacts leaf1721Box leaf1721Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1721Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553843) }) = true
      norm_num [leaf1721Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1721CertificateValid :
    WideCertificateValid leaf1721Box leaf1721Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi147ValidityFacts
    leaf1721LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1721CoverageChecked :
    coverageCheck (innerAD leaf1721Box) leaf1721InnerLog = true := by
  rfl'

private theorem leaf1721InnerLogValid :
    leaf1721InnerLog.Valid 8 (innerAD leaf1721Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1721CoverageChecked

private noncomputable def leaf1721InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1721InputLogOnePlusV_eq :
    leaf1721InputLogOnePlusV = outerEnclosure 24
      (leaf1721Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1721RoundedFacts : LeafRoundedFacts 8
    leaf1721Certificate.logOnePlusV leaf1721InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1721InputLogOnePlusV_eq }

private noncomputable def leaf1721Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi147InputQChi innerPair16Input
    leaf1721InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1721LowerChecked :
    lowerCheck 24 leaf1721Box leaf1721Inputs = true := by
  rfl'

private theorem leaf1721CoversExact : CoversExact 8
    leaf1721Box leaf1721Certificate leaf1721InnerLog leaf1721Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi147RoundedFacts
    innerPair16RoundedFacts leaf1721RoundedFacts (by rfl)

private theorem leaf1721FlatSound : Sound leaf1721Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1721CertificateValid
    leaf1721InnerLogValid leaf1721CoversExact leaf1721LowerChecked

private noncomputable def leaf1722Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1722Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553817) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (688741037/536870912) }, upper := { exponent := 0, mantissa := (2663/2048) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108281/67107634) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf1722InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1722LocalValidity :
    LeafFacts leaf1722Box leaf1722Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1722Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553817) }) = true
      norm_num [leaf1722Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1722CertificateValid :
    WideCertificateValid leaf1722Box leaf1722Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi148ValidityFacts
    leaf1722LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1722CoverageChecked :
    coverageCheck (innerAD leaf1722Box) leaf1722InnerLog = true := by
  rfl'

private theorem leaf1722InnerLogValid :
    leaf1722InnerLog.Valid 8 (innerAD leaf1722Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1722CoverageChecked

private noncomputable def leaf1722InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814621/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1722InputLogOnePlusV_eq :
    leaf1722InputLogOnePlusV = outerEnclosure 24
      (leaf1722Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1722RoundedFacts : LeafRoundedFacts 8
    leaf1722Certificate.logOnePlusV leaf1722InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1722InputLogOnePlusV_eq }

private noncomputable def leaf1722Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi148InputQChi innerPair16Input
    leaf1722InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1722LowerChecked :
    lowerCheck 24 leaf1722Box leaf1722Inputs = true := by
  rfl'

private theorem leaf1722CoversExact : CoversExact 8
    leaf1722Box leaf1722Certificate leaf1722InnerLog leaf1722Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi148RoundedFacts
    innerPair16RoundedFacts leaf1722RoundedFacts (by rfl)

private theorem leaf1722FlatSound : Sound leaf1722Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1722CertificateValid
    leaf1722InnerLogValid leaf1722CoversExact leaf1722LowerChecked

private noncomputable def leaf1723Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1723Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388453) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (689986143/536870912) }, upper := { exponent := 0, mantissa := (667/512) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777069/16776906) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1723InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1723LocalValidity :
    LeafFacts leaf1723Box leaf1723Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1723Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388453) }) = true
      norm_num [leaf1723Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1723CertificateValid :
    WideCertificateValid leaf1723Box leaf1723Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi148ValidityFacts
    leaf1723LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1723CoverageChecked :
    coverageCheck (innerAD leaf1723Box) leaf1723InnerLog = true := by
  rfl'

private theorem leaf1723InnerLogValid :
    leaf1723InnerLog.Valid 8 (innerAD leaf1723Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1723CoverageChecked

private noncomputable def leaf1723InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1723InputLogOnePlusV_eq :
    leaf1723InputLogOnePlusV = outerEnclosure 24
      (leaf1723Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1723RoundedFacts : LeafRoundedFacts 8
    leaf1723Certificate.logOnePlusV leaf1723InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1723InputLogOnePlusV_eq }

private noncomputable def leaf1723Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi148InputQChi innerPair16Input
    leaf1723InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1723LowerChecked :
    lowerCheck 24 leaf1723Box leaf1723Inputs = true := by
  rfl'

private theorem leaf1723CoversExact : CoversExact 8
    leaf1723Box leaf1723Certificate leaf1723InnerLog leaf1723Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi148RoundedFacts
    innerPair16RoundedFacts leaf1723RoundedFacts (by rfl)

private theorem leaf1723FlatSound : Sound leaf1723Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1723CertificateValid
    leaf1723InnerLogValid leaf1723CoversExact leaf1723LowerChecked

private noncomputable def leaf1724Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (1/16), chiHi := (33/512) }

private noncomputable def leaf1724Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871103/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217984/134215649) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (666853443/536870912) }, upper := { exponent := 0, mantissa := (10271/8192) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi161LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268433633/268431298) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf1724InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1724LocalValidity :
    LeafFacts leaf1724Box leaf1724Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1724Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217984/134215649) }) = true
      norm_num [leaf1724Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1724CertificateValid :
    WideCertificateValid leaf1724Box leaf1724Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi161ValidityFacts
    leaf1724LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1724CoverageChecked :
    coverageCheck (innerAD leaf1724Box) leaf1724InnerLog = true := by
  rfl'

private theorem leaf1724InnerLogValid :
    leaf1724InnerLog.Valid 8 (innerAD leaf1724Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1724CoverageChecked

private noncomputable def leaf1724InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1724InputLogOnePlusV_eq :
    leaf1724InputLogOnePlusV = outerEnclosure 24
      (leaf1724Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1724RoundedFacts : LeafRoundedFacts 8
    leaf1724Certificate.logOnePlusV leaf1724InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1724InputLogOnePlusV_eq }

private noncomputable def leaf1724Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi161InputQChi innerPair13Input
    leaf1724InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1724LowerChecked :
    lowerCheck 24 leaf1724Box leaf1724Inputs = true := by
  rfl'

private theorem leaf1724CoversExact : CoversExact 8
    leaf1724Box leaf1724Certificate leaf1724InnerLog leaf1724Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi161RoundedFacts
    innerPair13RoundedFacts leaf1724RoundedFacts (by rfl)

private theorem leaf1724FlatSound : Sound leaf1724Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1724CertificateValid
    leaf1724InnerLogValid leaf1724CoversExact leaf1724LowerChecked

private noncomputable def leaf1725Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (33/512), chiHi := (17/256) }

private noncomputable def leaf1725Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871105/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108992/67107793) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (670916425/536870912) }, upper := { exponent := 0, mantissa := (5167/4096) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi162LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216785/134215586) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf1725InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1725LocalValidity :
    LeafFacts leaf1725Box leaf1725Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1725Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108992/67107793) }) = true
      norm_num [leaf1725Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1725CertificateValid :
    WideCertificateValid leaf1725Box leaf1725Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi162ValidityFacts
    leaf1725LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1725CoverageChecked :
    coverageCheck (innerAD leaf1725Box) leaf1725InnerLog = true := by
  rfl'

private theorem leaf1725InnerLogValid :
    leaf1725InnerLog.Valid 8 (innerAD leaf1725Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1725CoverageChecked

private noncomputable def leaf1725InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629231/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1725InputLogOnePlusV_eq :
    leaf1725InputLogOnePlusV = outerEnclosure 24
      (leaf1725Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1725RoundedFacts : LeafRoundedFacts 8
    leaf1725Certificate.logOnePlusV leaf1725InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1725InputLogOnePlusV_eq }

private noncomputable def leaf1725Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi162InputQChi innerPair13Input
    leaf1725InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1725LowerChecked :
    lowerCheck 24 leaf1725Box leaf1725Inputs = true := by
  rfl'

private theorem leaf1725CoversExact : CoversExact 8
    leaf1725Box leaf1725Certificate leaf1725InnerLog leaf1725Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi162RoundedFacts
    innerPair13RoundedFacts leaf1725RoundedFacts (by rfl)

private theorem leaf1725FlatSound : Sound leaf1725Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1725CertificateValid
    leaf1725InnerLogValid leaf1725CoversExact leaf1725LowerChecked

private noncomputable def leaf1726Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (17/256), chiHi := (35/512) }

private noncomputable def leaf1726Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871107/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217984/134215523) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (674979407/536870912) }, upper := { exponent := 0, mantissa := (10397/8192) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi163LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268433507/268431046) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf1726InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1726LocalValidity :
    LeafFacts leaf1726Box leaf1726Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1726Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217984/134215523) }) = true
      norm_num [leaf1726Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1726CertificateValid :
    WideCertificateValid leaf1726Box leaf1726Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi163ValidityFacts
    leaf1726LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1726CoverageChecked :
    coverageCheck (innerAD leaf1726Box) leaf1726InnerLog = true := by
  rfl'

private theorem leaf1726InnerLogValid :
    leaf1726InnerLog.Valid 8 (innerAD leaf1726Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1726CoverageChecked

private noncomputable def leaf1726InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1726InputLogOnePlusV_eq :
    leaf1726InputLogOnePlusV = outerEnclosure 24
      (leaf1726Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1726RoundedFacts : LeafRoundedFacts 8
    leaf1726Certificate.logOnePlusV leaf1726InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1726InputLogOnePlusV_eq }

private noncomputable def leaf1726Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi163InputQChi innerPair16Input
    leaf1726InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1726LowerChecked :
    lowerCheck 24 leaf1726Box leaf1726Inputs = true := by
  rfl'

private theorem leaf1726CoversExact : CoversExact 8
    leaf1726Box leaf1726Certificate leaf1726InnerLog leaf1726Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi163RoundedFacts
    innerPair16RoundedFacts leaf1726RoundedFacts (by rfl)

private theorem leaf1726FlatSound : Sound leaf1726Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1726CertificateValid
    leaf1726InnerLogValid leaf1726CoversExact leaf1726LowerChecked

private noncomputable def leaf1727Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (35/512), chiHi := (9/128) }

private noncomputable def leaf1727Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871109/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554496/33553865) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (679042389/536870912) }, upper := { exponent := 0, mantissa := (2615/2048) } }, logOuter := sk159LogOuterCertificate, logK := sk159LogKCertificate, logChi := chi164LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108361/67107730) } }, logDArg := sk159LogDArgCertificate }

private noncomputable def leaf1727InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1727LocalValidity :
    LeafFacts leaf1727Box leaf1727Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1727Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554496/33553865) }) = true
      norm_num [leaf1727Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1727CertificateValid :
    WideCertificateValid leaf1727Box leaf1727Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk159ValidityFacts chi164ValidityFacts
    leaf1727LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1727CoverageChecked :
    coverageCheck (innerAD leaf1727Box) leaf1727InnerLog = true := by
  rfl'

private theorem leaf1727InnerLogValid :
    leaf1727InnerLog.Valid 8 (innerAD leaf1727Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1727CoverageChecked

private noncomputable def leaf1727InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814619/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1727InputLogOnePlusV_eq :
    leaf1727InputLogOnePlusV = outerEnclosure 24
      (leaf1727Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1727RoundedFacts : LeafRoundedFacts 8
    leaf1727Certificate.logOnePlusV leaf1727InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1727InputLogOnePlusV_eq }

private noncomputable def leaf1727Inputs : Inputs :=
  inputsOfCaches globalInput sk159RoundedInputs
    chi164InputQChi innerPair16Input
    leaf1727InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1727LowerChecked :
    lowerCheck 24 leaf1727Box leaf1727Inputs = true := by
  rfl'

private theorem leaf1727CoversExact : CoversExact 8
    leaf1727Box leaf1727Certificate leaf1727InnerLog leaf1727Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk159RoundedFacts chi164RoundedFacts
    innerPair16RoundedFacts leaf1727RoundedFacts (by rfl)

private theorem leaf1727FlatSound : Sound leaf1727Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1727CertificateValid
    leaf1727InnerLogValid leaf1727CoversExact leaf1727LowerChecked

private noncomputable def leaf1728Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (1/16), chiHi := (33/512) }

private noncomputable def leaf1728Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871105/536870912) }, vSqrt := { lower := (65527/65536), upper := (2097156/2097119) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (668950465/536870912) }, upper := { exponent := 0, mantissa := (161/128) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi161LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (4194275/4194238) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf1728InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1728LocalValidity :
    LeafFacts leaf1728Box leaf1728Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1728Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (2097156/2097119) }) = true
      norm_num [leaf1728Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1728CertificateValid :
    WideCertificateValid leaf1728Box leaf1728Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi161ValidityFacts
    leaf1728LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1728CoverageChecked :
    coverageCheck (innerAD leaf1728Box) leaf1728InnerLog = true := by
  rfl'

private theorem leaf1728InnerLogValid :
    leaf1728InnerLog.Valid 8 (innerAD leaf1728Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1728CoverageChecked

private noncomputable def leaf1728InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1728InputLogOnePlusV_eq :
    leaf1728InputLogOnePlusV = outerEnclosure 24
      (leaf1728Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1728RoundedFacts : LeafRoundedFacts 8
    leaf1728Certificate.logOnePlusV leaf1728InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1728InputLogOnePlusV_eq }

private noncomputable def leaf1728Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi161InputQChi innerPair13Input
    leaf1728InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1728LowerChecked :
    lowerCheck 24 leaf1728Box leaf1728Inputs = true := by
  rfl'

private theorem leaf1728CoversExact : CoversExact 8
    leaf1728Box leaf1728Certificate leaf1728InnerLog leaf1728Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi161RoundedFacts
    innerPair13RoundedFacts leaf1728RoundedFacts (by rfl)

private theorem leaf1728FlatSound : Sound leaf1728Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1728CertificateValid
    leaf1728InnerLogValid leaf1728CoversExact leaf1728LowerChecked

private noncomputable def leaf1729Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (33/512), chiHi := (17/256) }

private noncomputable def leaf1729Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871107/536870912) }, vSqrt := { lower := (65527/65536), upper := (1048578/1048559) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (673078979/536870912) }, upper := { exponent := 0, mantissa := (81/64) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi162LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (2097137/2097118) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf1729InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1729LocalValidity :
    LeafFacts leaf1729Box leaf1729Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1729Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048578/1048559) }) = true
      norm_num [leaf1729Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1729CertificateValid :
    WideCertificateValid leaf1729Box leaf1729Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi162ValidityFacts
    leaf1729LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1729CoverageChecked :
    coverageCheck (innerAD leaf1729Box) leaf1729InnerLog = true := by
  rfl'

private theorem leaf1729InnerLogValid :
    leaf1729InnerLog.Valid 8 (innerAD leaf1729Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1729CoverageChecked

private noncomputable def leaf1729InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629233/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1729InputLogOnePlusV_eq :
    leaf1729InputLogOnePlusV = outerEnclosure 24
      (leaf1729Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1729RoundedFacts : LeafRoundedFacts 8
    leaf1729Certificate.logOnePlusV leaf1729InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1729InputLogOnePlusV_eq }

private noncomputable def leaf1729Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi162InputQChi innerPair16Input
    leaf1729InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1729LowerChecked :
    lowerCheck 24 leaf1729Box leaf1729Inputs = true := by
  rfl'

private theorem leaf1729CoversExact : CoversExact 8
    leaf1729Box leaf1729Certificate leaf1729InnerLog leaf1729Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi162RoundedFacts
    innerPair16RoundedFacts leaf1729RoundedFacts (by rfl)

private theorem leaf1729FlatSound : Sound leaf1729Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1729CertificateValid
    leaf1729InnerLogValid leaf1729CoversExact leaf1729LowerChecked

private noncomputable def leaf1730Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (17/256), chiHi := (35/512) }

private noncomputable def leaf1730Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871109/536870912) }, vSqrt := { lower := (65527/65536), upper := (699052/699039) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (677207493/536870912) }, upper := { exponent := 0, mantissa := (163/128) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi163LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (1398091/1398078) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf1730InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1730LocalValidity :
    LeafFacts leaf1730Box leaf1730Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1730Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (699052/699039) }) = true
      norm_num [leaf1730Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1730CertificateValid :
    WideCertificateValid leaf1730Box leaf1730Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi163ValidityFacts
    leaf1730LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1730CoverageChecked :
    coverageCheck (innerAD leaf1730Box) leaf1730InnerLog = true := by
  rfl'

private theorem leaf1730InnerLogValid :
    leaf1730InnerLog.Valid 8 (innerAD leaf1730Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1730CoverageChecked

private noncomputable def leaf1730InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1730InputLogOnePlusV_eq :
    leaf1730InputLogOnePlusV = outerEnclosure 24
      (leaf1730Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1730RoundedFacts : LeafRoundedFacts 8
    leaf1730Certificate.logOnePlusV leaf1730InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1730InputLogOnePlusV_eq }

private noncomputable def leaf1730Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi163InputQChi innerPair16Input
    leaf1730InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1730LowerChecked :
    lowerCheck 24 leaf1730Box leaf1730Inputs = true := by
  rfl'

private theorem leaf1730CoversExact : CoversExact 8
    leaf1730Box leaf1730Certificate leaf1730InnerLog leaf1730Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi163RoundedFacts
    innerPair16RoundedFacts leaf1730RoundedFacts (by rfl)

private theorem leaf1730FlatSound : Sound leaf1730Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1730CertificateValid
    leaf1730InnerLogValid leaf1730CoversExact leaf1730LowerChecked

private noncomputable def leaf1731Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (35/512), chiHi := (9/128) }

private noncomputable def leaf1731Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871111/536870912) }, vSqrt := { lower := (65527/65536), upper := (524289/524279) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (681336007/536870912) }, upper := { exponent := 0, mantissa := (41/32) } }, logOuter := sk160LogOuterCertificate, logK := sk160LogKCertificate, logChi := chi164LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (524284/524279) } }, logDArg := sk160LogDArgCertificate }

private noncomputable def leaf1731InnerLog : WideLogData :=
  innerPair388Data

set_option maxRecDepth 1000000 in
private theorem leaf1731LocalValidity :
    LeafFacts leaf1731Box leaf1731Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1731Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (524289/524279) }) = true
      norm_num [leaf1731Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1731CertificateValid :
    WideCertificateValid leaf1731Box leaf1731Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk160ValidityFacts chi164ValidityFacts
    leaf1731LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1731CoverageChecked :
    coverageCheck (innerAD leaf1731Box) leaf1731InnerLog = true := by
  rfl'

private theorem leaf1731InnerLogValid :
    leaf1731InnerLog.Valid 8 (innerAD leaf1731Box) :=
  wideLogDataValid_of_cachedCheck endpoint100PositiveFacts
    endpoint28PositiveFacts.valid leaf1731CoverageChecked

private noncomputable def leaf1731InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1731InputLogOnePlusV_eq :
    leaf1731InputLogOnePlusV = outerEnclosure 24
      (leaf1731Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1731RoundedFacts : LeafRoundedFacts 8
    leaf1731Certificate.logOnePlusV leaf1731InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1731InputLogOnePlusV_eq }

private noncomputable def leaf1731Inputs : Inputs :=
  inputsOfCaches globalInput sk160RoundedInputs
    chi164InputQChi innerPair388Input
    leaf1731InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1731LowerChecked :
    lowerCheck 24 leaf1731Box leaf1731Inputs = true := by
  rfl'

private theorem leaf1731CoversExact : CoversExact 8
    leaf1731Box leaf1731Certificate leaf1731InnerLog leaf1731Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk160RoundedFacts chi164RoundedFacts
    innerPair388RoundedFacts leaf1731RoundedFacts (by rfl)

private theorem leaf1731FlatSound : Sound leaf1731Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1731CertificateValid
    leaf1731InnerLogValid leaf1731CoversExact leaf1731LowerChecked

private noncomputable def leaf1732Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1732Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134215353) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (683105283/536870912) }, upper := { exponent := 0, mantissa := (10567/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268433209/268430706) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1732InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1732LocalValidity :
    LeafFacts leaf1732Box leaf1732Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1732Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134215353) }) = true
      norm_num [leaf1732Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1732CertificateValid :
    WideCertificateValid leaf1732Box leaf1732Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi147ValidityFacts
    leaf1732LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1732CoverageChecked :
    coverageCheck (innerAD leaf1732Box) leaf1732InnerLog = true := by
  rfl'

private theorem leaf1732InnerLogValid :
    leaf1732InnerLog.Valid 8 (innerAD leaf1732Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1732CoverageChecked

private noncomputable def leaf1732InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1732InputLogOnePlusV_eq :
    leaf1732InputLogOnePlusV = outerEnclosure 24
      (leaf1732Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1732RoundedFacts : LeafRoundedFacts 8
    leaf1732Certificate.logOnePlusV leaf1732InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1732InputLogOnePlusV_eq }

private noncomputable def leaf1732Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi147InputQChi innerPair16Input
    leaf1732InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1732LowerChecked :
    lowerCheck 24 leaf1732Box leaf1732Inputs = true := by
  rfl'

private theorem leaf1732CoversExact : CoversExact 8
    leaf1732Box leaf1732Certificate leaf1732InnerLog leaf1732Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi147RoundedFacts
    innerPair16RoundedFacts leaf1732RoundedFacts (by rfl)

private theorem leaf1732FlatSound : Sound leaf1732Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1732CertificateValid
    leaf1732InnerLogValid leaf1732CoversExact leaf1732LowerChecked

private noncomputable def leaf1733Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1733Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107667) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (684284857/536870912) }, upper := { exponent := 0, mantissa := (5293/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216595/134215334) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1733InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1733LocalValidity :
    LeafFacts leaf1733Box leaf1733Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1733Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107667) }) = true
      norm_num [leaf1733Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1733CertificateValid :
    WideCertificateValid leaf1733Box leaf1733Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi147ValidityFacts
    leaf1733LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1733CoverageChecked :
    coverageCheck (innerAD leaf1733Box) leaf1733InnerLog = true := by
  rfl'

private theorem leaf1733InnerLogValid :
    leaf1733InnerLog.Valid 8 (innerAD leaf1733Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1733CoverageChecked

private noncomputable def leaf1733InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814619/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1733InputLogOnePlusV_eq :
    leaf1733InputLogOnePlusV = outerEnclosure 24
      (leaf1733Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1733RoundedFacts : LeafRoundedFacts 8
    leaf1733Certificate.logOnePlusV leaf1733InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1733InputLogOnePlusV_eq }

private noncomputable def leaf1733Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi147InputQChi innerPair16Input
    leaf1733InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1733LowerChecked :
    lowerCheck 24 leaf1733Box leaf1733Inputs = true := by
  rfl'

private theorem leaf1733CoversExact : CoversExact 8
    leaf1733Box leaf1733Certificate leaf1733InnerLog leaf1733Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi147RoundedFacts
    innerPair16RoundedFacts leaf1733RoundedFacts (by rfl)

private theorem leaf1733FlatSound : Sound leaf1733Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1733CertificateValid
    leaf1733InnerLogValid leaf1733CoversExact leaf1733LowerChecked

private noncomputable def leaf1734Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1734Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553807) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (691231249/536870912) }, upper := { exponent := 0, mantissa := (2673/2048) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108271/67107614) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1734InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1734LocalValidity :
    LeafFacts leaf1734Box leaf1734Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1734Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553807) }) = true
      norm_num [leaf1734Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1734CertificateValid :
    WideCertificateValid leaf1734Box leaf1734Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi148ValidityFacts
    leaf1734LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1734CoverageChecked :
    coverageCheck (innerAD leaf1734Box) leaf1734InnerLog = true := by
  rfl'

private theorem leaf1734InnerLogValid :
    leaf1734InnerLog.Valid 8 (innerAD leaf1734Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1734CoverageChecked

private noncomputable def leaf1734InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1734InputLogOnePlusV_eq :
    leaf1734InputLogOnePlusV = outerEnclosure 24
      (leaf1734Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1734RoundedFacts : LeafRoundedFacts 8
    leaf1734Certificate.logOnePlusV leaf1734InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1734InputLogOnePlusV_eq }

private noncomputable def leaf1734Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi148InputQChi innerPair16Input
    leaf1734InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1734LowerChecked :
    lowerCheck 24 leaf1734Box leaf1734Inputs = true := by
  rfl'

private theorem leaf1734CoversExact : CoversExact 8
    leaf1734Box leaf1734Certificate leaf1734InnerLog leaf1734Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi148RoundedFacts
    innerPair16RoundedFacts leaf1734RoundedFacts (by rfl)

private theorem leaf1734FlatSound : Sound leaf1734Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1734CertificateValid
    leaf1734InnerLogValid leaf1734CoversExact leaf1734LowerChecked

private noncomputable def leaf1735Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1735Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776901) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (692476355/536870912) }, upper := { exponent := 0, mantissa := (1339/1024) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554133/33553802) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1735InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1735LocalValidity :
    LeafFacts leaf1735Box leaf1735Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1735Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776901) }) = true
      norm_num [leaf1735Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1735CertificateValid :
    WideCertificateValid leaf1735Box leaf1735Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi148ValidityFacts
    leaf1735LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1735CoverageChecked :
    coverageCheck (innerAD leaf1735Box) leaf1735InnerLog = true := by
  rfl'

private theorem leaf1735InnerLogValid :
    leaf1735InnerLog.Valid 8 (innerAD leaf1735Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1735CoverageChecked

private noncomputable def leaf1735InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814623/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1735InputLogOnePlusV_eq :
    leaf1735InputLogOnePlusV = outerEnclosure 24
      (leaf1735Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1735RoundedFacts : LeafRoundedFacts 8
    leaf1735Certificate.logOnePlusV leaf1735InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1735InputLogOnePlusV_eq }

private noncomputable def leaf1735Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi148InputQChi innerPair16Input
    leaf1735InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1735LowerChecked :
    lowerCheck 24 leaf1735Box leaf1735Inputs = true := by
  rfl'

private theorem leaf1735CoversExact : CoversExact 8
    leaf1735Box leaf1735Certificate leaf1735InnerLog leaf1735Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi148RoundedFacts
    innerPair16RoundedFacts leaf1735RoundedFacts (by rfl)

private theorem leaf1735FlatSound : Sound leaf1735Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1735CertificateValid
    leaf1735InnerLogValid leaf1735CoversExact leaf1735LowerChecked

private noncomputable def leaf1736Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1736Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134215315) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (685464431/536870912) }, upper := { exponent := 0, mantissa := (10605/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268433171/268430630) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1736InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1736LocalValidity :
    LeafFacts leaf1736Box leaf1736Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1736Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134215315) }) = true
      norm_num [leaf1736Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1736CertificateValid :
    WideCertificateValid leaf1736Box leaf1736Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi147ValidityFacts
    leaf1736LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1736CoverageChecked :
    coverageCheck (innerAD leaf1736Box) leaf1736InnerLog = true := by
  rfl'

private theorem leaf1736InnerLogValid :
    leaf1736InnerLog.Valid 8 (innerAD leaf1736Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1736CoverageChecked

private noncomputable def leaf1736InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1736InputLogOnePlusV_eq :
    leaf1736InputLogOnePlusV = outerEnclosure 24
      (leaf1736Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1736RoundedFacts : LeafRoundedFacts 8
    leaf1736Certificate.logOnePlusV leaf1736InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1736InputLogOnePlusV_eq }

private noncomputable def leaf1736Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi147InputQChi innerPair16Input
    leaf1736InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1736LowerChecked :
    lowerCheck 24 leaf1736Box leaf1736Inputs = true := by
  rfl'

private theorem leaf1736CoversExact : CoversExact 8
    leaf1736Box leaf1736Certificate leaf1736InnerLog leaf1736Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi147RoundedFacts
    innerPair16RoundedFacts leaf1736RoundedFacts (by rfl)

private theorem leaf1736FlatSound : Sound leaf1736Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1736CertificateValid
    leaf1736InnerLogValid leaf1736CoversExact leaf1736LowerChecked

private noncomputable def leaf1737Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1737Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (65527/65536), upper := (1048577/1048557) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (686644005/536870912) }, upper := { exponent := 0, mantissa := (83/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (1048567/1048557) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1737InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1737LocalValidity :
    LeafFacts leaf1737Box leaf1737Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1737Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048577/1048557) }) = true
      norm_num [leaf1737Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1737CertificateValid :
    WideCertificateValid leaf1737Box leaf1737Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi147ValidityFacts
    leaf1737LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1737CoverageChecked :
    coverageCheck (innerAD leaf1737Box) leaf1737InnerLog = true := by
  rfl'

private theorem leaf1737InnerLogValid :
    leaf1737InnerLog.Valid 8 (innerAD leaf1737Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1737CoverageChecked

private noncomputable def leaf1737InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1737InputLogOnePlusV_eq :
    leaf1737InputLogOnePlusV = outerEnclosure 24
      (leaf1737Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1737RoundedFacts : LeafRoundedFacts 8
    leaf1737Certificate.logOnePlusV leaf1737InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1737InputLogOnePlusV_eq }

private noncomputable def leaf1737Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi147InputQChi innerPair16Input
    leaf1737InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1737LowerChecked :
    lowerCheck 24 leaf1737Box leaf1737Inputs = true := by
  rfl'

private theorem leaf1737CoversExact : CoversExact 8
    leaf1737Box leaf1737Certificate leaf1737InnerLog leaf1737Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi147RoundedFacts
    innerPair16RoundedFacts leaf1737RoundedFacts (by rfl)

private theorem leaf1737FlatSound : Sound leaf1737Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1737CertificateValid
    leaf1737InnerLogValid leaf1737CoversExact leaf1737LowerChecked

private noncomputable def leaf1738Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1738Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553797) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (693721461/536870912) }, upper := { exponent := 0, mantissa := (2683/2048) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108261/67107594) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1738InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1738LocalValidity :
    LeafFacts leaf1738Box leaf1738Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1738Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553797) }) = true
      norm_num [leaf1738Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1738CertificateValid :
    WideCertificateValid leaf1738Box leaf1738Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi148ValidityFacts
    leaf1738LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1738CoverageChecked :
    coverageCheck (innerAD leaf1738Box) leaf1738InnerLog = true := by
  rfl'

private theorem leaf1738InnerLogValid :
    leaf1738InnerLog.Valid 8 (innerAD leaf1738Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1738CoverageChecked

private noncomputable def leaf1738InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1738InputLogOnePlusV_eq :
    leaf1738InputLogOnePlusV = outerEnclosure 24
      (leaf1738Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1738RoundedFacts : LeafRoundedFacts 8
    leaf1738Certificate.logOnePlusV leaf1738InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1738InputLogOnePlusV_eq }

private noncomputable def leaf1738Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi148InputQChi innerPair16Input
    leaf1738InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1738LowerChecked :
    lowerCheck 24 leaf1738Box leaf1738Inputs = true := by
  rfl'

private theorem leaf1738CoversExact : CoversExact 8
    leaf1738Box leaf1738Certificate leaf1738InnerLog leaf1738Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi148RoundedFacts
    innerPair16RoundedFacts leaf1738RoundedFacts (by rfl)

private theorem leaf1738FlatSound : Sound leaf1738Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1738CertificateValid
    leaf1738InnerLogValid leaf1738CoversExact leaf1738LowerChecked

private noncomputable def leaf1739Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1739Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871207/536870912) }, vSqrt := { lower := (65527/65536), upper := (1048577/1048556) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (694966567/536870912) }, upper := { exponent := 0, mantissa := (21/16) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (2097133/2097112) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1739InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1739LocalValidity :
    LeafFacts leaf1739Box leaf1739Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1739Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048577/1048556) }) = true
      norm_num [leaf1739Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1739CertificateValid :
    WideCertificateValid leaf1739Box leaf1739Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi148ValidityFacts
    leaf1739LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1739CoverageChecked :
    coverageCheck (innerAD leaf1739Box) leaf1739InnerLog = true := by
  rfl'

private theorem leaf1739InnerLogValid :
    leaf1739InnerLog.Valid 8 (innerAD leaf1739Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1739CoverageChecked

private noncomputable def leaf1739InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1739InputLogOnePlusV_eq :
    leaf1739InputLogOnePlusV = outerEnclosure 24
      (leaf1739Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1739RoundedFacts : LeafRoundedFacts 8
    leaf1739Certificate.logOnePlusV leaf1739InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1739InputLogOnePlusV_eq }

private noncomputable def leaf1739Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi148InputQChi innerPair16Input
    leaf1739InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1739LowerChecked :
    lowerCheck 24 leaf1739Box leaf1739Inputs = true := by
  rfl'

private theorem leaf1739CoversExact : CoversExact 8
    leaf1739Box leaf1739Certificate leaf1739InnerLog leaf1739Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi148RoundedFacts
    innerPair16RoundedFacts leaf1739RoundedFacts (by rfl)

private theorem leaf1739FlatSound : Sound leaf1739Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1739CertificateValid
    leaf1739InnerLogValid leaf1739CoversExact leaf1739LowerChecked

private noncomputable def leaf1740Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1740Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (8191/8192), upper := (7895168/7895011) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (694114663/536870912) }, upper := { exponent := 0, mantissa := (10733/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (15790179/15790022) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf1740InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1740LocalValidity :
    LeafFacts leaf1740Box leaf1740Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1740Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (7895168/7895011) }) = true
      norm_num [leaf1740Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1740CertificateValid :
    WideCertificateValid leaf1740Box leaf1740Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi127ValidityFacts
    leaf1740LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1740CoverageChecked :
    coverageCheck (innerAD leaf1740Box) leaf1740InnerLog = true := by
  rfl'

private theorem leaf1740InnerLogValid :
    leaf1740InnerLog.Valid 8 (innerAD leaf1740Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1740CoverageChecked

private noncomputable def leaf1740InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf1740InputLogOnePlusV_eq :
    leaf1740InputLogOnePlusV = outerEnclosure 24
      (leaf1740Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1740RoundedFacts : LeafRoundedFacts 8
    leaf1740Certificate.logOnePlusV leaf1740InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1740InputLogOnePlusV_eq }

private noncomputable def leaf1740Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi127InputQChi innerPair16Input
    leaf1740InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1740LowerChecked :
    lowerCheck 24 leaf1740Box leaf1740Inputs = true := by
  rfl'

private theorem leaf1740CoversExact : CoversExact 8
    leaf1740Box leaf1740Certificate leaf1740InnerLog leaf1740Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi127RoundedFacts
    innerPair16RoundedFacts leaf1740RoundedFacts (by rfl)

private theorem leaf1740FlatSound : Sound leaf1740Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1740CertificateValid
    leaf1740InnerLogValid leaf1740CoversExact leaf1740LowerChecked

private noncomputable def leaf1741Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1741Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107583) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (695425301/536870912) }, upper := { exponent := 0, mantissa := (5377/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216511/134215166) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf1741InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1741LocalValidity :
    LeafFacts leaf1741Box leaf1741Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1741Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107583) }) = true
      norm_num [leaf1741Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1741CertificateValid :
    WideCertificateValid leaf1741Box leaf1741Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi127ValidityFacts
    leaf1741LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1741CoverageChecked :
    coverageCheck (innerAD leaf1741Box) leaf1741InnerLog = true := by
  rfl'

private theorem leaf1741InnerLogValid :
    leaf1741InnerLog.Valid 8 (innerAD leaf1741Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1741CoverageChecked

private noncomputable def leaf1741InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1741InputLogOnePlusV_eq :
    leaf1741InputLogOnePlusV = outerEnclosure 24
      (leaf1741Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1741RoundedFacts : LeafRoundedFacts 8
    leaf1741Certificate.logOnePlusV leaf1741InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1741InputLogOnePlusV_eq }

private noncomputable def leaf1741Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi127InputQChi innerPair17Input
    leaf1741InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1741LowerChecked :
    lowerCheck 24 leaf1741Box leaf1741Inputs = true := by
  rfl'

private theorem leaf1741CoversExact : CoversExact 8
    leaf1741Box leaf1741Certificate leaf1741InnerLog leaf1741Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi127RoundedFacts
    innerPair17RoundedFacts leaf1741RoundedFacts (by rfl)

private theorem leaf1741FlatSound : Sound leaf1741Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1741CertificateValid
    leaf1741InnerLogValid leaf1741CoversExact leaf1741LowerChecked

private noncomputable def leaf1742Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1742Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107533) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (701978501/536870912) }, upper := { exponent := 0, mantissa := (5427/4096) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216461/134215066) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf1742InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1742LocalValidity :
    LeafFacts leaf1742Box leaf1742Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1742Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107533) }) = true
      norm_num [leaf1742Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1742CertificateValid :
    WideCertificateValid leaf1742Box leaf1742Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi128ValidityFacts
    leaf1742LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1742CoverageChecked :
    coverageCheck (innerAD leaf1742Box) leaf1742InnerLog = true := by
  rfl'

private theorem leaf1742InnerLogValid :
    leaf1742InnerLog.Valid 8 (innerAD leaf1742Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1742CoverageChecked

private noncomputable def leaf1742InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1742InputLogOnePlusV_eq :
    leaf1742InputLogOnePlusV = outerEnclosure 24
      (leaf1742Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1742RoundedFacts : LeafRoundedFacts 8
    leaf1742Certificate.logOnePlusV leaf1742InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1742InputLogOnePlusV_eq }

private noncomputable def leaf1742Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi128InputQChi innerPair17Input
    leaf1742InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1742LowerChecked :
    lowerCheck 24 leaf1742Box leaf1742Inputs = true := by
  rfl'

private theorem leaf1742CoversExact : CoversExact 8
    leaf1742Box leaf1742Certificate leaf1742InnerLog leaf1742Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi128RoundedFacts
    innerPair17RoundedFacts leaf1742RoundedFacts (by rfl)

private theorem leaf1742FlatSound : Sound leaf1742Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1742CertificateValid
    leaf1742InnerLogValid leaf1742CoversExact leaf1742LowerChecked

private noncomputable def leaf1743Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1743Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553761) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (703354671/536870912) }, upper := { exponent := 0, mantissa := (2719/2048) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108225/67107522) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf1743InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1743LocalValidity :
    LeafFacts leaf1743Box leaf1743Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1743Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553761) }) = true
      norm_num [leaf1743Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1743CertificateValid :
    WideCertificateValid leaf1743Box leaf1743Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi128ValidityFacts
    leaf1743LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1743CoverageChecked :
    coverageCheck (innerAD leaf1743Box) leaf1743InnerLog = true := by
  rfl'

private theorem leaf1743InnerLogValid :
    leaf1743InnerLog.Valid 8 (innerAD leaf1743Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1743CoverageChecked

private noncomputable def leaf1743InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453657/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1743InputLogOnePlusV_eq :
    leaf1743InputLogOnePlusV = outerEnclosure 24
      (leaf1743Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1743RoundedFacts : LeafRoundedFacts 8
    leaf1743Certificate.logOnePlusV leaf1743InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1743InputLogOnePlusV_eq }

private noncomputable def leaf1743Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi128InputQChi innerPair17Input
    leaf1743InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1743LowerChecked :
    lowerCheck 24 leaf1743Box leaf1743Inputs = true := by
  rfl'

private theorem leaf1743CoversExact : CoversExact 8
    leaf1743Box leaf1743Certificate leaf1743InnerLog leaf1743Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi128RoundedFacts
    innerPair17RoundedFacts leaf1743RoundedFacts (by rfl)

private theorem leaf1743FlatSound : Sound leaf1743Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1743CertificateValid
    leaf1743InnerLogValid leaf1743CoversExact leaf1743LowerChecked

private noncomputable def leaf1744Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1744Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134215145) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (696735939/536870912) }, upper := { exponent := 0, mantissa := (10775/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268433001/268430290) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf1744InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1744LocalValidity :
    LeafFacts leaf1744Box leaf1744Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1744Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134215145) }) = true
      norm_num [leaf1744Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1744CertificateValid :
    WideCertificateValid leaf1744Box leaf1744Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi127ValidityFacts
    leaf1744LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1744CoverageChecked :
    coverageCheck (innerAD leaf1744Box) leaf1744InnerLog = true := by
  rfl'

private theorem leaf1744InnerLogValid :
    leaf1744InnerLog.Valid 8 (innerAD leaf1744Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1744CoverageChecked

private noncomputable def leaf1744InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1744InputLogOnePlusV_eq :
    leaf1744InputLogOnePlusV = outerEnclosure 24
      (leaf1744Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1744RoundedFacts : LeafRoundedFacts 8
    leaf1744Certificate.logOnePlusV leaf1744InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1744InputLogOnePlusV_eq }

private noncomputable def leaf1744Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi127InputQChi innerPair17Input
    leaf1744InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1744LowerChecked :
    lowerCheck 24 leaf1744Box leaf1744Inputs = true := by
  rfl'

private theorem leaf1744CoversExact : CoversExact 8
    leaf1744Box leaf1744Certificate leaf1744InnerLog leaf1744Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi127RoundedFacts
    innerPair17RoundedFacts leaf1744RoundedFacts (by rfl)

private theorem leaf1744FlatSound : Sound leaf1744Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1744CertificateValid
    leaf1744InnerLogValid leaf1744CoversExact leaf1744LowerChecked

private noncomputable def leaf1745Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1745Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553781) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (698046577/536870912) }, upper := { exponent := 0, mantissa := (2699/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108245/67107562) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1745InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1745LocalValidity :
    LeafFacts leaf1745Box leaf1745Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1745Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553781) }) = true
      norm_num [leaf1745Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1745CertificateValid :
    WideCertificateValid leaf1745Box leaf1745Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi127ValidityFacts
    leaf1745LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1745CoverageChecked :
    coverageCheck (innerAD leaf1745Box) leaf1745InnerLog = true := by
  rfl'

private theorem leaf1745InnerLogValid :
    leaf1745InnerLog.Valid 8 (innerAD leaf1745Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1745CoverageChecked

private noncomputable def leaf1745InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1745InputLogOnePlusV_eq :
    leaf1745InputLogOnePlusV = outerEnclosure 24
      (leaf1745Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1745RoundedFacts : LeafRoundedFacts 8
    leaf1745Certificate.logOnePlusV leaf1745InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1745InputLogOnePlusV_eq }

private noncomputable def leaf1745Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi127InputQChi innerPair17Input
    leaf1745InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1745LowerChecked :
    lowerCheck 24 leaf1745Box leaf1745Inputs = true := by
  rfl'

private theorem leaf1745CoversExact : CoversExact 8
    leaf1745Box leaf1745Certificate leaf1745InnerLog leaf1745Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi127RoundedFacts
    innerPair17RoundedFacts leaf1745RoundedFacts (by rfl)

private theorem leaf1745FlatSound : Sound leaf1745Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1745CertificateValid
    leaf1745InnerLogValid leaf1745CoversExact leaf1745LowerChecked

private noncomputable def leaf1746Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1746Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107511) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (704730841/536870912) }, upper := { exponent := 0, mantissa := (5449/4096) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216439/134215022) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf1746InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1746LocalValidity :
    LeafFacts leaf1746Box leaf1746Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1746Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107511) }) = true
      norm_num [leaf1746Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1746CertificateValid :
    WideCertificateValid leaf1746Box leaf1746Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi128ValidityFacts
    leaf1746LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1746CoverageChecked :
    coverageCheck (innerAD leaf1746Box) leaf1746InnerLog = true := by
  rfl'

private theorem leaf1746InnerLogValid :
    leaf1746InnerLog.Valid 8 (innerAD leaf1746Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1746CoverageChecked

private noncomputable def leaf1746InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1746InputLogOnePlusV_eq :
    leaf1746InputLogOnePlusV = outerEnclosure 24
      (leaf1746Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1746RoundedFacts : LeafRoundedFacts 8
    leaf1746Certificate.logOnePlusV leaf1746InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1746InputLogOnePlusV_eq }

private noncomputable def leaf1746Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi128InputQChi innerPair21Input
    leaf1746InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1746LowerChecked :
    lowerCheck 24 leaf1746Box leaf1746Inputs = true := by
  rfl'

private theorem leaf1746CoversExact : CoversExact 8
    leaf1746Box leaf1746Certificate leaf1746InnerLog leaf1746Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi128RoundedFacts
    innerPair21RoundedFacts leaf1746RoundedFacts (by rfl)

private theorem leaf1746FlatSound : Sound leaf1746Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1746CertificateValid
    leaf1746InnerLogValid leaf1746CoversExact leaf1746LowerChecked

private noncomputable def leaf1747Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1747Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (8191/8192), upper := (986896/986875) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (706107011/536870912) }, upper := { exponent := 0, mantissa := (1365/1024) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1973771/1973750) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1747InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1747LocalValidity :
    LeafFacts leaf1747Box leaf1747Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1747Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (986896/986875) }) = true
      norm_num [leaf1747Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1747CertificateValid :
    WideCertificateValid leaf1747Box leaf1747Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi128ValidityFacts
    leaf1747LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1747CoverageChecked :
    coverageCheck (innerAD leaf1747Box) leaf1747InnerLog = true := by
  rfl'

private theorem leaf1747InnerLogValid :
    leaf1747InnerLog.Valid 8 (innerAD leaf1747Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1747CoverageChecked

private noncomputable def leaf1747InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1747InputLogOnePlusV_eq :
    leaf1747InputLogOnePlusV = outerEnclosure 24
      (leaf1747Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1747RoundedFacts : LeafRoundedFacts 8
    leaf1747Certificate.logOnePlusV leaf1747InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1747InputLogOnePlusV_eq }

private noncomputable def leaf1747Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi128InputQChi innerPair21Input
    leaf1747InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1747LowerChecked :
    lowerCheck 24 leaf1747Box leaf1747Inputs = true := by
  rfl'

private theorem leaf1747CoversExact : CoversExact 8
    leaf1747Box leaf1747Certificate leaf1747InnerLog leaf1747Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi128RoundedFacts
    innerPair21RoundedFacts leaf1747RoundedFacts (by rfl)

private theorem leaf1747FlatSound : Sound leaf1747Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1747CertificateValid
    leaf1747InnerLogValid leaf1747CoversExact leaf1747LowerChecked

private noncomputable def leaf1748Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1748Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214945) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (709842339/536870912) }, upper := { exponent := 0, mantissa := (10975/8192) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432801/268429890) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf1748InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1748LocalValidity :
    LeafFacts leaf1748Box leaf1748Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1748Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214945) }) = true
      norm_num [leaf1748Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1748CertificateValid :
    WideCertificateValid leaf1748Box leaf1748Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi129ValidityFacts
    leaf1748LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1748CoverageChecked :
    coverageCheck (innerAD leaf1748Box) leaf1748InnerLog = true := by
  rfl'

private theorem leaf1748InnerLogValid :
    leaf1748InnerLog.Valid 8 (innerAD leaf1748Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1748CoverageChecked

private noncomputable def leaf1748InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1748InputLogOnePlusV_eq :
    leaf1748InputLogOnePlusV = outerEnclosure 24
      (leaf1748Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1748RoundedFacts : LeafRoundedFacts 8
    leaf1748Certificate.logOnePlusV leaf1748InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1748InputLogOnePlusV_eq }

private noncomputable def leaf1748Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi129InputQChi innerPair21Input
    leaf1748InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1748LowerChecked :
    lowerCheck 24 leaf1748Box leaf1748Inputs = true := by
  rfl'

private theorem leaf1748CoversExact : CoversExact 8
    leaf1748Box leaf1748Certificate leaf1748InnerLog leaf1748Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi129RoundedFacts
    innerPair21RoundedFacts leaf1748RoundedFacts (by rfl)

private theorem leaf1748FlatSound : Sound leaf1748Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1748CertificateValid
    leaf1748InnerLogValid leaf1748CoversExact leaf1748LowerChecked

private noncomputable def leaf1749Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1749Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107461) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (711284041/536870912) }, upper := { exponent := 0, mantissa := (5499/4096) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216389/134214922) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf1749InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1749LocalValidity :
    LeafFacts leaf1749Box leaf1749Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1749Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107461) }) = true
      norm_num [leaf1749Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1749CertificateValid :
    WideCertificateValid leaf1749Box leaf1749Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi129ValidityFacts
    leaf1749LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1749CoverageChecked :
    coverageCheck (innerAD leaf1749Box) leaf1749InnerLog = true := by
  rfl'

private theorem leaf1749InnerLogValid :
    leaf1749InnerLog.Valid 8 (innerAD leaf1749Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1749CoverageChecked

private noncomputable def leaf1749InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726829/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1749InputLogOnePlusV_eq :
    leaf1749InputLogOnePlusV = outerEnclosure 24
      (leaf1749Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1749RoundedFacts : LeafRoundedFacts 8
    leaf1749Certificate.logOnePlusV leaf1749InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1749InputLogOnePlusV_eq }

private noncomputable def leaf1749Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi129InputQChi innerPair21Input
    leaf1749InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1749LowerChecked :
    lowerCheck 24 leaf1749Box leaf1749Inputs = true := by
  rfl'

private theorem leaf1749CoversExact : CoversExact 8
    leaf1749Box leaf1749Certificate leaf1749InnerLog leaf1749Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi129RoundedFacts
    innerPair21RoundedFacts leaf1749RoundedFacts (by rfl)

private theorem leaf1749FlatSound : Sound leaf1749Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1749CertificateValid
    leaf1749InnerLogValid leaf1749CoversExact leaf1749LowerChecked

private noncomputable def leaf1750Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1750Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871201/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776853) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (717706177/536870912) }, upper := { exponent := 0, mantissa := (1387/1024) } }, logOuter := sk169LogOuterCertificate, logK := sk169LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554085/33553706) } }, logDArg := sk169LogDArgCertificate }

private noncomputable def leaf1750InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1750LocalValidity :
    LeafFacts leaf1750Box leaf1750Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1750Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776853) }) = true
      norm_num [leaf1750Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1750CertificateValid :
    WideCertificateValid leaf1750Box leaf1750Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk169ValidityFacts chi130ValidityFacts
    leaf1750LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1750CoverageChecked :
    coverageCheck (innerAD leaf1750Box) leaf1750InnerLog = true := by
  rfl'

private theorem leaf1750InnerLogValid :
    leaf1750InnerLog.Valid 8 (innerAD leaf1750Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1750CoverageChecked

private noncomputable def leaf1750InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814635/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1750InputLogOnePlusV_eq :
    leaf1750InputLogOnePlusV = outerEnclosure 24
      (leaf1750Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1750RoundedFacts : LeafRoundedFacts 8
    leaf1750Certificate.logOnePlusV leaf1750InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1750InputLogOnePlusV_eq }

private noncomputable def leaf1750Inputs : Inputs :=
  inputsOfCaches globalInput sk169RoundedInputs
    chi130InputQChi innerPair21Input
    leaf1750InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1750LowerChecked :
    lowerCheck 24 leaf1750Box leaf1750Inputs = true := by
  rfl'

private theorem leaf1750CoversExact : CoversExact 8
    leaf1750Box leaf1750Certificate leaf1750InnerLog leaf1750Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk169RoundedFacts chi130RoundedFacts
    innerPair21RoundedFacts leaf1750RoundedFacts (by rfl)

private theorem leaf1750FlatSound : Sound leaf1750Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1750CertificateValid
    leaf1750InnerLogValid leaf1750CoversExact leaf1750LowerChecked

private noncomputable def leaf1751Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1751Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388425) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (719213411/536870912) }, upper := { exponent := 0, mantissa := (695/512) } }, logOuter := sk170LogOuterCertificate, logK := sk170LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777041/16776850) } }, logDArg := sk170LogDArgCertificate }

private noncomputable def leaf1751InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1751LocalValidity :
    LeafFacts leaf1751Box leaf1751Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1751Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388425) }) = true
      norm_num [leaf1751Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1751CertificateValid :
    WideCertificateValid leaf1751Box leaf1751Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk170ValidityFacts chi130ValidityFacts
    leaf1751LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1751CoverageChecked :
    coverageCheck (innerAD leaf1751Box) leaf1751InnerLog = true := by
  rfl'

private theorem leaf1751InnerLogValid :
    leaf1751InnerLog.Valid 8 (innerAD leaf1751Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1751CoverageChecked

private noncomputable def leaf1751InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1751InputLogOnePlusV_eq :
    leaf1751InputLogOnePlusV = outerEnclosure 24
      (leaf1751Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1751RoundedFacts : LeafRoundedFacts 8
    leaf1751Certificate.logOnePlusV leaf1751InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1751InputLogOnePlusV_eq }

private noncomputable def leaf1751Inputs : Inputs :=
  inputsOfCaches globalInput sk170RoundedInputs
    chi130InputQChi innerPair21Input
    leaf1751InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1751LowerChecked :
    lowerCheck 24 leaf1751Box leaf1751Inputs = true := by
  rfl'

private theorem leaf1751CoversExact : CoversExact 8
    leaf1751Box leaf1751Certificate leaf1751InnerLog leaf1751Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk170RoundedFacts chi130RoundedFacts
    innerPair21RoundedFacts leaf1751RoundedFacts (by rfl)

private theorem leaf1751FlatSound : Sound leaf1751Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1751CertificateValid
    leaf1751InnerLogValid leaf1751CoversExact leaf1751LowerChecked

private noncomputable def leaf1752Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1752Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214899) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (712725743/536870912) }, upper := { exponent := 0, mantissa := (11021/8192) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432755/268429798) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf1752InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1752LocalValidity :
    LeafFacts leaf1752Box leaf1752Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1752Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214899) }) = true
      norm_num [leaf1752Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1752CertificateValid :
    WideCertificateValid leaf1752Box leaf1752Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi129ValidityFacts
    leaf1752LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1752CoverageChecked :
    coverageCheck (innerAD leaf1752Box) leaf1752InnerLog = true := by
  rfl'

private theorem leaf1752InnerLogValid :
    leaf1752InnerLog.Valid 8 (innerAD leaf1752Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1752CoverageChecked

private noncomputable def leaf1752InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814633/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1752InputLogOnePlusV_eq :
    leaf1752InputLogOnePlusV = outerEnclosure 24
      (leaf1752Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1752RoundedFacts : LeafRoundedFacts 8
    leaf1752Certificate.logOnePlusV leaf1752InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1752InputLogOnePlusV_eq }

private noncomputable def leaf1752Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi129InputQChi innerPair21Input
    leaf1752InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1752LowerChecked :
    lowerCheck 24 leaf1752Box leaf1752Inputs = true := by
  rfl'

private theorem leaf1752CoversExact : CoversExact 8
    leaf1752Box leaf1752Certificate leaf1752InnerLog leaf1752Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi129RoundedFacts
    innerPair21RoundedFacts leaf1752RoundedFacts (by rfl)

private theorem leaf1752FlatSound : Sound leaf1752Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1752CertificateValid
    leaf1752InnerLogValid leaf1752CoversExact leaf1752LowerChecked

private noncomputable def leaf1753Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1753Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553719) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (714167445/536870912) }, upper := { exponent := 0, mantissa := (2761/2048) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108183/67107438) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1753InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1753LocalValidity :
    LeafFacts leaf1753Box leaf1753Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1753Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553719) }) = true
      norm_num [leaf1753Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1753CertificateValid :
    WideCertificateValid leaf1753Box leaf1753Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi129ValidityFacts
    leaf1753LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1753CoverageChecked :
    coverageCheck (innerAD leaf1753Box) leaf1753InnerLog = true := by
  rfl'

private theorem leaf1753InnerLogValid :
    leaf1753InnerLog.Valid 8 (innerAD leaf1753Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1753CoverageChecked

private noncomputable def leaf1753InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1753InputLogOnePlusV_eq :
    leaf1753InputLogOnePlusV = outerEnclosure 24
      (leaf1753Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1753RoundedFacts : LeafRoundedFacts 8
    leaf1753Certificate.logOnePlusV leaf1753InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1753InputLogOnePlusV_eq }

private noncomputable def leaf1753Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi129InputQChi innerPair21Input
    leaf1753InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1753LowerChecked :
    lowerCheck 24 leaf1753Box leaf1753Inputs = true := by
  rfl'

private theorem leaf1753CoversExact : CoversExact 8
    leaf1753Box leaf1753Certificate leaf1753InnerLog leaf1753Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi129RoundedFacts
    innerPair21RoundedFacts leaf1753RoundedFacts (by rfl)

private theorem leaf1753FlatSound : Sound leaf1753Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1753CertificateValid
    leaf1753InnerLogValid leaf1753CoversExact leaf1753LowerChecked

private noncomputable def leaf1754Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1754Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776847) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (720720645/536870912) }, upper := { exponent := 0, mantissa := (1393/1024) } }, logOuter := sk171LogOuterCertificate, logK := sk171LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554079/33553694) } }, logDArg := sk171LogDArgCertificate }

private noncomputable def leaf1754InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1754LocalValidity :
    LeafFacts leaf1754Box leaf1754Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1754Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776847) }) = true
      norm_num [leaf1754Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1754CertificateValid :
    WideCertificateValid leaf1754Box leaf1754Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk171ValidityFacts chi130ValidityFacts
    leaf1754LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1754CoverageChecked :
    coverageCheck (innerAD leaf1754Box) leaf1754InnerLog = true := by
  rfl'

private theorem leaf1754InnerLogValid :
    leaf1754InnerLog.Valid 8 (innerAD leaf1754Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1754CoverageChecked

private noncomputable def leaf1754InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1754InputLogOnePlusV_eq :
    leaf1754InputLogOnePlusV = outerEnclosure 24
      (leaf1754Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1754RoundedFacts : LeafRoundedFacts 8
    leaf1754Certificate.logOnePlusV leaf1754InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1754InputLogOnePlusV_eq }

private noncomputable def leaf1754Inputs : Inputs :=
  inputsOfCaches globalInput sk171RoundedInputs
    chi130InputQChi innerPair21Input
    leaf1754InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1754LowerChecked :
    lowerCheck 24 leaf1754Box leaf1754Inputs = true := by
  rfl'

private theorem leaf1754CoversExact : CoversExact 8
    leaf1754Box leaf1754Certificate leaf1754InnerLog leaf1754Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk171RoundedFacts chi130RoundedFacts
    innerPair21RoundedFacts leaf1754RoundedFacts (by rfl)

private theorem leaf1754FlatSound : Sound leaf1754Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1754CertificateValid
    leaf1754InnerLogValid leaf1754CoversExact leaf1754LowerChecked

private noncomputable def leaf1755Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1755Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871207/536870912) }, vSqrt := { lower := (8191/8192), upper := (4194308/4194211) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (722227879/536870912) }, upper := { exponent := 0, mantissa := (349/256) } }, logOuter := sk172LogOuterCertificate, logK := sk172LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388519/8388422) } }, logDArg := sk172LogDArgCertificate }

private noncomputable def leaf1755InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1755LocalValidity :
    LeafFacts leaf1755Box leaf1755Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1755Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194308/4194211) }) = true
      norm_num [leaf1755Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1755CertificateValid :
    WideCertificateValid leaf1755Box leaf1755Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk172ValidityFacts chi130ValidityFacts
    leaf1755LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1755CoverageChecked :
    coverageCheck (innerAD leaf1755Box) leaf1755InnerLog = true := by
  rfl'

private theorem leaf1755InnerLogValid :
    leaf1755InnerLog.Valid 8 (innerAD leaf1755Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1755CoverageChecked

private noncomputable def leaf1755InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629275/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1755InputLogOnePlusV_eq :
    leaf1755InputLogOnePlusV = outerEnclosure 24
      (leaf1755Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1755RoundedFacts : LeafRoundedFacts 8
    leaf1755Certificate.logOnePlusV leaf1755InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1755InputLogOnePlusV_eq }

private noncomputable def leaf1755Inputs : Inputs :=
  inputsOfCaches globalInput sk172RoundedInputs
    chi130InputQChi innerPair21Input
    leaf1755InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1755LowerChecked :
    lowerCheck 24 leaf1755Box leaf1755Inputs = true := by
  rfl'

private theorem leaf1755CoversExact : CoversExact 8
    leaf1755Box leaf1755Certificate leaf1755InnerLog leaf1755Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk172RoundedFacts chi130RoundedFacts
    innerPair21RoundedFacts leaf1755RoundedFacts (by rfl)

private theorem leaf1755FlatSound : Sound leaf1755Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1755CertificateValid
    leaf1755InnerLogValid leaf1755CoversExact leaf1755LowerChecked

private noncomputable def leaf1756Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1756Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871203/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134215103) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (699357215/536870912) }, upper := { exponent := 0, mantissa := (10817/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432959/268430206) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1756InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1756LocalValidity :
    LeafFacts leaf1756Box leaf1756Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1756Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134215103) }) = true
      norm_num [leaf1756Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1756CertificateValid :
    WideCertificateValid leaf1756Box leaf1756Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi127ValidityFacts
    leaf1756LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1756CoverageChecked :
    coverageCheck (innerAD leaf1756Box) leaf1756InnerLog = true := by
  rfl'

private theorem leaf1756InnerLogValid :
    leaf1756InnerLog.Valid 8 (innerAD leaf1756Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1756CoverageChecked

private noncomputable def leaf1756InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1756InputLogOnePlusV_eq :
    leaf1756InputLogOnePlusV = outerEnclosure 24
      (leaf1756Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1756RoundedFacts : LeafRoundedFacts 8
    leaf1756Certificate.logOnePlusV leaf1756InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1756InputLogOnePlusV_eq }

private noncomputable def leaf1756Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi127InputQChi innerPair17Input
    leaf1756InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1756LowerChecked :
    lowerCheck 24 leaf1756Box leaf1756Inputs = true := by
  rfl'

private theorem leaf1756CoversExact : CoversExact 8
    leaf1756Box leaf1756Certificate leaf1756InnerLog leaf1756Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi127RoundedFacts
    innerPair17RoundedFacts leaf1756RoundedFacts (by rfl)

private theorem leaf1756FlatSound : Sound leaf1756Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1756CertificateValid
    leaf1756InnerLogValid leaf1756CoversExact leaf1756LowerChecked

private noncomputable def leaf1757Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1757Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107541) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (700667853/536870912) }, upper := { exponent := 0, mantissa := (5419/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216469/134215082) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1757InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1757LocalValidity :
    LeafFacts leaf1757Box leaf1757Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1757Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107541) }) = true
      norm_num [leaf1757Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1757CertificateValid :
    WideCertificateValid leaf1757Box leaf1757Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi127ValidityFacts
    leaf1757LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1757CoverageChecked :
    coverageCheck (innerAD leaf1757Box) leaf1757InnerLog = true := by
  rfl'

private theorem leaf1757InnerLogValid :
    leaf1757InnerLog.Valid 8 (innerAD leaf1757Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1757CoverageChecked

private noncomputable def leaf1757InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1757InputLogOnePlusV_eq :
    leaf1757InputLogOnePlusV = outerEnclosure 24
      (leaf1757Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1757RoundedFacts : LeafRoundedFacts 8
    leaf1757Certificate.logOnePlusV leaf1757InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1757InputLogOnePlusV_eq }

private noncomputable def leaf1757Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi127InputQChi innerPair17Input
    leaf1757InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1757LowerChecked :
    lowerCheck 24 leaf1757Box leaf1757Inputs = true := by
  rfl'

private theorem leaf1757CoversExact : CoversExact 8
    leaf1757Box leaf1757Certificate leaf1757InnerLog leaf1757Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi127RoundedFacts
    innerPair17RoundedFacts leaf1757RoundedFacts (by rfl)

private theorem leaf1757FlatSound : Sound leaf1757Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1757CertificateValid
    leaf1757InnerLogValid leaf1757CoversExact leaf1757LowerChecked

private noncomputable def leaf1758Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1758Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871205/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107489) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (707483181/536870912) }, upper := { exponent := 0, mantissa := (5471/4096) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216417/134214978) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1758InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1758LocalValidity :
    LeafFacts leaf1758Box leaf1758Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1758Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107489) }) = true
      norm_num [leaf1758Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1758CertificateValid :
    WideCertificateValid leaf1758Box leaf1758Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi128ValidityFacts
    leaf1758LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1758CoverageChecked :
    coverageCheck (innerAD leaf1758Box) leaf1758InnerLog = true := by
  rfl'

private theorem leaf1758InnerLogValid :
    leaf1758InnerLog.Valid 8 (innerAD leaf1758Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1758CoverageChecked

private noncomputable def leaf1758InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1758InputLogOnePlusV_eq :
    leaf1758InputLogOnePlusV = outerEnclosure 24
      (leaf1758Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1758RoundedFacts : LeafRoundedFacts 8
    leaf1758Certificate.logOnePlusV leaf1758InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1758InputLogOnePlusV_eq }

private noncomputable def leaf1758Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi128InputQChi innerPair21Input
    leaf1758InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1758LowerChecked :
    lowerCheck 24 leaf1758Box leaf1758Inputs = true := by
  rfl'

private theorem leaf1758CoversExact : CoversExact 8
    leaf1758Box leaf1758Certificate leaf1758InnerLog leaf1758Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi128RoundedFacts
    innerPair21RoundedFacts leaf1758RoundedFacts (by rfl)

private theorem leaf1758FlatSound : Sound leaf1758Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1758CertificateValid
    leaf1758InnerLogValid leaf1758CoversExact leaf1758LowerChecked

private noncomputable def leaf1759Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1759Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871207/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553739) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (708859351/536870912) }, upper := { exponent := 0, mantissa := (2741/2048) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108203/67107478) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1759InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1759LocalValidity :
    LeafFacts leaf1759Box leaf1759Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1759Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553739) }) = true
      norm_num [leaf1759Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1759CertificateValid :
    WideCertificateValid leaf1759Box leaf1759Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi128ValidityFacts
    leaf1759LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1759CoverageChecked :
    coverageCheck (innerAD leaf1759Box) leaf1759InnerLog = true := by
  rfl'

private theorem leaf1759InnerLogValid :
    leaf1759InnerLog.Valid 8 (innerAD leaf1759Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1759CoverageChecked

private noncomputable def leaf1759InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814631/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1759InputLogOnePlusV_eq :
    leaf1759InputLogOnePlusV = outerEnclosure 24
      (leaf1759Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1759RoundedFacts : LeafRoundedFacts 8
    leaf1759Certificate.logOnePlusV leaf1759InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1759InputLogOnePlusV_eq }

private noncomputable def leaf1759Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi128InputQChi innerPair21Input
    leaf1759InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1759LowerChecked :
    lowerCheck 24 leaf1759Box leaf1759Inputs = true := by
  rfl'

private theorem leaf1759CoversExact : CoversExact 8
    leaf1759Box leaf1759Certificate leaf1759InnerLog leaf1759Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi128RoundedFacts
    innerPair21RoundedFacts leaf1759RoundedFacts (by rfl)

private theorem leaf1759FlatSound : Sound leaf1759Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1759CertificateValid
    leaf1759InnerLogValid leaf1759CoversExact leaf1759LowerChecked

private noncomputable def leaf1760Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1760Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871207/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134215061) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (701978491/536870912) }, upper := { exponent := 0, mantissa := (10859/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432917/268430122) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1760InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1760LocalValidity :
    LeafFacts leaf1760Box leaf1760Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1760Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134215061) }) = true
      norm_num [leaf1760Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1760CertificateValid :
    WideCertificateValid leaf1760Box leaf1760Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi127ValidityFacts
    leaf1760LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1760CoverageChecked :
    coverageCheck (innerAD leaf1760Box) leaf1760InnerLog = true := by
  rfl'

private theorem leaf1760InnerLogValid :
    leaf1760InnerLog.Valid 8 (innerAD leaf1760Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1760CoverageChecked

private noncomputable def leaf1760InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1760InputLogOnePlusV_eq :
    leaf1760InputLogOnePlusV = outerEnclosure 24
      (leaf1760Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1760RoundedFacts : LeafRoundedFacts 8
    leaf1760Certificate.logOnePlusV leaf1760InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1760InputLogOnePlusV_eq }

private noncomputable def leaf1760Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi127InputQChi innerPair17Input
    leaf1760InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1760LowerChecked :
    lowerCheck 24 leaf1760Box leaf1760Inputs = true := by
  rfl'

private theorem leaf1760CoversExact : CoversExact 8
    leaf1760Box leaf1760Certificate leaf1760InnerLog leaf1760Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi127RoundedFacts
    innerPair17RoundedFacts leaf1760RoundedFacts (by rfl)

private theorem leaf1760FlatSound : Sound leaf1760Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1760CertificateValid
    leaf1760InnerLogValid leaf1760CoversExact leaf1760LowerChecked

private noncomputable def leaf1761Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1761Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871209/536870912) }, vSqrt := { lower := (65527/65536), upper := (1048577/1048555) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (703289129/536870912) }, upper := { exponent := 0, mantissa := (85/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (1048566/1048555) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1761InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1761LocalValidity :
    LeafFacts leaf1761Box leaf1761Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1761Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048577/1048555) }) = true
      norm_num [leaf1761Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1761CertificateValid :
    WideCertificateValid leaf1761Box leaf1761Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi127ValidityFacts
    leaf1761LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1761CoverageChecked :
    coverageCheck (innerAD leaf1761Box) leaf1761InnerLog = true := by
  rfl'

private theorem leaf1761InnerLogValid :
    leaf1761InnerLog.Valid 8 (innerAD leaf1761Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1761CoverageChecked

private noncomputable def leaf1761InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1761InputLogOnePlusV_eq :
    leaf1761InputLogOnePlusV = outerEnclosure 24
      (leaf1761Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1761RoundedFacts : LeafRoundedFacts 8
    leaf1761Certificate.logOnePlusV leaf1761InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1761InputLogOnePlusV_eq }

private noncomputable def leaf1761Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi127InputQChi innerPair17Input
    leaf1761InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1761LowerChecked :
    lowerCheck 24 leaf1761Box leaf1761Inputs = true := by
  rfl'

private theorem leaf1761CoversExact : CoversExact 8
    leaf1761Box leaf1761Certificate leaf1761InnerLog leaf1761Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi127RoundedFacts
    innerPair17RoundedFacts leaf1761RoundedFacts (by rfl)

private theorem leaf1761FlatSound : Sound leaf1761Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1761CertificateValid
    leaf1761InnerLogValid leaf1761CoversExact leaf1761LowerChecked

private noncomputable def leaf1762Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1762Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871209/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107467) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (710235521/536870912) }, upper := { exponent := 0, mantissa := (5493/4096) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216395/134214934) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1762InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1762LocalValidity :
    LeafFacts leaf1762Box leaf1762Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1762Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107467) }) = true
      norm_num [leaf1762Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1762CertificateValid :
    WideCertificateValid leaf1762Box leaf1762Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi128ValidityFacts
    leaf1762LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1762CoverageChecked :
    coverageCheck (innerAD leaf1762Box) leaf1762InnerLog = true := by
  rfl'

private theorem leaf1762InnerLogValid :
    leaf1762InnerLog.Valid 8 (innerAD leaf1762Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1762CoverageChecked

private noncomputable def leaf1762InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1762InputLogOnePlusV_eq :
    leaf1762InputLogOnePlusV = outerEnclosure 24
      (leaf1762Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1762RoundedFacts : LeafRoundedFacts 8
    leaf1762Certificate.logOnePlusV leaf1762InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1762InputLogOnePlusV_eq }

private noncomputable def leaf1762Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi128InputQChi innerPair21Input
    leaf1762InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1762LowerChecked :
    lowerCheck 24 leaf1762Box leaf1762Inputs = true := by
  rfl'

private theorem leaf1762CoversExact : CoversExact 8
    leaf1762Box leaf1762Certificate leaf1762InnerLog leaf1762Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi128RoundedFacts
    innerPair21RoundedFacts leaf1762RoundedFacts (by rfl)

private theorem leaf1762FlatSound : Sound leaf1762Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1762CertificateValid
    leaf1762InnerLogValid leaf1762CoversExact leaf1762LowerChecked

private noncomputable def leaf1763Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1763Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871211/536870912) }, vSqrt := { lower := (65527/65536), upper := (1048577/1048554) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (711611691/536870912) }, upper := { exponent := 0, mantissa := (43/32) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (2097131/2097108) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1763InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1763LocalValidity :
    LeafFacts leaf1763Box leaf1763Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1763Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048577/1048554) }) = true
      norm_num [leaf1763Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1763CertificateValid :
    WideCertificateValid leaf1763Box leaf1763Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi128ValidityFacts
    leaf1763LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1763CoverageChecked :
    coverageCheck (innerAD leaf1763Box) leaf1763InnerLog = true := by
  rfl'

private theorem leaf1763InnerLogValid :
    leaf1763InnerLog.Valid 8 (innerAD leaf1763Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1763CoverageChecked

private noncomputable def leaf1763InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1763InputLogOnePlusV_eq :
    leaf1763InputLogOnePlusV = outerEnclosure 24
      (leaf1763Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1763RoundedFacts : LeafRoundedFacts 8
    leaf1763Certificate.logOnePlusV leaf1763InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1763InputLogOnePlusV_eq }

private noncomputable def leaf1763Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi128InputQChi innerPair21Input
    leaf1763InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1763LowerChecked :
    lowerCheck 24 leaf1763Box leaf1763Inputs = true := by
  rfl'

private theorem leaf1763CoversExact : CoversExact 8
    leaf1763Box leaf1763Certificate leaf1763InnerLog leaf1763Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi128RoundedFacts
    innerPair21RoundedFacts leaf1763RoundedFacts (by rfl)

private theorem leaf1763FlatSound : Sound leaf1763Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1763CertificateValid
    leaf1763InnerLogValid leaf1763CoversExact leaf1763LowerChecked

private noncomputable def leaf1764Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1764Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871207/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214853) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (715609147/536870912) }, upper := { exponent := 0, mantissa := (11067/8192) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432709/268429706) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1764InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1764LocalValidity :
    LeafFacts leaf1764Box leaf1764Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1764Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214853) }) = true
      norm_num [leaf1764Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1764CertificateValid :
    WideCertificateValid leaf1764Box leaf1764Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi129ValidityFacts
    leaf1764LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1764CoverageChecked :
    coverageCheck (innerAD leaf1764Box) leaf1764InnerLog = true := by
  rfl'

private theorem leaf1764InnerLogValid :
    leaf1764InnerLog.Valid 8 (innerAD leaf1764Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1764CoverageChecked

private noncomputable def leaf1764InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1764InputLogOnePlusV_eq :
    leaf1764InputLogOnePlusV = outerEnclosure 24
      (leaf1764Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1764RoundedFacts : LeafRoundedFacts 8
    leaf1764Certificate.logOnePlusV leaf1764InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1764InputLogOnePlusV_eq }

private noncomputable def leaf1764Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi129InputQChi innerPair21Input
    leaf1764InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1764LowerChecked :
    lowerCheck 24 leaf1764Box leaf1764Inputs = true := by
  rfl'

private theorem leaf1764CoversExact : CoversExact 8
    leaf1764Box leaf1764Certificate leaf1764InnerLog leaf1764Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi129RoundedFacts
    innerPair21RoundedFacts leaf1764RoundedFacts (by rfl)

private theorem leaf1764FlatSound : Sound leaf1764Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1764CertificateValid
    leaf1764InnerLogValid leaf1764CoversExact leaf1764LowerChecked

private noncomputable def leaf1765Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1765Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871209/536870912) }, vSqrt := { lower := (8191/8192), upper := (3947584/3947495) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (717050849/536870912) }, upper := { exponent := 0, mantissa := (5545/4096) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (7895079/7894990) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1765InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1765LocalValidity :
    LeafFacts leaf1765Box leaf1765Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1765Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3947584/3947495) }) = true
      norm_num [leaf1765Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1765CertificateValid :
    WideCertificateValid leaf1765Box leaf1765Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi129ValidityFacts
    leaf1765LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1765CoverageChecked :
    coverageCheck (innerAD leaf1765Box) leaf1765InnerLog = true := by
  rfl'

private theorem leaf1765InnerLogValid :
    leaf1765InnerLog.Valid 8 (innerAD leaf1765Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1765CoverageChecked

private noncomputable def leaf1765InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814635/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1765InputLogOnePlusV_eq :
    leaf1765InputLogOnePlusV = outerEnclosure 24
      (leaf1765Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1765RoundedFacts : LeafRoundedFacts 8
    leaf1765Certificate.logOnePlusV leaf1765InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1765InputLogOnePlusV_eq }

private noncomputable def leaf1765Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi129InputQChi innerPair21Input
    leaf1765InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1765LowerChecked :
    lowerCheck 24 leaf1765Box leaf1765Inputs = true := by
  rfl'

private theorem leaf1765CoversExact : CoversExact 8
    leaf1765Box leaf1765Certificate leaf1765InnerLog leaf1765Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi129RoundedFacts
    innerPair21RoundedFacts leaf1765RoundedFacts (by rfl)

private theorem leaf1765FlatSound : Sound leaf1765Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1765CertificateValid
    leaf1765InnerLogValid leaf1765CoversExact leaf1765LowerChecked

private noncomputable def leaf1766Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1766Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871209/536870912) }, vSqrt := { lower := (8191/8192), upper := (986896/986873) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (723735113/536870912) }, upper := { exponent := 0, mantissa := (1399/1024) } }, logOuter := sk173LogOuterCertificate, logK := sk173LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1973769/1973746) } }, logDArg := sk173LogDArgCertificate }

private noncomputable def leaf1766InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1766LocalValidity :
    LeafFacts leaf1766Box leaf1766Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1766Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (986896/986873) }) = true
      norm_num [leaf1766Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1766CertificateValid :
    WideCertificateValid leaf1766Box leaf1766Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk173ValidityFacts chi130ValidityFacts
    leaf1766LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1766CoverageChecked :
    coverageCheck (innerAD leaf1766Box) leaf1766InnerLog = true := by
  rfl'

private theorem leaf1766InnerLogValid :
    leaf1766InnerLog.Valid 8 (innerAD leaf1766Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1766CoverageChecked

private noncomputable def leaf1766InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1766InputLogOnePlusV_eq :
    leaf1766InputLogOnePlusV = outerEnclosure 24
      (leaf1766Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1766RoundedFacts : LeafRoundedFacts 8
    leaf1766Certificate.logOnePlusV leaf1766InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1766InputLogOnePlusV_eq }

private noncomputable def leaf1766Inputs : Inputs :=
  inputsOfCaches globalInput sk173RoundedInputs
    chi130InputQChi innerPair21Input
    leaf1766InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1766LowerChecked :
    lowerCheck 24 leaf1766Box leaf1766Inputs = true := by
  rfl'

private theorem leaf1766CoversExact : CoversExact 8
    leaf1766Box leaf1766Certificate leaf1766InnerLog leaf1766Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk173RoundedFacts chi130RoundedFacts
    innerPair21RoundedFacts leaf1766RoundedFacts (by rfl)

private theorem leaf1766FlatSound : Sound leaf1766Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1766CertificateValid
    leaf1766InnerLogValid leaf1766CoversExact leaf1766LowerChecked

private noncomputable def leaf1767Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1767Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871211/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388419) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (725242347/536870912) }, upper := { exponent := 0, mantissa := (701/512) } }, logOuter := sk174LogOuterCertificate, logK := sk174LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777035/16776838) } }, logDArg := sk174LogDArgCertificate }

private noncomputable def leaf1767InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1767LocalValidity :
    LeafFacts leaf1767Box leaf1767Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1767Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388419) }) = true
      norm_num [leaf1767Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1767CertificateValid :
    WideCertificateValid leaf1767Box leaf1767Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk174ValidityFacts chi130ValidityFacts
    leaf1767LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1767CoverageChecked :
    coverageCheck (innerAD leaf1767Box) leaf1767InnerLog = true := by
  rfl'

private theorem leaf1767InnerLogValid :
    leaf1767InnerLog.Valid 8 (innerAD leaf1767Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1767CoverageChecked

private noncomputable def leaf1767InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814639/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1767InputLogOnePlusV_eq :
    leaf1767InputLogOnePlusV = outerEnclosure 24
      (leaf1767Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1767RoundedFacts : LeafRoundedFacts 8
    leaf1767Certificate.logOnePlusV leaf1767InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1767InputLogOnePlusV_eq }

private noncomputable def leaf1767Inputs : Inputs :=
  inputsOfCaches globalInput sk174RoundedInputs
    chi130InputQChi innerPair21Input
    leaf1767InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1767LowerChecked :
    lowerCheck 24 leaf1767Box leaf1767Inputs = true := by
  rfl'

private theorem leaf1767CoversExact : CoversExact 8
    leaf1767Box leaf1767Certificate leaf1767InnerLog leaf1767Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk174RoundedFacts chi130RoundedFacts
    innerPair21RoundedFacts leaf1767RoundedFacts (by rfl)

private theorem leaf1767FlatSound : Sound leaf1767Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1767CertificateValid
    leaf1767InnerLogValid leaf1767CoversExact leaf1767LowerChecked

private noncomputable def leaf1768Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1768Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871211/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214807) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (718492551/536870912) }, upper := { exponent := 0, mantissa := (11113/8192) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432663/268429614) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1768InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1768LocalValidity :
    LeafFacts leaf1768Box leaf1768Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1768Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214807) }) = true
      norm_num [leaf1768Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1768CertificateValid :
    WideCertificateValid leaf1768Box leaf1768Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi129ValidityFacts
    leaf1768LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1768CoverageChecked :
    coverageCheck (innerAD leaf1768Box) leaf1768InnerLog = true := by
  rfl'

private theorem leaf1768InnerLogValid :
    leaf1768InnerLog.Valid 8 (innerAD leaf1768Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1768CoverageChecked

private noncomputable def leaf1768InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1768InputLogOnePlusV_eq :
    leaf1768InputLogOnePlusV = outerEnclosure 24
      (leaf1768Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1768RoundedFacts : LeafRoundedFacts 8
    leaf1768Certificate.logOnePlusV leaf1768InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1768InputLogOnePlusV_eq }

private noncomputable def leaf1768Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi129InputQChi innerPair21Input
    leaf1768InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1768LowerChecked :
    lowerCheck 24 leaf1768Box leaf1768Inputs = true := by
  rfl'

private theorem leaf1768CoversExact : CoversExact 8
    leaf1768Box leaf1768Certificate leaf1768InnerLog leaf1768Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi129RoundedFacts
    innerPair21RoundedFacts leaf1768RoundedFacts (by rfl)

private theorem leaf1768FlatSound : Sound leaf1768Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1768CertificateValid
    leaf1768InnerLogValid leaf1768CoversExact leaf1768LowerChecked

private noncomputable def leaf1769Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1769Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871213/536870912) }, vSqrt := { lower := (65527/65536), upper := (1048577/1048553) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (719934253/536870912) }, upper := { exponent := 0, mantissa := (87/64) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (1048565/1048553) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1769InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1769LocalValidity :
    LeafFacts leaf1769Box leaf1769Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1769Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048577/1048553) }) = true
      norm_num [leaf1769Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1769CertificateValid :
    WideCertificateValid leaf1769Box leaf1769Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi129ValidityFacts
    leaf1769LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1769CoverageChecked :
    coverageCheck (innerAD leaf1769Box) leaf1769InnerLog = true := by
  rfl'

private theorem leaf1769InnerLogValid :
    leaf1769InnerLog.Valid 8 (innerAD leaf1769Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1769CoverageChecked

private noncomputable def leaf1769InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1769InputLogOnePlusV_eq :
    leaf1769InputLogOnePlusV = outerEnclosure 24
      (leaf1769Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1769RoundedFacts : LeafRoundedFacts 8
    leaf1769Certificate.logOnePlusV leaf1769InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1769InputLogOnePlusV_eq }

private noncomputable def leaf1769Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi129InputQChi innerPair21Input
    leaf1769InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1769LowerChecked :
    lowerCheck 24 leaf1769Box leaf1769Inputs = true := by
  rfl'

private theorem leaf1769CoversExact : CoversExact 8
    leaf1769Box leaf1769Certificate leaf1769InnerLog leaf1769Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi129RoundedFacts
    innerPair21RoundedFacts leaf1769RoundedFacts (by rfl)

private theorem leaf1769FlatSound : Sound leaf1769Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1769CertificateValid
    leaf1769InnerLogValid leaf1769CoversExact leaf1769LowerChecked

private noncomputable def leaf1770Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1770Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871213/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776835) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (726749581/536870912) }, upper := { exponent := 0, mantissa := (1405/1024) } }, logOuter := sk175LogOuterCertificate, logK := sk175LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554067/33553670) } }, logDArg := sk175LogDArgCertificate }

private noncomputable def leaf1770InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1770LocalValidity :
    LeafFacts leaf1770Box leaf1770Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1770Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776835) }) = true
      norm_num [leaf1770Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1770CertificateValid :
    WideCertificateValid leaf1770Box leaf1770Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk175ValidityFacts chi130ValidityFacts
    leaf1770LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1770CoverageChecked :
    coverageCheck (innerAD leaf1770Box) leaf1770InnerLog = true := by
  rfl'

private theorem leaf1770InnerLogValid :
    leaf1770InnerLog.Valid 8 (innerAD leaf1770Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1770CoverageChecked

private noncomputable def leaf1770InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1770InputLogOnePlusV_eq :
    leaf1770InputLogOnePlusV = outerEnclosure 24
      (leaf1770Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1770RoundedFacts : LeafRoundedFacts 8
    leaf1770Certificate.logOnePlusV leaf1770InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1770InputLogOnePlusV_eq }

private noncomputable def leaf1770Inputs : Inputs :=
  inputsOfCaches globalInput sk175RoundedInputs
    chi130InputQChi innerPair21Input
    leaf1770InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1770LowerChecked :
    lowerCheck 24 leaf1770Box leaf1770Inputs = true := by
  rfl'

private theorem leaf1770CoversExact : CoversExact 8
    leaf1770Box leaf1770Certificate leaf1770InnerLog leaf1770Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk175RoundedFacts chi130RoundedFacts
    innerPair21RoundedFacts leaf1770RoundedFacts (by rfl)

private theorem leaf1770FlatSound : Sound leaf1770Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1770CertificateValid
    leaf1770InnerLogValid leaf1770CoversExact leaf1770LowerChecked

private noncomputable def leaf1771Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1771Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871215/536870912) }, vSqrt := { lower := (65527/65536), upper := (1048577/1048552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (728256815/536870912) }, upper := { exponent := 0, mantissa := (11/8) } }, logOuter := sk176LogOuterCertificate, logK := sk176LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (2097129/2097104) } }, logDArg := sk176LogDArgCertificate }

private noncomputable def leaf1771InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1771LocalValidity :
    LeafFacts leaf1771Box leaf1771Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1771Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1048577/1048552) }) = true
      norm_num [leaf1771Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1771CertificateValid :
    WideCertificateValid leaf1771Box leaf1771Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk176ValidityFacts chi130ValidityFacts
    leaf1771LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1771CoverageChecked :
    coverageCheck (innerAD leaf1771Box) leaf1771InnerLog = true := by
  rfl'

private theorem leaf1771InnerLogValid :
    leaf1771InnerLog.Valid 8 (innerAD leaf1771Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1771CoverageChecked

private noncomputable def leaf1771InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1771InputLogOnePlusV_eq :
    leaf1771InputLogOnePlusV = outerEnclosure 24
      (leaf1771Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1771RoundedFacts : LeafRoundedFacts 8
    leaf1771Certificate.logOnePlusV leaf1771InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1771InputLogOnePlusV_eq }

private noncomputable def leaf1771Inputs : Inputs :=
  inputsOfCaches globalInput sk176RoundedInputs
    chi130InputQChi innerPair21Input
    leaf1771InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1771LowerChecked :
    lowerCheck 24 leaf1771Box leaf1771Inputs = true := by
  rfl'

private theorem leaf1771CoversExact : CoversExact 8
    leaf1771Box leaf1771Certificate leaf1771InnerLog leaf1771Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk176RoundedFacts chi130RoundedFacts
    innerPair21RoundedFacts leaf1771RoundedFacts (by rfl)

private theorem leaf1771FlatSound : Sound leaf1771Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1771CertificateValid
    leaf1771InnerLogValid leaf1771CoversExact leaf1771LowerChecked

private noncomputable def component39Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (17/256), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node0_sound : Sound component39Node0Box :=
  sound_of_literal_split component39Node0Box leaf1711Box leaf1712Box
    .k (121/32) (by rfl) (by rfl)
    leaf1711FlatSound leaf1712FlatSound

private noncomputable def component39Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node1_sound : Sound component39Node1Box :=
  sound_of_literal_split component39Node1Box leaf1710Box component39Node0Box
    .chi (17/256) (by rfl) (by rfl)
    leaf1710FlatSound component39Node0_sound

private noncomputable def component39Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (17/256), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node2_sound : Sound component39Node2Box :=
  sound_of_literal_split component39Node2Box leaf1714Box leaf1715Box
    .k (123/32) (by rfl) (by rfl)
    leaf1714FlatSound leaf1715FlatSound

private noncomputable def component39Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node3_sound : Sound component39Node3Box :=
  sound_of_literal_split component39Node3Box leaf1713Box component39Node2Box
    .chi (17/256) (by rfl) (by rfl)
    leaf1713FlatSound component39Node2_sound

private noncomputable def component39Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node4_sound : Sound component39Node4Box :=
  sound_of_literal_split component39Node4Box component39Node1Box component39Node3Box
    .k (61/16) (by rfl) (by rfl)
    component39Node1_sound component39Node3_sound

private noncomputable def component39Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (9/128), chiHi := (19/256) }

set_option maxRecDepth 1000000 in
private theorem component39Node5_sound : Sound component39Node5Box :=
  sound_of_literal_split component39Node5Box leaf1716Box leaf1717Box
    .k (121/32) (by rfl) (by rfl)
    leaf1716FlatSound leaf1717FlatSound

private noncomputable def component39Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (19/256), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component39Node6_sound : Sound component39Node6Box :=
  sound_of_literal_split component39Node6Box leaf1718Box leaf1719Box
    .k (121/32) (by rfl) (by rfl)
    leaf1718FlatSound leaf1719FlatSound

private noncomputable def component39Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component39Node7_sound : Sound component39Node7Box :=
  sound_of_literal_split component39Node7Box component39Node5Box component39Node6Box
    .chi (19/256) (by rfl) (by rfl)
    component39Node5_sound component39Node6_sound

private noncomputable def component39Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (9/128), chiHi := (19/256) }

set_option maxRecDepth 1000000 in
private theorem component39Node8_sound : Sound component39Node8Box :=
  sound_of_literal_split component39Node8Box leaf1720Box leaf1721Box
    .k (123/32) (by rfl) (by rfl)
    leaf1720FlatSound leaf1721FlatSound

private noncomputable def component39Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (19/256), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component39Node9_sound : Sound component39Node9Box :=
  sound_of_literal_split component39Node9Box leaf1722Box leaf1723Box
    .k (123/32) (by rfl) (by rfl)
    leaf1722FlatSound leaf1723FlatSound

private noncomputable def component39Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component39Node10_sound : Sound component39Node10Box :=
  sound_of_literal_split component39Node10Box component39Node8Box component39Node9Box
    .chi (19/256) (by rfl) (by rfl)
    component39Node8_sound component39Node9_sound

private noncomputable def component39Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component39Node11_sound : Sound component39Node11Box :=
  sound_of_literal_split component39Node11Box component39Node7Box component39Node10Box
    .k (61/16) (by rfl) (by rfl)
    component39Node7_sound component39Node10_sound

private noncomputable def component39Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component39Node12_sound : Sound component39Node12Box :=
  sound_of_literal_split component39Node12Box component39Node4Box component39Node11Box
    .chi (9/128) (by rfl) (by rfl)
    component39Node4_sound component39Node11_sound

private noncomputable def component39Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (1/16), chiHi := (17/256) }

set_option maxRecDepth 1000000 in
private theorem component39Node13_sound : Sound component39Node13Box :=
  sound_of_literal_split component39Node13Box leaf1724Box leaf1725Box
    .chi (33/512) (by rfl) (by rfl)
    leaf1724FlatSound leaf1725FlatSound

private noncomputable def component39Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (17/256), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node14_sound : Sound component39Node14Box :=
  sound_of_literal_split component39Node14Box leaf1726Box leaf1727Box
    .chi (35/512) (by rfl) (by rfl)
    leaf1726FlatSound leaf1727FlatSound

private noncomputable def component39Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node15_sound : Sound component39Node15Box :=
  sound_of_literal_split component39Node15Box component39Node13Box component39Node14Box
    .chi (17/256) (by rfl) (by rfl)
    component39Node13_sound component39Node14_sound

private noncomputable def component39Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (1/16), chiHi := (17/256) }

set_option maxRecDepth 1000000 in
private theorem component39Node16_sound : Sound component39Node16Box :=
  sound_of_literal_split component39Node16Box leaf1728Box leaf1729Box
    .chi (33/512) (by rfl) (by rfl)
    leaf1728FlatSound leaf1729FlatSound

private noncomputable def component39Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (17/256), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node17_sound : Sound component39Node17Box :=
  sound_of_literal_split component39Node17Box leaf1730Box leaf1731Box
    .chi (35/512) (by rfl) (by rfl)
    leaf1730FlatSound leaf1731FlatSound

private noncomputable def component39Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node18_sound : Sound component39Node18Box :=
  sound_of_literal_split component39Node18Box component39Node16Box component39Node17Box
    .chi (17/256) (by rfl) (by rfl)
    component39Node16_sound component39Node17_sound

private noncomputable def component39Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node19_sound : Sound component39Node19Box :=
  sound_of_literal_split component39Node19Box component39Node15Box component39Node18Box
    .k (63/16) (by rfl) (by rfl)
    component39Node15_sound component39Node18_sound

private noncomputable def component39Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (9/128), chiHi := (19/256) }

set_option maxRecDepth 1000000 in
private theorem component39Node20_sound : Sound component39Node20Box :=
  sound_of_literal_split component39Node20Box leaf1732Box leaf1733Box
    .k (125/32) (by rfl) (by rfl)
    leaf1732FlatSound leaf1733FlatSound

private noncomputable def component39Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (19/256), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component39Node21_sound : Sound component39Node21Box :=
  sound_of_literal_split component39Node21Box leaf1734Box leaf1735Box
    .k (125/32) (by rfl) (by rfl)
    leaf1734FlatSound leaf1735FlatSound

private noncomputable def component39Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component39Node22_sound : Sound component39Node22Box :=
  sound_of_literal_split component39Node22Box component39Node20Box component39Node21Box
    .chi (19/256) (by rfl) (by rfl)
    component39Node20_sound component39Node21_sound

private noncomputable def component39Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (9/128), chiHi := (19/256) }

set_option maxRecDepth 1000000 in
private theorem component39Node23_sound : Sound component39Node23Box :=
  sound_of_literal_split component39Node23Box leaf1736Box leaf1737Box
    .k (127/32) (by rfl) (by rfl)
    leaf1736FlatSound leaf1737FlatSound

private noncomputable def component39Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (19/256), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component39Node24_sound : Sound component39Node24Box :=
  sound_of_literal_split component39Node24Box leaf1738Box leaf1739Box
    .k (127/32) (by rfl) (by rfl)
    leaf1738FlatSound leaf1739FlatSound

private noncomputable def component39Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component39Node25_sound : Sound component39Node25Box :=
  sound_of_literal_split component39Node25Box component39Node23Box component39Node24Box
    .chi (19/256) (by rfl) (by rfl)
    component39Node23_sound component39Node24_sound

private noncomputable def component39Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component39Node26_sound : Sound component39Node26Box :=
  sound_of_literal_split component39Node26Box component39Node22Box component39Node25Box
    .k (63/16) (by rfl) (by rfl)
    component39Node22_sound component39Node25_sound

private noncomputable def component39Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component39Node27_sound : Sound component39Node27Box :=
  sound_of_literal_split component39Node27Box component39Node19Box component39Node26Box
    .chi (9/128) (by rfl) (by rfl)
    component39Node19_sound component39Node26_sound

private noncomputable def component39Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component39Node28_sound : Sound component39Node28Box :=
  sound_of_literal_split component39Node28Box component39Node12Box component39Node27Box
    .k (31/8) (by rfl) (by rfl)
    component39Node12_sound component39Node27_sound

private noncomputable def component39Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (5/64), chiHi := (21/256) }

set_option maxRecDepth 1000000 in
private theorem component39Node29_sound : Sound component39Node29Box :=
  sound_of_literal_split component39Node29Box leaf1740Box leaf1741Box
    .k (121/32) (by rfl) (by rfl)
    leaf1740FlatSound leaf1741FlatSound

private noncomputable def component39Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (21/256), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node30_sound : Sound component39Node30Box :=
  sound_of_literal_split component39Node30Box leaf1742Box leaf1743Box
    .k (121/32) (by rfl) (by rfl)
    leaf1742FlatSound leaf1743FlatSound

private noncomputable def component39Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node31_sound : Sound component39Node31Box :=
  sound_of_literal_split component39Node31Box component39Node29Box component39Node30Box
    .chi (21/256) (by rfl) (by rfl)
    component39Node29_sound component39Node30_sound

private noncomputable def component39Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (5/64), chiHi := (21/256) }

set_option maxRecDepth 1000000 in
private theorem component39Node32_sound : Sound component39Node32Box :=
  sound_of_literal_split component39Node32Box leaf1744Box leaf1745Box
    .k (123/32) (by rfl) (by rfl)
    leaf1744FlatSound leaf1745FlatSound

private noncomputable def component39Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (21/256), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node33_sound : Sound component39Node33Box :=
  sound_of_literal_split component39Node33Box leaf1746Box leaf1747Box
    .k (123/32) (by rfl) (by rfl)
    leaf1746FlatSound leaf1747FlatSound

private noncomputable def component39Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node34_sound : Sound component39Node34Box :=
  sound_of_literal_split component39Node34Box component39Node32Box component39Node33Box
    .chi (21/256) (by rfl) (by rfl)
    component39Node32_sound component39Node33_sound

private noncomputable def component39Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node35_sound : Sound component39Node35Box :=
  sound_of_literal_split component39Node35Box component39Node31Box component39Node34Box
    .k (61/16) (by rfl) (by rfl)
    component39Node31_sound component39Node34_sound

private noncomputable def component39Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (11/128), chiHi := (23/256) }

set_option maxRecDepth 1000000 in
private theorem component39Node36_sound : Sound component39Node36Box :=
  sound_of_literal_split component39Node36Box leaf1748Box leaf1749Box
    .k (121/32) (by rfl) (by rfl)
    leaf1748FlatSound leaf1749FlatSound

private noncomputable def component39Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (23/256), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component39Node37_sound : Sound component39Node37Box :=
  sound_of_literal_split component39Node37Box leaf1750Box leaf1751Box
    .k (121/32) (by rfl) (by rfl)
    leaf1750FlatSound leaf1751FlatSound

private noncomputable def component39Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component39Node38_sound : Sound component39Node38Box :=
  sound_of_literal_split component39Node38Box component39Node36Box component39Node37Box
    .chi (23/256) (by rfl) (by rfl)
    component39Node36_sound component39Node37_sound

private noncomputable def component39Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (11/128), chiHi := (23/256) }

set_option maxRecDepth 1000000 in
private theorem component39Node39_sound : Sound component39Node39Box :=
  sound_of_literal_split component39Node39Box leaf1752Box leaf1753Box
    .k (123/32) (by rfl) (by rfl)
    leaf1752FlatSound leaf1753FlatSound

private noncomputable def component39Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (23/256), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component39Node40_sound : Sound component39Node40Box :=
  sound_of_literal_split component39Node40Box leaf1754Box leaf1755Box
    .k (123/32) (by rfl) (by rfl)
    leaf1754FlatSound leaf1755FlatSound

private noncomputable def component39Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component39Node41_sound : Sound component39Node41Box :=
  sound_of_literal_split component39Node41Box component39Node39Box component39Node40Box
    .chi (23/256) (by rfl) (by rfl)
    component39Node39_sound component39Node40_sound

private noncomputable def component39Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component39Node42_sound : Sound component39Node42Box :=
  sound_of_literal_split component39Node42Box component39Node38Box component39Node41Box
    .k (61/16) (by rfl) (by rfl)
    component39Node38_sound component39Node41_sound

private noncomputable def component39Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component39Node43_sound : Sound component39Node43Box :=
  sound_of_literal_split component39Node43Box component39Node35Box component39Node42Box
    .chi (11/128) (by rfl) (by rfl)
    component39Node35_sound component39Node42_sound

private noncomputable def component39Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (5/64), chiHi := (21/256) }

set_option maxRecDepth 1000000 in
private theorem component39Node44_sound : Sound component39Node44Box :=
  sound_of_literal_split component39Node44Box leaf1756Box leaf1757Box
    .k (125/32) (by rfl) (by rfl)
    leaf1756FlatSound leaf1757FlatSound

private noncomputable def component39Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (21/256), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node45_sound : Sound component39Node45Box :=
  sound_of_literal_split component39Node45Box leaf1758Box leaf1759Box
    .k (125/32) (by rfl) (by rfl)
    leaf1758FlatSound leaf1759FlatSound

private noncomputable def component39Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node46_sound : Sound component39Node46Box :=
  sound_of_literal_split component39Node46Box component39Node44Box component39Node45Box
    .chi (21/256) (by rfl) (by rfl)
    component39Node44_sound component39Node45_sound

private noncomputable def component39Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (5/64), chiHi := (21/256) }

set_option maxRecDepth 1000000 in
private theorem component39Node47_sound : Sound component39Node47Box :=
  sound_of_literal_split component39Node47Box leaf1760Box leaf1761Box
    .k (127/32) (by rfl) (by rfl)
    leaf1760FlatSound leaf1761FlatSound

private noncomputable def component39Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (21/256), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node48_sound : Sound component39Node48Box :=
  sound_of_literal_split component39Node48Box leaf1762Box leaf1763Box
    .k (127/32) (by rfl) (by rfl)
    leaf1762FlatSound leaf1763FlatSound

private noncomputable def component39Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node49_sound : Sound component39Node49Box :=
  sound_of_literal_split component39Node49Box component39Node47Box component39Node48Box
    .chi (21/256) (by rfl) (by rfl)
    component39Node47_sound component39Node48_sound

private noncomputable def component39Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component39Node50_sound : Sound component39Node50Box :=
  sound_of_literal_split component39Node50Box component39Node46Box component39Node49Box
    .k (63/16) (by rfl) (by rfl)
    component39Node46_sound component39Node49_sound

private noncomputable def component39Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (11/128), chiHi := (23/256) }

set_option maxRecDepth 1000000 in
private theorem component39Node51_sound : Sound component39Node51Box :=
  sound_of_literal_split component39Node51Box leaf1764Box leaf1765Box
    .k (125/32) (by rfl) (by rfl)
    leaf1764FlatSound leaf1765FlatSound

private noncomputable def component39Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (23/256), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component39Node52_sound : Sound component39Node52Box :=
  sound_of_literal_split component39Node52Box leaf1766Box leaf1767Box
    .k (125/32) (by rfl) (by rfl)
    leaf1766FlatSound leaf1767FlatSound

private noncomputable def component39Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component39Node53_sound : Sound component39Node53Box :=
  sound_of_literal_split component39Node53Box component39Node51Box component39Node52Box
    .chi (23/256) (by rfl) (by rfl)
    component39Node51_sound component39Node52_sound

private noncomputable def component39Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (11/128), chiHi := (23/256) }

set_option maxRecDepth 1000000 in
private theorem component39Node54_sound : Sound component39Node54Box :=
  sound_of_literal_split component39Node54Box leaf1768Box leaf1769Box
    .k (127/32) (by rfl) (by rfl)
    leaf1768FlatSound leaf1769FlatSound

private noncomputable def component39Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (23/256), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component39Node55_sound : Sound component39Node55Box :=
  sound_of_literal_split component39Node55Box leaf1770Box leaf1771Box
    .k (127/32) (by rfl) (by rfl)
    leaf1770FlatSound leaf1771FlatSound

private noncomputable def component39Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component39Node56_sound : Sound component39Node56Box :=
  sound_of_literal_split component39Node56Box component39Node54Box component39Node55Box
    .chi (23/256) (by rfl) (by rfl)
    component39Node54_sound component39Node55_sound

private noncomputable def component39Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component39Node57_sound : Sound component39Node57Box :=
  sound_of_literal_split component39Node57Box component39Node53Box component39Node56Box
    .k (63/16) (by rfl) (by rfl)
    component39Node53_sound component39Node56_sound

private noncomputable def component39Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component39Node58_sound : Sound component39Node58Box :=
  sound_of_literal_split component39Node58Box component39Node50Box component39Node57Box
    .chi (11/128) (by rfl) (by rfl)
    component39Node50_sound component39Node57_sound

private noncomputable def component39Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component39Node59_sound : Sound component39Node59Box :=
  sound_of_literal_split component39Node59Box component39Node43Box component39Node58Box
    .k (31/8) (by rfl) (by rfl)
    component39Node43_sound component39Node58_sound

noncomputable def component39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (4), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
theorem component39_sound : Sound component39Box :=
  sound_of_literal_split component39Box component39Node28Box component39Node59Box
    .chi (5/64) (by rfl) (by rfl)
    component39Node28_sound component39Node59_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
