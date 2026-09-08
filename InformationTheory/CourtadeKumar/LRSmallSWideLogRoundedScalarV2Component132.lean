import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch10
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch12
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch1
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

private noncomputable def leaf6549Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6549Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217955/134217728) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11452158976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (335499039/268435456) }, upper := { exponent := 1, mantissa := (5233/4096) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904902655/22904317952) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6549InnerLog : WideLogData :=
  innerPair821Data

set_option maxRecDepth 1000000 in
private theorem leaf6549LocalValidity :
    LeafFacts leaf6549Box leaf6549Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6549Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11452158976) }) = true
      norm_num [leaf6549Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6549CertificateValid :
    WideCertificateValid leaf6549Box leaf6549Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi329ValidityFacts
    leaf6549LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6549CoverageChecked :
    coverageCheck (innerAD leaf6549Box) leaf6549InnerLog = true := by
  rfl'

private theorem leaf6549InnerLogValid :
    leaf6549InnerLog.Valid 8 (innerAD leaf6549Box) :=
  wideLogDataValid_of_cachedCheck endpoint507PositiveFacts
    endpoint508PositiveFacts.valid leaf6549CoverageChecked

private noncomputable def leaf6549InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629509/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6549InputLogOnePlusV_eq :
    leaf6549InputLogOnePlusV = outerEnclosure 24
      (leaf6549Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6549RoundedFacts : LeafRoundedFacts 8
    leaf6549Certificate.logOnePlusV leaf6549InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6549InputLogOnePlusV_eq }

private noncomputable def leaf6549Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi329InputQChi innerPair821Input
    leaf6549InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6549LowerChecked :
    lowerCheck 24 leaf6549Box leaf6549Inputs = true := by
  rfl'

private theorem leaf6549CoversExact : CoversExact 8
    leaf6549Box leaf6549Certificate leaf6549InnerLog leaf6549Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi329RoundedFacts
    innerPair821RoundedFacts leaf6549RoundedFacts (by rfl)

private theorem leaf6549FlatSound : Sound leaf6549Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6549CertificateValid
    leaf6549InnerLogValid leaf6549CoversExact leaf6549LowerChecked

private noncomputable def leaf6550Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6550Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217957/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356426752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (338644573/268435456) }, upper := { exponent := 1, mantissa := (2641/2048) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714657789/68712853504) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6550InnerLog : WideLogData :=
  innerPair822Data

set_option maxRecDepth 1000000 in
private theorem leaf6550LocalValidity :
    LeafFacts leaf6550Box leaf6550Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6550Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356426752) }) = true
      norm_num [leaf6550Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6550CertificateValid :
    WideCertificateValid leaf6550Box leaf6550Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi330ValidityFacts
    leaf6550LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6550CoverageChecked :
    coverageCheck (innerAD leaf6550Box) leaf6550InnerLog = true := by
  rfl'

private theorem leaf6550InnerLogValid :
    leaf6550InnerLog.Valid 8 (innerAD leaf6550Box) :=
  wideLogDataValid_of_cachedCheck endpoint509PositiveFacts
    endpoint443PositiveFacts.valid leaf6550CoverageChecked

private noncomputable def leaf6550InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629521/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6550InputLogOnePlusV_eq :
    leaf6550InputLogOnePlusV = outerEnclosure 24
      (leaf6550Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6550RoundedFacts : LeafRoundedFacts 8
    leaf6550Certificate.logOnePlusV leaf6550InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6550InputLogOnePlusV_eq }

private noncomputable def leaf6550Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi330InputQChi innerPair822Input
    leaf6550InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6550LowerChecked :
    lowerCheck 24 leaf6550Box leaf6550Inputs = true := by
  rfl'

private theorem leaf6550CoversExact : CoversExact 8
    leaf6550Box leaf6550Certificate leaf6550InnerLog leaf6550Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi330RoundedFacts
    innerPair822RoundedFacts leaf6550RoundedFacts (by rfl)

private theorem leaf6550FlatSound : Sound leaf6550Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6550CertificateValid
    leaf6550InnerLogValid leaf6550CoversExact leaf6550LowerChecked

private noncomputable def leaf6551Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6551Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217959/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356376576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (341790107/268435456) }, upper := { exponent := 1, mantissa := (5331/4096) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714607613/68712753152) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6551InnerLog : WideLogData :=
  innerPair683Data

set_option maxRecDepth 1000000 in
private theorem leaf6551LocalValidity :
    LeafFacts leaf6551Box leaf6551Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6551Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356376576) }) = true
      norm_num [leaf6551Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6551CertificateValid :
    WideCertificateValid leaf6551Box leaf6551Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi331ValidityFacts
    leaf6551LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6551CoverageChecked :
    coverageCheck (innerAD leaf6551Box) leaf6551InnerLog = true := by
  rfl'

private theorem leaf6551InnerLogValid :
    leaf6551InnerLog.Valid 8 (innerAD leaf6551Box) :=
  wideLogDataValid_of_cachedCheck endpoint434PositiveFacts
    endpoint444PositiveFacts.valid leaf6551CoverageChecked

private noncomputable def leaf6551InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814767/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6551InputLogOnePlusV_eq :
    leaf6551InputLogOnePlusV = outerEnclosure 24
      (leaf6551Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6551RoundedFacts : LeafRoundedFacts 8
    leaf6551Certificate.logOnePlusV leaf6551InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6551InputLogOnePlusV_eq }

private noncomputable def leaf6551Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi331InputQChi innerPair683Input
    leaf6551InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6551LowerChecked :
    lowerCheck 24 leaf6551Box leaf6551Inputs = true := by
  rfl'

private theorem leaf6551CoversExact : CoversExact 8
    leaf6551Box leaf6551Certificate leaf6551InnerLog leaf6551Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi331RoundedFacts
    innerPair683RoundedFacts leaf6551RoundedFacts (by rfl)

private theorem leaf6551FlatSound : Sound leaf6551Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6551CertificateValid
    leaf6551InnerLogValid leaf6551CoversExact leaf6551LowerChecked

private noncomputable def leaf6552Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6552Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217961/134217728) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11452108800) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (344935641/268435456) }, upper := { exponent := 1, mantissa := (1345/1024) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904852479/22904217600) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6552InnerLog : WideLogData :=
  innerPair342Data

set_option maxRecDepth 1000000 in
private theorem leaf6552LocalValidity :
    LeafFacts leaf6552Box leaf6552Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6552Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11452108800) }) = true
      norm_num [leaf6552Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6552CertificateValid :
    WideCertificateValid leaf6552Box leaf6552Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi332ValidityFacts
    leaf6552LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6552CoverageChecked :
    coverageCheck (innerAD leaf6552Box) leaf6552InnerLog = true := by
  rfl'

private theorem leaf6552InnerLogValid :
    leaf6552InnerLog.Valid 8 (innerAD leaf6552Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint95PositiveFacts.valid leaf6552CoverageChecked

private noncomputable def leaf6552InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814773/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6552InputLogOnePlusV_eq :
    leaf6552InputLogOnePlusV = outerEnclosure 24
      (leaf6552Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6552RoundedFacts : LeafRoundedFacts 8
    leaf6552Certificate.logOnePlusV leaf6552InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6552InputLogOnePlusV_eq }

private noncomputable def leaf6552Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi332InputQChi innerPair342Input
    leaf6552InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6552LowerChecked :
    lowerCheck 24 leaf6552Box leaf6552Inputs = true := by
  rfl'

private theorem leaf6552CoversExact : CoversExact 8
    leaf6552Box leaf6552Certificate leaf6552InnerLog leaf6552Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi332RoundedFacts
    innerPair342RoundedFacts leaf6552RoundedFacts (by rfl)

private theorem leaf6552FlatSound : Sound leaf6552Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6552CertificateValid
    leaf6552InnerLogValid leaf6552CoversExact leaf6552LowerChecked

private noncomputable def leaf6553Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (99/32), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6553Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435783/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712887296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (679419067/536870912) }, upper := { exponent := 1, mantissa := (10531/8192) } }, logOuter := sk135LogOuterCertificate, logK := sk135LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429283837/137425774592) } }, logDArg := sk135LogDArgCertificate }

private noncomputable def leaf6553InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf6553LocalValidity :
    LeafFacts leaf6553Box leaf6553Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6553Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712887296) }) = true
      norm_num [leaf6553Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6553CertificateValid :
    WideCertificateValid leaf6553Box leaf6553Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk135ValidityFacts chi329ValidityFacts
    leaf6553LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6553CoverageChecked :
    coverageCheck (innerAD leaf6553Box) leaf6553InnerLog = true := by
  rfl'

private theorem leaf6553InnerLogValid :
    leaf6553InnerLog.Valid 8 (innerAD leaf6553Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf6553CoverageChecked

private noncomputable def leaf6553InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629509/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6553InputLogOnePlusV_eq :
    leaf6553InputLogOnePlusV = outerEnclosure 24
      (leaf6553Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6553RoundedFacts : LeafRoundedFacts 8
    leaf6553Certificate.logOnePlusV leaf6553InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6553InputLogOnePlusV_eq }

private noncomputable def leaf6553Inputs : Inputs :=
  inputsOfCaches globalInput sk135RoundedInputs
    chi329InputQChi innerPair294Input
    leaf6553InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6553LowerChecked :
    lowerCheck 24 leaf6553Box leaf6553Inputs = true := by
  rfl'

private theorem leaf6553CoversExact : CoversExact 8
    leaf6553Box leaf6553Certificate leaf6553InnerLog leaf6553Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk135RoundedFacts chi329RoundedFacts
    innerPair294RoundedFacts leaf6553RoundedFacts (by rfl)

private theorem leaf6553FlatSound : Sound leaf6553Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6553CertificateValid
    leaf6553InnerLogValid leaf6553CoversExact leaf6553LowerChecked

private noncomputable def leaf6554Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (99/32), kHi := (25/8), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6554Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435785/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712820736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (683613113/536870912) }, upper := { exponent := 1, mantissa := (2649/2048) } }, logOuter := sk136LogOuterCertificate, logK := sk136LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429217277/137425641472) } }, logDArg := sk136LogDArgCertificate }

private noncomputable def leaf6554InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf6554LocalValidity :
    LeafFacts leaf6554Box leaf6554Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6554Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712820736) }) = true
      norm_num [leaf6554Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6554CertificateValid :
    WideCertificateValid leaf6554Box leaf6554Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk136ValidityFacts chi329ValidityFacts
    leaf6554LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6554CoverageChecked :
    coverageCheck (innerAD leaf6554Box) leaf6554InnerLog = true := by
  rfl'

private theorem leaf6554InnerLogValid :
    leaf6554InnerLog.Valid 8 (innerAD leaf6554Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf6554CoverageChecked

private noncomputable def leaf6554InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629517/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6554InputLogOnePlusV_eq :
    leaf6554InputLogOnePlusV = outerEnclosure 24
      (leaf6554Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6554RoundedFacts : LeafRoundedFacts 8
    leaf6554Certificate.logOnePlusV leaf6554InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6554InputLogOnePlusV_eq }

private noncomputable def leaf6554Inputs : Inputs :=
  inputsOfCaches globalInput sk136RoundedInputs
    chi329InputQChi innerPair294Input
    leaf6554InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6554LowerChecked :
    lowerCheck 24 leaf6554Box leaf6554Inputs = true := by
  rfl'

private theorem leaf6554CoversExact : CoversExact 8
    leaf6554Box leaf6554Certificate leaf6554InnerLog leaf6554Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk136RoundedFacts chi329RoundedFacts
    innerPair294RoundedFacts leaf6554RoundedFacts (by rfl)

private theorem leaf6554FlatSound : Sound leaf6554Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6554CertificateValid
    leaf6554InnerLogValid leaf6554CoversExact leaf6554LowerChecked

private noncomputable def leaf6555Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6555Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217959/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356359168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (342904151/268435456) }, upper := { exponent := 1, mantissa := (1337/1024) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714590205/68712718336) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6555InnerLog : WideLogData :=
  innerPair823Data

set_option maxRecDepth 1000000 in
private theorem leaf6555LocalValidity :
    LeafFacts leaf6555Box leaf6555Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6555Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356359168) }) = true
      norm_num [leaf6555Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6555CertificateValid :
    WideCertificateValid leaf6555Box leaf6555Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi330ValidityFacts
    leaf6555LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6555CoverageChecked :
    coverageCheck (innerAD leaf6555Box) leaf6555InnerLog = true := by
  rfl'

private theorem leaf6555InnerLogValid :
    leaf6555InnerLog.Valid 8 (innerAD leaf6555Box) :=
  wideLogDataValid_of_cachedCheck endpoint510PositiveFacts
    endpoint511PositiveFacts.valid leaf6555CoverageChecked

private noncomputable def leaf6555InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814769/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6555InputLogOnePlusV_eq :
    leaf6555InputLogOnePlusV = outerEnclosure 24
      (leaf6555Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6555RoundedFacts : LeafRoundedFacts 8
    leaf6555Certificate.logOnePlusV leaf6555InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6555InputLogOnePlusV_eq }

private noncomputable def leaf6555Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi330InputQChi innerPair823Input
    leaf6555InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6555LowerChecked :
    lowerCheck 24 leaf6555Box leaf6555Inputs = true := by
  rfl'

private theorem leaf6555CoversExact : CoversExact 8
    leaf6555Box leaf6555Certificate leaf6555InnerLog leaf6555Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi330RoundedFacts
    innerPair823RoundedFacts leaf6555RoundedFacts (by rfl)

private theorem leaf6555FlatSound : Sound leaf6555Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6555CertificateValid
    leaf6555InnerLogValid leaf6555CoversExact leaf6555LowerChecked

private noncomputable def leaf6556Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6556Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217961/134217728) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11452102656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (346115217/268435456) }, upper := { exponent := 1, mantissa := (2699/2048) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904846335/22904205312) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6556InnerLog : WideLogData :=
  innerPair684Data

set_option maxRecDepth 1000000 in
private theorem leaf6556LocalValidity :
    LeafFacts leaf6556Box leaf6556Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6556Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11452102656) }) = true
      norm_num [leaf6556Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6556CertificateValid :
    WideCertificateValid leaf6556Box leaf6556Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi331ValidityFacts
    leaf6556LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6556CoverageChecked :
    coverageCheck (innerAD leaf6556Box) leaf6556InnerLog = true := by
  rfl'

private theorem leaf6556InnerLogValid :
    leaf6556InnerLog.Valid 8 (innerAD leaf6556Box) :=
  wideLogDataValid_of_cachedCheck endpoint435PositiveFacts
    endpoint95PositiveFacts.valid leaf6556CoverageChecked

private noncomputable def leaf6556InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814775/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6556InputLogOnePlusV_eq :
    leaf6556InputLogOnePlusV = outerEnclosure 24
      (leaf6556Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6556RoundedFacts : LeafRoundedFacts 8
    leaf6556Certificate.logOnePlusV leaf6556InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6556InputLogOnePlusV_eq }

private noncomputable def leaf6556Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi331InputQChi innerPair684Input
    leaf6556InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6556LowerChecked :
    lowerCheck 24 leaf6556Box leaf6556Inputs = true := by
  rfl'

private theorem leaf6556CoversExact : CoversExact 8
    leaf6556Box leaf6556Certificate leaf6556InnerLog leaf6556Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi331RoundedFacts
    innerPair684RoundedFacts leaf6556RoundedFacts (by rfl)

private theorem leaf6556FlatSound : Sound leaf6556Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6556CertificateValid
    leaf6556InnerLogValid leaf6556CoversExact leaf6556LowerChecked

private noncomputable def leaf6557Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6557Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217963/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356256768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (349326283/268435456) }, upper := { exponent := 1, mantissa := (681/512) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714487805/68712513536) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6557InnerLog : WideLogData :=
  innerPair690Data

set_option maxRecDepth 1000000 in
private theorem leaf6557LocalValidity :
    LeafFacts leaf6557Box leaf6557Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6557Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356256768) }) = true
      norm_num [leaf6557Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6557CertificateValid :
    WideCertificateValid leaf6557Box leaf6557Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi332ValidityFacts
    leaf6557LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6557CoverageChecked :
    coverageCheck (innerAD leaf6557Box) leaf6557InnerLog = true := by
  rfl'

private theorem leaf6557InnerLogValid :
    leaf6557InnerLog.Valid 8 (innerAD leaf6557Box) :=
  wideLogDataValid_of_cachedCheck endpoint436PositiveFacts
    endpoint448PositiveFacts.valid leaf6557CoverageChecked

private noncomputable def leaf6557InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629563/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6557InputLogOnePlusV_eq :
    leaf6557InputLogOnePlusV = outerEnclosure 24
      (leaf6557Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6557RoundedFacts : LeafRoundedFacts 8
    leaf6557Certificate.logOnePlusV leaf6557InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6557InputLogOnePlusV_eq }

private noncomputable def leaf6557Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi332InputQChi innerPair690Input
    leaf6557InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6557LowerChecked :
    lowerCheck 24 leaf6557Box leaf6557Inputs = true := by
  rfl'

private theorem leaf6557CoversExact : CoversExact 8
    leaf6557Box leaf6557Certificate leaf6557InnerLog leaf6557Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi332RoundedFacts
    innerPair690RoundedFacts leaf6557RoundedFacts (by rfl)

private theorem leaf6557FlatSound : Sound leaf6557Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6557CertificateValid
    leaf6557InnerLogValid leaf6557CoversExact leaf6557LowerChecked

private noncomputable def leaf6558Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6558Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217963/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356276224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (348081175/268435456) }, upper := { exponent := 1, mantissa := (5429/4096) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714507261/68712552448) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6558InnerLog : WideLogData :=
  innerPair685Data

set_option maxRecDepth 1000000 in
private theorem leaf6558LocalValidity :
    LeafFacts leaf6558Box leaf6558Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6558Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356276224) }) = true
      norm_num [leaf6558Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6558CertificateValid :
    WideCertificateValid leaf6558Box leaf6558Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi327ValidityFacts
    leaf6558LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6558CoverageChecked :
    coverageCheck (innerAD leaf6558Box) leaf6558InnerLog = true := by
  rfl'

private theorem leaf6558InnerLogValid :
    leaf6558InnerLog.Valid 8 (innerAD leaf6558Box) :=
  wideLogDataValid_of_cachedCheck endpoint435PositiveFacts
    endpoint447PositiveFacts.valid leaf6558CoverageChecked

private noncomputable def leaf6558InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814779/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6558InputLogOnePlusV_eq :
    leaf6558InputLogOnePlusV = outerEnclosure 24
      (leaf6558Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6558RoundedFacts : LeafRoundedFacts 8
    leaf6558Certificate.logOnePlusV leaf6558InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6558InputLogOnePlusV_eq }

private noncomputable def leaf6558Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi327InputQChi innerPair685Input
    leaf6558InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6558LowerChecked :
    lowerCheck 24 leaf6558Box leaf6558Inputs = true := by
  rfl'

private theorem leaf6558CoversExact : CoversExact 8
    leaf6558Box leaf6558Certificate leaf6558InnerLog leaf6558Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi327RoundedFacts
    innerPair685RoundedFacts leaf6558RoundedFacts (by rfl)

private theorem leaf6558FlatSound : Sound leaf6558Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6558CertificateValid
    leaf6558InnerLogValid leaf6558CoversExact leaf6558LowerChecked

private noncomputable def leaf6559Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6559Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217965/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356226048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (351226709/268435456) }, upper := { exponent := 1, mantissa := (2739/2048) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714457085/68712452096) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6559InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6559LocalValidity :
    LeafFacts leaf6559Box leaf6559Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6559Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356226048) }) = true
      norm_num [leaf6559Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6559CertificateValid :
    WideCertificateValid leaf6559Box leaf6559Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi328ValidityFacts
    leaf6559LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6559CoverageChecked :
    coverageCheck (innerAD leaf6559Box) leaf6559InnerLog = true := by
  rfl'

private theorem leaf6559InnerLogValid :
    leaf6559InnerLog.Valid 8 (innerAD leaf6559Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6559CoverageChecked

private noncomputable def leaf6559InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814785/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6559InputLogOnePlusV_eq :
    leaf6559InputLogOnePlusV = outerEnclosure 24
      (leaf6559Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6559RoundedFacts : LeafRoundedFacts 8
    leaf6559Certificate.logOnePlusV leaf6559InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6559InputLogOnePlusV_eq }

private noncomputable def leaf6559Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi328InputQChi innerPair340Input
    leaf6559InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6559LowerChecked :
    lowerCheck 24 leaf6559Box leaf6559Inputs = true := by
  rfl'

private theorem leaf6559CoversExact : CoversExact 8
    leaf6559Box leaf6559Certificate leaf6559InnerLog leaf6559Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi328RoundedFacts
    innerPair340RoundedFacts leaf6559RoundedFacts (by rfl)

private theorem leaf6559FlatSound : Sound leaf6559Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6559CertificateValid
    leaf6559InnerLogValid leaf6559CoversExact leaf6559LowerChecked

private noncomputable def leaf6560Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6560Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217967/134217728) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11452058624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (354372243/268435456) }, upper := { exponent := 1, mantissa := (5527/4096) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904802303/22904117248) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6560InnerLog : WideLogData :=
  innerPair348Data

set_option maxRecDepth 1000000 in
private theorem leaf6560LocalValidity :
    LeafFacts leaf6560Box leaf6560Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6560Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11452058624) }) = true
      norm_num [leaf6560Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6560CertificateValid :
    WideCertificateValid leaf6560Box leaf6560Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi333ValidityFacts
    leaf6560LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6560CoverageChecked :
    coverageCheck (innerAD leaf6560Box) leaf6560InnerLog = true := by
  rfl'

private theorem leaf6560InnerLogValid :
    leaf6560InnerLog.Valid 8 (innerAD leaf6560Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint451PositiveFacts.valid leaf6560CoverageChecked

private noncomputable def leaf6560InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629583/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6560InputLogOnePlusV_eq :
    leaf6560InputLogOnePlusV = outerEnclosure 24
      (leaf6560Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6560RoundedFacts : LeafRoundedFacts 8
    leaf6560Certificate.logOnePlusV leaf6560InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6560InputLogOnePlusV_eq }

private noncomputable def leaf6560Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi333InputQChi innerPair348Input
    leaf6560InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6560LowerChecked :
    lowerCheck 24 leaf6560Box leaf6560Inputs = true := by
  rfl'

private theorem leaf6560CoversExact : CoversExact 8
    leaf6560Box leaf6560Certificate leaf6560InnerLog leaf6560Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi333RoundedFacts
    innerPair348RoundedFacts leaf6560RoundedFacts (by rfl)

private theorem leaf6560FlatSound : Sound leaf6560Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6560CertificateValid
    leaf6560InnerLogValid leaf6560CoversExact leaf6560LowerChecked

private noncomputable def leaf6561Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6561Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217969/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356125696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (357517777/268435456) }, upper := { exponent := 1, mantissa := (697/512) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714356733/68712251392) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6561InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6561LocalValidity :
    LeafFacts leaf6561Box leaf6561Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6561Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356125696) }) = true
      norm_num [leaf6561Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6561CertificateValid :
    WideCertificateValid leaf6561Box leaf6561Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi334ValidityFacts
    leaf6561LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6561CoverageChecked :
    coverageCheck (innerAD leaf6561Box) leaf6561InnerLog = true := by
  rfl'

private theorem leaf6561InnerLogValid :
    leaf6561InnerLog.Valid 8 (innerAD leaf6561Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6561CoverageChecked

private noncomputable def leaf6561InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629595/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6561InputLogOnePlusV_eq :
    leaf6561InputLogOnePlusV = outerEnclosure 24
      (leaf6561Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6561RoundedFacts : LeafRoundedFacts 8
    leaf6561Certificate.logOnePlusV leaf6561InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6561InputLogOnePlusV_eq }

private noncomputable def leaf6561Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi334InputQChi innerPair346Input
    leaf6561InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6561LowerChecked :
    lowerCheck 24 leaf6561Box leaf6561Inputs = true := by
  rfl'

private theorem leaf6561CoversExact : CoversExact 8
    leaf6561Box leaf6561Certificate leaf6561InnerLog leaf6561Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi334RoundedFacts
    innerPair346RoundedFacts leaf6561RoundedFacts (by rfl)

private theorem leaf6561FlatSound : Sound leaf6561Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6561CertificateValid
    leaf6561InnerLogValid leaf6561CoversExact leaf6561LowerChecked

private noncomputable def leaf6562Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6562Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217965/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356205568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (352537349/268435456) }, upper := { exponent := 1, mantissa := (2749/2048) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714436605/68712411136) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6562InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6562LocalValidity :
    LeafFacts leaf6562Box leaf6562Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6562Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356205568) }) = true
      norm_num [leaf6562Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6562CertificateValid :
    WideCertificateValid leaf6562Box leaf6562Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi327ValidityFacts
    leaf6562LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6562CoverageChecked :
    coverageCheck (innerAD leaf6562Box) leaf6562InnerLog = true := by
  rfl'

private theorem leaf6562InnerLogValid :
    leaf6562InnerLog.Valid 8 (innerAD leaf6562Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6562CoverageChecked

private noncomputable def leaf6562InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629575/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6562InputLogOnePlusV_eq :
    leaf6562InputLogOnePlusV = outerEnclosure 24
      (leaf6562Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6562RoundedFacts : LeafRoundedFacts 8
    leaf6562Certificate.logOnePlusV leaf6562InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6562InputLogOnePlusV_eq }

private noncomputable def leaf6562Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi327InputQChi innerPair345Input
    leaf6562InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6562LowerChecked :
    lowerCheck 24 leaf6562Box leaf6562Inputs = true := by
  rfl'

private theorem leaf6562CoversExact : CoversExact 8
    leaf6562Box leaf6562Certificate leaf6562InnerLog leaf6562Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi327RoundedFacts
    innerPair345RoundedFacts leaf6562RoundedFacts (by rfl)

private theorem leaf6562FlatSound : Sound leaf6562Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6562CertificateValid
    leaf6562InnerLogValid leaf6562CoversExact leaf6562LowerChecked

private noncomputable def leaf6563Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6563Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217967/134217728) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11452051456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (355748415/268435456) }, upper := { exponent := 1, mantissa := (1387/1024) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904795135/22904102912) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6563InnerLog : WideLogData :=
  innerPair366Data

set_option maxRecDepth 1000000 in
private theorem leaf6563LocalValidity :
    LeafFacts leaf6563Box leaf6563Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6563Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11452051456) }) = true
      norm_num [leaf6563Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6563CertificateValid :
    WideCertificateValid leaf6563Box leaf6563Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi328ValidityFacts
    leaf6563LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6563CoverageChecked :
    coverageCheck (innerAD leaf6563Box) leaf6563InnerLog = true := by
  rfl'

private theorem leaf6563InnerLogValid :
    leaf6563InnerLog.Valid 8 (innerAD leaf6563Box) :=
  wideLogDataValid_of_cachedCheck endpoint95PositiveFacts
    endpoint461PositiveFacts.valid leaf6563CoverageChecked

private noncomputable def leaf6563InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907397/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6563InputLogOnePlusV_eq :
    leaf6563InputLogOnePlusV = outerEnclosure 24
      (leaf6563Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6563RoundedFacts : LeafRoundedFacts 8
    leaf6563Certificate.logOnePlusV leaf6563InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6563InputLogOnePlusV_eq }

private noncomputable def leaf6563Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi328InputQChi innerPair366Input
    leaf6563InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6563LowerChecked :
    lowerCheck 24 leaf6563Box leaf6563Inputs = true := by
  rfl'

private theorem leaf6563CoversExact : CoversExact 8
    leaf6563Box leaf6563Certificate leaf6563InnerLog leaf6563Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi328RoundedFacts
    innerPair366RoundedFacts leaf6563RoundedFacts (by rfl)

private theorem leaf6563FlatSound : Sound leaf6563Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6563CertificateValid
    leaf6563InnerLogValid leaf6563CoversExact leaf6563LowerChecked

private noncomputable def leaf6564Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6564Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217969/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356103168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (358959481/268435456) }, upper := { exponent := 1, mantissa := (2799/2048) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714334205/68712206336) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6564InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6564LocalValidity :
    LeafFacts leaf6564Box leaf6564Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6564Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356103168) }) = true
      norm_num [leaf6564Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6564CertificateValid :
    WideCertificateValid leaf6564Box leaf6564Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi333ValidityFacts
    leaf6564LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6564CoverageChecked :
    coverageCheck (innerAD leaf6564Box) leaf6564InnerLog = true := by
  rfl'

private theorem leaf6564InnerLogValid :
    leaf6564InnerLog.Valid 8 (innerAD leaf6564Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6564CoverageChecked

private noncomputable def leaf6564InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363425/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf6564InputLogOnePlusV_eq :
    leaf6564InputLogOnePlusV = outerEnclosure 24
      (leaf6564Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6564RoundedFacts : LeafRoundedFacts 8
    leaf6564Certificate.logOnePlusV leaf6564InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6564InputLogOnePlusV_eq }

private noncomputable def leaf6564Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi333InputQChi innerPair346Input
    leaf6564InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6564LowerChecked :
    lowerCheck 24 leaf6564Box leaf6564Inputs = true := by
  rfl'

private theorem leaf6564CoversExact : CoversExact 8
    leaf6564Box leaf6564Certificate leaf6564InnerLog leaf6564Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi333RoundedFacts
    innerPair346RoundedFacts leaf6564RoundedFacts (by rfl)

private theorem leaf6564FlatSound : Sound leaf6564Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6564CertificateValid
    leaf6564InnerLogValid leaf6564CoversExact leaf6564LowerChecked

private noncomputable def leaf6565Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6565Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217971/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356051968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (362170547/268435456) }, upper := { exponent := 1, mantissa := (353/256) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714283005/68712103936) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6565InnerLog : WideLogData :=
  innerPair355Data

set_option maxRecDepth 1000000 in
private theorem leaf6565LocalValidity :
    LeafFacts leaf6565Box leaf6565Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6565Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356051968) }) = true
      norm_num [leaf6565Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6565CertificateValid :
    WideCertificateValid leaf6565Box leaf6565Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi334ValidityFacts
    leaf6565LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6565CoverageChecked :
    coverageCheck (innerAD leaf6565Box) leaf6565InnerLog = true := by
  rfl'

private theorem leaf6565InnerLogValid :
    leaf6565InnerLog.Valid 8 (innerAD leaf6565Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint460PositiveFacts.valid leaf6565CoverageChecked

private noncomputable def leaf6565InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629613/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6565InputLogOnePlusV_eq :
    leaf6565InputLogOnePlusV = outerEnclosure 24
      (leaf6565Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6565RoundedFacts : LeafRoundedFacts 8
    leaf6565Certificate.logOnePlusV leaf6565InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6565InputLogOnePlusV_eq }

private noncomputable def leaf6565Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi334InputQChi innerPair355Input
    leaf6565InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6565LowerChecked :
    lowerCheck 24 leaf6565Box leaf6565Inputs = true := by
  rfl'

private theorem leaf6565CoversExact : CoversExact 8
    leaf6565Box leaf6565Certificate leaf6565InnerLog leaf6565Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi334RoundedFacts
    innerPair355RoundedFacts leaf6565RoundedFacts (by rfl)

private theorem leaf6565FlatSound : Sound leaf6565Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6565CertificateValid
    leaf6565InnerLogValid leaf6565CoversExact leaf6565LowerChecked

private noncomputable def leaf6566Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6566Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435787/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712754176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (687807159/536870912) }, upper := { exponent := 1, mantissa := (10661/8192) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429150717/137425508352) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf6566InnerLog : WideLogData :=
  innerPair294Data

set_option maxRecDepth 1000000 in
private theorem leaf6566LocalValidity :
    LeafFacts leaf6566Box leaf6566Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6566Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712754176) }) = true
      norm_num [leaf6566Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6566CertificateValid :
    WideCertificateValid leaf6566Box leaf6566Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi329ValidityFacts
    leaf6566LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6566CoverageChecked :
    coverageCheck (innerAD leaf6566Box) leaf6566InnerLog = true := by
  rfl'

private theorem leaf6566InnerLogValid :
    leaf6566InnerLog.Valid 8 (innerAD leaf6566Box) :=
  wideLogDataValid_of_cachedCheck endpoint79PositiveFacts
    endpoint91PositiveFacts.valid leaf6566CoverageChecked

private noncomputable def leaf6566InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629525/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6566InputLogOnePlusV_eq :
    leaf6566InputLogOnePlusV = outerEnclosure 24
      (leaf6566Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6566RoundedFacts : LeafRoundedFacts 8
    leaf6566Certificate.logOnePlusV leaf6566InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6566InputLogOnePlusV_eq }

private noncomputable def leaf6566Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi329InputQChi innerPair294Input
    leaf6566InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6566LowerChecked :
    lowerCheck 24 leaf6566Box leaf6566Inputs = true := by
  rfl'

private theorem leaf6566CoversExact : CoversExact 8
    leaf6566Box leaf6566Certificate leaf6566InnerLog leaf6566Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi329RoundedFacts
    innerPair294RoundedFacts leaf6566RoundedFacts (by rfl)

private theorem leaf6566FlatSound : Sound leaf6566Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6566CertificateValid
    leaf6566InnerLogValid leaf6566CoversExact leaf6566LowerChecked

private noncomputable def leaf6567Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6567Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435789/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712687616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (692001205/536870912) }, upper := { exponent := 1, mantissa := (5363/4096) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429084157/137425375232) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf6567InnerLog : WideLogData :=
  innerPair339Data

set_option maxRecDepth 1000000 in
private theorem leaf6567LocalValidity :
    LeafFacts leaf6567Box leaf6567Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6567Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712687616) }) = true
      norm_num [leaf6567Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6567CertificateValid :
    WideCertificateValid leaf6567Box leaf6567Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi329ValidityFacts
    leaf6567LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6567CoverageChecked :
    coverageCheck (innerAD leaf6567Box) leaf6567InnerLog = true := by
  rfl'

private theorem leaf6567InnerLogValid :
    leaf6567InnerLog.Valid 8 (innerAD leaf6567Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint91PositiveFacts.valid leaf6567CoverageChecked

private noncomputable def leaf6567InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814767/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6567InputLogOnePlusV_eq :
    leaf6567InputLogOnePlusV = outerEnclosure 24
      (leaf6567Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6567RoundedFacts : LeafRoundedFacts 8
    leaf6567Certificate.logOnePlusV leaf6567InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6567InputLogOnePlusV_eq }

private noncomputable def leaf6567Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi329InputQChi innerPair339Input
    leaf6567InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6567LowerChecked :
    lowerCheck 24 leaf6567Box leaf6567Inputs = true := by
  rfl'

private theorem leaf6567CoversExact : CoversExact 8
    leaf6567Box leaf6567Certificate leaf6567InnerLog leaf6567Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi329RoundedFacts
    innerPair339RoundedFacts leaf6567RoundedFacts (by rfl)

private theorem leaf6567FlatSound : Sound leaf6567Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6567CertificateValid
    leaf6567InnerLogValid leaf6567CoversExact leaf6567LowerChecked

private noncomputable def leaf6568Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (101/32), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6568Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435789/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712650752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (694360357/536870912) }, upper := { exponent := 1, mantissa := (5381/4096) } }, logOuter := sk137LogOuterCertificate, logK := sk137LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429047293/137425301504) } }, logDArg := sk137LogDArgCertificate }

private noncomputable def leaf6568InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6568LocalValidity :
    LeafFacts leaf6568Box leaf6568Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6568Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712650752) }) = true
      norm_num [leaf6568Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6568CertificateValid :
    WideCertificateValid leaf6568Box leaf6568Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk137ValidityFacts chi330ValidityFacts
    leaf6568LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6568CoverageChecked :
    coverageCheck (innerAD leaf6568Box) leaf6568InnerLog = true := by
  rfl'

private theorem leaf6568InnerLogValid :
    leaf6568InnerLog.Valid 8 (innerAD leaf6568Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6568CoverageChecked

private noncomputable def leaf6568InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814769/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6568InputLogOnePlusV_eq :
    leaf6568InputLogOnePlusV = outerEnclosure 24
      (leaf6568Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6568RoundedFacts : LeafRoundedFacts 8
    leaf6568Certificate.logOnePlusV leaf6568InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6568InputLogOnePlusV_eq }

private noncomputable def leaf6568Inputs : Inputs :=
  inputsOfCaches globalInput sk137RoundedInputs
    chi330InputQChi innerPair340Input
    leaf6568InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6568LowerChecked :
    lowerCheck 24 leaf6568Box leaf6568Inputs = true := by
  rfl'

private theorem leaf6568CoversExact : CoversExact 8
    leaf6568Box leaf6568Certificate leaf6568InnerLog leaf6568Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk137RoundedFacts chi330RoundedFacts
    innerPair340RoundedFacts leaf6568RoundedFacts (by rfl)

private theorem leaf6568FlatSound : Sound leaf6568Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6568CertificateValid
    leaf6568InnerLogValid leaf6568CoversExact leaf6568LowerChecked

private noncomputable def leaf6569Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (101/32), kHi := (51/16), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6569Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435791/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712583168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (698619935/536870912) }, upper := { exponent := 1, mantissa := (2707/2048) } }, logOuter := sk138LogOuterCertificate, logK := sk138LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428979709/137425166336) } }, logDArg := sk138LogDArgCertificate }

private noncomputable def leaf6569InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6569LocalValidity :
    LeafFacts leaf6569Box leaf6569Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6569Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712583168) }) = true
      norm_num [leaf6569Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6569CertificateValid :
    WideCertificateValid leaf6569Box leaf6569Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk138ValidityFacts chi330ValidityFacts
    leaf6569LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6569CoverageChecked :
    coverageCheck (innerAD leaf6569Box) leaf6569InnerLog = true := by
  rfl'

private theorem leaf6569InnerLogValid :
    leaf6569InnerLog.Valid 8 (innerAD leaf6569Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6569CoverageChecked

private noncomputable def leaf6569InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814773/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6569InputLogOnePlusV_eq :
    leaf6569InputLogOnePlusV = outerEnclosure 24
      (leaf6569Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6569RoundedFacts : LeafRoundedFacts 8
    leaf6569Certificate.logOnePlusV leaf6569InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6569InputLogOnePlusV_eq }

private noncomputable def leaf6569Inputs : Inputs :=
  inputsOfCaches globalInput sk138RoundedInputs
    chi330InputQChi innerPair340Input
    leaf6569InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6569LowerChecked :
    lowerCheck 24 leaf6569Box leaf6569Inputs = true := by
  rfl'

private theorem leaf6569CoversExact : CoversExact 8
    leaf6569Box leaf6569Certificate leaf6569InnerLog leaf6569Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk138RoundedFacts chi330RoundedFacts
    innerPair340RoundedFacts leaf6569RoundedFacts (by rfl)

private theorem leaf6569FlatSound : Sound leaf6569Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6569CertificateValid
    leaf6569InnerLogValid leaf6569CoversExact leaf6569LowerChecked

private noncomputable def leaf6570Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6570Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435791/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712621056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (696195251/536870912) }, upper := { exponent := 1, mantissa := (10791/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137429017597/137425242112) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf6570InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6570LocalValidity :
    LeafFacts leaf6570Box leaf6570Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6570Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712621056) }) = true
      norm_num [leaf6570Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6570CertificateValid :
    WideCertificateValid leaf6570Box leaf6570Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi329ValidityFacts
    leaf6570LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6570CoverageChecked :
    coverageCheck (innerAD leaf6570Box) leaf6570InnerLog = true := by
  rfl'

private theorem leaf6570InnerLogValid :
    leaf6570InnerLog.Valid 8 (innerAD leaf6570Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6570CoverageChecked

private noncomputable def leaf6570InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814771/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6570InputLogOnePlusV_eq :
    leaf6570InputLogOnePlusV = outerEnclosure 24
      (leaf6570Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6570RoundedFacts : LeafRoundedFacts 8
    leaf6570Certificate.logOnePlusV leaf6570InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6570InputLogOnePlusV_eq }

private noncomputable def leaf6570Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi329InputQChi innerPair340Input
    leaf6570InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6570LowerChecked :
    lowerCheck 24 leaf6570Box leaf6570Inputs = true := by
  rfl'

private theorem leaf6570CoversExact : CoversExact 8
    leaf6570Box leaf6570Certificate leaf6570InnerLog leaf6570Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi329RoundedFacts
    innerPair340RoundedFacts leaf6570RoundedFacts (by rfl)

private theorem leaf6570FlatSound : Sound leaf6570Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6570CertificateValid
    leaf6570InnerLogValid leaf6570CoversExact leaf6570LowerChecked

private noncomputable def leaf6571Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (1/2), chiHi := (65/128) }

private noncomputable def leaf6571Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435793/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712554496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (700389297/536870912) }, upper := { exponent := 1, mantissa := (1357/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi329LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428951037/137425108992) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf6571InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6571LocalValidity :
    LeafFacts leaf6571Box leaf6571Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6571Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712554496) }) = true
      norm_num [leaf6571Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6571CertificateValid :
    WideCertificateValid leaf6571Box leaf6571Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi329ValidityFacts
    leaf6571LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6571CoverageChecked :
    coverageCheck (innerAD leaf6571Box) leaf6571InnerLog = true := by
  rfl'

private theorem leaf6571InnerLogValid :
    leaf6571InnerLog.Valid 8 (innerAD leaf6571Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6571CoverageChecked

private noncomputable def leaf6571InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814775/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6571InputLogOnePlusV_eq :
    leaf6571InputLogOnePlusV = outerEnclosure 24
      (leaf6571Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6571RoundedFacts : LeafRoundedFacts 8
    leaf6571Certificate.logOnePlusV leaf6571InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6571InputLogOnePlusV_eq }

private noncomputable def leaf6571Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi329InputQChi innerPair340Input
    leaf6571InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6571LowerChecked :
    lowerCheck 24 leaf6571Box leaf6571Inputs = true := by
  rfl'

private theorem leaf6571CoversExact : CoversExact 8
    leaf6571Box leaf6571Certificate leaf6571InnerLog leaf6571Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi329RoundedFacts
    innerPair340RoundedFacts leaf6571RoundedFacts (by rfl)

private theorem leaf6571FlatSound : Sound leaf6571Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6571CertificateValid
    leaf6571InnerLogValid leaf6571CoversExact leaf6571LowerChecked

private noncomputable def leaf6572Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6572Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435793/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712515584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (702879513/536870912) }, upper := { exponent := 1, mantissa := (5447/4096) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428912125/137425031168) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf6572InnerLog : WideLogData :=
  innerPair340Data

set_option maxRecDepth 1000000 in
private theorem leaf6572LocalValidity :
    LeafFacts leaf6572Box leaf6572Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6572Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712515584) }) = true
      norm_num [leaf6572Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6572CertificateValid :
    WideCertificateValid leaf6572Box leaf6572Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi330ValidityFacts
    leaf6572LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6572CoverageChecked :
    coverageCheck (innerAD leaf6572Box) leaf6572InnerLog = true := by
  rfl'

private theorem leaf6572InnerLogValid :
    leaf6572InnerLog.Valid 8 (innerAD leaf6572Box) :=
  wideLogDataValid_of_cachedCheck endpoint90PositiveFacts
    endpoint92PositiveFacts.valid leaf6572CoverageChecked

private noncomputable def leaf6572InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629555/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6572InputLogOnePlusV_eq :
    leaf6572InputLogOnePlusV = outerEnclosure 24
      (leaf6572Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6572RoundedFacts : LeafRoundedFacts 8
    leaf6572Certificate.logOnePlusV leaf6572InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6572InputLogOnePlusV_eq }

private noncomputable def leaf6572Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi330InputQChi innerPair340Input
    leaf6572InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6572LowerChecked :
    lowerCheck 24 leaf6572Box leaf6572Inputs = true := by
  rfl'

private theorem leaf6572CoversExact : CoversExact 8
    leaf6572Box leaf6572Certificate leaf6572InnerLog leaf6572Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi330RoundedFacts
    innerPair340RoundedFacts leaf6572RoundedFacts (by rfl)

private theorem leaf6572FlatSound : Sound leaf6572Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6572CertificateValid
    leaf6572InnerLogValid leaf6572CoversExact leaf6572LowerChecked

private noncomputable def leaf6573Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (65/128), chiHi := (33/64) }

private noncomputable def leaf6573Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435795/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712448000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (707139091/536870912) }, upper := { exponent := 1, mantissa := (685/512) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi330LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428844541/137424896000) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf6573InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6573LocalValidity :
    LeafFacts leaf6573Box leaf6573Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6573Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712448000) }) = true
      norm_num [leaf6573Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6573CertificateValid :
    WideCertificateValid leaf6573Box leaf6573Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi330ValidityFacts
    leaf6573LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6573CoverageChecked :
    coverageCheck (innerAD leaf6573Box) leaf6573InnerLog = true := by
  rfl'

private theorem leaf6573InnerLogValid :
    leaf6573InnerLog.Valid 8 (innerAD leaf6573Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6573CoverageChecked

private noncomputable def leaf6573InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629563/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6573InputLogOnePlusV_eq :
    leaf6573InputLogOnePlusV = outerEnclosure 24
      (leaf6573Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6573RoundedFacts : LeafRoundedFacts 8
    leaf6573Certificate.logOnePlusV leaf6573InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6573InputLogOnePlusV_eq }

private noncomputable def leaf6573Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi330InputQChi innerPair345Input
    leaf6573InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6573LowerChecked :
    lowerCheck 24 leaf6573Box leaf6573Inputs = true := by
  rfl'

private theorem leaf6573CoversExact : CoversExact 8
    leaf6573Box leaf6573Certificate leaf6573InnerLog leaf6573Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi330RoundedFacts
    innerPair345RoundedFacts leaf6573RoundedFacts (by rfl)

private theorem leaf6573FlatSound : Sound leaf6573Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6573CertificateValid
    leaf6573InnerLogValid leaf6573CoversExact leaf6573LowerChecked

private noncomputable def leaf6574Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6574Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217963/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356239360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (350440327/268435456) }, upper := { exponent := 1, mantissa := (5465/4096) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714470397/68712478720) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6574InnerLog : WideLogData :=
  innerPair824Data

set_option maxRecDepth 1000000 in
private theorem leaf6574LocalValidity :
    LeafFacts leaf6574Box leaf6574Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6574Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356239360) }) = true
      norm_num [leaf6574Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6574CertificateValid :
    WideCertificateValid leaf6574Box leaf6574Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi331ValidityFacts
    leaf6574LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6574CoverageChecked :
    coverageCheck (innerAD leaf6574Box) leaf6574InnerLog = true := by
  rfl'

private theorem leaf6574InnerLogValid :
    leaf6574InnerLog.Valid 8 (innerAD leaf6574Box) :=
  wideLogDataValid_of_cachedCheck endpoint512PositiveFacts
    endpoint513PositiveFacts.valid leaf6574CoverageChecked

private noncomputable def leaf6574InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629567/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6574InputLogOnePlusV_eq :
    leaf6574InputLogOnePlusV = outerEnclosure 24
      (leaf6574Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6574RoundedFacts : LeafRoundedFacts 8
    leaf6574Certificate.logOnePlusV leaf6574InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6574InputLogOnePlusV_eq }

private noncomputable def leaf6574Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi331InputQChi innerPair824Input
    leaf6574InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6574LowerChecked :
    lowerCheck 24 leaf6574Box leaf6574Inputs = true := by
  rfl'

private theorem leaf6574CoversExact : CoversExact 8
    leaf6574Box leaf6574Certificate leaf6574InnerLog leaf6574Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi331RoundedFacts
    innerPair824RoundedFacts leaf6574RoundedFacts (by rfl)

private theorem leaf6574FlatSound : Sound leaf6574Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6574CertificateValid
    leaf6574InnerLogValid leaf6574CoversExact leaf6574LowerChecked

private noncomputable def leaf6575Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6575Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217965/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356187136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (353716925/268435456) }, upper := { exponent := 1, mantissa := (1379/1024) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714418173/68712374272) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6575InnerLog : WideLogData :=
  innerPair738Data

set_option maxRecDepth 1000000 in
private theorem leaf6575LocalValidity :
    LeafFacts leaf6575Box leaf6575Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6575Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356187136) }) = true
      norm_num [leaf6575Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6575CertificateValid :
    WideCertificateValid leaf6575Box leaf6575Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi332ValidityFacts
    leaf6575LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6575CoverageChecked :
    coverageCheck (innerAD leaf6575Box) leaf6575InnerLog = true := by
  rfl'

private theorem leaf6575InnerLogValid :
    leaf6575InnerLog.Valid 8 (innerAD leaf6575Box) :=
  wideLogDataValid_of_cachedCheck endpoint473PositiveFacts
    endpoint514PositiveFacts.valid leaf6575CoverageChecked

private noncomputable def leaf6575InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907395/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6575InputLogOnePlusV_eq :
    leaf6575InputLogOnePlusV = outerEnclosure 24
      (leaf6575Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6575RoundedFacts : LeafRoundedFacts 8
    leaf6575Certificate.logOnePlusV leaf6575InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6575InputLogOnePlusV_eq }

private noncomputable def leaf6575Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi332InputQChi innerPair738Input
    leaf6575InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6575LowerChecked :
    lowerCheck 24 leaf6575Box leaf6575Inputs = true := by
  rfl'

private theorem leaf6575CoversExact : CoversExact 8
    leaf6575Box leaf6575Certificate leaf6575InnerLog leaf6575Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi332RoundedFacts
    innerPair738RoundedFacts leaf6575RoundedFacts (by rfl)

private theorem leaf6575FlatSound : Sound leaf6575Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6575CertificateValid
    leaf6575InnerLogValid leaf6575CoversExact leaf6575LowerChecked

private noncomputable def leaf6576Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (103/32), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6576Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435795/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712410112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (709563775/536870912) }, upper := { exponent := 1, mantissa := (10997/8192) } }, logOuter := sk139LogOuterCertificate, logK := sk139LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428806653/137424820224) } }, logDArg := sk139LogDArgCertificate }

private noncomputable def leaf6576InnerLog : WideLogData :=
  innerPair345Data

set_option maxRecDepth 1000000 in
private theorem leaf6576LocalValidity :
    LeafFacts leaf6576Box leaf6576Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6576Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712410112) }) = true
      norm_num [leaf6576Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6576CertificateValid :
    WideCertificateValid leaf6576Box leaf6576Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk139ValidityFacts chi331ValidityFacts
    leaf6576LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6576CoverageChecked :
    coverageCheck (innerAD leaf6576Box) leaf6576InnerLog = true := by
  rfl'

private theorem leaf6576InnerLogValid :
    leaf6576InnerLog.Valid 8 (innerAD leaf6576Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint92PositiveFacts.valid leaf6576CoverageChecked

private noncomputable def leaf6576InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629567/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6576InputLogOnePlusV_eq :
    leaf6576InputLogOnePlusV = outerEnclosure 24
      (leaf6576Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6576RoundedFacts : LeafRoundedFacts 8
    leaf6576Certificate.logOnePlusV leaf6576InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6576InputLogOnePlusV_eq }

private noncomputable def leaf6576Inputs : Inputs :=
  inputsOfCaches globalInput sk139RoundedInputs
    chi331InputQChi innerPair345Input
    leaf6576InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6576LowerChecked :
    lowerCheck 24 leaf6576Box leaf6576Inputs = true := by
  rfl'

private theorem leaf6576CoversExact : CoversExact 8
    leaf6576Box leaf6576Certificate leaf6576InnerLog leaf6576Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk139RoundedFacts chi331RoundedFacts
    innerPair345RoundedFacts leaf6576RoundedFacts (by rfl)

private theorem leaf6576FlatSound : Sound leaf6576Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6576CertificateValid
    leaf6576InnerLogValid leaf6576CoversExact leaf6576LowerChecked

private noncomputable def leaf6577Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (103/32), kHi := (13/4), chiLo := (33/64), chiHi := (67/128) }

private noncomputable def leaf6577Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (268435797/268435456) }, vSqrt := { lower := (65529/65536), upper := (68716396541/68712341504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (713888885/536870912) }, upper := { exponent := 1, mantissa := (1383/1024) } }, logOuter := sk140LogOuterCertificate, logK := sk140LogKCertificate, logChi := chi331LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137428738045/137424683008) } }, logDArg := sk140LogDArgCertificate }

private noncomputable def leaf6577InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6577LocalValidity :
    LeafFacts leaf6577Box leaf6577Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6577Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68716396541/68712341504) }) = true
      norm_num [leaf6577Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6577CertificateValid :
    WideCertificateValid leaf6577Box leaf6577Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk140ValidityFacts chi331ValidityFacts
    leaf6577LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6577CoverageChecked :
    coverageCheck (innerAD leaf6577Box) leaf6577InnerLog = true := by
  rfl'

private theorem leaf6577InnerLogValid :
    leaf6577InnerLog.Valid 8 (innerAD leaf6577Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6577CoverageChecked

private noncomputable def leaf6577InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453697/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6577InputLogOnePlusV_eq :
    leaf6577InputLogOnePlusV = outerEnclosure 24
      (leaf6577Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6577RoundedFacts : LeafRoundedFacts 8
    leaf6577Certificate.logOnePlusV leaf6577InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6577InputLogOnePlusV_eq }

private noncomputable def leaf6577Inputs : Inputs :=
  inputsOfCaches globalInput sk140RoundedInputs
    chi331InputQChi innerPair346Input
    leaf6577InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6577LowerChecked :
    lowerCheck 24 leaf6577Box leaf6577Inputs = true := by
  rfl'

private theorem leaf6577CoversExact : CoversExact 8
    leaf6577Box leaf6577Certificate leaf6577InnerLog leaf6577Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk140RoundedFacts chi331RoundedFacts
    innerPair346RoundedFacts leaf6577RoundedFacts (by rfl)

private theorem leaf6577FlatSound : Sound leaf6577Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6577CertificateValid
    leaf6577InnerLogValid leaf6577CoversExact leaf6577LowerChecked

private noncomputable def leaf6578Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (67/128), chiHi := (17/32) }

private noncomputable def leaf6578Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217967/134217728) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11452039168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (358107567/268435456) }, upper := { exponent := 1, mantissa := (349/256) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi332LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904782847/22904078336) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6578InnerLog : WideLogData :=
  innerPair742Data

set_option maxRecDepth 1000000 in
private theorem leaf6578LocalValidity :
    LeafFacts leaf6578Box leaf6578Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6578Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11452039168) }) = true
      norm_num [leaf6578Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6578CertificateValid :
    WideCertificateValid leaf6578Box leaf6578Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi332ValidityFacts
    leaf6578LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6578CoverageChecked :
    coverageCheck (innerAD leaf6578Box) leaf6578InnerLog = true := by
  rfl'

private theorem leaf6578InnerLogValid :
    leaf6578InnerLog.Valid 8 (innerAD leaf6578Box) :=
  wideLogDataValid_of_cachedCheck endpoint479PositiveFacts
    endpoint515PositiveFacts.valid leaf6578CoverageChecked

private noncomputable def leaf6578InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629597/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6578InputLogOnePlusV_eq :
    leaf6578InputLogOnePlusV = outerEnclosure 24
      (leaf6578Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6578RoundedFacts : LeafRoundedFacts 8
    leaf6578Certificate.logOnePlusV leaf6578InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6578InputLogOnePlusV_eq }

private noncomputable def leaf6578Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi332InputQChi innerPair742Input
    leaf6578InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6578LowerChecked :
    lowerCheck 24 leaf6578Box leaf6578Inputs = true := by
  rfl'

private theorem leaf6578CoversExact : CoversExact 8
    leaf6578Box leaf6578Certificate leaf6578InnerLog leaf6578Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi332RoundedFacts
    innerPair742RoundedFacts leaf6578RoundedFacts (by rfl)

private theorem leaf6578FlatSound : Sound leaf6578Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6578CertificateValid
    leaf6578InnerLogValid leaf6578CoversExact leaf6578LowerChecked

private noncomputable def leaf6579Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6579Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217967/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356134912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (356993523/268435456) }, upper := { exponent := 1, mantissa := (5567/4096) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714365949/68712269824) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6579InnerLog : WideLogData :=
  innerPair703Data

set_option maxRecDepth 1000000 in
private theorem leaf6579LocalValidity :
    LeafFacts leaf6579Box leaf6579Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6579Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356134912) }) = true
      norm_num [leaf6579Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6579CertificateValid :
    WideCertificateValid leaf6579Box leaf6579Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi327ValidityFacts
    leaf6579LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6579CoverageChecked :
    coverageCheck (innerAD leaf6579Box) leaf6579InnerLog = true := by
  rfl'

private theorem leaf6579InnerLogValid :
    leaf6579InnerLog.Valid 8 (innerAD leaf6579Box) :=
  wideLogDataValid_of_cachedCheck endpoint447PositiveFacts
    endpoint461PositiveFacts.valid leaf6579CoverageChecked

private noncomputable def leaf6579InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629593/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6579InputLogOnePlusV_eq :
    leaf6579InputLogOnePlusV = outerEnclosure 24
      (leaf6579Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6579RoundedFacts : LeafRoundedFacts 8
    leaf6579Certificate.logOnePlusV leaf6579InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6579InputLogOnePlusV_eq }

private noncomputable def leaf6579Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi327InputQChi innerPair703Input
    leaf6579InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6579LowerChecked :
    lowerCheck 24 leaf6579Box leaf6579Inputs = true := by
  rfl'

private theorem leaf6579CoversExact : CoversExact 8
    leaf6579Box leaf6579Certificate leaf6579InnerLog leaf6579Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi327RoundedFacts
    innerPair703RoundedFacts leaf6579RoundedFacts (by rfl)

private theorem leaf6579FlatSound : Sound leaf6579Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6579CertificateValid
    leaf6579InnerLogValid leaf6579CoversExact leaf6579LowerChecked

private noncomputable def leaf6580Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6580Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217969/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356082688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (360270121/268435456) }, upper := { exponent := 1, mantissa := (2809/2048) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714313725/68712165376) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6580InnerLog : WideLogData :=
  innerPair346Data

set_option maxRecDepth 1000000 in
private theorem leaf6580LocalValidity :
    LeafFacts leaf6580Box leaf6580Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6580Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356082688) }) = true
      norm_num [leaf6580Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6580CertificateValid :
    WideCertificateValid leaf6580Box leaf6580Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi328ValidityFacts
    leaf6580LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6580CoverageChecked :
    coverageCheck (innerAD leaf6580Box) leaf6580InnerLog = true := by
  rfl'

private theorem leaf6580InnerLogValid :
    leaf6580InnerLog.Valid 8 (innerAD leaf6580Box) :=
  wideLogDataValid_of_cachedCheck endpoint91PositiveFacts
    endpoint93PositiveFacts.valid leaf6580CoverageChecked

private noncomputable def leaf6580InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629605/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6580InputLogOnePlusV_eq :
    leaf6580InputLogOnePlusV = outerEnclosure 24
      (leaf6580Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6580RoundedFacts : LeafRoundedFacts 8
    leaf6580Certificate.logOnePlusV leaf6580InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6580InputLogOnePlusV_eq }

private noncomputable def leaf6580Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi328InputQChi innerPair346Input
    leaf6580InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6580LowerChecked :
    lowerCheck 24 leaf6580Box leaf6580Inputs = true := by
  rfl'

private theorem leaf6580CoversExact : CoversExact 8
    leaf6580Box leaf6580Certificate leaf6580InnerLog leaf6580Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi328RoundedFacts
    innerPair346RoundedFacts leaf6580RoundedFacts (by rfl)

private theorem leaf6580FlatSound : Sound leaf6580Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6580CertificateValid
    leaf6580InnerLogValid leaf6580CoversExact leaf6580LowerChecked

private noncomputable def leaf6581Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (17/32), chiHi := (69/128) }

private noncomputable def leaf6581Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217969/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356064256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (361449697/268435456) }, upper := { exponent := 1, mantissa := (1409/1024) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi327LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714295293/68712128512) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6581InnerLog : WideLogData :=
  innerPair717Data

set_option maxRecDepth 1000000 in
private theorem leaf6581LocalValidity :
    LeafFacts leaf6581Box leaf6581Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6581Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356064256) }) = true
      norm_num [leaf6581Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6581CertificateValid :
    WideCertificateValid leaf6581Box leaf6581Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi327ValidityFacts
    leaf6581LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6581CoverageChecked :
    coverageCheck (innerAD leaf6581Box) leaf6581InnerLog = true := by
  rfl'

private theorem leaf6581InnerLogValid :
    leaf6581InnerLog.Valid 8 (innerAD leaf6581Box) :=
  wideLogDataValid_of_cachedCheck endpoint458PositiveFacts
    endpoint466PositiveFacts.valid leaf6581CoverageChecked

private noncomputable def leaf6581InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814805/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6581InputLogOnePlusV_eq :
    leaf6581InputLogOnePlusV = outerEnclosure 24
      (leaf6581Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6581RoundedFacts : LeafRoundedFacts 8
    leaf6581Certificate.logOnePlusV leaf6581InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6581InputLogOnePlusV_eq }

private noncomputable def leaf6581Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi327InputQChi innerPair717Input
    leaf6581InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6581LowerChecked :
    lowerCheck 24 leaf6581Box leaf6581Inputs = true := by
  rfl'

private theorem leaf6581CoversExact : CoversExact 8
    leaf6581Box leaf6581Certificate leaf6581InnerLog leaf6581Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi327RoundedFacts
    innerPair717RoundedFacts leaf6581RoundedFacts (by rfl)

private theorem leaf6581FlatSound : Sound leaf6581Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6581CertificateValid
    leaf6581InnerLogValid leaf6581CoversExact leaf6581LowerChecked

private noncomputable def leaf6582Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (69/128), chiHi := (35/64) }

private noncomputable def leaf6582Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217971/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356011008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (364791827/268435456) }, upper := { exponent := 1, mantissa := (711/512) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi328LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714242045/68712022016) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6582InnerLog : WideLogData :=
  innerPair709Data

set_option maxRecDepth 1000000 in
private theorem leaf6582LocalValidity :
    LeafFacts leaf6582Box leaf6582Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6582Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356011008) }) = true
      norm_num [leaf6582Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6582CertificateValid :
    WideCertificateValid leaf6582Box leaf6582Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi328ValidityFacts
    leaf6582LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6582CoverageChecked :
    coverageCheck (innerAD leaf6582Box) leaf6582InnerLog = true := by
  rfl'

private theorem leaf6582InnerLogValid :
    leaf6582InnerLog.Valid 8 (innerAD leaf6582Box) :=
  wideLogDataValid_of_cachedCheck endpoint451PositiveFacts
    endpoint463PositiveFacts.valid leaf6582CoverageChecked

private noncomputable def leaf6582InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629623/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6582InputLogOnePlusV_eq :
    leaf6582InputLogOnePlusV = outerEnclosure 24
      (leaf6582Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6582RoundedFacts : LeafRoundedFacts 8
    leaf6582Certificate.logOnePlusV leaf6582InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6582InputLogOnePlusV_eq }

private noncomputable def leaf6582Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi328InputQChi innerPair709Input
    leaf6582InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6582LowerChecked :
    lowerCheck 24 leaf6582Box leaf6582Inputs = true := by
  rfl'

private theorem leaf6582CoversExact : CoversExact 8
    leaf6582Box leaf6582Certificate leaf6582InnerLog leaf6582Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi328RoundedFacts
    innerPair709RoundedFacts leaf6582RoundedFacts (by rfl)

private theorem leaf6582FlatSound : Sound leaf6582Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6582CertificateValid
    leaf6582InnerLogValid leaf6582CoversExact leaf6582LowerChecked

private noncomputable def leaf6583Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6583Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217971/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34356030464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (363546719/268435456) }, upper := { exponent := 1, mantissa := (5669/4096) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714261501/68712060928) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6583InnerLog : WideLogData :=
  innerPair709Data

set_option maxRecDepth 1000000 in
private theorem leaf6583LocalValidity :
    LeafFacts leaf6583Box leaf6583Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6583Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34356030464) }) = true
      norm_num [leaf6583Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6583CertificateValid :
    WideCertificateValid leaf6583Box leaf6583Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi333ValidityFacts
    leaf6583LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6583CoverageChecked :
    coverageCheck (innerAD leaf6583Box) leaf6583InnerLog = true := by
  rfl'

private theorem leaf6583InnerLogValid :
    leaf6583InnerLog.Valid 8 (innerAD leaf6583Box) :=
  wideLogDataValid_of_cachedCheck endpoint451PositiveFacts
    endpoint463PositiveFacts.valid leaf6583CoverageChecked

private noncomputable def leaf6583InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814809/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6583InputLogOnePlusV_eq :
    leaf6583InputLogOnePlusV = outerEnclosure 24
      (leaf6583Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6583RoundedFacts : LeafRoundedFacts 8
    leaf6583Certificate.logOnePlusV leaf6583InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6583InputLogOnePlusV_eq }

private noncomputable def leaf6583Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi333InputQChi innerPair709Input
    leaf6583InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6583LowerChecked :
    lowerCheck 24 leaf6583Box leaf6583Inputs = true := by
  rfl'

private theorem leaf6583CoversExact : CoversExact 8
    leaf6583Box leaf6583Certificate leaf6583InnerLog leaf6583Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi333RoundedFacts
    innerPair709RoundedFacts leaf6583RoundedFacts (by rfl)

private theorem leaf6583FlatSound : Sound leaf6583Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6583CertificateValid
    leaf6583InnerLogValid leaf6583CoversExact leaf6583LowerChecked

private noncomputable def leaf6584Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6584Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217973/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355978240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (366823317/268435456) }, upper := { exponent := 1, mantissa := (715/512) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714209277/68711956480) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6584InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6584LocalValidity :
    LeafFacts leaf6584Box leaf6584Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6584Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355978240) }) = true
      norm_num [leaf6584Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6584CertificateValid :
    WideCertificateValid leaf6584Box leaf6584Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi334ValidityFacts
    leaf6584LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6584CoverageChecked :
    coverageCheck (innerAD leaf6584Box) leaf6584InnerLog = true := by
  rfl'

private theorem leaf6584InnerLogValid :
    leaf6584InnerLog.Valid 8 (innerAD leaf6584Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6584CoverageChecked

private noncomputable def leaf6584InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629631/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6584InputLogOnePlusV_eq :
    leaf6584InputLogOnePlusV = outerEnclosure 24
      (leaf6584Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6584RoundedFacts : LeafRoundedFacts 8
    leaf6584Certificate.logOnePlusV leaf6584InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6584InputLogOnePlusV_eq }

private noncomputable def leaf6584Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi334InputQChi innerPair353Input
    leaf6584InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6584LowerChecked :
    lowerCheck 24 leaf6584Box leaf6584Inputs = true := by
  rfl'

private theorem leaf6584CoversExact : CoversExact 8
    leaf6584Box leaf6584Certificate leaf6584InnerLog leaf6584Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi334RoundedFacts
    innerPair353RoundedFacts leaf6584RoundedFacts (by rfl)

private theorem leaf6584FlatSound : Sound leaf6584Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6584CertificateValid
    leaf6584InnerLogValid leaf6584CoversExact leaf6584LowerChecked

private noncomputable def leaf6585Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (35/64), chiHi := (71/128) }

private noncomputable def leaf6585Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217973/134217728) }, vSqrt := { lower := (65529/65536), upper := (11452743679/11451985920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (368133957/268435456) }, upper := { exponent := 1, mantissa := (1435/1024) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi333LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22904729599/22903971840) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6585InnerLog : WideLogData :=
  innerPair353Data

set_option maxRecDepth 1000000 in
private theorem leaf6585LocalValidity :
    LeafFacts leaf6585Box leaf6585Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6585Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452743679/11451985920) }) = true
      norm_num [leaf6585Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6585CertificateValid :
    WideCertificateValid leaf6585Box leaf6585Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi333ValidityFacts
    leaf6585LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6585CoverageChecked :
    coverageCheck (innerAD leaf6585Box) leaf6585InnerLog = true := by
  rfl'

private theorem leaf6585InnerLogValid :
    leaf6585InnerLog.Valid 8 (innerAD leaf6585Box) :=
  wideLogDataValid_of_cachedCheck endpoint92PositiveFacts
    endpoint96PositiveFacts.valid leaf6585CoverageChecked

private noncomputable def leaf6585InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907409/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6585InputLogOnePlusV_eq :
    leaf6585InputLogOnePlusV = outerEnclosure 24
      (leaf6585Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6585RoundedFacts : LeafRoundedFacts 8
    leaf6585Certificate.logOnePlusV leaf6585InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6585InputLogOnePlusV_eq }

private noncomputable def leaf6585Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi333InputQChi innerPair353Input
    leaf6585InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6585LowerChecked :
    lowerCheck 24 leaf6585Box leaf6585Inputs = true := by
  rfl'

private theorem leaf6585CoversExact : CoversExact 8
    leaf6585Box leaf6585Certificate leaf6585InnerLog leaf6585Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi333RoundedFacts
    innerPair353RoundedFacts leaf6585RoundedFacts (by rfl)

private theorem leaf6585FlatSound : Sound leaf6585Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6585CertificateValid
    leaf6585InnerLogValid leaf6585CoversExact leaf6585LowerChecked

private noncomputable def leaf6586Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (71/128), chiHi := (9/16) }

private noncomputable def leaf6586Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (134217975/134217728) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355904512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (371476087/268435456) }, upper := { exponent := 1, mantissa := (181/128) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi334LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68714135549/68711809024) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6586InnerLog : WideLogData :=
  innerPair718Data

set_option maxRecDepth 1000000 in
private theorem leaf6586LocalValidity :
    LeafFacts leaf6586Box leaf6586Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6586Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355904512) }) = true
      norm_num [leaf6586Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6586CertificateValid :
    WideCertificateValid leaf6586Box leaf6586Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi334ValidityFacts
    leaf6586LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6586CoverageChecked :
    coverageCheck (innerAD leaf6586Box) leaf6586InnerLog = true := by
  rfl'

private theorem leaf6586InnerLogValid :
    leaf6586InnerLog.Valid 8 (innerAD leaf6586Box) :=
  wideLogDataValid_of_cachedCheck endpoint460PositiveFacts
    endpoint464PositiveFacts.valid leaf6586CoverageChecked

private noncomputable def leaf6586InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629649/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6586InputLogOnePlusV_eq :
    leaf6586InputLogOnePlusV = outerEnclosure 24
      (leaf6586Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6586RoundedFacts : LeafRoundedFacts 8
    leaf6586Certificate.logOnePlusV leaf6586InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6586InputLogOnePlusV_eq }

private noncomputable def leaf6586Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi334InputQChi innerPair718Input
    leaf6586InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6586LowerChecked :
    lowerCheck 24 leaf6586Box leaf6586Inputs = true := by
  rfl'

private theorem leaf6586CoversExact : CoversExact 8
    leaf6586Box leaf6586Certificate leaf6586InnerLog leaf6586Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi334RoundedFacts
    innerPair718RoundedFacts leaf6586RoundedFacts (by rfl)

private theorem leaf6586FlatSound : Sound leaf6586Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6586CertificateValid
    leaf6586InnerLogValid leaf6586CoversExact leaf6586LowerChecked

private noncomputable def component132Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component132Node0_sound : Sound component132Node0Box :=
  sound_of_literal_split component132Node0Box leaf6549Box leaf6550Box
    .chi (65/128) (by rfl) (by rfl)
    leaf6549FlatSound leaf6550FlatSound

private noncomputable def component132Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component132Node1_sound : Sound component132Node1Box :=
  sound_of_literal_split component132Node1Box leaf6551Box leaf6552Box
    .chi (67/128) (by rfl) (by rfl)
    leaf6551FlatSound leaf6552FlatSound

private noncomputable def component132Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component132Node2_sound : Sound component132Node2Box :=
  sound_of_literal_split component132Node2Box component132Node0Box component132Node1Box
    .chi (33/64) (by rfl) (by rfl)
    component132Node0_sound component132Node1_sound

private noncomputable def component132Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (1/2), chiHi := (65/128) }

set_option maxRecDepth 1000000 in
private theorem component132Node3_sound : Sound component132Node3Box :=
  sound_of_literal_split component132Node3Box leaf6553Box leaf6554Box
    .k (99/32) (by rfl) (by rfl)
    leaf6553FlatSound leaf6554FlatSound

private noncomputable def component132Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component132Node4_sound : Sound component132Node4Box :=
  sound_of_literal_split component132Node4Box component132Node3Box leaf6555Box
    .chi (65/128) (by rfl) (by rfl)
    component132Node3_sound leaf6555FlatSound

private noncomputable def component132Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component132Node5_sound : Sound component132Node5Box :=
  sound_of_literal_split component132Node5Box leaf6556Box leaf6557Box
    .chi (67/128) (by rfl) (by rfl)
    leaf6556FlatSound leaf6557FlatSound

private noncomputable def component132Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component132Node6_sound : Sound component132Node6Box :=
  sound_of_literal_split component132Node6Box component132Node4Box component132Node5Box
    .chi (33/64) (by rfl) (by rfl)
    component132Node4_sound component132Node5_sound

private noncomputable def component132Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component132Node7_sound : Sound component132Node7Box :=
  sound_of_literal_split component132Node7Box component132Node2Box component132Node6Box
    .k (49/16) (by rfl) (by rfl)
    component132Node2_sound component132Node6_sound

private noncomputable def component132Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component132Node8_sound : Sound component132Node8Box :=
  sound_of_literal_split component132Node8Box leaf6558Box leaf6559Box
    .chi (69/128) (by rfl) (by rfl)
    leaf6558FlatSound leaf6559FlatSound

private noncomputable def component132Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component132Node9_sound : Sound component132Node9Box :=
  sound_of_literal_split component132Node9Box leaf6560Box leaf6561Box
    .chi (71/128) (by rfl) (by rfl)
    leaf6560FlatSound leaf6561FlatSound

private noncomputable def component132Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component132Node10_sound : Sound component132Node10Box :=
  sound_of_literal_split component132Node10Box component132Node8Box component132Node9Box
    .chi (35/64) (by rfl) (by rfl)
    component132Node8_sound component132Node9_sound

private noncomputable def component132Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component132Node11_sound : Sound component132Node11Box :=
  sound_of_literal_split component132Node11Box leaf6562Box leaf6563Box
    .chi (69/128) (by rfl) (by rfl)
    leaf6562FlatSound leaf6563FlatSound

private noncomputable def component132Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component132Node12_sound : Sound component132Node12Box :=
  sound_of_literal_split component132Node12Box leaf6564Box leaf6565Box
    .chi (71/128) (by rfl) (by rfl)
    leaf6564FlatSound leaf6565FlatSound

private noncomputable def component132Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component132Node13_sound : Sound component132Node13Box :=
  sound_of_literal_split component132Node13Box component132Node11Box component132Node12Box
    .chi (35/64) (by rfl) (by rfl)
    component132Node11_sound component132Node12_sound

private noncomputable def component132Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component132Node14_sound : Sound component132Node14Box :=
  sound_of_literal_split component132Node14Box component132Node10Box component132Node13Box
    .k (49/16) (by rfl) (by rfl)
    component132Node10_sound component132Node13_sound

private noncomputable def component132Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component132Node15_sound : Sound component132Node15Box :=
  sound_of_literal_split component132Node15Box component132Node7Box component132Node14Box
    .chi (17/32) (by rfl) (by rfl)
    component132Node7_sound component132Node14_sound

private noncomputable def component132Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (1/2), chiHi := (65/128) }

set_option maxRecDepth 1000000 in
private theorem component132Node16_sound : Sound component132Node16Box :=
  sound_of_literal_split component132Node16Box leaf6566Box leaf6567Box
    .k (101/32) (by rfl) (by rfl)
    leaf6566FlatSound leaf6567FlatSound

private noncomputable def component132Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (65/128), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component132Node17_sound : Sound component132Node17Box :=
  sound_of_literal_split component132Node17Box leaf6568Box leaf6569Box
    .k (101/32) (by rfl) (by rfl)
    leaf6568FlatSound leaf6569FlatSound

private noncomputable def component132Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component132Node18_sound : Sound component132Node18Box :=
  sound_of_literal_split component132Node18Box component132Node16Box component132Node17Box
    .chi (65/128) (by rfl) (by rfl)
    component132Node16_sound component132Node17_sound

private noncomputable def component132Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (1/2), chiHi := (65/128) }

set_option maxRecDepth 1000000 in
private theorem component132Node19_sound : Sound component132Node19Box :=
  sound_of_literal_split component132Node19Box leaf6570Box leaf6571Box
    .k (103/32) (by rfl) (by rfl)
    leaf6570FlatSound leaf6571FlatSound

private noncomputable def component132Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (65/128), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component132Node20_sound : Sound component132Node20Box :=
  sound_of_literal_split component132Node20Box leaf6572Box leaf6573Box
    .k (103/32) (by rfl) (by rfl)
    leaf6572FlatSound leaf6573FlatSound

private noncomputable def component132Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component132Node21_sound : Sound component132Node21Box :=
  sound_of_literal_split component132Node21Box component132Node19Box component132Node20Box
    .chi (65/128) (by rfl) (by rfl)
    component132Node19_sound component132Node20_sound

private noncomputable def component132Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (1/2), chiHi := (33/64) }

set_option maxRecDepth 1000000 in
private theorem component132Node22_sound : Sound component132Node22Box :=
  sound_of_literal_split component132Node22Box component132Node18Box component132Node21Box
    .k (51/16) (by rfl) (by rfl)
    component132Node18_sound component132Node21_sound

private noncomputable def component132Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component132Node23_sound : Sound component132Node23Box :=
  sound_of_literal_split component132Node23Box leaf6574Box leaf6575Box
    .chi (67/128) (by rfl) (by rfl)
    leaf6574FlatSound leaf6575FlatSound

private noncomputable def component132Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (33/64), chiHi := (67/128) }

set_option maxRecDepth 1000000 in
private theorem component132Node24_sound : Sound component132Node24Box :=
  sound_of_literal_split component132Node24Box leaf6576Box leaf6577Box
    .k (103/32) (by rfl) (by rfl)
    leaf6576FlatSound leaf6577FlatSound

private noncomputable def component132Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component132Node25_sound : Sound component132Node25Box :=
  sound_of_literal_split component132Node25Box component132Node24Box leaf6578Box
    .chi (67/128) (by rfl) (by rfl)
    component132Node24_sound leaf6578FlatSound

private noncomputable def component132Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (33/64), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component132Node26_sound : Sound component132Node26Box :=
  sound_of_literal_split component132Node26Box component132Node23Box component132Node25Box
    .k (51/16) (by rfl) (by rfl)
    component132Node23_sound component132Node25_sound

private noncomputable def component132Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (1/2), chiHi := (17/32) }

set_option maxRecDepth 1000000 in
private theorem component132Node27_sound : Sound component132Node27Box :=
  sound_of_literal_split component132Node27Box component132Node22Box component132Node26Box
    .chi (33/64) (by rfl) (by rfl)
    component132Node22_sound component132Node26_sound

private noncomputable def component132Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component132Node28_sound : Sound component132Node28Box :=
  sound_of_literal_split component132Node28Box leaf6579Box leaf6580Box
    .chi (69/128) (by rfl) (by rfl)
    leaf6579FlatSound leaf6580FlatSound

private noncomputable def component132Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component132Node29_sound : Sound component132Node29Box :=
  sound_of_literal_split component132Node29Box leaf6581Box leaf6582Box
    .chi (69/128) (by rfl) (by rfl)
    leaf6581FlatSound leaf6582FlatSound

private noncomputable def component132Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (17/32), chiHi := (35/64) }

set_option maxRecDepth 1000000 in
private theorem component132Node30_sound : Sound component132Node30Box :=
  sound_of_literal_split component132Node30Box component132Node28Box component132Node29Box
    .k (51/16) (by rfl) (by rfl)
    component132Node28_sound component132Node29_sound

private noncomputable def component132Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component132Node31_sound : Sound component132Node31Box :=
  sound_of_literal_split component132Node31Box leaf6583Box leaf6584Box
    .chi (71/128) (by rfl) (by rfl)
    leaf6583FlatSound leaf6584FlatSound

private noncomputable def component132Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component132Node32_sound : Sound component132Node32Box :=
  sound_of_literal_split component132Node32Box leaf6585Box leaf6586Box
    .chi (71/128) (by rfl) (by rfl)
    leaf6585FlatSound leaf6586FlatSound

private noncomputable def component132Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (35/64), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component132Node33_sound : Sound component132Node33Box :=
  sound_of_literal_split component132Node33Box component132Node31Box component132Node32Box
    .k (51/16) (by rfl) (by rfl)
    component132Node31_sound component132Node32_sound

private noncomputable def component132Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (17/32), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component132Node34_sound : Sound component132Node34Box :=
  sound_of_literal_split component132Node34Box component132Node30Box component132Node33Box
    .chi (35/64) (by rfl) (by rfl)
    component132Node30_sound component132Node33_sound

private noncomputable def component132Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component132Node35_sound : Sound component132Node35Box :=
  sound_of_literal_split component132Node35Box component132Node27Box component132Node34Box
    .chi (17/32) (by rfl) (by rfl)
    component132Node27_sound component132Node34_sound

noncomputable def component132Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
theorem component132_sound : Sound component132Box :=
  sound_of_literal_split component132Box component132Node15Box component132Node35Box
    .k (25/8) (by rfl) (by rfl)
    component132Node15_sound component132Node35_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
