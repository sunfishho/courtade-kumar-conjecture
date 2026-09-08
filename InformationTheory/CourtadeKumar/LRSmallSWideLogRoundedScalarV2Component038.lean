import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
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

private noncomputable def leaf1657Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (1/16), chiHi := (17/256) }

private noncomputable def leaf1657Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435603/268435456) }, vSqrt := { lower := (8191/8192), upper := (67108992/67107895) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (327119215/268435456) }, upper := { exponent := 0, mantissa := (5065/4096) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi151LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216887/134215790) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf1657InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1657LocalValidity :
    LeafFacts leaf1657Box leaf1657Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1657Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108992/67107895) }) = true
      norm_num [leaf1657Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1657CertificateValid :
    WideCertificateValid leaf1657Box leaf1657Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi151ValidityFacts
    leaf1657LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1657CoverageChecked :
    coverageCheck (innerAD leaf1657Box) leaf1657InnerLog = true := by
  rfl'

private theorem leaf1657InnerLogValid :
    leaf1657InnerLog.Valid 8 (innerAD leaf1657Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1657CoverageChecked

private noncomputable def leaf1657InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814609/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1657InputLogOnePlusV_eq :
    leaf1657InputLogOnePlusV = outerEnclosure 24
      (leaf1657Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1657RoundedFacts : LeafRoundedFacts 8
    leaf1657Certificate.logOnePlusV leaf1657InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1657InputLogOnePlusV_eq }

private noncomputable def leaf1657Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi151InputQChi innerPair12Input
    leaf1657InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1657LowerChecked :
    lowerCheck 24 leaf1657Box leaf1657Inputs = true := by
  rfl'

private theorem leaf1657CoversExact : CoversExact 8
    leaf1657Box leaf1657Certificate leaf1657InnerLog leaf1657Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi151RoundedFacts
    innerPair12RoundedFacts leaf1657RoundedFacts (by rfl)

private theorem leaf1657FlatSound : Sound leaf1657Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1657CertificateValid
    leaf1657InnerLogValid leaf1657CoversExact leaf1657LowerChecked

private noncomputable def leaf1658Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (17/256), chiHi := (9/128) }

private noncomputable def leaf1658Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435605/268435456) }, vSqrt := { lower := (8191/8192), upper := (33554496/33553919) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (330789005/268435456) }, upper := { exponent := 0, mantissa := (2561/2048) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi152LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108415/67107838) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf1658InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1658LocalValidity :
    LeafFacts leaf1658Box leaf1658Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1658Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554496/33553919) }) = true
      norm_num [leaf1658Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1658CertificateValid :
    WideCertificateValid leaf1658Box leaf1658Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi152ValidityFacts
    leaf1658LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1658CoverageChecked :
    coverageCheck (innerAD leaf1658Box) leaf1658InnerLog = true := by
  rfl'

private theorem leaf1658InnerLogValid :
    leaf1658InnerLog.Valid 8 (innerAD leaf1658Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1658CoverageChecked

private noncomputable def leaf1658InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1658InputLogOnePlusV_eq :
    leaf1658InputLogOnePlusV = outerEnclosure 24
      (leaf1658Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1658RoundedFacts : LeafRoundedFacts 8
    leaf1658Certificate.logOnePlusV leaf1658InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1658InputLogOnePlusV_eq }

private noncomputable def leaf1658Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi152InputQChi innerPair13Input
    leaf1658InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1658LowerChecked :
    lowerCheck 24 leaf1658Box leaf1658Inputs = true := by
  rfl'

private theorem leaf1658CoversExact : CoversExact 8
    leaf1658Box leaf1658Certificate leaf1658InnerLog leaf1658Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi152RoundedFacts
    innerPair13RoundedFacts leaf1658RoundedFacts (by rfl)

private theorem leaf1658FlatSound : Sound leaf1658Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1658CertificateValid
    leaf1658InnerLogValid leaf1658CoversExact leaf1658LowerChecked

private noncomputable def leaf1659Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (1/16), chiHi := (17/256) }

private noncomputable def leaf1659Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435605/268435456) }, vSqrt := { lower := (8191/8192), upper := (33554496/33553939) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (328167725/268435456) }, upper := { exponent := 0, mantissa := (2541/2048) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi151LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108435/67107878) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf1659InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1659LocalValidity :
    LeafFacts leaf1659Box leaf1659Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1659Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554496/33553939) }) = true
      norm_num [leaf1659Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1659CertificateValid :
    WideCertificateValid leaf1659Box leaf1659Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi151ValidityFacts
    leaf1659LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1659CoverageChecked :
    coverageCheck (innerAD leaf1659Box) leaf1659InnerLog = true := by
  rfl'

private theorem leaf1659InnerLogValid :
    leaf1659InnerLog.Valid 8 (innerAD leaf1659Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1659CoverageChecked

private noncomputable def leaf1659InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907305/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1659InputLogOnePlusV_eq :
    leaf1659InputLogOnePlusV = outerEnclosure 24
      (leaf1659Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1659RoundedFacts : LeafRoundedFacts 8
    leaf1659Certificate.logOnePlusV leaf1659InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1659InputLogOnePlusV_eq }

private noncomputable def leaf1659Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi151InputQChi innerPair12Input
    leaf1659InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1659LowerChecked :
    lowerCheck 24 leaf1659Box leaf1659Inputs = true := by
  rfl'

private theorem leaf1659CoversExact : CoversExact 8
    leaf1659Box leaf1659Certificate leaf1659InnerLog leaf1659Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi151RoundedFacts
    innerPair12RoundedFacts leaf1659RoundedFacts (by rfl)

private theorem leaf1659FlatSound : Sound leaf1659Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1659CertificateValid
    leaf1659InnerLogValid leaf1659CoversExact leaf1659LowerChecked

private noncomputable def leaf1660Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (17/256), chiHi := (9/128) }

private noncomputable def leaf1660Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435607/268435456) }, vSqrt := { lower := (8191/8192), upper := (16777248/16776955) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (331903047/268435456) }, upper := { exponent := 0, mantissa := (1285/1024) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi152LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554203/33553910) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf1660InnerLog : WideLogData :=
  innerPair402Data

set_option maxRecDepth 1000000 in
private theorem leaf1660LocalValidity :
    LeafFacts leaf1660Box leaf1660Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1660Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777248/16776955) }) = true
      norm_num [leaf1660Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1660CertificateValid :
    WideCertificateValid leaf1660Box leaf1660Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi152ValidityFacts
    leaf1660LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1660CoverageChecked :
    coverageCheck (innerAD leaf1660Box) leaf1660InnerLog = true := by
  rfl'

private theorem leaf1660InnerLogValid :
    leaf1660InnerLog.Valid 8 (innerAD leaf1660Box) :=
  wideLogDataValid_of_cachedCheck endpoint116PositiveFacts
    endpoint100PositiveFacts.valid leaf1660CoverageChecked

private noncomputable def leaf1660InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1660InputLogOnePlusV_eq :
    leaf1660InputLogOnePlusV = outerEnclosure 24
      (leaf1660Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1660RoundedFacts : LeafRoundedFacts 8
    leaf1660Certificate.logOnePlusV leaf1660InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1660InputLogOnePlusV_eq }

private noncomputable def leaf1660Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi152InputQChi innerPair402Input
    leaf1660InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1660LowerChecked :
    lowerCheck 24 leaf1660Box leaf1660Inputs = true := by
  rfl'

private theorem leaf1660CoversExact : CoversExact 8
    leaf1660Box leaf1660Certificate leaf1660InnerLog leaf1660Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi152RoundedFacts
    innerPair402RoundedFacts leaf1660RoundedFacts (by rfl)

private theorem leaf1660FlatSound : Sound leaf1660Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1660CertificateValid
    leaf1660InnerLogValid leaf1660CoversExact leaf1660LowerChecked

private noncomputable def leaf1661Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1661Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435607/268435456) }, vSqrt := { lower := (8191/8192), upper := (67108992/67107781) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (334458795/268435456) }, upper := { exponent := 0, mantissa := (5179/4096) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216773/134215562) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf1661InnerLog : WideLogData :=
  innerPair402Data

set_option maxRecDepth 1000000 in
private theorem leaf1661LocalValidity :
    LeafFacts leaf1661Box leaf1661Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1661Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108992/67107781) }) = true
      norm_num [leaf1661Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1661CertificateValid :
    WideCertificateValid leaf1661Box leaf1661Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi147ValidityFacts
    leaf1661LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1661CoverageChecked :
    coverageCheck (innerAD leaf1661Box) leaf1661InnerLog = true := by
  rfl'

private theorem leaf1661InnerLogValid :
    leaf1661InnerLog.Valid 8 (innerAD leaf1661Box) :=
  wideLogDataValid_of_cachedCheck endpoint116PositiveFacts
    endpoint100PositiveFacts.valid leaf1661CoverageChecked

private noncomputable def leaf1661InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1661InputLogOnePlusV_eq :
    leaf1661InputLogOnePlusV = outerEnclosure 24
      (leaf1661Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1661RoundedFacts : LeafRoundedFacts 8
    leaf1661Certificate.logOnePlusV leaf1661InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1661InputLogOnePlusV_eq }

private noncomputable def leaf1661Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi147InputQChi innerPair402Input
    leaf1661InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1661LowerChecked :
    lowerCheck 24 leaf1661Box leaf1661Inputs = true := by
  rfl'

private theorem leaf1661CoversExact : CoversExact 8
    leaf1661Box leaf1661Certificate leaf1661InnerLog leaf1661Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi147RoundedFacts
    innerPair402RoundedFacts leaf1661RoundedFacts (by rfl)

private theorem leaf1661FlatSound : Sound leaf1661Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1661CertificateValid
    leaf1661InnerLogValid leaf1661CoversExact leaf1661LowerChecked

private noncomputable def leaf1662Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1662Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435609/268435456) }, vSqrt := { lower := (8191/8192), upper := (16777248/16776931) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (338128585/268435456) }, upper := { exponent := 0, mantissa := (1309/1024) } }, logOuter := sk151LogOuterCertificate, logK := sk151LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554179/33553862) } }, logDArg := sk151LogDArgCertificate }

private noncomputable def leaf1662InnerLog : WideLogData :=
  innerPair441Data

set_option maxRecDepth 1000000 in
private theorem leaf1662LocalValidity :
    LeafFacts leaf1662Box leaf1662Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1662Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777248/16776931) }) = true
      norm_num [leaf1662Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1662CertificateValid :
    WideCertificateValid leaf1662Box leaf1662Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk151ValidityFacts chi148ValidityFacts
    leaf1662LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1662CoverageChecked :
    coverageCheck (innerAD leaf1662Box) leaf1662InnerLog = true := by
  rfl'

private theorem leaf1662InnerLogValid :
    leaf1662InnerLog.Valid 8 (innerAD leaf1662Box) :=
  wideLogDataValid_of_cachedCheck endpoint152PositiveFacts
    endpoint153PositiveFacts.valid leaf1662CoverageChecked

private noncomputable def leaf1662InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629239/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1662InputLogOnePlusV_eq :
    leaf1662InputLogOnePlusV = outerEnclosure 24
      (leaf1662Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1662RoundedFacts : LeafRoundedFacts 8
    leaf1662Certificate.logOnePlusV leaf1662InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1662InputLogOnePlusV_eq }

private noncomputable def leaf1662Inputs : Inputs :=
  inputsOfCaches globalInput sk151RoundedInputs
    chi148InputQChi innerPair441Input
    leaf1662InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1662LowerChecked :
    lowerCheck 24 leaf1662Box leaf1662Inputs = true := by
  rfl'

private theorem leaf1662CoversExact : CoversExact 8
    leaf1662Box leaf1662Certificate leaf1662InnerLog leaf1662Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk151RoundedFacts chi148RoundedFacts
    innerPair441RoundedFacts leaf1662RoundedFacts (by rfl)

private theorem leaf1662FlatSound : Sound leaf1662Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1662CertificateValid
    leaf1662InnerLogValid leaf1662CoversExact leaf1662LowerChecked

private noncomputable def leaf1663Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1663Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435609/268435456) }, vSqrt := { lower := (8191/8192), upper := (11184832/11184627) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (335638369/268435456) }, upper := { exponent := 0, mantissa := (2599/2048) } }, logOuter := sk152LogOuterCertificate, logK := sk152LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22369459/22369254) } }, logDArg := sk152LogDArgCertificate }

private noncomputable def leaf1663InnerLog : WideLogData :=
  innerPair20Data

set_option maxRecDepth 1000000 in
private theorem leaf1663LocalValidity :
    LeafFacts leaf1663Box leaf1663Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1663Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11184832/11184627) }) = true
      norm_num [leaf1663Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1663CertificateValid :
    WideCertificateValid leaf1663Box leaf1663Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk152ValidityFacts chi147ValidityFacts
    leaf1663LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1663CoverageChecked :
    coverageCheck (innerAD leaf1663Box) leaf1663InnerLog = true := by
  rfl'

private theorem leaf1663InnerLogValid :
    leaf1663InnerLog.Valid 8 (innerAD leaf1663Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint28PositiveFacts.valid leaf1663CoverageChecked

private noncomputable def leaf1663InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1663InputLogOnePlusV_eq :
    leaf1663InputLogOnePlusV = outerEnclosure 24
      (leaf1663Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1663RoundedFacts : LeafRoundedFacts 8
    leaf1663Certificate.logOnePlusV leaf1663InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1663InputLogOnePlusV_eq }

private noncomputable def leaf1663Inputs : Inputs :=
  inputsOfCaches globalInput sk152RoundedInputs
    chi147InputQChi innerPair20Input
    leaf1663InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1663LowerChecked :
    lowerCheck 24 leaf1663Box leaf1663Inputs = true := by
  rfl'

private theorem leaf1663CoversExact : CoversExact 8
    leaf1663Box leaf1663Certificate leaf1663InnerLog leaf1663Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk152RoundedFacts chi147RoundedFacts
    innerPair20RoundedFacts leaf1663RoundedFacts (by rfl)

private theorem leaf1663FlatSound : Sound leaf1663Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1663CertificateValid
    leaf1663InnerLogValid leaf1663CoversExact leaf1663LowerChecked

private noncomputable def leaf1664Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1664Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871181/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553857) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (678780189/536870912) }, upper := { exponent := 0, mantissa := (2623/2048) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108321/67107714) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf1664InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1664LocalValidity :
    LeafFacts leaf1664Box leaf1664Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1664Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553857) }) = true
      norm_num [leaf1664Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1664CertificateValid :
    WideCertificateValid leaf1664Box leaf1664Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi148ValidityFacts
    leaf1664LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1664CoverageChecked :
    coverageCheck (innerAD leaf1664Box) leaf1664InnerLog = true := by
  rfl'

private theorem leaf1664InnerLogValid :
    leaf1664InnerLog.Valid 8 (innerAD leaf1664Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1664CoverageChecked

private noncomputable def leaf1664InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1664InputLogOnePlusV_eq :
    leaf1664InputLogOnePlusV = outerEnclosure 24
      (leaf1664Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1664RoundedFacts : LeafRoundedFacts 8
    leaf1664Certificate.logOnePlusV leaf1664InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1664InputLogOnePlusV_eq }

private noncomputable def leaf1664Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi148InputQChi innerPair16Input
    leaf1664InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1664LowerChecked :
    lowerCheck 24 leaf1664Box leaf1664Inputs = true := by
  rfl'

private theorem leaf1664CoversExact : CoversExact 8
    leaf1664Box leaf1664Certificate leaf1664InnerLog leaf1664Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi148RoundedFacts
    innerPair16RoundedFacts leaf1664RoundedFacts (by rfl)

private theorem leaf1664FlatSound : Sound leaf1664Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1664CertificateValid
    leaf1664InnerLogValid leaf1664CoversExact leaf1664LowerChecked

private noncomputable def leaf1665Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1665Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871183/536870912) }, vSqrt := { lower := (8191/8192), upper := (493448/493439) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (680025295/536870912) }, upper := { exponent := 0, mantissa := (657/512) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (986887/986878) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf1665InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1665LocalValidity :
    LeafFacts leaf1665Box leaf1665Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1665Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (493448/493439) }) = true
      norm_num [leaf1665Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1665CertificateValid :
    WideCertificateValid leaf1665Box leaf1665Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi148ValidityFacts
    leaf1665LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1665CoverageChecked :
    coverageCheck (innerAD leaf1665Box) leaf1665InnerLog = true := by
  rfl'

private theorem leaf1665InnerLogValid :
    leaf1665InnerLog.Valid 8 (innerAD leaf1665Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1665CoverageChecked

private noncomputable def leaf1665InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1665InputLogOnePlusV_eq :
    leaf1665InputLogOnePlusV = outerEnclosure 24
      (leaf1665Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1665RoundedFacts : LeafRoundedFacts 8
    leaf1665Certificate.logOnePlusV leaf1665InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1665InputLogOnePlusV_eq }

private noncomputable def leaf1665Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi148InputQChi innerPair16Input
    leaf1665InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1665LowerChecked :
    lowerCheck 24 leaf1665Box leaf1665Inputs = true := by
  rfl'

private theorem leaf1665CoversExact : CoversExact 8
    leaf1665Box leaf1665Certificate leaf1665InnerLog leaf1665Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi148RoundedFacts
    innerPair16RoundedFacts leaf1665RoundedFacts (by rfl)

private theorem leaf1665FlatSound : Sound leaf1665Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1665CertificateValid
    leaf1665InnerLogValid leaf1665CoversExact leaf1665LowerChecked

private noncomputable def leaf1666Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (1/16), chiHi := (17/256) }

private noncomputable def leaf1666Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435607/268435456) }, vSqrt := { lower := (8191/8192), upper := (22369664/22369287) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (329216235/268435456) }, upper := { exponent := 0, mantissa := (5099/4096) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi151LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (44738951/44738574) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf1666InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1666LocalValidity :
    LeafFacts leaf1666Box leaf1666Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1666Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (22369664/22369287) }) = true
      norm_num [leaf1666Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1666CertificateValid :
    WideCertificateValid leaf1666Box leaf1666Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi151ValidityFacts
    leaf1666LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1666CoverageChecked :
    coverageCheck (innerAD leaf1666Box) leaf1666InnerLog = true := by
  rfl'

private theorem leaf1666InnerLogValid :
    leaf1666InnerLog.Valid 8 (innerAD leaf1666Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1666CoverageChecked

private noncomputable def leaf1666InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814611/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1666InputLogOnePlusV_eq :
    leaf1666InputLogOnePlusV = outerEnclosure 24
      (leaf1666Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1666RoundedFacts : LeafRoundedFacts 8
    leaf1666Certificate.logOnePlusV leaf1666InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1666InputLogOnePlusV_eq }

private noncomputable def leaf1666Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi151InputQChi innerPair12Input
    leaf1666InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1666LowerChecked :
    lowerCheck 24 leaf1666Box leaf1666Inputs = true := by
  rfl'

private theorem leaf1666CoversExact : CoversExact 8
    leaf1666Box leaf1666Certificate leaf1666InnerLog leaf1666Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi151RoundedFacts
    innerPair12RoundedFacts leaf1666RoundedFacts (by rfl)

private theorem leaf1666FlatSound : Sound leaf1666Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1666CertificateValid
    leaf1666InnerLogValid leaf1666CoversExact leaf1666LowerChecked

private noncomputable def leaf1667Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (17/256), chiHi := (9/128) }

private noncomputable def leaf1667Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435609/268435456) }, vSqrt := { lower := (8191/8192), upper := (33554496/33553901) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (333017089/268435456) }, upper := { exponent := 0, mantissa := (2579/2048) } }, logOuter := sk153LogOuterCertificate, logK := sk153LogKCertificate, logChi := chi152LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108397/67107802) } }, logDArg := sk153LogDArgCertificate }

private noncomputable def leaf1667InnerLog : WideLogData :=
  innerPair402Data

set_option maxRecDepth 1000000 in
private theorem leaf1667LocalValidity :
    LeafFacts leaf1667Box leaf1667Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1667Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554496/33553901) }) = true
      norm_num [leaf1667Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1667CertificateValid :
    WideCertificateValid leaf1667Box leaf1667Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk153ValidityFacts chi152ValidityFacts
    leaf1667LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1667CoverageChecked :
    coverageCheck (innerAD leaf1667Box) leaf1667InnerLog = true := by
  rfl'

private theorem leaf1667InnerLogValid :
    leaf1667InnerLog.Valid 8 (innerAD leaf1667Box) :=
  wideLogDataValid_of_cachedCheck endpoint116PositiveFacts
    endpoint100PositiveFacts.valid leaf1667CoverageChecked

private noncomputable def leaf1667InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1667InputLogOnePlusV_eq :
    leaf1667InputLogOnePlusV = outerEnclosure 24
      (leaf1667Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1667RoundedFacts : LeafRoundedFacts 8
    leaf1667Certificate.logOnePlusV leaf1667InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1667InputLogOnePlusV_eq }

private noncomputable def leaf1667Inputs : Inputs :=
  inputsOfCaches globalInput sk153RoundedInputs
    chi152InputQChi innerPair402Input
    leaf1667InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1667LowerChecked :
    lowerCheck 24 leaf1667Box leaf1667Inputs = true := by
  rfl'

private theorem leaf1667CoversExact : CoversExact 8
    leaf1667Box leaf1667Certificate leaf1667InnerLog leaf1667Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk153RoundedFacts chi152RoundedFacts
    innerPair402RoundedFacts leaf1667RoundedFacts (by rfl)

private theorem leaf1667FlatSound : Sound leaf1667Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1667CertificateValid
    leaf1667InnerLogValid leaf1667CoversExact leaf1667LowerChecked

private noncomputable def leaf1668Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (1/16), chiHi := (17/256) }

private noncomputable def leaf1668Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435609/268435456) }, vSqrt := { lower := (8191/8192), upper := (16777248/16776961) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (330264745/268435456) }, upper := { exponent := 0, mantissa := (1279/1024) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi151LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554209/33553922) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf1668InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1668LocalValidity :
    LeafFacts leaf1668Box leaf1668Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1668Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777248/16776961) }) = true
      norm_num [leaf1668Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1668CertificateValid :
    WideCertificateValid leaf1668Box leaf1668Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi151ValidityFacts
    leaf1668LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1668CoverageChecked :
    coverageCheck (innerAD leaf1668Box) leaf1668InnerLog = true := by
  rfl'

private theorem leaf1668InnerLogValid :
    leaf1668InnerLog.Valid 8 (innerAD leaf1668Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1668CoverageChecked

private noncomputable def leaf1668InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453653/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1668InputLogOnePlusV_eq :
    leaf1668InputLogOnePlusV = outerEnclosure 24
      (leaf1668Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1668RoundedFacts : LeafRoundedFacts 8
    leaf1668Certificate.logOnePlusV leaf1668InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1668InputLogOnePlusV_eq }

private noncomputable def leaf1668Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi151InputQChi innerPair12Input
    leaf1668InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1668LowerChecked :
    lowerCheck 24 leaf1668Box leaf1668Inputs = true := by
  rfl'

private theorem leaf1668CoversExact : CoversExact 8
    leaf1668Box leaf1668Certificate leaf1668InnerLog leaf1668Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi151RoundedFacts
    innerPair12RoundedFacts leaf1668RoundedFacts (by rfl)

private theorem leaf1668FlatSound : Sound leaf1668Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1668CertificateValid
    leaf1668InnerLogValid leaf1668CoversExact leaf1668LowerChecked

private noncomputable def leaf1669Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (17/256), chiHi := (9/128) }

private noncomputable def leaf1669Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435611/268435456) }, vSqrt := { lower := (8191/8192), upper := (8388624/8388473) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (334131131/268435456) }, upper := { exponent := 0, mantissa := (647/512) } }, logOuter := sk154LogOuterCertificate, logK := sk154LogKCertificate, logChi := chi152LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777097/16776946) } }, logDArg := sk154LogDArgCertificate }

private noncomputable def leaf1669InnerLog : WideLogData :=
  innerPair402Data

set_option maxRecDepth 1000000 in
private theorem leaf1669LocalValidity :
    LeafFacts leaf1669Box leaf1669Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1669Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388624/8388473) }) = true
      norm_num [leaf1669Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1669CertificateValid :
    WideCertificateValid leaf1669Box leaf1669Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk154ValidityFacts chi152ValidityFacts
    leaf1669LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1669CoverageChecked :
    coverageCheck (innerAD leaf1669Box) leaf1669InnerLog = true := by
  rfl'

private theorem leaf1669InnerLogValid :
    leaf1669InnerLog.Valid 8 (innerAD leaf1669Box) :=
  wideLogDataValid_of_cachedCheck endpoint116PositiveFacts
    endpoint100PositiveFacts.valid leaf1669CoverageChecked

private noncomputable def leaf1669InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1669InputLogOnePlusV_eq :
    leaf1669InputLogOnePlusV = outerEnclosure 24
      (leaf1669Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1669RoundedFacts : LeafRoundedFacts 8
    leaf1669Certificate.logOnePlusV leaf1669InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1669InputLogOnePlusV_eq }

private noncomputable def leaf1669Inputs : Inputs :=
  inputsOfCaches globalInput sk154RoundedInputs
    chi152InputQChi innerPair402Input
    leaf1669InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1669LowerChecked :
    lowerCheck 24 leaf1669Box leaf1669Inputs = true := by
  rfl'

private theorem leaf1669CoversExact : CoversExact 8
    leaf1669Box leaf1669Certificate leaf1669InnerLog leaf1669Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk154RoundedFacts chi152RoundedFacts
    innerPair402RoundedFacts leaf1669RoundedFacts (by rfl)

private theorem leaf1669FlatSound : Sound leaf1669Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1669CertificateValid
    leaf1669InnerLogValid leaf1669CoversExact leaf1669LowerChecked

private noncomputable def leaf1670Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1670Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871183/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134215505) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (673668691/536870912) }, upper := { exponent := 0, mantissa := (10415/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268433361/268431010) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf1670InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1670LocalValidity :
    LeafFacts leaf1670Box leaf1670Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1670Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134215505) }) = true
      norm_num [leaf1670Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1670CertificateValid :
    WideCertificateValid leaf1670Box leaf1670Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi147ValidityFacts
    leaf1670LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1670CoverageChecked :
    coverageCheck (innerAD leaf1670Box) leaf1670InnerLog = true := by
  rfl'

private theorem leaf1670InnerLogValid :
    leaf1670InnerLog.Valid 8 (innerAD leaf1670Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1670CoverageChecked

private noncomputable def leaf1670InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907307/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1670InputLogOnePlusV_eq :
    leaf1670InputLogOnePlusV = outerEnclosure 24
      (leaf1670Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1670RoundedFacts : LeafRoundedFacts 8
    leaf1670Certificate.logOnePlusV leaf1670InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1670InputLogOnePlusV_eq }

private noncomputable def leaf1670Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi147InputQChi innerPair16Input
    leaf1670InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1670LowerChecked :
    lowerCheck 24 leaf1670Box leaf1670Inputs = true := by
  rfl'

private theorem leaf1670CoversExact : CoversExact 8
    leaf1670Box leaf1670Certificate leaf1670InnerLog leaf1670Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi147RoundedFacts
    innerPair16RoundedFacts leaf1670RoundedFacts (by rfl)

private theorem leaf1670FlatSound : Sound leaf1670Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1670CertificateValid
    leaf1670InnerLogValid leaf1670CoversExact leaf1670LowerChecked

private noncomputable def leaf1671Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1671Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107743) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (674848265/536870912) }, upper := { exponent := 0, mantissa := (5217/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216671/134215486) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf1671InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1671LocalValidity :
    LeafFacts leaf1671Box leaf1671Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1671Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107743) }) = true
      norm_num [leaf1671Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1671CertificateValid :
    WideCertificateValid leaf1671Box leaf1671Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi147ValidityFacts
    leaf1671LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1671CoverageChecked :
    coverageCheck (innerAD leaf1671Box) leaf1671InnerLog = true := by
  rfl'

private theorem leaf1671InnerLogValid :
    leaf1671InnerLog.Valid 8 (innerAD leaf1671Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1671CoverageChecked

private noncomputable def leaf1671InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1671InputLogOnePlusV_eq :
    leaf1671InputLogOnePlusV = outerEnclosure 24
      (leaf1671Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1671RoundedFacts : LeafRoundedFacts 8
    leaf1671Certificate.logOnePlusV leaf1671InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1671InputLogOnePlusV_eq }

private noncomputable def leaf1671Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi147InputQChi innerPair16Input
    leaf1671InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1671LowerChecked :
    lowerCheck 24 leaf1671Box leaf1671Inputs = true := by
  rfl'

private theorem leaf1671CoversExact : CoversExact 8
    leaf1671Box leaf1671Certificate leaf1671InnerLog leaf1671Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi147RoundedFacts
    innerPair16RoundedFacts leaf1671RoundedFacts (by rfl)

private theorem leaf1671FlatSound : Sound leaf1671Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1671CertificateValid
    leaf1671InnerLogValid leaf1671CoversExact leaf1671LowerChecked

private noncomputable def leaf1672Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1672Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553847) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (681270401/536870912) }, upper := { exponent := 0, mantissa := (2633/2048) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108311/67107694) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf1672InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1672LocalValidity :
    LeafFacts leaf1672Box leaf1672Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1672Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553847) }) = true
      norm_num [leaf1672Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1672CertificateValid :
    WideCertificateValid leaf1672Box leaf1672Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi148ValidityFacts
    leaf1672LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1672CoverageChecked :
    coverageCheck (innerAD leaf1672Box) leaf1672InnerLog = true := by
  rfl'

private theorem leaf1672InnerLogValid :
    leaf1672InnerLog.Valid 8 (innerAD leaf1672Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1672CoverageChecked

private noncomputable def leaf1672InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629235/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1672InputLogOnePlusV_eq :
    leaf1672InputLogOnePlusV = outerEnclosure 24
      (leaf1672Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1672RoundedFacts : LeafRoundedFacts 8
    leaf1672Certificate.logOnePlusV leaf1672InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1672InputLogOnePlusV_eq }

private noncomputable def leaf1672Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi148InputQChi innerPair16Input
    leaf1672InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1672LowerChecked :
    lowerCheck 24 leaf1672Box leaf1672Inputs = true := by
  rfl'

private theorem leaf1672CoversExact : CoversExact 8
    leaf1672Box leaf1672Certificate leaf1672InnerLog leaf1672Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi148RoundedFacts
    innerPair16RoundedFacts leaf1672RoundedFacts (by rfl)

private theorem leaf1672FlatSound : Sound leaf1672Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1672CertificateValid
    leaf1672InnerLogValid leaf1672CoversExact leaf1672LowerChecked

private noncomputable def leaf1673Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1673Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776921) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (682515507/536870912) }, upper := { exponent := 0, mantissa := (1319/1024) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554153/33553842) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf1673InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1673LocalValidity :
    LeafFacts leaf1673Box leaf1673Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1673Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776921) }) = true
      norm_num [leaf1673Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1673CertificateValid :
    WideCertificateValid leaf1673Box leaf1673Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi148ValidityFacts
    leaf1673LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1673CoverageChecked :
    coverageCheck (innerAD leaf1673Box) leaf1673InnerLog = true := by
  rfl'

private theorem leaf1673InnerLogValid :
    leaf1673InnerLog.Valid 8 (innerAD leaf1673Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1673CoverageChecked

private noncomputable def leaf1673InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1673InputLogOnePlusV_eq :
    leaf1673InputLogOnePlusV = outerEnclosure 24
      (leaf1673Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1673RoundedFacts : LeafRoundedFacts 8
    leaf1673Certificate.logOnePlusV leaf1673InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1673InputLogOnePlusV_eq }

private noncomputable def leaf1673Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi148InputQChi innerPair16Input
    leaf1673InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1673LowerChecked :
    lowerCheck 24 leaf1673Box leaf1673Inputs = true := by
  rfl'

private theorem leaf1673CoversExact : CoversExact 8
    leaf1673Box leaf1673Certificate leaf1673InnerLog leaf1673Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi148RoundedFacts
    innerPair16RoundedFacts leaf1673RoundedFacts (by rfl)

private theorem leaf1673FlatSound : Sound leaf1673Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1673CertificateValid
    leaf1673InnerLogValid leaf1673CoversExact leaf1673LowerChecked

private noncomputable def leaf1674Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1674Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134215467) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (676027839/536870912) }, upper := { exponent := 0, mantissa := (10453/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268433323/268430934) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf1674InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1674LocalValidity :
    LeafFacts leaf1674Box leaf1674Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1674Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134215467) }) = true
      norm_num [leaf1674Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1674CertificateValid :
    WideCertificateValid leaf1674Box leaf1674Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi147ValidityFacts
    leaf1674LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1674CoverageChecked :
    coverageCheck (innerAD leaf1674Box) leaf1674InnerLog = true := by
  rfl'

private theorem leaf1674InnerLogValid :
    leaf1674InnerLog.Valid 8 (innerAD leaf1674Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1674CoverageChecked

private noncomputable def leaf1674InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814615/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1674InputLogOnePlusV_eq :
    leaf1674InputLogOnePlusV = outerEnclosure 24
      (leaf1674Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1674RoundedFacts : LeafRoundedFacts 8
    leaf1674Certificate.logOnePlusV leaf1674InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1674InputLogOnePlusV_eq }

private noncomputable def leaf1674Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi147InputQChi innerPair16Input
    leaf1674InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1674LowerChecked :
    lowerCheck 24 leaf1674Box leaf1674Inputs = true := by
  rfl'

private theorem leaf1674CoversExact : CoversExact 8
    leaf1674Box leaf1674Certificate leaf1674InnerLog leaf1674Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi147RoundedFacts
    innerPair16RoundedFacts leaf1674RoundedFacts (by rfl)

private theorem leaf1674FlatSound : Sound leaf1674Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1674CertificateValid
    leaf1674InnerLogValid leaf1674CoversExact leaf1674LowerChecked

private noncomputable def leaf1675Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1675Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776931) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (677207413/536870912) }, upper := { exponent := 0, mantissa := (1309/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554163/33553862) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf1675InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1675LocalValidity :
    LeafFacts leaf1675Box leaf1675Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1675Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776931) }) = true
      norm_num [leaf1675Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1675CertificateValid :
    WideCertificateValid leaf1675Box leaf1675Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi147ValidityFacts
    leaf1675LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1675CoverageChecked :
    coverageCheck (innerAD leaf1675Box) leaf1675InnerLog = true := by
  rfl'

private theorem leaf1675InnerLogValid :
    leaf1675InnerLog.Valid 8 (innerAD leaf1675Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1675CoverageChecked

private noncomputable def leaf1675InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629231/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1675InputLogOnePlusV_eq :
    leaf1675InputLogOnePlusV = outerEnclosure 24
      (leaf1675Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1675RoundedFacts : LeafRoundedFacts 8
    leaf1675Certificate.logOnePlusV leaf1675InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1675InputLogOnePlusV_eq }

private noncomputable def leaf1675Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi147InputQChi innerPair16Input
    leaf1675InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1675LowerChecked :
    lowerCheck 24 leaf1675Box leaf1675Inputs = true := by
  rfl'

private theorem leaf1675CoversExact : CoversExact 8
    leaf1675Box leaf1675Certificate leaf1675InnerLog leaf1675Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi147RoundedFacts
    innerPair16RoundedFacts leaf1675RoundedFacts (by rfl)

private theorem leaf1675FlatSound : Sound leaf1675Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1675CertificateValid
    leaf1675InnerLogValid leaf1675CoversExact leaf1675LowerChecked

private noncomputable def leaf1676Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1676Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553837) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (683760613/536870912) }, upper := { exponent := 0, mantissa := (2643/2048) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108301/67107674) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf1676InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1676LocalValidity :
    LeafFacts leaf1676Box leaf1676Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1676Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553837) }) = true
      norm_num [leaf1676Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1676CertificateValid :
    WideCertificateValid leaf1676Box leaf1676Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi148ValidityFacts
    leaf1676LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1676CoverageChecked :
    coverageCheck (innerAD leaf1676Box) leaf1676InnerLog = true := by
  rfl'

private theorem leaf1676InnerLogValid :
    leaf1676InnerLog.Valid 8 (innerAD leaf1676Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1676CoverageChecked

private noncomputable def leaf1676InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1676InputLogOnePlusV_eq :
    leaf1676InputLogOnePlusV = outerEnclosure 24
      (leaf1676Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1676RoundedFacts : LeafRoundedFacts 8
    leaf1676Certificate.logOnePlusV leaf1676InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1676InputLogOnePlusV_eq }

private noncomputable def leaf1676Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi148InputQChi innerPair16Input
    leaf1676InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1676LowerChecked :
    lowerCheck 24 leaf1676Box leaf1676Inputs = true := by
  rfl'

private theorem leaf1676CoversExact : CoversExact 8
    leaf1676Box leaf1676Certificate leaf1676InnerLog leaf1676Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi148RoundedFacts
    innerPair16RoundedFacts leaf1676RoundedFacts (by rfl)

private theorem leaf1676FlatSound : Sound leaf1676Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1676CertificateValid
    leaf1676InnerLogValid leaf1676CoversExact leaf1676LowerChecked

private noncomputable def leaf1677Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1677Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (8191/8192), upper := (4194308/4194229) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (685005719/536870912) }, upper := { exponent := 0, mantissa := (331/256) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388537/8388458) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf1677InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1677LocalValidity :
    LeafFacts leaf1677Box leaf1677Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1677Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194308/4194229) }) = true
      norm_num [leaf1677Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1677CertificateValid :
    WideCertificateValid leaf1677Box leaf1677Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi148ValidityFacts
    leaf1677LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1677CoverageChecked :
    coverageCheck (innerAD leaf1677Box) leaf1677InnerLog = true := by
  rfl'

private theorem leaf1677InnerLogValid :
    leaf1677InnerLog.Valid 8 (innerAD leaf1677Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1677CoverageChecked

private noncomputable def leaf1677InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629239/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1677InputLogOnePlusV_eq :
    leaf1677InputLogOnePlusV = outerEnclosure 24
      (leaf1677Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1677RoundedFacts : LeafRoundedFacts 8
    leaf1677Certificate.logOnePlusV leaf1677InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1677InputLogOnePlusV_eq }

private noncomputable def leaf1677Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi148InputQChi innerPair16Input
    leaf1677InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1677LowerChecked :
    lowerCheck 24 leaf1677Box leaf1677Inputs = true := by
  rfl'

private theorem leaf1677CoversExact : CoversExact 8
    leaf1677Box leaf1677Certificate leaf1677InnerLog leaf1677Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi148RoundedFacts
    innerPair16RoundedFacts leaf1677RoundedFacts (by rfl)

private theorem leaf1677FlatSound : Sound leaf1677Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1677CertificateValid
    leaf1677InnerLogValid leaf1677CoversExact leaf1677LowerChecked

private noncomputable def leaf1678Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1678Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871179/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134215355) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (683629559/536870912) }, upper := { exponent := 0, mantissa := (10565/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268433211/268430710) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf1678InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1678LocalValidity :
    LeafFacts leaf1678Box leaf1678Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1678Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134215355) }) = true
      norm_num [leaf1678Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1678CertificateValid :
    WideCertificateValid leaf1678Box leaf1678Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi127ValidityFacts
    leaf1678LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1678CoverageChecked :
    coverageCheck (innerAD leaf1678Box) leaf1678InnerLog = true := by
  rfl'

private theorem leaf1678InnerLogValid :
    leaf1678InnerLog.Valid 8 (innerAD leaf1678Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1678CoverageChecked

private noncomputable def leaf1678InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1678InputLogOnePlusV_eq :
    leaf1678InputLogOnePlusV = outerEnclosure 24
      (leaf1678Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1678RoundedFacts : LeafRoundedFacts 8
    leaf1678Certificate.logOnePlusV leaf1678InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1678InputLogOnePlusV_eq }

private noncomputable def leaf1678Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi127InputQChi innerPair16Input
    leaf1678InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1678LowerChecked :
    lowerCheck 24 leaf1678Box leaf1678Inputs = true := by
  rfl'

private theorem leaf1678CoversExact : CoversExact 8
    leaf1678Box leaf1678Certificate leaf1678InnerLog leaf1678Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi127RoundedFacts
    innerPair16RoundedFacts leaf1678RoundedFacts (by rfl)

private theorem leaf1678FlatSound : Sound leaf1678Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1678CertificateValid
    leaf1678InnerLogValid leaf1678CoversExact leaf1678LowerChecked

private noncomputable def leaf1679Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1679Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871181/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107667) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (684940197/536870912) }, upper := { exponent := 0, mantissa := (5293/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216595/134215334) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf1679InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1679LocalValidity :
    LeafFacts leaf1679Box leaf1679Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1679Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107667) }) = true
      norm_num [leaf1679Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1679CertificateValid :
    WideCertificateValid leaf1679Box leaf1679Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi127ValidityFacts
    leaf1679LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1679CoverageChecked :
    coverageCheck (innerAD leaf1679Box) leaf1679InnerLog = true := by
  rfl'

private theorem leaf1679InnerLogValid :
    leaf1679InnerLog.Valid 8 (innerAD leaf1679Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1679CoverageChecked

private noncomputable def leaf1679InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814619/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1679InputLogOnePlusV_eq :
    leaf1679InputLogOnePlusV = outerEnclosure 24
      (leaf1679Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1679RoundedFacts : LeafRoundedFacts 8
    leaf1679Certificate.logOnePlusV leaf1679InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1679InputLogOnePlusV_eq }

private noncomputable def leaf1679Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi127InputQChi innerPair16Input
    leaf1679InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1679LowerChecked :
    lowerCheck 24 leaf1679Box leaf1679Inputs = true := by
  rfl'

private theorem leaf1679CoversExact : CoversExact 8
    leaf1679Box leaf1679Certificate leaf1679InnerLog leaf1679Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi127RoundedFacts
    innerPair16RoundedFacts leaf1679RoundedFacts (by rfl)

private theorem leaf1679FlatSound : Sound leaf1679Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1679CertificateValid
    leaf1679InnerLogValid leaf1679CoversExact leaf1679LowerChecked

private noncomputable def leaf1680Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1680Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871181/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107621) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (690969141/536870912) }, upper := { exponent := 0, mantissa := (5339/4096) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216549/134215242) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf1680InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1680LocalValidity :
    LeafFacts leaf1680Box leaf1680Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1680Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107621) }) = true
      norm_num [leaf1680Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1680CertificateValid :
    WideCertificateValid leaf1680Box leaf1680Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi128ValidityFacts
    leaf1680LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1680CoverageChecked :
    coverageCheck (innerAD leaf1680Box) leaf1680InnerLog = true := by
  rfl'

private theorem leaf1680InnerLogValid :
    leaf1680InnerLog.Valid 8 (innerAD leaf1680Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1680CoverageChecked

private noncomputable def leaf1680InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1680InputLogOnePlusV_eq :
    leaf1680InputLogOnePlusV = outerEnclosure 24
      (leaf1680Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1680RoundedFacts : LeafRoundedFacts 8
    leaf1680Certificate.logOnePlusV leaf1680InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1680InputLogOnePlusV_eq }

private noncomputable def leaf1680Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi128InputQChi innerPair16Input
    leaf1680InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1680LowerChecked :
    lowerCheck 24 leaf1680Box leaf1680Inputs = true := by
  rfl'

private theorem leaf1680CoversExact : CoversExact 8
    leaf1680Box leaf1680Certificate leaf1680InnerLog leaf1680Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi128RoundedFacts
    innerPair16RoundedFacts leaf1680RoundedFacts (by rfl)

private theorem leaf1680FlatSound : Sound leaf1680Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1680CertificateValid
    leaf1680InnerLogValid leaf1680CoversExact leaf1680LowerChecked

private noncomputable def leaf1681Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1681Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871183/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553805) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (692345311/536870912) }, upper := { exponent := 0, mantissa := (2675/2048) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108269/67107610) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf1681InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1681LocalValidity :
    LeafFacts leaf1681Box leaf1681Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1681Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553805) }) = true
      norm_num [leaf1681Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1681CertificateValid :
    WideCertificateValid leaf1681Box leaf1681Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi128ValidityFacts
    leaf1681LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1681CoverageChecked :
    coverageCheck (innerAD leaf1681Box) leaf1681InnerLog = true := by
  rfl'

private theorem leaf1681InnerLogValid :
    leaf1681InnerLog.Valid 8 (innerAD leaf1681Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1681CoverageChecked

private noncomputable def leaf1681InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1681InputLogOnePlusV_eq :
    leaf1681InputLogOnePlusV = outerEnclosure 24
      (leaf1681Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1681RoundedFacts : LeafRoundedFacts 8
    leaf1681Certificate.logOnePlusV leaf1681InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1681InputLogOnePlusV_eq }

private noncomputable def leaf1681Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi128InputQChi innerPair16Input
    leaf1681InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1681LowerChecked :
    lowerCheck 24 leaf1681Box leaf1681Inputs = true := by
  rfl'

private theorem leaf1681CoversExact : CoversExact 8
    leaf1681Box leaf1681Certificate leaf1681InnerLog leaf1681Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi128RoundedFacts
    innerPair16RoundedFacts leaf1681RoundedFacts (by rfl)

private theorem leaf1681FlatSound : Sound leaf1681Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1681CertificateValid
    leaf1681InnerLogValid leaf1681CoversExact leaf1681LowerChecked

private noncomputable def leaf1682Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1682Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871183/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134215313) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (686250835/536870912) }, upper := { exponent := 0, mantissa := (10607/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268433169/268430626) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf1682InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1682LocalValidity :
    LeafFacts leaf1682Box leaf1682Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1682Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134215313) }) = true
      norm_num [leaf1682Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1682CertificateValid :
    WideCertificateValid leaf1682Box leaf1682Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi127ValidityFacts
    leaf1682LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1682CoverageChecked :
    coverageCheck (innerAD leaf1682Box) leaf1682InnerLog = true := by
  rfl'

private theorem leaf1682InnerLogValid :
    leaf1682InnerLog.Valid 8 (innerAD leaf1682Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1682CoverageChecked

private noncomputable def leaf1682InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1682InputLogOnePlusV_eq :
    leaf1682InputLogOnePlusV = outerEnclosure 24
      (leaf1682Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1682RoundedFacts : LeafRoundedFacts 8
    leaf1682Certificate.logOnePlusV leaf1682InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1682InputLogOnePlusV_eq }

private noncomputable def leaf1682Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi127InputQChi innerPair16Input
    leaf1682InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1682LowerChecked :
    lowerCheck 24 leaf1682Box leaf1682Inputs = true := by
  rfl'

private theorem leaf1682CoversExact : CoversExact 8
    leaf1682Box leaf1682Certificate leaf1682InnerLog leaf1682Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi127RoundedFacts
    innerPair16RoundedFacts leaf1682RoundedFacts (by rfl)

private theorem leaf1682FlatSound : Sound leaf1682Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1682CertificateValid
    leaf1682InnerLogValid leaf1682CoversExact leaf1682LowerChecked

private noncomputable def leaf1683Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1683Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553823) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (687561473/536870912) }, upper := { exponent := 0, mantissa := (2657/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108287/67107646) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf1683InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1683LocalValidity :
    LeafFacts leaf1683Box leaf1683Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1683Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553823) }) = true
      norm_num [leaf1683Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1683CertificateValid :
    WideCertificateValid leaf1683Box leaf1683Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi127ValidityFacts
    leaf1683LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1683CoverageChecked :
    coverageCheck (innerAD leaf1683Box) leaf1683InnerLog = true := by
  rfl'

private theorem leaf1683InnerLogValid :
    leaf1683InnerLog.Valid 8 (innerAD leaf1683Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1683CoverageChecked

private noncomputable def leaf1683InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1683InputLogOnePlusV_eq :
    leaf1683InputLogOnePlusV = outerEnclosure 24
      (leaf1683Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1683RoundedFacts : LeafRoundedFacts 8
    leaf1683Certificate.logOnePlusV leaf1683InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1683InputLogOnePlusV_eq }

private noncomputable def leaf1683Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi127InputQChi innerPair16Input
    leaf1683InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1683LowerChecked :
    lowerCheck 24 leaf1683Box leaf1683Inputs = true := by
  rfl'

private theorem leaf1683CoversExact : CoversExact 8
    leaf1683Box leaf1683Certificate leaf1683InnerLog leaf1683Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi127RoundedFacts
    innerPair16RoundedFacts leaf1683RoundedFacts (by rfl)

private theorem leaf1683FlatSound : Sound leaf1683Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1683CertificateValid
    leaf1683InnerLogValid leaf1683CoversExact leaf1683LowerChecked

private noncomputable def leaf1684Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1684Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107599) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (693721481/536870912) }, upper := { exponent := 0, mantissa := (5361/4096) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216527/134215198) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf1684InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1684LocalValidity :
    LeafFacts leaf1684Box leaf1684Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1684Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107599) }) = true
      norm_num [leaf1684Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1684CertificateValid :
    WideCertificateValid leaf1684Box leaf1684Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi128ValidityFacts
    leaf1684LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1684CoverageChecked :
    coverageCheck (innerAD leaf1684Box) leaf1684InnerLog = true := by
  rfl'

private theorem leaf1684InnerLogValid :
    leaf1684InnerLog.Valid 8 (innerAD leaf1684Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1684CoverageChecked

private noncomputable def leaf1684InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1684InputLogOnePlusV_eq :
    leaf1684InputLogOnePlusV = outerEnclosure 24
      (leaf1684Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1684RoundedFacts : LeafRoundedFacts 8
    leaf1684Certificate.logOnePlusV leaf1684InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1684InputLogOnePlusV_eq }

private noncomputable def leaf1684Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi128InputQChi innerPair16Input
    leaf1684InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1684LowerChecked :
    lowerCheck 24 leaf1684Box leaf1684Inputs = true := by
  rfl'

private theorem leaf1684CoversExact : CoversExact 8
    leaf1684Box leaf1684Certificate leaf1684InnerLog leaf1684Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi128RoundedFacts
    innerPair16RoundedFacts leaf1684RoundedFacts (by rfl)

private theorem leaf1684FlatSound : Sound leaf1684Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1684CertificateValid
    leaf1684InnerLogValid leaf1684CoversExact leaf1684LowerChecked

private noncomputable def leaf1685Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1685Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776897) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (695097651/536870912) }, upper := { exponent := 0, mantissa := (1343/1024) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554129/33553794) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf1685InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1685LocalValidity :
    LeafFacts leaf1685Box leaf1685Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1685Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776897) }) = true
      norm_num [leaf1685Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1685CertificateValid :
    WideCertificateValid leaf1685Box leaf1685Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi128ValidityFacts
    leaf1685LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1685CoverageChecked :
    coverageCheck (innerAD leaf1685Box) leaf1685InnerLog = true := by
  rfl'

private theorem leaf1685InnerLogValid :
    leaf1685InnerLog.Valid 8 (innerAD leaf1685Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1685CoverageChecked

private noncomputable def leaf1685InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf1685InputLogOnePlusV_eq :
    leaf1685InputLogOnePlusV = outerEnclosure 24
      (leaf1685Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1685RoundedFacts : LeafRoundedFacts 8
    leaf1685Certificate.logOnePlusV leaf1685InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1685InputLogOnePlusV_eq }

private noncomputable def leaf1685Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi128InputQChi innerPair16Input
    leaf1685InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1685LowerChecked :
    lowerCheck 24 leaf1685Box leaf1685Inputs = true := by
  rfl'

private theorem leaf1685CoversExact : CoversExact 8
    leaf1685Box leaf1685Certificate leaf1685InnerLog leaf1685Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi128RoundedFacts
    innerPair16RoundedFacts leaf1685RoundedFacts (by rfl)

private theorem leaf1685FlatSound : Sound leaf1685Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1685CertificateValid
    leaf1685InnerLogValid leaf1685CoversExact leaf1685LowerChecked

private noncomputable def leaf1686Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1686Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871183/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134215129) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (698308723/536870912) }, upper := { exponent := 0, mantissa := (10791/8192) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432985/268430258) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf1686InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1686LocalValidity :
    LeafFacts leaf1686Box leaf1686Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1686Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134215129) }) = true
      norm_num [leaf1686Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1686CertificateValid :
    WideCertificateValid leaf1686Box leaf1686Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi129ValidityFacts
    leaf1686LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1686CoverageChecked :
    coverageCheck (innerAD leaf1686Box) leaf1686InnerLog = true := by
  rfl'

private theorem leaf1686InnerLogValid :
    leaf1686InnerLog.Valid 8 (innerAD leaf1686Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1686CoverageChecked

private noncomputable def leaf1686InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1686InputLogOnePlusV_eq :
    leaf1686InputLogOnePlusV = outerEnclosure 24
      (leaf1686Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1686RoundedFacts : LeafRoundedFacts 8
    leaf1686Certificate.logOnePlusV leaf1686InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1686InputLogOnePlusV_eq }

private noncomputable def leaf1686Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi129InputQChi innerPair17Input
    leaf1686InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1686LowerChecked :
    lowerCheck 24 leaf1686Box leaf1686Inputs = true := by
  rfl'

private theorem leaf1686CoversExact : CoversExact 8
    leaf1686Box leaf1686Certificate leaf1686InnerLog leaf1686Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi129RoundedFacts
    innerPair17RoundedFacts leaf1686RoundedFacts (by rfl)

private theorem leaf1686FlatSound : Sound leaf1686Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1686CertificateValid
    leaf1686InnerLogValid leaf1686CoversExact leaf1686LowerChecked

private noncomputable def leaf1687Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1687Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107553) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (699750425/536870912) }, upper := { exponent := 0, mantissa := (5407/4096) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216481/134215106) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf1687InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1687LocalValidity :
    LeafFacts leaf1687Box leaf1687Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1687Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107553) }) = true
      norm_num [leaf1687Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1687CertificateValid :
    WideCertificateValid leaf1687Box leaf1687Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi129ValidityFacts
    leaf1687LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1687CoverageChecked :
    coverageCheck (innerAD leaf1687Box) leaf1687InnerLog = true := by
  rfl'

private theorem leaf1687InnerLogValid :
    leaf1687InnerLog.Valid 8 (innerAD leaf1687Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1687CoverageChecked

private noncomputable def leaf1687InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1687InputLogOnePlusV_eq :
    leaf1687InputLogOnePlusV = outerEnclosure 24
      (leaf1687Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1687RoundedFacts : LeafRoundedFacts 8
    leaf1687Certificate.logOnePlusV leaf1687InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1687InputLogOnePlusV_eq }

private noncomputable def leaf1687Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi129InputQChi innerPair17Input
    leaf1687InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1687LowerChecked :
    lowerCheck 24 leaf1687Box leaf1687Inputs = true := by
  rfl'

private theorem leaf1687CoversExact : CoversExact 8
    leaf1687Box leaf1687Certificate leaf1687InnerLog leaf1687Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi129RoundedFacts
    innerPair17RoundedFacts leaf1687RoundedFacts (by rfl)

private theorem leaf1687FlatSound : Sound leaf1687Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1687CertificateValid
    leaf1687InnerLogValid leaf1687CoversExact leaf1687LowerChecked

private noncomputable def leaf1688Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1688Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776877) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (705648305/536870912) }, upper := { exponent := 0, mantissa := (1363/1024) } }, logOuter := sk167LogOuterCertificate, logK := sk167LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554109/33553754) } }, logDArg := sk167LogDArgCertificate }

private noncomputable def leaf1688InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1688LocalValidity :
    LeafFacts leaf1688Box leaf1688Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1688Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776877) }) = true
      norm_num [leaf1688Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1688CertificateValid :
    WideCertificateValid leaf1688Box leaf1688Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk167ValidityFacts chi130ValidityFacts
    leaf1688LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1688CoverageChecked :
    coverageCheck (innerAD leaf1688Box) leaf1688InnerLog = true := by
  rfl'

private theorem leaf1688InnerLogValid :
    leaf1688InnerLog.Valid 8 (innerAD leaf1688Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1688CoverageChecked

private noncomputable def leaf1688InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1688InputLogOnePlusV_eq :
    leaf1688InputLogOnePlusV = outerEnclosure 24
      (leaf1688Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1688RoundedFacts : LeafRoundedFacts 8
    leaf1688Certificate.logOnePlusV leaf1688InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1688InputLogOnePlusV_eq }

private noncomputable def leaf1688Inputs : Inputs :=
  inputsOfCaches globalInput sk167RoundedInputs
    chi130InputQChi innerPair21Input
    leaf1688InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1688LowerChecked :
    lowerCheck 24 leaf1688Box leaf1688Inputs = true := by
  rfl'

private theorem leaf1688CoversExact : CoversExact 8
    leaf1688Box leaf1688Certificate leaf1688InnerLog leaf1688Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk167RoundedFacts chi130RoundedFacts
    innerPair21RoundedFacts leaf1688RoundedFacts (by rfl)

private theorem leaf1688FlatSound : Sound leaf1688Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1688CertificateValid
    leaf1688InnerLogValid leaf1688CoversExact leaf1688LowerChecked

private noncomputable def leaf1689Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1689Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388437) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (707155539/536870912) }, upper := { exponent := 0, mantissa := (683/512) } }, logOuter := sk168LogOuterCertificate, logK := sk168LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777053/16776874) } }, logDArg := sk168LogDArgCertificate }

private noncomputable def leaf1689InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1689LocalValidity :
    LeafFacts leaf1689Box leaf1689Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1689Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388437) }) = true
      norm_num [leaf1689Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1689CertificateValid :
    WideCertificateValid leaf1689Box leaf1689Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk168ValidityFacts chi130ValidityFacts
    leaf1689LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1689CoverageChecked :
    coverageCheck (innerAD leaf1689Box) leaf1689InnerLog = true := by
  rfl'

private theorem leaf1689InnerLogValid :
    leaf1689InnerLog.Valid 8 (innerAD leaf1689Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1689CoverageChecked

private noncomputable def leaf1689InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907315/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1689InputLogOnePlusV_eq :
    leaf1689InputLogOnePlusV = outerEnclosure 24
      (leaf1689Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1689RoundedFacts : LeafRoundedFacts 8
    leaf1689Certificate.logOnePlusV leaf1689InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1689InputLogOnePlusV_eq }

private noncomputable def leaf1689Inputs : Inputs :=
  inputsOfCaches globalInput sk168RoundedInputs
    chi130InputQChi innerPair21Input
    leaf1689InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1689LowerChecked :
    lowerCheck 24 leaf1689Box leaf1689Inputs = true := by
  rfl'

private theorem leaf1689CoversExact : CoversExact 8
    leaf1689Box leaf1689Certificate leaf1689InnerLog leaf1689Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk168RoundedFacts chi130RoundedFacts
    innerPair21RoundedFacts leaf1689RoundedFacts (by rfl)

private theorem leaf1689FlatSound : Sound leaf1689Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1689CertificateValid
    leaf1689InnerLogValid leaf1689CoversExact leaf1689LowerChecked

private noncomputable def leaf1690Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1690Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134215083) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (701192127/536870912) }, upper := { exponent := 0, mantissa := (10837/8192) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432939/268430166) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf1690InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1690LocalValidity :
    LeafFacts leaf1690Box leaf1690Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1690Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134215083) }) = true
      norm_num [leaf1690Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1690CertificateValid :
    WideCertificateValid leaf1690Box leaf1690Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi129ValidityFacts
    leaf1690LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1690CoverageChecked :
    coverageCheck (innerAD leaf1690Box) leaf1690InnerLog = true := by
  rfl'

private theorem leaf1690InnerLogValid :
    leaf1690InnerLog.Valid 8 (innerAD leaf1690Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1690CoverageChecked

private noncomputable def leaf1690InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1690InputLogOnePlusV_eq :
    leaf1690InputLogOnePlusV = outerEnclosure 24
      (leaf1690Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1690RoundedFacts : LeafRoundedFacts 8
    leaf1690Certificate.logOnePlusV leaf1690InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1690InputLogOnePlusV_eq }

private noncomputable def leaf1690Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi129InputQChi innerPair17Input
    leaf1690InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1690LowerChecked :
    lowerCheck 24 leaf1690Box leaf1690Inputs = true := by
  rfl'

private theorem leaf1690CoversExact : CoversExact 8
    leaf1690Box leaf1690Certificate leaf1690InnerLog leaf1690Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi129RoundedFacts
    innerPair17RoundedFacts leaf1690RoundedFacts (by rfl)

private theorem leaf1690FlatSound : Sound leaf1690Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1690CertificateValid
    leaf1690InnerLogValid leaf1690CoversExact leaf1690LowerChecked

private noncomputable def leaf1691Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1691Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553765) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (702633829/536870912) }, upper := { exponent := 0, mantissa := (2715/2048) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108229/67107530) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf1691InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1691LocalValidity :
    LeafFacts leaf1691Box leaf1691Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1691Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553765) }) = true
      norm_num [leaf1691Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1691CertificateValid :
    WideCertificateValid leaf1691Box leaf1691Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi129ValidityFacts
    leaf1691LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1691CoverageChecked :
    coverageCheck (innerAD leaf1691Box) leaf1691InnerLog = true := by
  rfl'

private theorem leaf1691InnerLogValid :
    leaf1691InnerLog.Valid 8 (innerAD leaf1691Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1691CoverageChecked

private noncomputable def leaf1691InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1691InputLogOnePlusV_eq :
    leaf1691InputLogOnePlusV = outerEnclosure 24
      (leaf1691Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1691RoundedFacts : LeafRoundedFacts 8
    leaf1691Certificate.logOnePlusV leaf1691InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1691InputLogOnePlusV_eq }

private noncomputable def leaf1691Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi129InputQChi innerPair17Input
    leaf1691InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1691LowerChecked :
    lowerCheck 24 leaf1691Box leaf1691Inputs = true := by
  rfl'

private theorem leaf1691CoversExact : CoversExact 8
    leaf1691Box leaf1691Certificate leaf1691InnerLog leaf1691Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi129RoundedFacts
    innerPair17RoundedFacts leaf1691RoundedFacts (by rfl)

private theorem leaf1691FlatSound : Sound leaf1691Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1691CertificateValid
    leaf1691InnerLogValid leaf1691CoversExact leaf1691LowerChecked

private noncomputable def leaf1692Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1692Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776871) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (708662773/536870912) }, upper := { exponent := 0, mantissa := (1369/1024) } }, logOuter := sk161LogOuterCertificate, logK := sk161LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554103/33553742) } }, logDArg := sk161LogDArgCertificate }

private noncomputable def leaf1692InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1692LocalValidity :
    LeafFacts leaf1692Box leaf1692Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1692Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776871) }) = true
      norm_num [leaf1692Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1692CertificateValid :
    WideCertificateValid leaf1692Box leaf1692Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk161ValidityFacts chi130ValidityFacts
    leaf1692LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1692CoverageChecked :
    coverageCheck (innerAD leaf1692Box) leaf1692InnerLog = true := by
  rfl'

private theorem leaf1692InnerLogValid :
    leaf1692InnerLog.Valid 8 (innerAD leaf1692Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1692CoverageChecked

private noncomputable def leaf1692InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1692InputLogOnePlusV_eq :
    leaf1692InputLogOnePlusV = outerEnclosure 24
      (leaf1692Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1692RoundedFacts : LeafRoundedFacts 8
    leaf1692Certificate.logOnePlusV leaf1692InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1692InputLogOnePlusV_eq }

private noncomputable def leaf1692Inputs : Inputs :=
  inputsOfCaches globalInput sk161RoundedInputs
    chi130InputQChi innerPair21Input
    leaf1692InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1692LowerChecked :
    lowerCheck 24 leaf1692Box leaf1692Inputs = true := by
  rfl'

private theorem leaf1692CoversExact : CoversExact 8
    leaf1692Box leaf1692Certificate leaf1692InnerLog leaf1692Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk161RoundedFacts chi130RoundedFacts
    innerPair21RoundedFacts leaf1692RoundedFacts (by rfl)

private theorem leaf1692FlatSound : Sound leaf1692Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1692CertificateValid
    leaf1692InnerLogValid leaf1692CoversExact leaf1692LowerChecked

private noncomputable def leaf1693Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1693Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (8191/8192), upper := (4194308/4194217) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (710170007/536870912) }, upper := { exponent := 0, mantissa := (343/256) } }, logOuter := sk162LogOuterCertificate, logK := sk162LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388525/8388434) } }, logDArg := sk162LogDArgCertificate }

private noncomputable def leaf1693InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1693LocalValidity :
    LeafFacts leaf1693Box leaf1693Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1693Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194308/4194217) }) = true
      norm_num [leaf1693Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1693CertificateValid :
    WideCertificateValid leaf1693Box leaf1693Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk162ValidityFacts chi130ValidityFacts
    leaf1693LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1693CoverageChecked :
    coverageCheck (innerAD leaf1693Box) leaf1693InnerLog = true := by
  rfl'

private theorem leaf1693InnerLogValid :
    leaf1693InnerLog.Valid 8 (innerAD leaf1693Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1693CoverageChecked

private noncomputable def leaf1693InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1693InputLogOnePlusV_eq :
    leaf1693InputLogOnePlusV = outerEnclosure 24
      (leaf1693Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1693RoundedFacts : LeafRoundedFacts 8
    leaf1693Certificate.logOnePlusV leaf1693InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1693InputLogOnePlusV_eq }

private noncomputable def leaf1693Inputs : Inputs :=
  inputsOfCaches globalInput sk162RoundedInputs
    chi130InputQChi innerPair21Input
    leaf1693InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1693LowerChecked :
    lowerCheck 24 leaf1693Box leaf1693Inputs = true := by
  rfl'

private theorem leaf1693CoversExact : CoversExact 8
    leaf1693Box leaf1693Certificate leaf1693InnerLog leaf1693Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk162RoundedFacts chi130RoundedFacts
    innerPair21RoundedFacts leaf1693RoundedFacts (by rfl)

private theorem leaf1693FlatSound : Sound leaf1693Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1693CertificateValid
    leaf1693InnerLogValid leaf1693CoversExact leaf1693LowerChecked

private noncomputable def leaf1694Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1694Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134215271) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (688872111/536870912) }, upper := { exponent := 0, mantissa := (10649/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268433127/268430542) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf1694InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1694LocalValidity :
    LeafFacts leaf1694Box leaf1694Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1694Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134215271) }) = true
      norm_num [leaf1694Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1694CertificateValid :
    WideCertificateValid leaf1694Box leaf1694Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi127ValidityFacts
    leaf1694LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1694CoverageChecked :
    coverageCheck (innerAD leaf1694Box) leaf1694InnerLog = true := by
  rfl'

private theorem leaf1694InnerLogValid :
    leaf1694InnerLog.Valid 8 (innerAD leaf1694Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1694CoverageChecked

private noncomputable def leaf1694InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814621/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1694InputLogOnePlusV_eq :
    leaf1694InputLogOnePlusV = outerEnclosure 24
      (leaf1694Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1694RoundedFacts : LeafRoundedFacts 8
    leaf1694Certificate.logOnePlusV leaf1694InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1694InputLogOnePlusV_eq }

private noncomputable def leaf1694Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi127InputQChi innerPair16Input
    leaf1694InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1694LowerChecked :
    lowerCheck 24 leaf1694Box leaf1694Inputs = true := by
  rfl'

private theorem leaf1694CoversExact : CoversExact 8
    leaf1694Box leaf1694Certificate leaf1694InnerLog leaf1694Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi127RoundedFacts
    innerPair16RoundedFacts leaf1694RoundedFacts (by rfl)

private theorem leaf1694FlatSound : Sound leaf1694Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1694CertificateValid
    leaf1694InnerLogValid leaf1694CoversExact leaf1694LowerChecked

private noncomputable def leaf1695Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1695Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107625) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (690182749/536870912) }, upper := { exponent := 0, mantissa := (5335/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216553/134215250) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf1695InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1695LocalValidity :
    LeafFacts leaf1695Box leaf1695Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1695Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107625) }) = true
      norm_num [leaf1695Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1695CertificateValid :
    WideCertificateValid leaf1695Box leaf1695Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi127ValidityFacts
    leaf1695LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1695CoverageChecked :
    coverageCheck (innerAD leaf1695Box) leaf1695InnerLog = true := by
  rfl'

private theorem leaf1695InnerLogValid :
    leaf1695InnerLog.Valid 8 (innerAD leaf1695Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1695CoverageChecked

private noncomputable def leaf1695InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1695InputLogOnePlusV_eq :
    leaf1695InputLogOnePlusV = outerEnclosure 24
      (leaf1695Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1695RoundedFacts : LeafRoundedFacts 8
    leaf1695Certificate.logOnePlusV leaf1695InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1695InputLogOnePlusV_eq }

private noncomputable def leaf1695Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi127InputQChi innerPair16Input
    leaf1695InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1695LowerChecked :
    lowerCheck 24 leaf1695Box leaf1695Inputs = true := by
  rfl'

private theorem leaf1695CoversExact : CoversExact 8
    leaf1695Box leaf1695Certificate leaf1695InnerLog leaf1695Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi127RoundedFacts
    innerPair16RoundedFacts leaf1695RoundedFacts (by rfl)

private theorem leaf1695FlatSound : Sound leaf1695Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1695CertificateValid
    leaf1695InnerLogValid leaf1695CoversExact leaf1695LowerChecked

private noncomputable def leaf1696Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1696Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107577) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (696473821/536870912) }, upper := { exponent := 0, mantissa := (5383/4096) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216505/134215154) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf1696InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1696LocalValidity :
    LeafFacts leaf1696Box leaf1696Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1696Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107577) }) = true
      norm_num [leaf1696Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1696CertificateValid :
    WideCertificateValid leaf1696Box leaf1696Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi128ValidityFacts
    leaf1696LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1696CoverageChecked :
    coverageCheck (innerAD leaf1696Box) leaf1696InnerLog = true := by
  rfl'

private theorem leaf1696InnerLogValid :
    leaf1696InnerLog.Valid 8 (innerAD leaf1696Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1696CoverageChecked

private noncomputable def leaf1696InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1696InputLogOnePlusV_eq :
    leaf1696InputLogOnePlusV = outerEnclosure 24
      (leaf1696Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1696RoundedFacts : LeafRoundedFacts 8
    leaf1696Certificate.logOnePlusV leaf1696InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1696InputLogOnePlusV_eq }

private noncomputable def leaf1696Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi128InputQChi innerPair17Input
    leaf1696InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1696LowerChecked :
    lowerCheck 24 leaf1696Box leaf1696Inputs = true := by
  rfl'

private theorem leaf1696CoversExact : CoversExact 8
    leaf1696Box leaf1696Certificate leaf1696InnerLog leaf1696Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi128RoundedFacts
    innerPair17RoundedFacts leaf1696RoundedFacts (by rfl)

private theorem leaf1696FlatSound : Sound leaf1696Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1696CertificateValid
    leaf1696InnerLogValid leaf1696CoversExact leaf1696LowerChecked

private noncomputable def leaf1697Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1697Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (8191/8192), upper := (33554464/33553783) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (697849991/536870912) }, upper := { exponent := 0, mantissa := (2697/2048) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (67108247/67107566) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf1697InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1697LocalValidity :
    LeafFacts leaf1697Box leaf1697Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1697Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (33554464/33553783) }) = true
      norm_num [leaf1697Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1697CertificateValid :
    WideCertificateValid leaf1697Box leaf1697Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi128ValidityFacts
    leaf1697LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1697CoverageChecked :
    coverageCheck (innerAD leaf1697Box) leaf1697InnerLog = true := by
  rfl'

private theorem leaf1697InnerLogValid :
    leaf1697InnerLog.Valid 8 (innerAD leaf1697Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1697CoverageChecked

private noncomputable def leaf1697InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1697InputLogOnePlusV_eq :
    leaf1697InputLogOnePlusV = outerEnclosure 24
      (leaf1697Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1697RoundedFacts : LeafRoundedFacts 8
    leaf1697Certificate.logOnePlusV leaf1697InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1697InputLogOnePlusV_eq }

private noncomputable def leaf1697Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi128InputQChi innerPair17Input
    leaf1697InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1697LowerChecked :
    lowerCheck 24 leaf1697Box leaf1697Inputs = true := by
  rfl'

private theorem leaf1697CoversExact : CoversExact 8
    leaf1697Box leaf1697Certificate leaf1697InnerLog leaf1697Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi128RoundedFacts
    innerPair17RoundedFacts leaf1697RoundedFacts (by rfl)

private theorem leaf1697FlatSound : Sound leaf1697Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1697CertificateValid
    leaf1697InnerLogValid leaf1697CoversExact leaf1697LowerChecked

private noncomputable def leaf1698Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1698Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134215229) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (691493387/536870912) }, upper := { exponent := 0, mantissa := (10691/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268433085/268430458) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf1698InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1698LocalValidity :
    LeafFacts leaf1698Box leaf1698Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1698Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134215229) }) = true
      norm_num [leaf1698Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1698CertificateValid :
    WideCertificateValid leaf1698Box leaf1698Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi127ValidityFacts
    leaf1698LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1698CoverageChecked :
    coverageCheck (innerAD leaf1698Box) leaf1698InnerLog = true := by
  rfl'

private theorem leaf1698InnerLogValid :
    leaf1698InnerLog.Valid 8 (innerAD leaf1698Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1698CoverageChecked

private noncomputable def leaf1698InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1698InputLogOnePlusV_eq :
    leaf1698InputLogOnePlusV = outerEnclosure 24
      (leaf1698Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1698RoundedFacts : LeafRoundedFacts 8
    leaf1698Certificate.logOnePlusV leaf1698InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1698InputLogOnePlusV_eq }

private noncomputable def leaf1698Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi127InputQChi innerPair16Input
    leaf1698InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1698LowerChecked :
    lowerCheck 24 leaf1698Box leaf1698Inputs = true := by
  rfl'

private theorem leaf1698CoversExact : CoversExact 8
    leaf1698Box leaf1698Certificate leaf1698InnerLog leaf1698Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi127RoundedFacts
    innerPair16RoundedFacts leaf1698RoundedFacts (by rfl)

private theorem leaf1698FlatSound : Sound leaf1698Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1698CertificateValid
    leaf1698InnerLogValid leaf1698CoversExact leaf1698LowerChecked

private noncomputable def leaf1699Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1699Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776901) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (692804025/536870912) }, upper := { exponent := 0, mantissa := (1339/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554133/33553802) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf1699InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1699LocalValidity :
    LeafFacts leaf1699Box leaf1699Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1699Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776901) }) = true
      norm_num [leaf1699Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1699CertificateValid :
    WideCertificateValid leaf1699Box leaf1699Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi127ValidityFacts
    leaf1699LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1699CoverageChecked :
    coverageCheck (innerAD leaf1699Box) leaf1699InnerLog = true := by
  rfl'

private theorem leaf1699InnerLogValid :
    leaf1699InnerLog.Valid 8 (innerAD leaf1699Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1699CoverageChecked

private noncomputable def leaf1699InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814623/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1699InputLogOnePlusV_eq :
    leaf1699InputLogOnePlusV = outerEnclosure 24
      (leaf1699Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1699RoundedFacts : LeafRoundedFacts 8
    leaf1699Certificate.logOnePlusV leaf1699InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1699InputLogOnePlusV_eq }

private noncomputable def leaf1699Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi127InputQChi innerPair16Input
    leaf1699InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1699LowerChecked :
    lowerCheck 24 leaf1699Box leaf1699Inputs = true := by
  rfl'

private theorem leaf1699CoversExact : CoversExact 8
    leaf1699Box leaf1699Certificate leaf1699InnerLog leaf1699Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi127RoundedFacts
    innerPair16RoundedFacts leaf1699RoundedFacts (by rfl)

private theorem leaf1699FlatSound : Sound leaf1699Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1699CertificateValid
    leaf1699InnerLogValid leaf1699CoversExact leaf1699LowerChecked

private noncomputable def leaf1700Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1700Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107555) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (699226161/536870912) }, upper := { exponent := 0, mantissa := (5405/4096) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216483/134215110) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf1700InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1700LocalValidity :
    LeafFacts leaf1700Box leaf1700Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1700Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107555) }) = true
      norm_num [leaf1700Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1700CertificateValid :
    WideCertificateValid leaf1700Box leaf1700Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi128ValidityFacts
    leaf1700LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1700CoverageChecked :
    coverageCheck (innerAD leaf1700Box) leaf1700InnerLog = true := by
  rfl'

private theorem leaf1700InnerLogValid :
    leaf1700InnerLog.Valid 8 (innerAD leaf1700Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1700CoverageChecked

private noncomputable def leaf1700InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907313/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1700InputLogOnePlusV_eq :
    leaf1700InputLogOnePlusV = outerEnclosure 24
      (leaf1700Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1700RoundedFacts : LeafRoundedFacts 8
    leaf1700Certificate.logOnePlusV leaf1700InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1700InputLogOnePlusV_eq }

private noncomputable def leaf1700Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi128InputQChi innerPair17Input
    leaf1700InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1700LowerChecked :
    lowerCheck 24 leaf1700Box leaf1700Inputs = true := by
  rfl'

private theorem leaf1700CoversExact : CoversExact 8
    leaf1700Box leaf1700Certificate leaf1700InnerLog leaf1700Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi128RoundedFacts
    innerPair17RoundedFacts leaf1700RoundedFacts (by rfl)

private theorem leaf1700FlatSound : Sound leaf1700Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1700CertificateValid
    leaf1700InnerLogValid leaf1700CoversExact leaf1700LowerChecked

private noncomputable def leaf1701Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1701Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388443) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (700602331/536870912) }, upper := { exponent := 0, mantissa := (677/512) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777059/16776886) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf1701InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1701LocalValidity :
    LeafFacts leaf1701Box leaf1701Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1701Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388443) }) = true
      norm_num [leaf1701Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1701CertificateValid :
    WideCertificateValid leaf1701Box leaf1701Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi128ValidityFacts
    leaf1701LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1701CoverageChecked :
    coverageCheck (innerAD leaf1701Box) leaf1701InnerLog = true := by
  rfl'

private theorem leaf1701InnerLogValid :
    leaf1701InnerLog.Valid 8 (innerAD leaf1701Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1701CoverageChecked

private noncomputable def leaf1701InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1701InputLogOnePlusV_eq :
    leaf1701InputLogOnePlusV = outerEnclosure 24
      (leaf1701Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1701RoundedFacts : LeafRoundedFacts 8
    leaf1701Certificate.logOnePlusV leaf1701InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1701InputLogOnePlusV_eq }

private noncomputable def leaf1701Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi128InputQChi innerPair17Input
    leaf1701InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1701LowerChecked :
    lowerCheck 24 leaf1701Box leaf1701Inputs = true := by
  rfl'

private theorem leaf1701CoversExact : CoversExact 8
    leaf1701Box leaf1701Certificate leaf1701InnerLog leaf1701Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi128RoundedFacts
    innerPair17RoundedFacts leaf1701RoundedFacts (by rfl)

private theorem leaf1701FlatSound : Sound leaf1701Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1701CertificateValid
    leaf1701InnerLogValid leaf1701CoversExact leaf1701LowerChecked

private noncomputable def leaf1702Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1702Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134215037) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (704075531/536870912) }, upper := { exponent := 0, mantissa := (10883/8192) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432893/268430074) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf1702InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1702LocalValidity :
    LeafFacts leaf1702Box leaf1702Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1702Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134215037) }) = true
      norm_num [leaf1702Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1702CertificateValid :
    WideCertificateValid leaf1702Box leaf1702Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi129ValidityFacts
    leaf1702LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1702CoverageChecked :
    coverageCheck (innerAD leaf1702Box) leaf1702InnerLog = true := by
  rfl'

private theorem leaf1702InnerLogValid :
    leaf1702InnerLog.Valid 8 (innerAD leaf1702Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1702CoverageChecked

private noncomputable def leaf1702InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1702InputLogOnePlusV_eq :
    leaf1702InputLogOnePlusV = outerEnclosure 24
      (leaf1702Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1702RoundedFacts : LeafRoundedFacts 8
    leaf1702Certificate.logOnePlusV leaf1702InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1702InputLogOnePlusV_eq }

private noncomputable def leaf1702Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi129InputQChi innerPair17Input
    leaf1702InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1702LowerChecked :
    lowerCheck 24 leaf1702Box leaf1702Inputs = true := by
  rfl'

private theorem leaf1702CoversExact : CoversExact 8
    leaf1702Box leaf1702Certificate leaf1702InnerLog leaf1702Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi129RoundedFacts
    innerPair17RoundedFacts leaf1702RoundedFacts (by rfl)

private theorem leaf1702FlatSound : Sound leaf1702Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1702CertificateValid
    leaf1702InnerLogValid leaf1702CoversExact leaf1702LowerChecked

private noncomputable def leaf1703Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1703Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (8191/8192), upper := (67108928/67107507) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (705517233/536870912) }, upper := { exponent := 0, mantissa := (5453/4096) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (134216435/134215014) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf1703InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1703LocalValidity :
    LeafFacts leaf1703Box leaf1703Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1703Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (67108928/67107507) }) = true
      norm_num [leaf1703Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1703CertificateValid :
    WideCertificateValid leaf1703Box leaf1703Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi129ValidityFacts
    leaf1703LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1703CoverageChecked :
    coverageCheck (innerAD leaf1703Box) leaf1703InnerLog = true := by
  rfl'

private theorem leaf1703InnerLogValid :
    leaf1703InnerLog.Valid 8 (innerAD leaf1703Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1703CoverageChecked

private noncomputable def leaf1703InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1703InputLogOnePlusV_eq :
    leaf1703InputLogOnePlusV = outerEnclosure 24
      (leaf1703Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1703RoundedFacts : LeafRoundedFacts 8
    leaf1703Certificate.logOnePlusV leaf1703InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1703InputLogOnePlusV_eq }

private noncomputable def leaf1703Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi129InputQChi innerPair21Input
    leaf1703InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1703LowerChecked :
    lowerCheck 24 leaf1703Box leaf1703Inputs = true := by
  rfl'

private theorem leaf1703CoversExact : CoversExact 8
    leaf1703Box leaf1703Certificate leaf1703InnerLog leaf1703Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi129RoundedFacts
    innerPair21RoundedFacts leaf1703RoundedFacts (by rfl)

private theorem leaf1703FlatSound : Sound leaf1703Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1703CertificateValid
    leaf1703InnerLogValid leaf1703CoversExact leaf1703LowerChecked

private noncomputable def leaf1704Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1704Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776865) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (711677241/536870912) }, upper := { exponent := 0, mantissa := (1375/1024) } }, logOuter := sk163LogOuterCertificate, logK := sk163LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554097/33553730) } }, logDArg := sk163LogDArgCertificate }

private noncomputable def leaf1704InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1704LocalValidity :
    LeafFacts leaf1704Box leaf1704Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1704Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776865) }) = true
      norm_num [leaf1704Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1704CertificateValid :
    WideCertificateValid leaf1704Box leaf1704Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk163ValidityFacts chi130ValidityFacts
    leaf1704LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1704CoverageChecked :
    coverageCheck (innerAD leaf1704Box) leaf1704InnerLog = true := by
  rfl'

private theorem leaf1704InnerLogValid :
    leaf1704InnerLog.Valid 8 (innerAD leaf1704Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1704CoverageChecked

private noncomputable def leaf1704InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726829/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1704InputLogOnePlusV_eq :
    leaf1704InputLogOnePlusV = outerEnclosure 24
      (leaf1704Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1704RoundedFacts : LeafRoundedFacts 8
    leaf1704Certificate.logOnePlusV leaf1704InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1704InputLogOnePlusV_eq }

private noncomputable def leaf1704Inputs : Inputs :=
  inputsOfCaches globalInput sk163RoundedInputs
    chi130InputQChi innerPair21Input
    leaf1704InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1704LowerChecked :
    lowerCheck 24 leaf1704Box leaf1704Inputs = true := by
  rfl'

private theorem leaf1704CoversExact : CoversExact 8
    leaf1704Box leaf1704Certificate leaf1704InnerLog leaf1704Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk163RoundedFacts chi130RoundedFacts
    innerPair21RoundedFacts leaf1704RoundedFacts (by rfl)

private theorem leaf1704FlatSound : Sound leaf1704Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1704CertificateValid
    leaf1704InnerLogValid leaf1704CoversExact leaf1704LowerChecked

private noncomputable def leaf1705Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1705Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388431) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (713184475/536870912) }, upper := { exponent := 0, mantissa := (689/512) } }, logOuter := sk164LogOuterCertificate, logK := sk164LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777047/16776862) } }, logDArg := sk164LogDArgCertificate }

private noncomputable def leaf1705InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1705LocalValidity :
    LeafFacts leaf1705Box leaf1705Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1705Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388431) }) = true
      norm_num [leaf1705Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1705CertificateValid :
    WideCertificateValid leaf1705Box leaf1705Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk164ValidityFacts chi130ValidityFacts
    leaf1705LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1705CoverageChecked :
    coverageCheck (innerAD leaf1705Box) leaf1705InnerLog = true := by
  rfl'

private theorem leaf1705InnerLogValid :
    leaf1705InnerLog.Valid 8 (innerAD leaf1705Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1705CoverageChecked

private noncomputable def leaf1705InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814633/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1705InputLogOnePlusV_eq :
    leaf1705InputLogOnePlusV = outerEnclosure 24
      (leaf1705Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1705RoundedFacts : LeafRoundedFacts 8
    leaf1705Certificate.logOnePlusV leaf1705InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1705InputLogOnePlusV_eq }

private noncomputable def leaf1705Inputs : Inputs :=
  inputsOfCaches globalInput sk164RoundedInputs
    chi130InputQChi innerPair21Input
    leaf1705InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1705LowerChecked :
    lowerCheck 24 leaf1705Box leaf1705Inputs = true := by
  rfl'

private theorem leaf1705CoversExact : CoversExact 8
    leaf1705Box leaf1705Certificate leaf1705InnerLog leaf1705Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk164RoundedFacts chi130RoundedFacts
    innerPair21RoundedFacts leaf1705RoundedFacts (by rfl)

private theorem leaf1705FlatSound : Sound leaf1705Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1705CertificateValid
    leaf1705InnerLogValid leaf1705CoversExact leaf1705LowerChecked

private noncomputable def leaf1706Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1706Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (8191/8192), upper := (134217856/134214991) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (706958935/536870912) }, upper := { exponent := 0, mantissa := (10929/8192) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (268432847/268429982) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf1706InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1706LocalValidity :
    LeafFacts leaf1706Box leaf1706Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1706Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (134217856/134214991) }) = true
      norm_num [leaf1706Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1706CertificateValid :
    WideCertificateValid leaf1706Box leaf1706Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi129ValidityFacts
    leaf1706LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1706CoverageChecked :
    coverageCheck (innerAD leaf1706Box) leaf1706InnerLog = true := by
  rfl'

private theorem leaf1706InnerLogValid :
    leaf1706InnerLog.Valid 8 (innerAD leaf1706Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1706CoverageChecked

private noncomputable def leaf1706InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907315/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1706InputLogOnePlusV_eq :
    leaf1706InputLogOnePlusV = outerEnclosure 24
      (leaf1706Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1706RoundedFacts : LeafRoundedFacts 8
    leaf1706Certificate.logOnePlusV leaf1706InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1706InputLogOnePlusV_eq }

private noncomputable def leaf1706Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi129InputQChi innerPair21Input
    leaf1706InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1706LowerChecked :
    lowerCheck 24 leaf1706Box leaf1706Inputs = true := by
  rfl'

private theorem leaf1706CoversExact : CoversExact 8
    leaf1706Box leaf1706Certificate leaf1706InnerLog leaf1706Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi129RoundedFacts
    innerPair21RoundedFacts leaf1706RoundedFacts (by rfl)

private theorem leaf1706FlatSound : Sound leaf1706Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1706CertificateValid
    leaf1706InnerLogValid leaf1706CoversExact leaf1706LowerChecked

private noncomputable def leaf1707Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1707Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776871) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (708400637/536870912) }, upper := { exponent := 0, mantissa := (1369/1024) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554103/33553742) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf1707InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1707LocalValidity :
    LeafFacts leaf1707Box leaf1707Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1707Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776871) }) = true
      norm_num [leaf1707Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1707CertificateValid :
    WideCertificateValid leaf1707Box leaf1707Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi129ValidityFacts
    leaf1707LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1707CoverageChecked :
    coverageCheck (innerAD leaf1707Box) leaf1707InnerLog = true := by
  rfl'

private theorem leaf1707InnerLogValid :
    leaf1707InnerLog.Valid 8 (innerAD leaf1707Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1707CoverageChecked

private noncomputable def leaf1707InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1707InputLogOnePlusV_eq :
    leaf1707InputLogOnePlusV = outerEnclosure 24
      (leaf1707Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1707RoundedFacts : LeafRoundedFacts 8
    leaf1707Certificate.logOnePlusV leaf1707InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1707InputLogOnePlusV_eq }

private noncomputable def leaf1707Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi129InputQChi innerPair21Input
    leaf1707InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1707LowerChecked :
    lowerCheck 24 leaf1707Box leaf1707Inputs = true := by
  rfl'

private theorem leaf1707CoversExact : CoversExact 8
    leaf1707Box leaf1707Certificate leaf1707InnerLog leaf1707Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi129RoundedFacts
    innerPair21RoundedFacts leaf1707RoundedFacts (by rfl)

private theorem leaf1707FlatSound : Sound leaf1707Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1707CertificateValid
    leaf1707InnerLogValid leaf1707CoversExact leaf1707LowerChecked

private noncomputable def leaf1708Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1708Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (8191/8192), upper := (16777232/16776859) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (714691709/536870912) }, upper := { exponent := 0, mantissa := (1381/1024) } }, logOuter := sk165LogOuterCertificate, logK := sk165LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (33554091/33553718) } }, logDArg := sk165LogDArgCertificate }

private noncomputable def leaf1708InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1708LocalValidity :
    LeafFacts leaf1708Box leaf1708Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1708Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16777232/16776859) }) = true
      norm_num [leaf1708Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1708CertificateValid :
    WideCertificateValid leaf1708Box leaf1708Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk165ValidityFacts chi130ValidityFacts
    leaf1708LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1708CoverageChecked :
    coverageCheck (innerAD leaf1708Box) leaf1708InnerLog = true := by
  rfl'

private theorem leaf1708InnerLogValid :
    leaf1708InnerLog.Valid 8 (innerAD leaf1708Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1708CoverageChecked

private noncomputable def leaf1708InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1708InputLogOnePlusV_eq :
    leaf1708InputLogOnePlusV = outerEnclosure 24
      (leaf1708Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1708RoundedFacts : LeafRoundedFacts 8
    leaf1708Certificate.logOnePlusV leaf1708InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1708InputLogOnePlusV_eq }

private noncomputable def leaf1708Inputs : Inputs :=
  inputsOfCaches globalInput sk165RoundedInputs
    chi130InputQChi innerPair21Input
    leaf1708InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1708LowerChecked :
    lowerCheck 24 leaf1708Box leaf1708Inputs = true := by
  rfl'

private theorem leaf1708CoversExact : CoversExact 8
    leaf1708Box leaf1708Certificate leaf1708InnerLog leaf1708Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk165RoundedFacts chi130RoundedFacts
    innerPair21RoundedFacts leaf1708RoundedFacts (by rfl)

private theorem leaf1708FlatSound : Sound leaf1708Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1708CertificateValid
    leaf1708InnerLogValid leaf1708CoversExact leaf1708LowerChecked

private noncomputable def leaf1709Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1709Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (8191/8192), upper := (2097154/2097107) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (716198943/536870912) }, upper := { exponent := 0, mantissa := (173/128) } }, logOuter := sk166LogOuterCertificate, logK := sk166LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (4194261/4194214) } }, logDArg := sk166LogDArgCertificate }

private noncomputable def leaf1709InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1709LocalValidity :
    LeafFacts leaf1709Box leaf1709Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1709Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2097154/2097107) }) = true
      norm_num [leaf1709Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1709CertificateValid :
    WideCertificateValid leaf1709Box leaf1709Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk166ValidityFacts chi130ValidityFacts
    leaf1709LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1709CoverageChecked :
    coverageCheck (innerAD leaf1709Box) leaf1709InnerLog = true := by
  rfl'

private theorem leaf1709InnerLogValid :
    leaf1709InnerLog.Valid 8 (innerAD leaf1709Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1709CoverageChecked

private noncomputable def leaf1709InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1709InputLogOnePlusV_eq :
    leaf1709InputLogOnePlusV = outerEnclosure 24
      (leaf1709Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1709RoundedFacts : LeafRoundedFacts 8
    leaf1709Certificate.logOnePlusV leaf1709InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1709InputLogOnePlusV_eq }

private noncomputable def leaf1709Inputs : Inputs :=
  inputsOfCaches globalInput sk166RoundedInputs
    chi130InputQChi innerPair21Input
    leaf1709InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1709LowerChecked :
    lowerCheck 24 leaf1709Box leaf1709Inputs = true := by
  rfl'

private theorem leaf1709CoversExact : CoversExact 8
    leaf1709Box leaf1709Certificate leaf1709InnerLog leaf1709Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk166RoundedFacts chi130RoundedFacts
    innerPair21RoundedFacts leaf1709RoundedFacts (by rfl)

private theorem leaf1709FlatSound : Sound leaf1709Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1709CertificateValid
    leaf1709InnerLogValid leaf1709CoversExact leaf1709LowerChecked

private noncomputable def component38Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component38Node0_sound : Sound component38Node0Box :=
  sound_of_literal_split component38Node0Box leaf1657Box leaf1658Box
    .chi (17/256) (by rfl) (by rfl)
    leaf1657FlatSound leaf1658FlatSound

private noncomputable def component38Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component38Node1_sound : Sound component38Node1Box :=
  sound_of_literal_split component38Node1Box leaf1659Box leaf1660Box
    .chi (17/256) (by rfl) (by rfl)
    leaf1659FlatSound leaf1660FlatSound

private noncomputable def component38Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component38Node2_sound : Sound component38Node2Box :=
  sound_of_literal_split component38Node2Box component38Node0Box component38Node1Box
    .k (57/16) (by rfl) (by rfl)
    component38Node0_sound component38Node1_sound

private noncomputable def component38Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component38Node3_sound : Sound component38Node3Box :=
  sound_of_literal_split component38Node3Box leaf1661Box leaf1662Box
    .chi (19/256) (by rfl) (by rfl)
    leaf1661FlatSound leaf1662FlatSound

private noncomputable def component38Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (19/256), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component38Node4_sound : Sound component38Node4Box :=
  sound_of_literal_split component38Node4Box leaf1664Box leaf1665Box
    .k (115/32) (by rfl) (by rfl)
    leaf1664FlatSound leaf1665FlatSound

private noncomputable def component38Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component38Node5_sound : Sound component38Node5Box :=
  sound_of_literal_split component38Node5Box leaf1663Box component38Node4Box
    .chi (19/256) (by rfl) (by rfl)
    leaf1663FlatSound component38Node4_sound

private noncomputable def component38Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component38Node6_sound : Sound component38Node6Box :=
  sound_of_literal_split component38Node6Box component38Node3Box component38Node5Box
    .k (57/16) (by rfl) (by rfl)
    component38Node3_sound component38Node5_sound

private noncomputable def component38Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component38Node7_sound : Sound component38Node7Box :=
  sound_of_literal_split component38Node7Box component38Node2Box component38Node6Box
    .chi (9/128) (by rfl) (by rfl)
    component38Node2_sound component38Node6_sound

private noncomputable def component38Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component38Node8_sound : Sound component38Node8Box :=
  sound_of_literal_split component38Node8Box leaf1666Box leaf1667Box
    .chi (17/256) (by rfl) (by rfl)
    leaf1666FlatSound leaf1667FlatSound

private noncomputable def component38Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component38Node9_sound : Sound component38Node9Box :=
  sound_of_literal_split component38Node9Box leaf1668Box leaf1669Box
    .chi (17/256) (by rfl) (by rfl)
    leaf1668FlatSound leaf1669FlatSound

private noncomputable def component38Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component38Node10_sound : Sound component38Node10Box :=
  sound_of_literal_split component38Node10Box component38Node8Box component38Node9Box
    .k (59/16) (by rfl) (by rfl)
    component38Node8_sound component38Node9_sound

private noncomputable def component38Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (9/128), chiHi := (19/256) }

set_option maxRecDepth 1000000 in
private theorem component38Node11_sound : Sound component38Node11Box :=
  sound_of_literal_split component38Node11Box leaf1670Box leaf1671Box
    .k (117/32) (by rfl) (by rfl)
    leaf1670FlatSound leaf1671FlatSound

private noncomputable def component38Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (19/256), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component38Node12_sound : Sound component38Node12Box :=
  sound_of_literal_split component38Node12Box leaf1672Box leaf1673Box
    .k (117/32) (by rfl) (by rfl)
    leaf1672FlatSound leaf1673FlatSound

private noncomputable def component38Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component38Node13_sound : Sound component38Node13Box :=
  sound_of_literal_split component38Node13Box component38Node11Box component38Node12Box
    .chi (19/256) (by rfl) (by rfl)
    component38Node11_sound component38Node12_sound

private noncomputable def component38Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (9/128), chiHi := (19/256) }

set_option maxRecDepth 1000000 in
private theorem component38Node14_sound : Sound component38Node14Box :=
  sound_of_literal_split component38Node14Box leaf1674Box leaf1675Box
    .k (119/32) (by rfl) (by rfl)
    leaf1674FlatSound leaf1675FlatSound

private noncomputable def component38Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (19/256), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component38Node15_sound : Sound component38Node15Box :=
  sound_of_literal_split component38Node15Box leaf1676Box leaf1677Box
    .k (119/32) (by rfl) (by rfl)
    leaf1676FlatSound leaf1677FlatSound

private noncomputable def component38Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component38Node16_sound : Sound component38Node16Box :=
  sound_of_literal_split component38Node16Box component38Node14Box component38Node15Box
    .chi (19/256) (by rfl) (by rfl)
    component38Node14_sound component38Node15_sound

private noncomputable def component38Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component38Node17_sound : Sound component38Node17Box :=
  sound_of_literal_split component38Node17Box component38Node13Box component38Node16Box
    .k (59/16) (by rfl) (by rfl)
    component38Node13_sound component38Node16_sound

private noncomputable def component38Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component38Node18_sound : Sound component38Node18Box :=
  sound_of_literal_split component38Node18Box component38Node10Box component38Node17Box
    .chi (9/128) (by rfl) (by rfl)
    component38Node10_sound component38Node17_sound

private noncomputable def component38Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component38Node19_sound : Sound component38Node19Box :=
  sound_of_literal_split component38Node19Box component38Node7Box component38Node18Box
    .k (29/8) (by rfl) (by rfl)
    component38Node7_sound component38Node18_sound

private noncomputable def component38Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (5/64), chiHi := (21/256) }

set_option maxRecDepth 1000000 in
private theorem component38Node20_sound : Sound component38Node20Box :=
  sound_of_literal_split component38Node20Box leaf1678Box leaf1679Box
    .k (113/32) (by rfl) (by rfl)
    leaf1678FlatSound leaf1679FlatSound

private noncomputable def component38Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (21/256), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component38Node21_sound : Sound component38Node21Box :=
  sound_of_literal_split component38Node21Box leaf1680Box leaf1681Box
    .k (113/32) (by rfl) (by rfl)
    leaf1680FlatSound leaf1681FlatSound

private noncomputable def component38Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component38Node22_sound : Sound component38Node22Box :=
  sound_of_literal_split component38Node22Box component38Node20Box component38Node21Box
    .chi (21/256) (by rfl) (by rfl)
    component38Node20_sound component38Node21_sound

private noncomputable def component38Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (5/64), chiHi := (21/256) }

set_option maxRecDepth 1000000 in
private theorem component38Node23_sound : Sound component38Node23Box :=
  sound_of_literal_split component38Node23Box leaf1682Box leaf1683Box
    .k (115/32) (by rfl) (by rfl)
    leaf1682FlatSound leaf1683FlatSound

private noncomputable def component38Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (21/256), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component38Node24_sound : Sound component38Node24Box :=
  sound_of_literal_split component38Node24Box leaf1684Box leaf1685Box
    .k (115/32) (by rfl) (by rfl)
    leaf1684FlatSound leaf1685FlatSound

private noncomputable def component38Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component38Node25_sound : Sound component38Node25Box :=
  sound_of_literal_split component38Node25Box component38Node23Box component38Node24Box
    .chi (21/256) (by rfl) (by rfl)
    component38Node23_sound component38Node24_sound

private noncomputable def component38Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component38Node26_sound : Sound component38Node26Box :=
  sound_of_literal_split component38Node26Box component38Node22Box component38Node25Box
    .k (57/16) (by rfl) (by rfl)
    component38Node22_sound component38Node25_sound

private noncomputable def component38Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (11/128), chiHi := (23/256) }

set_option maxRecDepth 1000000 in
private theorem component38Node27_sound : Sound component38Node27Box :=
  sound_of_literal_split component38Node27Box leaf1686Box leaf1687Box
    .k (113/32) (by rfl) (by rfl)
    leaf1686FlatSound leaf1687FlatSound

private noncomputable def component38Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (23/256), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component38Node28_sound : Sound component38Node28Box :=
  sound_of_literal_split component38Node28Box leaf1688Box leaf1689Box
    .k (113/32) (by rfl) (by rfl)
    leaf1688FlatSound leaf1689FlatSound

private noncomputable def component38Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component38Node29_sound : Sound component38Node29Box :=
  sound_of_literal_split component38Node29Box component38Node27Box component38Node28Box
    .chi (23/256) (by rfl) (by rfl)
    component38Node27_sound component38Node28_sound

private noncomputable def component38Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (11/128), chiHi := (23/256) }

set_option maxRecDepth 1000000 in
private theorem component38Node30_sound : Sound component38Node30Box :=
  sound_of_literal_split component38Node30Box leaf1690Box leaf1691Box
    .k (115/32) (by rfl) (by rfl)
    leaf1690FlatSound leaf1691FlatSound

private noncomputable def component38Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (23/256), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component38Node31_sound : Sound component38Node31Box :=
  sound_of_literal_split component38Node31Box leaf1692Box leaf1693Box
    .k (115/32) (by rfl) (by rfl)
    leaf1692FlatSound leaf1693FlatSound

private noncomputable def component38Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component38Node32_sound : Sound component38Node32Box :=
  sound_of_literal_split component38Node32Box component38Node30Box component38Node31Box
    .chi (23/256) (by rfl) (by rfl)
    component38Node30_sound component38Node31_sound

private noncomputable def component38Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component38Node33_sound : Sound component38Node33Box :=
  sound_of_literal_split component38Node33Box component38Node29Box component38Node32Box
    .k (57/16) (by rfl) (by rfl)
    component38Node29_sound component38Node32_sound

private noncomputable def component38Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component38Node34_sound : Sound component38Node34Box :=
  sound_of_literal_split component38Node34Box component38Node26Box component38Node33Box
    .chi (11/128) (by rfl) (by rfl)
    component38Node26_sound component38Node33_sound

private noncomputable def component38Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (5/64), chiHi := (21/256) }

set_option maxRecDepth 1000000 in
private theorem component38Node35_sound : Sound component38Node35Box :=
  sound_of_literal_split component38Node35Box leaf1694Box leaf1695Box
    .k (117/32) (by rfl) (by rfl)
    leaf1694FlatSound leaf1695FlatSound

private noncomputable def component38Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (21/256), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component38Node36_sound : Sound component38Node36Box :=
  sound_of_literal_split component38Node36Box leaf1696Box leaf1697Box
    .k (117/32) (by rfl) (by rfl)
    leaf1696FlatSound leaf1697FlatSound

private noncomputable def component38Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component38Node37_sound : Sound component38Node37Box :=
  sound_of_literal_split component38Node37Box component38Node35Box component38Node36Box
    .chi (21/256) (by rfl) (by rfl)
    component38Node35_sound component38Node36_sound

private noncomputable def component38Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (5/64), chiHi := (21/256) }

set_option maxRecDepth 1000000 in
private theorem component38Node38_sound : Sound component38Node38Box :=
  sound_of_literal_split component38Node38Box leaf1698Box leaf1699Box
    .k (119/32) (by rfl) (by rfl)
    leaf1698FlatSound leaf1699FlatSound

private noncomputable def component38Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (21/256), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component38Node39_sound : Sound component38Node39Box :=
  sound_of_literal_split component38Node39Box leaf1700Box leaf1701Box
    .k (119/32) (by rfl) (by rfl)
    leaf1700FlatSound leaf1701FlatSound

private noncomputable def component38Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component38Node40_sound : Sound component38Node40Box :=
  sound_of_literal_split component38Node40Box component38Node38Box component38Node39Box
    .chi (21/256) (by rfl) (by rfl)
    component38Node38_sound component38Node39_sound

private noncomputable def component38Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component38Node41_sound : Sound component38Node41Box :=
  sound_of_literal_split component38Node41Box component38Node37Box component38Node40Box
    .k (59/16) (by rfl) (by rfl)
    component38Node37_sound component38Node40_sound

private noncomputable def component38Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (11/128), chiHi := (23/256) }

set_option maxRecDepth 1000000 in
private theorem component38Node42_sound : Sound component38Node42Box :=
  sound_of_literal_split component38Node42Box leaf1702Box leaf1703Box
    .k (117/32) (by rfl) (by rfl)
    leaf1702FlatSound leaf1703FlatSound

private noncomputable def component38Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (23/256), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component38Node43_sound : Sound component38Node43Box :=
  sound_of_literal_split component38Node43Box leaf1704Box leaf1705Box
    .k (117/32) (by rfl) (by rfl)
    leaf1704FlatSound leaf1705FlatSound

private noncomputable def component38Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component38Node44_sound : Sound component38Node44Box :=
  sound_of_literal_split component38Node44Box component38Node42Box component38Node43Box
    .chi (23/256) (by rfl) (by rfl)
    component38Node42_sound component38Node43_sound

private noncomputable def component38Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (11/128), chiHi := (23/256) }

set_option maxRecDepth 1000000 in
private theorem component38Node45_sound : Sound component38Node45Box :=
  sound_of_literal_split component38Node45Box leaf1706Box leaf1707Box
    .k (119/32) (by rfl) (by rfl)
    leaf1706FlatSound leaf1707FlatSound

private noncomputable def component38Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (23/256), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component38Node46_sound : Sound component38Node46Box :=
  sound_of_literal_split component38Node46Box leaf1708Box leaf1709Box
    .k (119/32) (by rfl) (by rfl)
    leaf1708FlatSound leaf1709FlatSound

private noncomputable def component38Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component38Node47_sound : Sound component38Node47Box :=
  sound_of_literal_split component38Node47Box component38Node45Box component38Node46Box
    .chi (23/256) (by rfl) (by rfl)
    component38Node45_sound component38Node46_sound

private noncomputable def component38Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component38Node48_sound : Sound component38Node48Box :=
  sound_of_literal_split component38Node48Box component38Node44Box component38Node47Box
    .k (59/16) (by rfl) (by rfl)
    component38Node44_sound component38Node47_sound

private noncomputable def component38Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component38Node49_sound : Sound component38Node49Box :=
  sound_of_literal_split component38Node49Box component38Node41Box component38Node48Box
    .chi (11/128) (by rfl) (by rfl)
    component38Node41_sound component38Node48_sound

private noncomputable def component38Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component38Node50_sound : Sound component38Node50Box :=
  sound_of_literal_split component38Node50Box component38Node34Box component38Node49Box
    .k (29/8) (by rfl) (by rfl)
    component38Node34_sound component38Node49_sound

noncomputable def component38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (15/4), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
theorem component38_sound : Sound component38Box :=
  sound_of_literal_split component38Box component38Node19Box component38Node50Box
    .chi (5/64) (by rfl) (by rfl)
    component38Node19_sound component38Node50_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
