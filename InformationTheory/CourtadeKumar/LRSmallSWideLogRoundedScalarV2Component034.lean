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

private noncomputable def leaf1461Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (1/16), chiHi := (17/256) }

private noncomputable def leaf1461Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435595/268435456) }, vSqrt := { lower := (65529/65536), upper := (22369664/22369321) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (322925175/268435456) }, upper := { exponent := 0, mantissa := (4997/4096) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi151LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (44738985/44738642) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf1461InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1461LocalValidity :
    LeafFacts leaf1461Box leaf1461Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1461Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22369664/22369321) }) = true
      norm_num [leaf1461Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1461CertificateValid :
    WideCertificateValid leaf1461Box leaf1461Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi151ValidityFacts
    leaf1461LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1461CoverageChecked :
    coverageCheck (innerAD leaf1461Box) leaf1461InnerLog = true := by
  rfl'

private theorem leaf1461InnerLogValid :
    leaf1461InnerLog.Valid 8 (innerAD leaf1461Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1461CoverageChecked

private noncomputable def leaf1461InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629209/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1461InputLogOnePlusV_eq :
    leaf1461InputLogOnePlusV = outerEnclosure 24
      (leaf1461Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1461RoundedFacts : LeafRoundedFacts 8
    leaf1461Certificate.logOnePlusV leaf1461InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1461InputLogOnePlusV_eq }

private noncomputable def leaf1461Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi151InputQChi innerPair12Input
    leaf1461InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1461LowerChecked :
    lowerCheck 24 leaf1461Box leaf1461Inputs = true := by
  rfl'

private theorem leaf1461CoversExact : CoversExact 8
    leaf1461Box leaf1461Certificate leaf1461InnerLog leaf1461Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi151RoundedFacts
    innerPair12RoundedFacts leaf1461RoundedFacts (by rfl)

private theorem leaf1461FlatSound : Sound leaf1461Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1461CertificateValid
    leaf1461InnerLogValid leaf1461CoversExact leaf1461LowerChecked

private noncomputable def leaf1462Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (17/256), chiHi := (9/128) }

private noncomputable def leaf1462Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435597/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554496/33553955) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (326332837/268435456) }, upper := { exponent := 0, mantissa := (2525/2048) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi152LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108451/67107910) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf1462InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1462LocalValidity :
    LeafFacts leaf1462Box leaf1462Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1462Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33553955) }) = true
      norm_num [leaf1462Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1462CertificateValid :
    WideCertificateValid leaf1462Box leaf1462Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi152ValidityFacts
    leaf1462LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1462CoverageChecked :
    coverageCheck (innerAD leaf1462Box) leaf1462InnerLog = true := by
  rfl'

private theorem leaf1462InnerLogValid :
    leaf1462InnerLog.Valid 8 (innerAD leaf1462Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1462CoverageChecked

private noncomputable def leaf1462InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363413/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf1462InputLogOnePlusV_eq :
    leaf1462InputLogOnePlusV = outerEnclosure 24
      (leaf1462Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1462RoundedFacts : LeafRoundedFacts 8
    leaf1462Certificate.logOnePlusV leaf1462InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1462InputLogOnePlusV_eq }

private noncomputable def leaf1462Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi152InputQChi innerPair12Input
    leaf1462InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1462LowerChecked :
    lowerCheck 24 leaf1462Box leaf1462Inputs = true := by
  rfl'

private theorem leaf1462CoversExact : CoversExact 8
    leaf1462Box leaf1462Certificate leaf1462InnerLog leaf1462Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi152RoundedFacts
    innerPair12RoundedFacts leaf1462RoundedFacts (by rfl)

private theorem leaf1462FlatSound : Sound leaf1462Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1462CertificateValid
    leaf1462InnerLogValid leaf1462CoversExact leaf1462LowerChecked

private noncomputable def leaf1463Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (1/16), chiHi := (17/256) }

private noncomputable def leaf1463Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435597/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554496/33553973) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (323973685/268435456) }, upper := { exponent := 0, mantissa := (2507/2048) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi151LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108469/67107946) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf1463InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1463LocalValidity :
    LeafFacts leaf1463Box leaf1463Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1463Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33553973) }) = true
      norm_num [leaf1463Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1463CertificateValid :
    WideCertificateValid leaf1463Box leaf1463Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi151ValidityFacts
    leaf1463LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1463CoverageChecked :
    coverageCheck (innerAD leaf1463Box) leaf1463InnerLog = true := by
  rfl'

private theorem leaf1463InnerLogValid :
    leaf1463InnerLog.Valid 8 (innerAD leaf1463Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1463CoverageChecked

private noncomputable def leaf1463InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629211/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1463InputLogOnePlusV_eq :
    leaf1463InputLogOnePlusV = outerEnclosure 24
      (leaf1463Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1463RoundedFacts : LeafRoundedFacts 8
    leaf1463Certificate.logOnePlusV leaf1463InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1463InputLogOnePlusV_eq }

private noncomputable def leaf1463Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi151InputQChi innerPair12Input
    leaf1463InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1463LowerChecked :
    lowerCheck 24 leaf1463Box leaf1463Inputs = true := by
  rfl'

private theorem leaf1463CoversExact : CoversExact 8
    leaf1463Box leaf1463Certificate leaf1463InnerLog leaf1463Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi151RoundedFacts
    innerPair12RoundedFacts leaf1463RoundedFacts (by rfl)

private theorem leaf1463FlatSound : Sound leaf1463Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1463CertificateValid
    leaf1463InnerLogValid leaf1463CoversExact leaf1463LowerChecked

private noncomputable def leaf1464Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (17/256), chiHi := (9/128) }

private noncomputable def leaf1464Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435599/268435456) }, vSqrt := { lower := (65529/65536), upper := (16777248/16776973) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (327446879/268435456) }, upper := { exponent := 0, mantissa := (1267/1024) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi152LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554221/33553946) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf1464InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1464LocalValidity :
    LeafFacts leaf1464Box leaf1464Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1464Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777248/16776973) }) = true
      norm_num [leaf1464Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1464CertificateValid :
    WideCertificateValid leaf1464Box leaf1464Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi152ValidityFacts
    leaf1464LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1464CoverageChecked :
    coverageCheck (innerAD leaf1464Box) leaf1464InnerLog = true := by
  rfl'

private theorem leaf1464InnerLogValid :
    leaf1464InnerLog.Valid 8 (innerAD leaf1464Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1464CoverageChecked

private noncomputable def leaf1464InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814609/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1464InputLogOnePlusV_eq :
    leaf1464InputLogOnePlusV = outerEnclosure 24
      (leaf1464Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1464RoundedFacts : LeafRoundedFacts 8
    leaf1464Certificate.logOnePlusV leaf1464InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1464InputLogOnePlusV_eq }

private noncomputable def leaf1464Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi152InputQChi innerPair12Input
    leaf1464InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1464LowerChecked :
    lowerCheck 24 leaf1464Box leaf1464Inputs = true := by
  rfl'

private theorem leaf1464CoversExact : CoversExact 8
    leaf1464Box leaf1464Certificate leaf1464InnerLog leaf1464Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi152RoundedFacts
    innerPair12RoundedFacts leaf1464RoundedFacts (by rfl)

private theorem leaf1464FlatSound : Sound leaf1464Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1464CertificateValid
    leaf1464InnerLogValid leaf1464CoversExact leaf1464LowerChecked

private noncomputable def leaf1465Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1465Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435599/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108992/67107857) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (329740499/268435456) }, upper := { exponent := 0, mantissa := (5103/4096) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216849/134215714) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf1465InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1465LocalValidity :
    LeafFacts leaf1465Box leaf1465Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1465Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108992/67107857) }) = true
      norm_num [leaf1465Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1465CertificateValid :
    WideCertificateValid leaf1465Box leaf1465Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi147ValidityFacts
    leaf1465LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1465CoverageChecked :
    coverageCheck (innerAD leaf1465Box) leaf1465InnerLog = true := by
  rfl'

private theorem leaf1465InnerLogValid :
    leaf1465InnerLog.Valid 8 (innerAD leaf1465Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1465CoverageChecked

private noncomputable def leaf1465InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1465InputLogOnePlusV_eq :
    leaf1465InputLogOnePlusV = outerEnclosure 24
      (leaf1465Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1465RoundedFacts : LeafRoundedFacts 8
    leaf1465Certificate.logOnePlusV leaf1465InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1465InputLogOnePlusV_eq }

private noncomputable def leaf1465Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi147InputQChi innerPair12Input
    leaf1465InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1465LowerChecked :
    lowerCheck 24 leaf1465Box leaf1465Inputs = true := by
  rfl'

private theorem leaf1465CoversExact : CoversExact 8
    leaf1465Box leaf1465Certificate leaf1465InnerLog leaf1465Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi147RoundedFacts
    innerPair12RoundedFacts leaf1465RoundedFacts (by rfl)

private theorem leaf1465FlatSound : Sound leaf1465Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1465CertificateValid
    leaf1465InnerLogValid leaf1465CoversExact leaf1465LowerChecked

private noncomputable def leaf1466Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1466Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435601/268435456) }, vSqrt := { lower := (65529/65536), upper := (5592416/5592317) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (333148161/268435456) }, upper := { exponent := 0, mantissa := (1289/1024) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (11184733/11184634) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf1466InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1466LocalValidity :
    LeafFacts leaf1466Box leaf1466Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1466Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5592416/5592317) }) = true
      norm_num [leaf1466Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1466CertificateValid :
    WideCertificateValid leaf1466Box leaf1466Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi148ValidityFacts
    leaf1466LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1466CoverageChecked :
    coverageCheck (innerAD leaf1466Box) leaf1466InnerLog = true := by
  rfl'

private theorem leaf1466InnerLogValid :
    leaf1466InnerLog.Valid 8 (innerAD leaf1466Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1466CoverageChecked

private noncomputable def leaf1466InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629229/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1466InputLogOnePlusV_eq :
    leaf1466InputLogOnePlusV = outerEnclosure 24
      (leaf1466Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1466RoundedFacts : LeafRoundedFacts 8
    leaf1466Certificate.logOnePlusV leaf1466InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1466InputLogOnePlusV_eq }

private noncomputable def leaf1466Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi148InputQChi innerPair13Input
    leaf1466InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1466LowerChecked :
    lowerCheck 24 leaf1466Box leaf1466Inputs = true := by
  rfl'

private theorem leaf1466CoversExact : CoversExact 8
    leaf1466Box leaf1466Certificate leaf1466InnerLog leaf1466Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi148RoundedFacts
    innerPair13RoundedFacts leaf1466RoundedFacts (by rfl)

private theorem leaf1466FlatSound : Sound leaf1466Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1466CertificateValid
    leaf1466InnerLogValid leaf1466CoversExact leaf1466LowerChecked

private noncomputable def leaf1467Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1467Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435601/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554496/33553919) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (330920073/268435456) }, upper := { exponent := 0, mantissa := (2561/2048) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108415/67107838) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf1467InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1467LocalValidity :
    LeafFacts leaf1467Box leaf1467Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1467Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33553919) }) = true
      norm_num [leaf1467Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1467CertificateValid :
    WideCertificateValid leaf1467Box leaf1467Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi147ValidityFacts
    leaf1467LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1467CoverageChecked :
    coverageCheck (innerAD leaf1467Box) leaf1467InnerLog = true := by
  rfl'

private theorem leaf1467InnerLogValid :
    leaf1467InnerLog.Valid 8 (innerAD leaf1467Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1467CoverageChecked

private noncomputable def leaf1467InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629225/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1467InputLogOnePlusV_eq :
    leaf1467InputLogOnePlusV = outerEnclosure 24
      (leaf1467Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1467RoundedFacts : LeafRoundedFacts 8
    leaf1467Certificate.logOnePlusV leaf1467InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1467InputLogOnePlusV_eq }

private noncomputable def leaf1467Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi147InputQChi innerPair13Input
    leaf1467InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1467LowerChecked :
    lowerCheck 24 leaf1467Box leaf1467Inputs = true := by
  rfl'

private theorem leaf1467CoversExact : CoversExact 8
    leaf1467Box leaf1467Certificate leaf1467InnerLog leaf1467Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi147RoundedFacts
    innerPair13RoundedFacts leaf1467RoundedFacts (by rfl)

private theorem leaf1467FlatSound : Sound leaf1467Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1467CertificateValid
    leaf1467InnerLogValid leaf1467CoversExact leaf1467LowerChecked

private noncomputable def leaf1468Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1468Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435603/268435456) }, vSqrt := { lower := (65529/65536), upper := (8388624/8388473) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (334393267/268435456) }, upper := { exponent := 0, mantissa := (647/512) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777097/16776946) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf1468InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1468LocalValidity :
    LeafFacts leaf1468Box leaf1468Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1468Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388624/8388473) }) = true
      norm_num [leaf1468Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1468CertificateValid :
    WideCertificateValid leaf1468Box leaf1468Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi148ValidityFacts
    leaf1468LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1468CoverageChecked :
    coverageCheck (innerAD leaf1468Box) leaf1468InnerLog = true := by
  rfl'

private theorem leaf1468InnerLogValid :
    leaf1468InnerLog.Valid 8 (innerAD leaf1468Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1468CoverageChecked

private noncomputable def leaf1468InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1468InputLogOnePlusV_eq :
    leaf1468InputLogOnePlusV = outerEnclosure 24
      (leaf1468Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1468RoundedFacts : LeafRoundedFacts 8
    leaf1468Certificate.logOnePlusV leaf1468InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1468InputLogOnePlusV_eq }

private noncomputable def leaf1468Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi148InputQChi innerPair13Input
    leaf1468InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1468LowerChecked :
    lowerCheck 24 leaf1468Box leaf1468Inputs = true := by
  rfl'

private theorem leaf1468CoversExact : CoversExact 8
    leaf1468Box leaf1468Certificate leaf1468InnerLog leaf1468Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi148RoundedFacts
    innerPair13RoundedFacts leaf1468RoundedFacts (by rfl)

private theorem leaf1468FlatSound : Sound leaf1468Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1468CertificateValid
    leaf1468InnerLogValid leaf1468CoversExact leaf1468LowerChecked

private noncomputable def leaf1469Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (1/16), chiHi := (17/256) }

private noncomputable def leaf1469Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435599/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108992/67107929) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (325022195/268435456) }, upper := { exponent := 0, mantissa := (5031/4096) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi151LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216921/134215858) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf1469InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1469LocalValidity :
    LeafFacts leaf1469Box leaf1469Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1469Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108992/67107929) }) = true
      norm_num [leaf1469Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1469CertificateValid :
    WideCertificateValid leaf1469Box leaf1469Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi151ValidityFacts
    leaf1469LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1469CoverageChecked :
    coverageCheck (innerAD leaf1469Box) leaf1469InnerLog = true := by
  rfl'

private theorem leaf1469InnerLogValid :
    leaf1469InnerLog.Valid 8 (innerAD leaf1469Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1469CoverageChecked

private noncomputable def leaf1469InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814607/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1469InputLogOnePlusV_eq :
    leaf1469InputLogOnePlusV = outerEnclosure 24
      (leaf1469Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1469RoundedFacts : LeafRoundedFacts 8
    leaf1469Certificate.logOnePlusV leaf1469InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1469InputLogOnePlusV_eq }

private noncomputable def leaf1469Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi151InputQChi innerPair12Input
    leaf1469InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1469LowerChecked :
    lowerCheck 24 leaf1469Box leaf1469Inputs = true := by
  rfl'

private theorem leaf1469CoversExact : CoversExact 8
    leaf1469Box leaf1469Certificate leaf1469InnerLog leaf1469Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi151RoundedFacts
    innerPair12RoundedFacts leaf1469RoundedFacts (by rfl)

private theorem leaf1469FlatSound : Sound leaf1469Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1469CertificateValid
    leaf1469InnerLogValid leaf1469CoversExact leaf1469LowerChecked

private noncomputable def leaf1470Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (17/256), chiHi := (9/128) }

private noncomputable def leaf1470Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435601/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554496/33553937) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (328560921/268435456) }, upper := { exponent := 0, mantissa := (2543/2048) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi152LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108433/67107874) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf1470InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1470LocalValidity :
    LeafFacts leaf1470Box leaf1470Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1470Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33553937) }) = true
      norm_num [leaf1470Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1470CertificateValid :
    WideCertificateValid leaf1470Box leaf1470Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi152ValidityFacts
    leaf1470LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1470CoverageChecked :
    coverageCheck (innerAD leaf1470Box) leaf1470InnerLog = true := by
  rfl'

private theorem leaf1470InnerLogValid :
    leaf1470InnerLog.Valid 8 (innerAD leaf1470Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1470CoverageChecked

private noncomputable def leaf1470InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907305/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1470InputLogOnePlusV_eq :
    leaf1470InputLogOnePlusV = outerEnclosure 24
      (leaf1470Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1470RoundedFacts : LeafRoundedFacts 8
    leaf1470Certificate.logOnePlusV leaf1470InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1470InputLogOnePlusV_eq }

private noncomputable def leaf1470Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi152InputQChi innerPair12Input
    leaf1470InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1470LowerChecked :
    lowerCheck 24 leaf1470Box leaf1470Inputs = true := by
  rfl'

private theorem leaf1470CoversExact : CoversExact 8
    leaf1470Box leaf1470Certificate leaf1470InnerLog leaf1470Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi152RoundedFacts
    innerPair12RoundedFacts leaf1470RoundedFacts (by rfl)

private theorem leaf1470FlatSound : Sound leaf1470Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1470CertificateValid
    leaf1470InnerLogValid leaf1470CoversExact leaf1470LowerChecked

private noncomputable def leaf1471Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (1/16), chiHi := (17/256) }

private noncomputable def leaf1471Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435601/268435456) }, vSqrt := { lower := (8191/8192), upper := (2796208/2796163) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (326070705/268435456) }, upper := { exponent := 0, mantissa := (631/512) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi151LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5592371/5592326) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf1471InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1471LocalValidity :
    LeafFacts leaf1471Box leaf1471Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1471Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2796208/2796163) }) = true
      norm_num [leaf1471Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1471CertificateValid :
    WideCertificateValid leaf1471Box leaf1471Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi151ValidityFacts
    leaf1471LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1471CoverageChecked :
    coverageCheck (innerAD leaf1471Box) leaf1471InnerLog = true := by
  rfl'

private theorem leaf1471InnerLogValid :
    leaf1471InnerLog.Valid 8 (innerAD leaf1471Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1471CoverageChecked

private noncomputable def leaf1471InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363413/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf1471InputLogOnePlusV_eq :
    leaf1471InputLogOnePlusV = outerEnclosure 24
      (leaf1471Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1471RoundedFacts : LeafRoundedFacts 8
    leaf1471Certificate.logOnePlusV leaf1471InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1471InputLogOnePlusV_eq }

private noncomputable def leaf1471Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi151InputQChi innerPair12Input
    leaf1471InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1471LowerChecked :
    lowerCheck 24 leaf1471Box leaf1471Inputs = true := by
  rfl'

private theorem leaf1471CoversExact : CoversExact 8
    leaf1471Box leaf1471Certificate leaf1471InnerLog leaf1471Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi151RoundedFacts
    innerPair12RoundedFacts leaf1471RoundedFacts (by rfl)

private theorem leaf1471FlatSound : Sound leaf1471Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1471CertificateValid
    leaf1471InnerLogValid leaf1471CoversExact leaf1471LowerChecked

private noncomputable def leaf1472Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (17/256), chiHi := (9/128) }

private noncomputable def leaf1472Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435603/268435456) }, vSqrt := { lower := (8191/8192), upper := (4194312/4194241) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (329674963/268435456) }, upper := { exponent := 0, mantissa := (319/256) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi152LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388553/8388482) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf1472InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf1472LocalValidity :
    LeafFacts leaf1472Box leaf1472Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1472Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194312/4194241) }) = true
      norm_num [leaf1472Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1472CertificateValid :
    WideCertificateValid leaf1472Box leaf1472Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi152ValidityFacts
    leaf1472LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1472CoverageChecked :
    coverageCheck (innerAD leaf1472Box) leaf1472InnerLog = true := by
  rfl'

private theorem leaf1472InnerLogValid :
    leaf1472InnerLog.Valid 8 (innerAD leaf1472Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf1472CoverageChecked

private noncomputable def leaf1472InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1472InputLogOnePlusV_eq :
    leaf1472InputLogOnePlusV = outerEnclosure 24
      (leaf1472Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1472RoundedFacts : LeafRoundedFacts 8
    leaf1472Certificate.logOnePlusV leaf1472InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1472InputLogOnePlusV_eq }

private noncomputable def leaf1472Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi152InputQChi innerPair12Input
    leaf1472InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1472LowerChecked :
    lowerCheck 24 leaf1472Box leaf1472Inputs = true := by
  rfl'

private theorem leaf1472CoversExact : CoversExact 8
    leaf1472Box leaf1472Certificate leaf1472InnerLog leaf1472Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi152RoundedFacts
    innerPair12RoundedFacts leaf1472RoundedFacts (by rfl)

private theorem leaf1472FlatSound : Sound leaf1472Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1472CertificateValid
    leaf1472InnerLogValid leaf1472CoversExact leaf1472LowerChecked

private noncomputable def leaf1473Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1473Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435603/268435456) }, vSqrt := { lower := (65529/65536), upper := (22369664/22369273) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (332099647/268435456) }, upper := { exponent := 0, mantissa := (5141/4096) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (44738937/44738546) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf1473InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1473LocalValidity :
    LeafFacts leaf1473Box leaf1473Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1473Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22369664/22369273) }) = true
      norm_num [leaf1473Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1473CertificateValid :
    WideCertificateValid leaf1473Box leaf1473Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi147ValidityFacts
    leaf1473LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1473CoverageChecked :
    coverageCheck (innerAD leaf1473Box) leaf1473InnerLog = true := by
  rfl'

private theorem leaf1473InnerLogValid :
    leaf1473InnerLog.Valid 8 (innerAD leaf1473Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1473CoverageChecked

private noncomputable def leaf1473InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1473InputLogOnePlusV_eq :
    leaf1473InputLogOnePlusV = outerEnclosure 24
      (leaf1473Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1473RoundedFacts : LeafRoundedFacts 8
    leaf1473Certificate.logOnePlusV leaf1473InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1473InputLogOnePlusV_eq }

private noncomputable def leaf1473Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi147InputQChi innerPair13Input
    leaf1473InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1473LowerChecked :
    lowerCheck 24 leaf1473Box leaf1473Inputs = true := by
  rfl'

private theorem leaf1473CoversExact : CoversExact 8
    leaf1473Box leaf1473Certificate leaf1473InnerLog leaf1473Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi147RoundedFacts
    innerPair13RoundedFacts leaf1473RoundedFacts (by rfl)

private theorem leaf1473FlatSound : Sound leaf1473Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1473CertificateValid
    leaf1473InnerLogValid leaf1473CoversExact leaf1473LowerChecked

private noncomputable def leaf1474Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1474Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435605/268435456) }, vSqrt := { lower := (65529/65536), upper := (16777248/16776941) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (335638373/268435456) }, upper := { exponent := 0, mantissa := (1299/1024) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554189/33553882) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf1474InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1474LocalValidity :
    LeafFacts leaf1474Box leaf1474Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1474Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777248/16776941) }) = true
      norm_num [leaf1474Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1474CertificateValid :
    WideCertificateValid leaf1474Box leaf1474Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi148ValidityFacts
    leaf1474LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1474CoverageChecked :
    coverageCheck (innerAD leaf1474Box) leaf1474InnerLog = true := by
  rfl'

private theorem leaf1474InnerLogValid :
    leaf1474InnerLog.Valid 8 (innerAD leaf1474Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1474CoverageChecked

private noncomputable def leaf1474InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1474InputLogOnePlusV_eq :
    leaf1474InputLogOnePlusV = outerEnclosure 24
      (leaf1474Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1474RoundedFacts : LeafRoundedFacts 8
    leaf1474Certificate.logOnePlusV leaf1474InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1474InputLogOnePlusV_eq }

private noncomputable def leaf1474Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi148InputQChi innerPair16Input
    leaf1474InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1474LowerChecked :
    lowerCheck 24 leaf1474Box leaf1474Inputs = true := by
  rfl'

private theorem leaf1474CoversExact : CoversExact 8
    leaf1474Box leaf1474Certificate leaf1474InnerLog leaf1474Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi148RoundedFacts
    innerPair16RoundedFacts leaf1474RoundedFacts (by rfl)

private theorem leaf1474FlatSound : Sound leaf1474Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1474CertificateValid
    leaf1474InnerLogValid leaf1474CoversExact leaf1474LowerChecked

private noncomputable def leaf1475Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (9/128), chiHi := (19/256) }

private noncomputable def leaf1475Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435605/268435456) }, vSqrt := { lower := (8191/8192), upper := (8388624/8388475) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (333279221/268435456) }, upper := { exponent := 0, mantissa := (645/512) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi147LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777099/16776950) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf1475InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf1475LocalValidity :
    LeafFacts leaf1475Box leaf1475Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1475Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388624/8388475) }) = true
      norm_num [leaf1475Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1475CertificateValid :
    WideCertificateValid leaf1475Box leaf1475Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi147ValidityFacts
    leaf1475LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1475CoverageChecked :
    coverageCheck (innerAD leaf1475Box) leaf1475InnerLog = true := by
  rfl'

private theorem leaf1475InnerLogValid :
    leaf1475InnerLog.Valid 8 (innerAD leaf1475Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf1475CoverageChecked

private noncomputable def leaf1475InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814615/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1475InputLogOnePlusV_eq :
    leaf1475InputLogOnePlusV = outerEnclosure 24
      (leaf1475Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1475RoundedFacts : LeafRoundedFacts 8
    leaf1475Certificate.logOnePlusV leaf1475InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1475InputLogOnePlusV_eq }

private noncomputable def leaf1475Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi147InputQChi innerPair13Input
    leaf1475InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1475LowerChecked :
    lowerCheck 24 leaf1475Box leaf1475Inputs = true := by
  rfl'

private theorem leaf1475CoversExact : CoversExact 8
    leaf1475Box leaf1475Certificate leaf1475InnerLog leaf1475Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi147RoundedFacts
    innerPair13RoundedFacts leaf1475RoundedFacts (by rfl)

private theorem leaf1475FlatSound : Sound leaf1475Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1475CertificateValid
    leaf1475InnerLogValid leaf1475CoversExact leaf1475LowerChecked

private noncomputable def leaf1476Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (19/256), chiHi := (5/64) }

private noncomputable def leaf1476Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435607/268435456) }, vSqrt := { lower := (8191/8192), upper := (699052/699039) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (336883479/268435456) }, upper := { exponent := 0, mantissa := (163/128) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi148LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1398091/1398078) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf1476InnerLog : WideLogData :=
  innerPair20Data

set_option maxRecDepth 1000000 in
private theorem leaf1476LocalValidity :
    LeafFacts leaf1476Box leaf1476Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1476Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (699052/699039) }) = true
      norm_num [leaf1476Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1476CertificateValid :
    WideCertificateValid leaf1476Box leaf1476Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi148ValidityFacts
    leaf1476LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1476CoverageChecked :
    coverageCheck (innerAD leaf1476Box) leaf1476InnerLog = true := by
  rfl'

private theorem leaf1476InnerLogValid :
    leaf1476InnerLog.Valid 8 (innerAD leaf1476Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint28PositiveFacts.valid leaf1476CoverageChecked

private noncomputable def leaf1476InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1476InputLogOnePlusV_eq :
    leaf1476InputLogOnePlusV = outerEnclosure 24
      (leaf1476Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1476RoundedFacts : LeafRoundedFacts 8
    leaf1476Certificate.logOnePlusV leaf1476InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1476InputLogOnePlusV_eq }

private noncomputable def leaf1476Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi148InputQChi innerPair20Input
    leaf1476InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1476LowerChecked :
    lowerCheck 24 leaf1476Box leaf1476Inputs = true := by
  rfl'

private theorem leaf1476CoversExact : CoversExact 8
    leaf1476Box leaf1476Certificate leaf1476InnerLog leaf1476Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi148RoundedFacts
    innerPair20RoundedFacts leaf1476RoundedFacts (by rfl)

private theorem leaf1476FlatSound : Sound leaf1476Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1476CertificateValid
    leaf1476InnerLogValid leaf1476CoversExact leaf1476LowerChecked

private noncomputable def leaf1477Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1477Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435603/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108992/67107751) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (336555823/268435456) }, upper := { exponent := 0, mantissa := (5209/4096) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216743/134215502) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf1477InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1477LocalValidity :
    LeafFacts leaf1477Box leaf1477Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1477Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108992/67107751) }) = true
      norm_num [leaf1477Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1477CertificateValid :
    WideCertificateValid leaf1477Box leaf1477Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi127ValidityFacts
    leaf1477LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1477CoverageChecked :
    coverageCheck (innerAD leaf1477Box) leaf1477InnerLog = true := by
  rfl'

private theorem leaf1477InnerLogValid :
    leaf1477InnerLog.Valid 8 (innerAD leaf1477Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1477CoverageChecked

private noncomputable def leaf1477InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1477InputLogOnePlusV_eq :
    leaf1477InputLogOnePlusV = outerEnclosure 24
      (leaf1477Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1477RoundedFacts : LeafRoundedFacts 8
    leaf1477Certificate.logOnePlusV leaf1477InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1477InputLogOnePlusV_eq }

private noncomputable def leaf1477Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi127InputQChi innerPair16Input
    leaf1477InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1477LowerChecked :
    lowerCheck 24 leaf1477Box leaf1477Inputs = true := by
  rfl'

private theorem leaf1477CoversExact : CoversExact 8
    leaf1477Box leaf1477Certificate leaf1477InnerLog leaf1477Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi127RoundedFacts
    innerPair16RoundedFacts leaf1477RoundedFacts (by rfl)

private theorem leaf1477FlatSound : Sound leaf1477Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1477CertificateValid
    leaf1477InnerLogValid leaf1477CoversExact leaf1477LowerChecked

private noncomputable def leaf1478Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1478Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435605/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554496/33553849) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (339963485/268435456) }, upper := { exponent := 0, mantissa := (2631/2048) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108345/67107698) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf1478InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1478LocalValidity :
    LeafFacts leaf1478Box leaf1478Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1478Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33553849) }) = true
      norm_num [leaf1478Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1478CertificateValid :
    WideCertificateValid leaf1478Box leaf1478Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi128ValidityFacts
    leaf1478LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1478CoverageChecked :
    coverageCheck (innerAD leaf1478Box) leaf1478InnerLog = true := by
  rfl'

private theorem leaf1478InnerLogValid :
    leaf1478InnerLog.Valid 8 (innerAD leaf1478Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1478CoverageChecked

private noncomputable def leaf1478InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814621/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1478InputLogOnePlusV_eq :
    leaf1478InputLogOnePlusV = outerEnclosure 24
      (leaf1478Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1478RoundedFacts : LeafRoundedFacts 8
    leaf1478Certificate.logOnePlusV leaf1478InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1478InputLogOnePlusV_eq }

private noncomputable def leaf1478Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi128InputQChi innerPair16Input
    leaf1478InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1478LowerChecked :
    lowerCheck 24 leaf1478Box leaf1478Inputs = true := by
  rfl'

private theorem leaf1478CoversExact : CoversExact 8
    leaf1478Box leaf1478Certificate leaf1478InnerLog leaf1478Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi128RoundedFacts
    innerPair16RoundedFacts leaf1478RoundedFacts (by rfl)

private theorem leaf1478FlatSound : Sound leaf1478Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1478CertificateValid
    leaf1478InnerLogValid leaf1478CoversExact leaf1478LowerChecked

private noncomputable def leaf1479Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1479Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435605/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554496/33553865) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (337866461/268435456) }, upper := { exponent := 0, mantissa := (2615/2048) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108361/67107730) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf1479InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1479LocalValidity :
    LeafFacts leaf1479Box leaf1479Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1479Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554496/33553865) }) = true
      norm_num [leaf1479Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1479CertificateValid :
    WideCertificateValid leaf1479Box leaf1479Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi127ValidityFacts
    leaf1479LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1479CoverageChecked :
    coverageCheck (innerAD leaf1479Box) leaf1479InnerLog = true := by
  rfl'

private theorem leaf1479InnerLogValid :
    leaf1479InnerLog.Valid 8 (innerAD leaf1479Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1479CoverageChecked

private noncomputable def leaf1479InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814619/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1479InputLogOnePlusV_eq :
    leaf1479InputLogOnePlusV = outerEnclosure 24
      (leaf1479Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1479RoundedFacts : LeafRoundedFacts 8
    leaf1479Certificate.logOnePlusV leaf1479InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1479InputLogOnePlusV_eq }

private noncomputable def leaf1479Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi127InputQChi innerPair16Input
    leaf1479InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1479LowerChecked :
    lowerCheck 24 leaf1479Box leaf1479Inputs = true := by
  rfl'

private theorem leaf1479CoversExact : CoversExact 8
    leaf1479Box leaf1479Certificate leaf1479InnerLog leaf1479Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi127RoundedFacts
    innerPair16RoundedFacts leaf1479RoundedFacts (by rfl)

private theorem leaf1479FlatSound : Sound leaf1479Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1479CertificateValid
    leaf1479InnerLogValid leaf1479CoversExact leaf1479LowerChecked

private noncomputable def leaf1480Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1480Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435607/268435456) }, vSqrt := { lower := (65529/65536), upper := (16777248/16776919) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (341339655/268435456) }, upper := { exponent := 0, mantissa := (1321/1024) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554167/33553838) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf1480InnerLog : WideLogData :=
  innerPair389Data

set_option maxRecDepth 1000000 in
private theorem leaf1480LocalValidity :
    LeafFacts leaf1480Box leaf1480Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1480Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777248/16776919) }) = true
      norm_num [leaf1480Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1480CertificateValid :
    WideCertificateValid leaf1480Box leaf1480Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi128ValidityFacts
    leaf1480LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1480CoverageChecked :
    coverageCheck (innerAD leaf1480Box) leaf1480InnerLog = true := by
  rfl'

private theorem leaf1480InnerLogValid :
    leaf1480InnerLog.Valid 8 (innerAD leaf1480Box) :=
  wideLogDataValid_of_cachedCheck endpoint100PositiveFacts
    endpoint29PositiveFacts.valid leaf1480CoverageChecked

private noncomputable def leaf1480InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1480InputLogOnePlusV_eq :
    leaf1480InputLogOnePlusV = outerEnclosure 24
      (leaf1480Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1480RoundedFacts : LeafRoundedFacts 8
    leaf1480Certificate.logOnePlusV leaf1480InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1480InputLogOnePlusV_eq }

private noncomputable def leaf1480Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi128InputQChi innerPair389Input
    leaf1480InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1480LowerChecked :
    lowerCheck 24 leaf1480Box leaf1480Inputs = true := by
  rfl'

private theorem leaf1480CoversExact : CoversExact 8
    leaf1480Box leaf1480Certificate leaf1480InnerLog leaf1480Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi128RoundedFacts
    innerPair389RoundedFacts leaf1480RoundedFacts (by rfl)

private theorem leaf1480FlatSound : Sound leaf1480Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1480CertificateValid
    leaf1480InnerLogValid leaf1480CoversExact leaf1480LowerChecked

private noncomputable def leaf1481Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1481Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435607/268435456) }, vSqrt := { lower := (65529/65536), upper := (22369664/22369215) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (343371147/268435456) }, upper := { exponent := 0, mantissa := (5315/4096) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (44738879/44738430) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf1481InnerLog : WideLogData :=
  innerPair438Data

set_option maxRecDepth 1000000 in
private theorem leaf1481LocalValidity :
    LeafFacts leaf1481Box leaf1481Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1481Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22369664/22369215) }) = true
      norm_num [leaf1481Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1481CertificateValid :
    WideCertificateValid leaf1481Box leaf1481Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi129ValidityFacts
    leaf1481LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1481CoverageChecked :
    coverageCheck (innerAD leaf1481Box) leaf1481InnerLog = true := by
  rfl'

private theorem leaf1481InnerLogValid :
    leaf1481InnerLog.Valid 8 (innerAD leaf1481Box) :=
  wideLogDataValid_of_cachedCheck endpoint148PositiveFacts
    endpoint149PositiveFacts.valid leaf1481CoverageChecked

private noncomputable def leaf1481InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1481InputLogOnePlusV_eq :
    leaf1481InputLogOnePlusV = outerEnclosure 24
      (leaf1481Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1481RoundedFacts : LeafRoundedFacts 8
    leaf1481Certificate.logOnePlusV leaf1481InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1481InputLogOnePlusV_eq }

private noncomputable def leaf1481Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi129InputQChi innerPair438Input
    leaf1481InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1481LowerChecked :
    lowerCheck 24 leaf1481Box leaf1481Inputs = true := by
  rfl'

private theorem leaf1481CoversExact : CoversExact 8
    leaf1481Box leaf1481Certificate leaf1481InnerLog leaf1481Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi129RoundedFacts
    innerPair438RoundedFacts leaf1481RoundedFacts (by rfl)

private theorem leaf1481FlatSound : Sound leaf1481Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1481CertificateValid
    leaf1481InnerLogValid leaf1481CoversExact leaf1481LowerChecked

private noncomputable def leaf1482Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1482Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871169/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776901) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (693590433/536870912) }, upper := { exponent := 0, mantissa := (1339/1024) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554133/33553802) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf1482InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1482LocalValidity :
    LeafFacts leaf1482Box leaf1482Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1482Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776901) }) = true
      norm_num [leaf1482Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1482CertificateValid :
    WideCertificateValid leaf1482Box leaf1482Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi130ValidityFacts
    leaf1482LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1482CoverageChecked :
    coverageCheck (innerAD leaf1482Box) leaf1482InnerLog = true := by
  rfl'

private theorem leaf1482InnerLogValid :
    leaf1482InnerLog.Valid 8 (innerAD leaf1482Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1482CoverageChecked

private noncomputable def leaf1482InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814623/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1482InputLogOnePlusV_eq :
    leaf1482InputLogOnePlusV = outerEnclosure 24
      (leaf1482Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1482RoundedFacts : LeafRoundedFacts 8
    leaf1482Certificate.logOnePlusV leaf1482InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1482InputLogOnePlusV_eq }

private noncomputable def leaf1482Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi130InputQChi innerPair16Input
    leaf1482InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1482LowerChecked :
    lowerCheck 24 leaf1482Box leaf1482Inputs = true := by
  rfl'

private theorem leaf1482CoversExact : CoversExact 8
    leaf1482Box leaf1482Certificate leaf1482InnerLog leaf1482Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi130RoundedFacts
    innerPair16RoundedFacts leaf1482RoundedFacts (by rfl)

private theorem leaf1482FlatSound : Sound leaf1482Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1482CertificateValid
    leaf1482InnerLogValid leaf1482CoversExact leaf1482LowerChecked

private noncomputable def leaf1483Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1483Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871171/536870912) }, vSqrt := { lower := (65529/65536), upper := (8388616/8388449) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (695097667/536870912) }, upper := { exponent := 0, mantissa := (671/512) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777065/16776898) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf1483InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1483LocalValidity :
    LeafFacts leaf1483Box leaf1483Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1483Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388616/8388449) }) = true
      norm_num [leaf1483Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1483CertificateValid :
    WideCertificateValid leaf1483Box leaf1483Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi130ValidityFacts
    leaf1483LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1483CoverageChecked :
    coverageCheck (innerAD leaf1483Box) leaf1483InnerLog = true := by
  rfl'

private theorem leaf1483InnerLogValid :
    leaf1483InnerLog.Valid 8 (innerAD leaf1483Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1483CoverageChecked

private noncomputable def leaf1483InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf1483InputLogOnePlusV_eq :
    leaf1483InputLogOnePlusV = outerEnclosure 24
      (leaf1483Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1483RoundedFacts : LeafRoundedFacts 8
    leaf1483Certificate.logOnePlusV leaf1483InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1483InputLogOnePlusV_eq }

private noncomputable def leaf1483Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi130InputQChi innerPair16Input
    leaf1483InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1483LowerChecked :
    lowerCheck 24 leaf1483Box leaf1483Inputs = true := by
  rfl'

private theorem leaf1483CoversExact : CoversExact 8
    leaf1483Box leaf1483Certificate leaf1483InnerLog leaf1483Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi130RoundedFacts
    innerPair16RoundedFacts leaf1483RoundedFacts (by rfl)

private theorem leaf1483FlatSound : Sound leaf1483Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1483CertificateValid
    leaf1483InnerLogValid leaf1483CoversExact leaf1483LowerChecked

private noncomputable def leaf1484Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1484Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871171/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134215267) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (689658511/536870912) }, upper := { exponent := 0, mantissa := (10653/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268433123/268430534) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf1484InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1484LocalValidity :
    LeafFacts leaf1484Box leaf1484Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1484Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134215267) }) = true
      norm_num [leaf1484Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1484CertificateValid :
    WideCertificateValid leaf1484Box leaf1484Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi129ValidityFacts
    leaf1484LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1484CoverageChecked :
    coverageCheck (innerAD leaf1484Box) leaf1484InnerLog = true := by
  rfl'

private theorem leaf1484InnerLogValid :
    leaf1484InnerLog.Valid 8 (innerAD leaf1484Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1484CoverageChecked

private noncomputable def leaf1484InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629243/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1484InputLogOnePlusV_eq :
    leaf1484InputLogOnePlusV = outerEnclosure 24
      (leaf1484Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1484RoundedFacts : LeafRoundedFacts 8
    leaf1484Certificate.logOnePlusV leaf1484InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1484InputLogOnePlusV_eq }

private noncomputable def leaf1484Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi129InputQChi innerPair16Input
    leaf1484InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1484LowerChecked :
    lowerCheck 24 leaf1484Box leaf1484Inputs = true := by
  rfl'

private theorem leaf1484CoversExact : CoversExact 8
    leaf1484Box leaf1484Certificate leaf1484InnerLog leaf1484Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi129RoundedFacts
    innerPair16RoundedFacts leaf1484RoundedFacts (by rfl)

private theorem leaf1484FlatSound : Sound leaf1484Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1484CertificateValid
    leaf1484InnerLogValid leaf1484CoversExact leaf1484LowerChecked

private noncomputable def leaf1485Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1485Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871173/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553811) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (691100213/536870912) }, upper := { exponent := 0, mantissa := (2669/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108275/67107622) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf1485InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1485LocalValidity :
    LeafFacts leaf1485Box leaf1485Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1485Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553811) }) = true
      norm_num [leaf1485Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1485CertificateValid :
    WideCertificateValid leaf1485Box leaf1485Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi129ValidityFacts
    leaf1485LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1485CoverageChecked :
    coverageCheck (innerAD leaf1485Box) leaf1485InnerLog = true := by
  rfl'

private theorem leaf1485InnerLogValid :
    leaf1485InnerLog.Valid 8 (innerAD leaf1485Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1485CoverageChecked

private noncomputable def leaf1485InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907311/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1485InputLogOnePlusV_eq :
    leaf1485InputLogOnePlusV = outerEnclosure 24
      (leaf1485Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1485RoundedFacts : LeafRoundedFacts 8
    leaf1485Certificate.logOnePlusV leaf1485InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1485InputLogOnePlusV_eq }

private noncomputable def leaf1485Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi129InputQChi innerPair16Input
    leaf1485InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1485LowerChecked :
    lowerCheck 24 leaf1485Box leaf1485Inputs = true := by
  rfl'

private theorem leaf1485CoversExact : CoversExact 8
    leaf1485Box leaf1485Certificate leaf1485InnerLog leaf1485Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi129RoundedFacts
    innerPair16RoundedFacts leaf1485RoundedFacts (by rfl)

private theorem leaf1485FlatSound : Sound leaf1485Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1485CertificateValid
    leaf1485InnerLogValid leaf1485CoversExact leaf1485LowerChecked

private noncomputable def leaf1486Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1486Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871173/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776895) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (696604901/536870912) }, upper := { exponent := 0, mantissa := (1345/1024) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554127/33553790) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf1486InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1486LocalValidity :
    LeafFacts leaf1486Box leaf1486Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1486Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776895) }) = true
      norm_num [leaf1486Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1486CertificateValid :
    WideCertificateValid leaf1486Box leaf1486Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi130ValidityFacts
    leaf1486LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1486CoverageChecked :
    coverageCheck (innerAD leaf1486Box) leaf1486InnerLog = true := by
  rfl'

private theorem leaf1486InnerLogValid :
    leaf1486InnerLog.Valid 8 (innerAD leaf1486Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1486CoverageChecked

private noncomputable def leaf1486InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1486InputLogOnePlusV_eq :
    leaf1486InputLogOnePlusV = outerEnclosure 24
      (leaf1486Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1486RoundedFacts : LeafRoundedFacts 8
    leaf1486Certificate.logOnePlusV leaf1486InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1486InputLogOnePlusV_eq }

private noncomputable def leaf1486Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi130InputQChi innerPair17Input
    leaf1486InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1486LowerChecked :
    lowerCheck 24 leaf1486Box leaf1486Inputs = true := by
  rfl'

private theorem leaf1486CoversExact : CoversExact 8
    leaf1486Box leaf1486Certificate leaf1486InnerLog leaf1486Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi130RoundedFacts
    innerPair17RoundedFacts leaf1486RoundedFacts (by rfl)

private theorem leaf1486FlatSound : Sound leaf1486Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1486CertificateValid
    leaf1486InnerLogValid leaf1486CoversExact leaf1486LowerChecked

private noncomputable def leaf1487Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1487Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871175/536870912) }, vSqrt := { lower := (65529/65536), upper := (246724/246719) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (698112135/536870912) }, upper := { exponent := 0, mantissa := (337/256) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (493443/493438) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf1487InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1487LocalValidity :
    LeafFacts leaf1487Box leaf1487Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1487Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (246724/246719) }) = true
      norm_num [leaf1487Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1487CertificateValid :
    WideCertificateValid leaf1487Box leaf1487Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi130ValidityFacts
    leaf1487LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1487CoverageChecked :
    coverageCheck (innerAD leaf1487Box) leaf1487InnerLog = true := by
  rfl'

private theorem leaf1487InnerLogValid :
    leaf1487InnerLog.Valid 8 (innerAD leaf1487Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1487CoverageChecked

private noncomputable def leaf1487InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1487InputLogOnePlusV_eq :
    leaf1487InputLogOnePlusV = outerEnclosure 24
      (leaf1487Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1487RoundedFacts : LeafRoundedFacts 8
    leaf1487Certificate.logOnePlusV leaf1487InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1487InputLogOnePlusV_eq }

private noncomputable def leaf1487Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi130InputQChi innerPair17Input
    leaf1487InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1487LowerChecked :
    lowerCheck 24 leaf1487Box leaf1487Inputs = true := by
  rfl'

private theorem leaf1487CoversExact : CoversExact 8
    leaf1487Box leaf1487Certificate leaf1487InnerLog leaf1487Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi130RoundedFacts
    innerPair17RoundedFacts leaf1487RoundedFacts (by rfl)

private theorem leaf1487FlatSound : Sound leaf1487Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1487CertificateValid
    leaf1487InnerLogValid leaf1487CoversExact leaf1487LowerChecked

private noncomputable def leaf1488Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1488Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435607/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108992/67107709) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (339177099/268435456) }, upper := { exponent := 0, mantissa := (5251/4096) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216701/134215418) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf1488InnerLog : WideLogData :=
  innerPair439Data

set_option maxRecDepth 1000000 in
private theorem leaf1488LocalValidity :
    LeafFacts leaf1488Box leaf1488Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1488Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108992/67107709) }) = true
      norm_num [leaf1488Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1488CertificateValid :
    WideCertificateValid leaf1488Box leaf1488Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi127ValidityFacts
    leaf1488LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1488CoverageChecked :
    coverageCheck (innerAD leaf1488Box) leaf1488InnerLog = true := by
  rfl'

private theorem leaf1488InnerLogValid :
    leaf1488InnerLog.Valid 8 (innerAD leaf1488Box) :=
  wideLogDataValid_of_cachedCheck endpoint150PositiveFacts
    endpoint143PositiveFacts.valid leaf1488CoverageChecked

private noncomputable def leaf1488InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1488InputLogOnePlusV_eq :
    leaf1488InputLogOnePlusV = outerEnclosure 24
      (leaf1488Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1488RoundedFacts : LeafRoundedFacts 8
    leaf1488Certificate.logOnePlusV leaf1488InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1488InputLogOnePlusV_eq }

private noncomputable def leaf1488Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi127InputQChi innerPair439Input
    leaf1488InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1488LowerChecked :
    lowerCheck 24 leaf1488Box leaf1488Inputs = true := by
  rfl'

private theorem leaf1488CoversExact : CoversExact 8
    leaf1488Box leaf1488Certificate leaf1488InnerLog leaf1488Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi127RoundedFacts
    innerPair439RoundedFacts leaf1488RoundedFacts (by rfl)

private theorem leaf1488FlatSound : Sound leaf1488Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1488CertificateValid
    leaf1488InnerLogValid leaf1488CoversExact leaf1488LowerChecked

private noncomputable def leaf1489Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1489Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871173/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107665) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (685464461/536870912) }, upper := { exponent := 0, mantissa := (5295/4096) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216593/134215330) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf1489InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1489LocalValidity :
    LeafFacts leaf1489Box leaf1489Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1489Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107665) }) = true
      norm_num [leaf1489Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1489CertificateValid :
    WideCertificateValid leaf1489Box leaf1489Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi128ValidityFacts
    leaf1489LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1489CoverageChecked :
    coverageCheck (innerAD leaf1489Box) leaf1489InnerLog = true := by
  rfl'

private theorem leaf1489InnerLogValid :
    leaf1489InnerLog.Valid 8 (innerAD leaf1489Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1489CoverageChecked

private noncomputable def leaf1489InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629239/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1489InputLogOnePlusV_eq :
    leaf1489InputLogOnePlusV = outerEnclosure 24
      (leaf1489Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1489RoundedFacts : LeafRoundedFacts 8
    leaf1489Certificate.logOnePlusV leaf1489InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1489InputLogOnePlusV_eq }

private noncomputable def leaf1489Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi128InputQChi innerPair16Input
    leaf1489InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1489LowerChecked :
    lowerCheck 24 leaf1489Box leaf1489Inputs = true := by
  rfl'

private theorem leaf1489CoversExact : CoversExact 8
    leaf1489Box leaf1489Certificate leaf1489InnerLog leaf1489Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi128RoundedFacts
    innerPair16RoundedFacts leaf1489RoundedFacts (by rfl)

private theorem leaf1489FlatSound : Sound leaf1489Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1489CertificateValid
    leaf1489InnerLogValid leaf1489CoversExact leaf1489LowerChecked

private noncomputable def leaf1490Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1490Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871175/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553827) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (686840631/536870912) }, upper := { exponent := 0, mantissa := (2653/2048) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108291/67107654) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf1490InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1490LocalValidity :
    LeafFacts leaf1490Box leaf1490Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1490Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553827) }) = true
      norm_num [leaf1490Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1490CertificateValid :
    WideCertificateValid leaf1490Box leaf1490Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi128ValidityFacts
    leaf1490LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1490CoverageChecked :
    coverageCheck (innerAD leaf1490Box) leaf1490InnerLog = true := by
  rfl'

private theorem leaf1490InnerLogValid :
    leaf1490InnerLog.Valid 8 (innerAD leaf1490Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1490CoverageChecked

private noncomputable def leaf1490InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1490InputLogOnePlusV_eq :
    leaf1490InputLogOnePlusV = outerEnclosure 24
      (leaf1490Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1490RoundedFacts : LeafRoundedFacts 8
    leaf1490Certificate.logOnePlusV leaf1490InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1490InputLogOnePlusV_eq }

private noncomputable def leaf1490Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi128InputQChi innerPair16Input
    leaf1490InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1490LowerChecked :
    lowerCheck 24 leaf1490Box leaf1490Inputs = true := by
  rfl'

private theorem leaf1490CoversExact : CoversExact 8
    leaf1490Box leaf1490Certificate leaf1490InnerLog leaf1490Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi128RoundedFacts
    innerPair16RoundedFacts leaf1490RoundedFacts (by rfl)

private theorem leaf1490FlatSound : Sound leaf1490Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1490CertificateValid
    leaf1490InnerLogValid leaf1490CoversExact leaf1490LowerChecked

private noncomputable def leaf1491Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1491Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871175/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134215397) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (681008283/536870912) }, upper := { exponent := 0, mantissa := (10523/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268433253/268430794) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf1491InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1491LocalValidity :
    LeafFacts leaf1491Box leaf1491Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1491Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134215397) }) = true
      norm_num [leaf1491Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1491CertificateValid :
    WideCertificateValid leaf1491Box leaf1491Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi127ValidityFacts
    leaf1491LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1491CoverageChecked :
    coverageCheck (innerAD leaf1491Box) leaf1491InnerLog = true := by
  rfl'

private theorem leaf1491InnerLogValid :
    leaf1491InnerLog.Valid 8 (innerAD leaf1491Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1491CoverageChecked

private noncomputable def leaf1491InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1491InputLogOnePlusV_eq :
    leaf1491InputLogOnePlusV = outerEnclosure 24
      (leaf1491Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1491RoundedFacts : LeafRoundedFacts 8
    leaf1491Certificate.logOnePlusV leaf1491InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1491InputLogOnePlusV_eq }

private noncomputable def leaf1491Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi127InputQChi innerPair16Input
    leaf1491InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1491LowerChecked :
    lowerCheck 24 leaf1491Box leaf1491Inputs = true := by
  rfl'

private theorem leaf1491CoversExact : CoversExact 8
    leaf1491Box leaf1491Certificate leaf1491InnerLog leaf1491Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi127RoundedFacts
    innerPair16RoundedFacts leaf1491RoundedFacts (by rfl)

private theorem leaf1491FlatSound : Sound leaf1491Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1491CertificateValid
    leaf1491InnerLogValid leaf1491CoversExact leaf1491LowerChecked

private noncomputable def leaf1492Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (5/64), chiHi := (21/256) }

private noncomputable def leaf1492Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871177/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388461) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (682318921/536870912) }, upper := { exponent := 0, mantissa := (659/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi127LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777077/16776922) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf1492InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1492LocalValidity :
    LeafFacts leaf1492Box leaf1492Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1492Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388461) }) = true
      norm_num [leaf1492Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1492CertificateValid :
    WideCertificateValid leaf1492Box leaf1492Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi127ValidityFacts
    leaf1492LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1492CoverageChecked :
    coverageCheck (innerAD leaf1492Box) leaf1492InnerLog = true := by
  rfl'

private theorem leaf1492InnerLogValid :
    leaf1492InnerLog.Valid 8 (innerAD leaf1492Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1492CoverageChecked

private noncomputable def leaf1492InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907309/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1492InputLogOnePlusV_eq :
    leaf1492InputLogOnePlusV = outerEnclosure 24
      (leaf1492Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1492RoundedFacts : LeafRoundedFacts 8
    leaf1492Certificate.logOnePlusV leaf1492InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1492InputLogOnePlusV_eq }

private noncomputable def leaf1492Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi127InputQChi innerPair16Input
    leaf1492InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1492LowerChecked :
    lowerCheck 24 leaf1492Box leaf1492Inputs = true := by
  rfl'

private theorem leaf1492CoversExact : CoversExact 8
    leaf1492Box leaf1492Certificate leaf1492InnerLog leaf1492Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi127RoundedFacts
    innerPair16RoundedFacts leaf1492RoundedFacts (by rfl)

private theorem leaf1492FlatSound : Sound leaf1492Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1492CertificateValid
    leaf1492InnerLogValid leaf1492CoversExact leaf1492LowerChecked

private noncomputable def leaf1493Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1493Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871177/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107643) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (688216801/536870912) }, upper := { exponent := 0, mantissa := (5317/4096) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216571/134215286) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf1493InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1493LocalValidity :
    LeafFacts leaf1493Box leaf1493Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1493Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107643) }) = true
      norm_num [leaf1493Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1493CertificateValid :
    WideCertificateValid leaf1493Box leaf1493Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi128ValidityFacts
    leaf1493LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1493CoverageChecked :
    coverageCheck (innerAD leaf1493Box) leaf1493InnerLog = true := by
  rfl'

private theorem leaf1493InnerLogValid :
    leaf1493InnerLog.Valid 8 (innerAD leaf1493Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1493CoverageChecked

private noncomputable def leaf1493InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629241/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1493InputLogOnePlusV_eq :
    leaf1493InputLogOnePlusV = outerEnclosure 24
      (leaf1493Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1493RoundedFacts : LeafRoundedFacts 8
    leaf1493Certificate.logOnePlusV leaf1493InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1493InputLogOnePlusV_eq }

private noncomputable def leaf1493Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi128InputQChi innerPair16Input
    leaf1493InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1493LowerChecked :
    lowerCheck 24 leaf1493Box leaf1493Inputs = true := by
  rfl'

private theorem leaf1493CoversExact : CoversExact 8
    leaf1493Box leaf1493Certificate leaf1493InnerLog leaf1493Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi128RoundedFacts
    innerPair16RoundedFacts leaf1493RoundedFacts (by rfl)

private theorem leaf1493FlatSound : Sound leaf1493Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1493CertificateValid
    leaf1493InnerLogValid leaf1493CoversExact leaf1493LowerChecked

private noncomputable def leaf1494Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (21/256), chiHi := (11/128) }

private noncomputable def leaf1494Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871179/536870912) }, vSqrt := { lower := (8191/8192), upper := (4194308/4194227) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (689592971/536870912) }, upper := { exponent := 0, mantissa := (333/256) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi128LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388535/8388454) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf1494InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1494LocalValidity :
    LeafFacts leaf1494Box leaf1494Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1494Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194308/4194227) }) = true
      norm_num [leaf1494Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1494CertificateValid :
    WideCertificateValid leaf1494Box leaf1494Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi128ValidityFacts
    leaf1494LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1494CoverageChecked :
    coverageCheck (innerAD leaf1494Box) leaf1494InnerLog = true := by
  rfl'

private theorem leaf1494InnerLogValid :
    leaf1494InnerLog.Valid 8 (innerAD leaf1494Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1494CoverageChecked

private noncomputable def leaf1494InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629243/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1494InputLogOnePlusV_eq :
    leaf1494InputLogOnePlusV = outerEnclosure 24
      (leaf1494Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1494RoundedFacts : LeafRoundedFacts 8
    leaf1494Certificate.logOnePlusV leaf1494InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1494InputLogOnePlusV_eq }

private noncomputable def leaf1494Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi128InputQChi innerPair16Input
    leaf1494InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1494LowerChecked :
    lowerCheck 24 leaf1494Box leaf1494Inputs = true := by
  rfl'

private theorem leaf1494CoversExact : CoversExact 8
    leaf1494Box leaf1494Certificate leaf1494InnerLog leaf1494Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi128RoundedFacts
    innerPair16RoundedFacts leaf1494RoundedFacts (by rfl)

private theorem leaf1494FlatSound : Sound leaf1494Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1494CertificateValid
    leaf1494InnerLogValid leaf1494CoversExact leaf1494LowerChecked

private noncomputable def leaf1495Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1495Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871175/536870912) }, vSqrt := { lower := (65529/65536), upper := (7895168/7895013) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (692541915/536870912) }, upper := { exponent := 0, mantissa := (10699/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (15790181/15790026) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf1495InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1495LocalValidity :
    LeafFacts leaf1495Box leaf1495Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1495Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (7895168/7895013) }) = true
      norm_num [leaf1495Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1495CertificateValid :
    WideCertificateValid leaf1495Box leaf1495Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi129ValidityFacts
    leaf1495LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1495CoverageChecked :
    coverageCheck (innerAD leaf1495Box) leaf1495InnerLog = true := by
  rfl'

private theorem leaf1495InnerLogValid :
    leaf1495InnerLog.Valid 8 (innerAD leaf1495Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1495CoverageChecked

private noncomputable def leaf1495InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1495InputLogOnePlusV_eq :
    leaf1495InputLogOnePlusV = outerEnclosure 24
      (leaf1495Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1495RoundedFacts : LeafRoundedFacts 8
    leaf1495Certificate.logOnePlusV leaf1495InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1495InputLogOnePlusV_eq }

private noncomputable def leaf1495Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi129InputQChi innerPair16Input
    leaf1495InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1495LowerChecked :
    lowerCheck 24 leaf1495Box leaf1495Inputs = true := by
  rfl'

private theorem leaf1495CoversExact : CoversExact 8
    leaf1495Box leaf1495Certificate leaf1495InnerLog leaf1495Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi129RoundedFacts
    innerPair16RoundedFacts leaf1495RoundedFacts (by rfl)

private theorem leaf1495FlatSound : Sound leaf1495Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1495CertificateValid
    leaf1495InnerLogValid leaf1495CoversExact leaf1495LowerChecked

private noncomputable def leaf1496Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1496Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871177/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107599) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (693983617/536870912) }, upper := { exponent := 0, mantissa := (5361/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216527/134215198) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf1496InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1496LocalValidity :
    LeafFacts leaf1496Box leaf1496Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1496Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107599) }) = true
      norm_num [leaf1496Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1496CertificateValid :
    WideCertificateValid leaf1496Box leaf1496Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi129ValidityFacts
    leaf1496LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1496CoverageChecked :
    coverageCheck (innerAD leaf1496Box) leaf1496InnerLog = true := by
  rfl'

private theorem leaf1496InnerLogValid :
    leaf1496InnerLog.Valid 8 (innerAD leaf1496Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1496CoverageChecked

private noncomputable def leaf1496InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1496InputLogOnePlusV_eq :
    leaf1496InputLogOnePlusV = outerEnclosure 24
      (leaf1496Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1496RoundedFacts : LeafRoundedFacts 8
    leaf1496Certificate.logOnePlusV leaf1496InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1496InputLogOnePlusV_eq }

private noncomputable def leaf1496Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi129InputQChi innerPair16Input
    leaf1496InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1496LowerChecked :
    lowerCheck 24 leaf1496Box leaf1496Inputs = true := by
  rfl'

private theorem leaf1496CoversExact : CoversExact 8
    leaf1496Box leaf1496Certificate leaf1496InnerLog leaf1496Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi129RoundedFacts
    innerPair16RoundedFacts leaf1496RoundedFacts (by rfl)

private theorem leaf1496FlatSound : Sound leaf1496Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1496CertificateValid
    leaf1496InnerLogValid leaf1496CoversExact leaf1496LowerChecked

private noncomputable def leaf1497Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1497Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871177/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776889) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (699619369/536870912) }, upper := { exponent := 0, mantissa := (1351/1024) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554121/33553778) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf1497InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1497LocalValidity :
    LeafFacts leaf1497Box leaf1497Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1497Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776889) }) = true
      norm_num [leaf1497Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1497CertificateValid :
    WideCertificateValid leaf1497Box leaf1497Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi130ValidityFacts
    leaf1497LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1497CoverageChecked :
    coverageCheck (innerAD leaf1497Box) leaf1497InnerLog = true := by
  rfl'

private theorem leaf1497InnerLogValid :
    leaf1497InnerLog.Valid 8 (innerAD leaf1497Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1497CoverageChecked

private noncomputable def leaf1497InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907313/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1497InputLogOnePlusV_eq :
    leaf1497InputLogOnePlusV = outerEnclosure 24
      (leaf1497Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1497RoundedFacts : LeafRoundedFacts 8
    leaf1497Certificate.logOnePlusV leaf1497InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1497InputLogOnePlusV_eq }

private noncomputable def leaf1497Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi130InputQChi innerPair17Input
    leaf1497InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1497LowerChecked :
    lowerCheck 24 leaf1497Box leaf1497Inputs = true := by
  rfl'

private theorem leaf1497CoversExact : CoversExact 8
    leaf1497Box leaf1497Certificate leaf1497InnerLog leaf1497Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi130RoundedFacts
    innerPair17RoundedFacts leaf1497RoundedFacts (by rfl)

private theorem leaf1497FlatSound : Sound leaf1497Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1497CertificateValid
    leaf1497InnerLogValid leaf1497CoversExact leaf1497LowerChecked

private noncomputable def leaf1498Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1498Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871179/536870912) }, vSqrt := { lower := (65529/65536), upper := (8388616/8388443) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (701126603/536870912) }, upper := { exponent := 0, mantissa := (677/512) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777059/16776886) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf1498InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1498LocalValidity :
    LeafFacts leaf1498Box leaf1498Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1498Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388616/8388443) }) = true
      norm_num [leaf1498Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1498CertificateValid :
    WideCertificateValid leaf1498Box leaf1498Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi130ValidityFacts
    leaf1498LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1498CoverageChecked :
    coverageCheck (innerAD leaf1498Box) leaf1498InnerLog = true := by
  rfl'

private theorem leaf1498InnerLogValid :
    leaf1498InnerLog.Valid 8 (innerAD leaf1498Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1498CoverageChecked

private noncomputable def leaf1498InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1498InputLogOnePlusV_eq :
    leaf1498InputLogOnePlusV = outerEnclosure 24
      (leaf1498Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1498RoundedFacts : LeafRoundedFacts 8
    leaf1498Certificate.logOnePlusV leaf1498InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1498InputLogOnePlusV_eq }

private noncomputable def leaf1498Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi130InputQChi innerPair17Input
    leaf1498InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1498LowerChecked :
    lowerCheck 24 leaf1498Box leaf1498Inputs = true := by
  rfl'

private theorem leaf1498CoversExact : CoversExact 8
    leaf1498Box leaf1498Certificate leaf1498InnerLog leaf1498Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi130RoundedFacts
    innerPair17RoundedFacts leaf1498RoundedFacts (by rfl)

private theorem leaf1498FlatSound : Sound leaf1498Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1498CertificateValid
    leaf1498InnerLogValid leaf1498CoversExact leaf1498LowerChecked

private noncomputable def leaf1499Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1499Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871179/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134215175) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (695425319/536870912) }, upper := { exponent := 0, mantissa := (10745/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268433031/268430350) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf1499InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf1499LocalValidity :
    LeafFacts leaf1499Box leaf1499Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1499Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134215175) }) = true
      norm_num [leaf1499Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1499CertificateValid :
    WideCertificateValid leaf1499Box leaf1499Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi129ValidityFacts
    leaf1499LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1499CoverageChecked :
    coverageCheck (innerAD leaf1499Box) leaf1499InnerLog = true := by
  rfl'

private theorem leaf1499InnerLogValid :
    leaf1499InnerLog.Valid 8 (innerAD leaf1499Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf1499CoverageChecked

private noncomputable def leaf1499InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf1499InputLogOnePlusV_eq :
    leaf1499InputLogOnePlusV = outerEnclosure 24
      (leaf1499Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1499RoundedFacts : LeafRoundedFacts 8
    leaf1499Certificate.logOnePlusV leaf1499InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1499InputLogOnePlusV_eq }

private noncomputable def leaf1499Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi129InputQChi innerPair16Input
    leaf1499InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1499LowerChecked :
    lowerCheck 24 leaf1499Box leaf1499Inputs = true := by
  rfl'

private theorem leaf1499CoversExact : CoversExact 8
    leaf1499Box leaf1499Certificate leaf1499InnerLog leaf1499Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi129RoundedFacts
    innerPair16RoundedFacts leaf1499RoundedFacts (by rfl)

private theorem leaf1499FlatSound : Sound leaf1499Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1499CertificateValid
    leaf1499InnerLogValid leaf1499CoversExact leaf1499LowerChecked

private noncomputable def leaf1500Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (11/128), chiHi := (23/256) }

private noncomputable def leaf1500Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871181/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388447) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (696867021/536870912) }, upper := { exponent := 0, mantissa := (673/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi129LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777063/16776894) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf1500InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1500LocalValidity :
    LeafFacts leaf1500Box leaf1500Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1500Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388447) }) = true
      norm_num [leaf1500Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1500CertificateValid :
    WideCertificateValid leaf1500Box leaf1500Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi129ValidityFacts
    leaf1500LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1500CoverageChecked :
    coverageCheck (innerAD leaf1500Box) leaf1500InnerLog = true := by
  rfl'

private theorem leaf1500InnerLogValid :
    leaf1500InnerLog.Valid 8 (innerAD leaf1500Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1500CoverageChecked

private noncomputable def leaf1500InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1500InputLogOnePlusV_eq :
    leaf1500InputLogOnePlusV = outerEnclosure 24
      (leaf1500Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1500RoundedFacts : LeafRoundedFacts 8
    leaf1500Certificate.logOnePlusV leaf1500InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1500InputLogOnePlusV_eq }

private noncomputable def leaf1500Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi129InputQChi innerPair17Input
    leaf1500InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1500LowerChecked :
    lowerCheck 24 leaf1500Box leaf1500Inputs = true := by
  rfl'

private theorem leaf1500CoversExact : CoversExact 8
    leaf1500Box leaf1500Certificate leaf1500InnerLog leaf1500Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi129RoundedFacts
    innerPair17RoundedFacts leaf1500RoundedFacts (by rfl)

private theorem leaf1500FlatSound : Sound leaf1500Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1500CertificateValid
    leaf1500InnerLogValid leaf1500CoversExact leaf1500LowerChecked

private noncomputable def leaf1501Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1501Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871181/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776883) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (702633837/536870912) }, upper := { exponent := 0, mantissa := (1357/1024) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554115/33553766) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf1501InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1501LocalValidity :
    LeafFacts leaf1501Box leaf1501Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1501Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776883) }) = true
      norm_num [leaf1501Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1501CertificateValid :
    WideCertificateValid leaf1501Box leaf1501Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi130ValidityFacts
    leaf1501LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1501CoverageChecked :
    coverageCheck (innerAD leaf1501Box) leaf1501InnerLog = true := by
  rfl'

private theorem leaf1501InnerLogValid :
    leaf1501InnerLog.Valid 8 (innerAD leaf1501Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1501CoverageChecked

private noncomputable def leaf1501InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1501InputLogOnePlusV_eq :
    leaf1501InputLogOnePlusV = outerEnclosure 24
      (leaf1501Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1501RoundedFacts : LeafRoundedFacts 8
    leaf1501Certificate.logOnePlusV leaf1501InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1501InputLogOnePlusV_eq }

private noncomputable def leaf1501Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi130InputQChi innerPair17Input
    leaf1501InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1501LowerChecked :
    lowerCheck 24 leaf1501Box leaf1501Inputs = true := by
  rfl'

private theorem leaf1501CoversExact : CoversExact 8
    leaf1501Box leaf1501Certificate leaf1501InnerLog leaf1501Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi130RoundedFacts
    innerPair17RoundedFacts leaf1501RoundedFacts (by rfl)

private theorem leaf1501FlatSound : Sound leaf1501Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1501CertificateValid
    leaf1501InnerLogValid leaf1501CoversExact leaf1501LowerChecked

private noncomputable def leaf1502Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (23/256), chiHi := (3/32) }

private noncomputable def leaf1502Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871183/536870912) }, vSqrt := { lower := (8191/8192), upper := (1048577/1048555) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (704141071/536870912) }, upper := { exponent := 0, mantissa := (85/64) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi130LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1048566/1048555) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf1502InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1502LocalValidity :
    LeafFacts leaf1502Box leaf1502Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1502Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1048577/1048555) }) = true
      norm_num [leaf1502Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1502CertificateValid :
    WideCertificateValid leaf1502Box leaf1502Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi130ValidityFacts
    leaf1502LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1502CoverageChecked :
    coverageCheck (innerAD leaf1502Box) leaf1502InnerLog = true := by
  rfl'

private theorem leaf1502InnerLogValid :
    leaf1502InnerLog.Valid 8 (innerAD leaf1502Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1502CoverageChecked

private noncomputable def leaf1502InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1502InputLogOnePlusV_eq :
    leaf1502InputLogOnePlusV = outerEnclosure 24
      (leaf1502Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1502RoundedFacts : LeafRoundedFacts 8
    leaf1502Certificate.logOnePlusV leaf1502InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1502InputLogOnePlusV_eq }

private noncomputable def leaf1502Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi130InputQChi innerPair17Input
    leaf1502InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1502LowerChecked :
    lowerCheck 24 leaf1502Box leaf1502Inputs = true := by
  rfl'

private theorem leaf1502CoversExact : CoversExact 8
    leaf1502Box leaf1502Certificate leaf1502InnerLog leaf1502Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi130RoundedFacts
    innerPair17RoundedFacts leaf1502RoundedFacts (by rfl)

private theorem leaf1502FlatSound : Sound leaf1502Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1502CertificateValid
    leaf1502InnerLogValid leaf1502CoversExact leaf1502LowerChecked

private noncomputable def component34Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component34Node0_sound : Sound component34Node0Box :=
  sound_of_literal_split component34Node0Box leaf1461Box leaf1462Box
    .chi (17/256) (by rfl) (by rfl)
    leaf1461FlatSound leaf1462FlatSound

private noncomputable def component34Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component34Node1_sound : Sound component34Node1Box :=
  sound_of_literal_split component34Node1Box leaf1463Box leaf1464Box
    .chi (17/256) (by rfl) (by rfl)
    leaf1463FlatSound leaf1464FlatSound

private noncomputable def component34Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component34Node2_sound : Sound component34Node2Box :=
  sound_of_literal_split component34Node2Box component34Node0Box component34Node1Box
    .k (53/16) (by rfl) (by rfl)
    component34Node0_sound component34Node1_sound

private noncomputable def component34Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component34Node3_sound : Sound component34Node3Box :=
  sound_of_literal_split component34Node3Box leaf1465Box leaf1466Box
    .chi (19/256) (by rfl) (by rfl)
    leaf1465FlatSound leaf1466FlatSound

private noncomputable def component34Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component34Node4_sound : Sound component34Node4Box :=
  sound_of_literal_split component34Node4Box leaf1467Box leaf1468Box
    .chi (19/256) (by rfl) (by rfl)
    leaf1467FlatSound leaf1468FlatSound

private noncomputable def component34Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component34Node5_sound : Sound component34Node5Box :=
  sound_of_literal_split component34Node5Box component34Node3Box component34Node4Box
    .k (53/16) (by rfl) (by rfl)
    component34Node3_sound component34Node4_sound

private noncomputable def component34Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component34Node6_sound : Sound component34Node6Box :=
  sound_of_literal_split component34Node6Box component34Node2Box component34Node5Box
    .chi (9/128) (by rfl) (by rfl)
    component34Node2_sound component34Node5_sound

private noncomputable def component34Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component34Node7_sound : Sound component34Node7Box :=
  sound_of_literal_split component34Node7Box leaf1469Box leaf1470Box
    .chi (17/256) (by rfl) (by rfl)
    leaf1469FlatSound leaf1470FlatSound

private noncomputable def component34Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component34Node8_sound : Sound component34Node8Box :=
  sound_of_literal_split component34Node8Box leaf1471Box leaf1472Box
    .chi (17/256) (by rfl) (by rfl)
    leaf1471FlatSound leaf1472FlatSound

private noncomputable def component34Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (1/16), chiHi := (9/128) }

set_option maxRecDepth 1000000 in
private theorem component34Node9_sound : Sound component34Node9Box :=
  sound_of_literal_split component34Node9Box component34Node7Box component34Node8Box
    .k (55/16) (by rfl) (by rfl)
    component34Node7_sound component34Node8_sound

private noncomputable def component34Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component34Node10_sound : Sound component34Node10Box :=
  sound_of_literal_split component34Node10Box leaf1473Box leaf1474Box
    .chi (19/256) (by rfl) (by rfl)
    leaf1473FlatSound leaf1474FlatSound

private noncomputable def component34Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component34Node11_sound : Sound component34Node11Box :=
  sound_of_literal_split component34Node11Box leaf1475Box leaf1476Box
    .chi (19/256) (by rfl) (by rfl)
    leaf1475FlatSound leaf1476FlatSound

private noncomputable def component34Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (9/128), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component34Node12_sound : Sound component34Node12Box :=
  sound_of_literal_split component34Node12Box component34Node10Box component34Node11Box
    .k (55/16) (by rfl) (by rfl)
    component34Node10_sound component34Node11_sound

private noncomputable def component34Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component34Node13_sound : Sound component34Node13Box :=
  sound_of_literal_split component34Node13Box component34Node9Box component34Node12Box
    .chi (9/128) (by rfl) (by rfl)
    component34Node9_sound component34Node12_sound

private noncomputable def component34Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (1/16), chiHi := (5/64) }

set_option maxRecDepth 1000000 in
private theorem component34Node14_sound : Sound component34Node14Box :=
  sound_of_literal_split component34Node14Box component34Node6Box component34Node13Box
    .k (27/8) (by rfl) (by rfl)
    component34Node6_sound component34Node13_sound

private noncomputable def component34Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component34Node15_sound : Sound component34Node15Box :=
  sound_of_literal_split component34Node15Box leaf1477Box leaf1478Box
    .chi (21/256) (by rfl) (by rfl)
    leaf1477FlatSound leaf1478FlatSound

private noncomputable def component34Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component34Node16_sound : Sound component34Node16Box :=
  sound_of_literal_split component34Node16Box leaf1479Box leaf1480Box
    .chi (21/256) (by rfl) (by rfl)
    leaf1479FlatSound leaf1480FlatSound

private noncomputable def component34Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component34Node17_sound : Sound component34Node17Box :=
  sound_of_literal_split component34Node17Box component34Node15Box component34Node16Box
    .k (53/16) (by rfl) (by rfl)
    component34Node15_sound component34Node16_sound

private noncomputable def component34Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (23/256), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component34Node18_sound : Sound component34Node18Box :=
  sound_of_literal_split component34Node18Box leaf1482Box leaf1483Box
    .k (105/32) (by rfl) (by rfl)
    leaf1482FlatSound leaf1483FlatSound

private noncomputable def component34Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component34Node19_sound : Sound component34Node19Box :=
  sound_of_literal_split component34Node19Box leaf1481Box component34Node18Box
    .chi (23/256) (by rfl) (by rfl)
    leaf1481FlatSound component34Node18_sound

private noncomputable def component34Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (11/128), chiHi := (23/256) }

set_option maxRecDepth 1000000 in
private theorem component34Node20_sound : Sound component34Node20Box :=
  sound_of_literal_split component34Node20Box leaf1484Box leaf1485Box
    .k (107/32) (by rfl) (by rfl)
    leaf1484FlatSound leaf1485FlatSound

private noncomputable def component34Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (23/256), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component34Node21_sound : Sound component34Node21Box :=
  sound_of_literal_split component34Node21Box leaf1486Box leaf1487Box
    .k (107/32) (by rfl) (by rfl)
    leaf1486FlatSound leaf1487FlatSound

private noncomputable def component34Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component34Node22_sound : Sound component34Node22Box :=
  sound_of_literal_split component34Node22Box component34Node20Box component34Node21Box
    .chi (23/256) (by rfl) (by rfl)
    component34Node20_sound component34Node21_sound

private noncomputable def component34Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component34Node23_sound : Sound component34Node23Box :=
  sound_of_literal_split component34Node23Box component34Node19Box component34Node22Box
    .k (53/16) (by rfl) (by rfl)
    component34Node19_sound component34Node22_sound

private noncomputable def component34Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component34Node24_sound : Sound component34Node24Box :=
  sound_of_literal_split component34Node24Box component34Node17Box component34Node23Box
    .chi (11/128) (by rfl) (by rfl)
    component34Node17_sound component34Node23_sound

private noncomputable def component34Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (21/256), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component34Node25_sound : Sound component34Node25Box :=
  sound_of_literal_split component34Node25Box leaf1489Box leaf1490Box
    .k (109/32) (by rfl) (by rfl)
    leaf1489FlatSound leaf1490FlatSound

private noncomputable def component34Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component34Node26_sound : Sound component34Node26Box :=
  sound_of_literal_split component34Node26Box leaf1488Box component34Node25Box
    .chi (21/256) (by rfl) (by rfl)
    leaf1488FlatSound component34Node25_sound

private noncomputable def component34Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (5/64), chiHi := (21/256) }

set_option maxRecDepth 1000000 in
private theorem component34Node27_sound : Sound component34Node27Box :=
  sound_of_literal_split component34Node27Box leaf1491Box leaf1492Box
    .k (111/32) (by rfl) (by rfl)
    leaf1491FlatSound leaf1492FlatSound

private noncomputable def component34Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (21/256), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component34Node28_sound : Sound component34Node28Box :=
  sound_of_literal_split component34Node28Box leaf1493Box leaf1494Box
    .k (111/32) (by rfl) (by rfl)
    leaf1493FlatSound leaf1494FlatSound

private noncomputable def component34Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component34Node29_sound : Sound component34Node29Box :=
  sound_of_literal_split component34Node29Box component34Node27Box component34Node28Box
    .chi (21/256) (by rfl) (by rfl)
    component34Node27_sound component34Node28_sound

private noncomputable def component34Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (5/64), chiHi := (11/128) }

set_option maxRecDepth 1000000 in
private theorem component34Node30_sound : Sound component34Node30Box :=
  sound_of_literal_split component34Node30Box component34Node26Box component34Node29Box
    .k (55/16) (by rfl) (by rfl)
    component34Node26_sound component34Node29_sound

private noncomputable def component34Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (11/128), chiHi := (23/256) }

set_option maxRecDepth 1000000 in
private theorem component34Node31_sound : Sound component34Node31Box :=
  sound_of_literal_split component34Node31Box leaf1495Box leaf1496Box
    .k (109/32) (by rfl) (by rfl)
    leaf1495FlatSound leaf1496FlatSound

private noncomputable def component34Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (23/256), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component34Node32_sound : Sound component34Node32Box :=
  sound_of_literal_split component34Node32Box leaf1497Box leaf1498Box
    .k (109/32) (by rfl) (by rfl)
    leaf1497FlatSound leaf1498FlatSound

private noncomputable def component34Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component34Node33_sound : Sound component34Node33Box :=
  sound_of_literal_split component34Node33Box component34Node31Box component34Node32Box
    .chi (23/256) (by rfl) (by rfl)
    component34Node31_sound component34Node32_sound

private noncomputable def component34Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (11/128), chiHi := (23/256) }

set_option maxRecDepth 1000000 in
private theorem component34Node34_sound : Sound component34Node34Box :=
  sound_of_literal_split component34Node34Box leaf1499Box leaf1500Box
    .k (111/32) (by rfl) (by rfl)
    leaf1499FlatSound leaf1500FlatSound

private noncomputable def component34Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (23/256), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component34Node35_sound : Sound component34Node35Box :=
  sound_of_literal_split component34Node35Box leaf1501Box leaf1502Box
    .k (111/32) (by rfl) (by rfl)
    leaf1501FlatSound leaf1502FlatSound

private noncomputable def component34Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component34Node36_sound : Sound component34Node36Box :=
  sound_of_literal_split component34Node36Box component34Node34Box component34Node35Box
    .chi (23/256) (by rfl) (by rfl)
    component34Node34_sound component34Node35_sound

private noncomputable def component34Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (11/128), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component34Node37_sound : Sound component34Node37Box :=
  sound_of_literal_split component34Node37Box component34Node33Box component34Node36Box
    .k (55/16) (by rfl) (by rfl)
    component34Node33_sound component34Node36_sound

private noncomputable def component34Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component34Node38_sound : Sound component34Node38Box :=
  sound_of_literal_split component34Node38Box component34Node30Box component34Node37Box
    .chi (11/128) (by rfl) (by rfl)
    component34Node30_sound component34Node37_sound

private noncomputable def component34Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (5/64), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
private theorem component34Node39_sound : Sound component34Node39Box :=
  sound_of_literal_split component34Node39Box component34Node24Box component34Node38Box
    .k (27/8) (by rfl) (by rfl)
    component34Node24_sound component34Node38_sound

noncomputable def component34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (1/16), chiHi := (3/32) }

set_option maxRecDepth 1000000 in
theorem component34_sound : Sound component34Box :=
  sound_of_literal_split component34Box component34Node14Box component34Node39Box
    .chi (5/64) (by rfl) (by rfl)
    component34Node14_sound component34Node39_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
