import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch0

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

private noncomputable def leaf503Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (1/2), chiHi := (9/16) }

private noncomputable def leaf503Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777267/16777216) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358484992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (25132495/16777216) }, upper := { exponent := 0, mantissa := (409/256) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi21LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717764607/68716969984) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf503InnerLog : WideLogData :=
  innerPair36Data

set_option maxRecDepth 1000000 in
private theorem leaf503LocalValidity :
    LeafFacts leaf503Box leaf503Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf503Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358484992) }) = true
      norm_num [leaf503Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf503CertificateValid :
    WideCertificateValid leaf503Box leaf503Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi21ValidityFacts
    leaf503LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf503CoverageChecked :
    coverageCheck (innerAD leaf503Box) leaf503InnerLog = true := by
  rfl'

private theorem leaf503InnerLogValid :
    leaf503InnerLog.Valid 8 (innerAD leaf503Box) :=
  wideLogDataValid_of_cachedCheck endpoint10PositiveFacts
    endpoint14PositiveFacts.valid leaf503CoverageChecked

private noncomputable def leaf503InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629275/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf503InputLogOnePlusV_eq :
    leaf503InputLogOnePlusV = outerEnclosure 24
      (leaf503Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf503RoundedFacts : LeafRoundedFacts 8
    leaf503Certificate.logOnePlusV leaf503InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf503InputLogOnePlusV_eq }

private noncomputable def leaf503Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi21InputQChi innerPair36Input
    leaf503InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf503LowerChecked :
    lowerCheck 24 leaf503Box leaf503Inputs = true := by
  rfl'

private theorem leaf503CoversExact : CoversExact 8
    leaf503Box leaf503Certificate leaf503InnerLog leaf503Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi21RoundedFacts
    innerPair36RoundedFacts leaf503RoundedFacts (by rfl)

private theorem leaf503FlatSound : Sound leaf503Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf503CertificateValid
    leaf503InnerLogValid leaf503CoversExact leaf503LowerChecked

private noncomputable def leaf504Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (1/2), chiHi := (9/16) }

private noncomputable def leaf504Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777269/16777216) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358411264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (25656749/16777216) }, upper := { exponent := 0, mantissa := (209/128) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi21LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717690879/68716822528) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf504InnerLog : WideLogData :=
  innerPair42Data

set_option maxRecDepth 1000000 in
private theorem leaf504LocalValidity :
    LeafFacts leaf504Box leaf504Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf504Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358411264) }) = true
      norm_num [leaf504Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf504CertificateValid :
    WideCertificateValid leaf504Box leaf504Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi21ValidityFacts
    leaf504LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf504CoverageChecked :
    coverageCheck (innerAD leaf504Box) leaf504InnerLog = true := by
  rfl'

private theorem leaf504InnerLogValid :
    leaf504InnerLog.Valid 8 (innerAD leaf504Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint15PositiveFacts.valid leaf504CoverageChecked

private noncomputable def leaf504InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf504InputLogOnePlusV_eq :
    leaf504InputLogOnePlusV = outerEnclosure 24
      (leaf504Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf504RoundedFacts : LeafRoundedFacts 8
    leaf504Certificate.logOnePlusV leaf504InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf504InputLogOnePlusV_eq }

private noncomputable def leaf504Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi21InputQChi innerPair42Input
    leaf504InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf504LowerChecked :
    lowerCheck 24 leaf504Box leaf504Inputs = true := by
  rfl'

private theorem leaf504CoversExact : CoversExact 8
    leaf504Box leaf504Certificate leaf504InnerLog leaf504Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi21RoundedFacts
    innerPair42RoundedFacts leaf504RoundedFacts (by rfl)

private theorem leaf504FlatSound : Sound leaf504Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf504CertificateValid
    leaf504InnerLogValid leaf504CoversExact leaf504LowerChecked

private noncomputable def leaf505Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (9/16), chiHi := (5/8) }

private noncomputable def leaf505Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777269/16777216) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358345728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (26181005/16777216) }, upper := { exponent := 0, mantissa := (213/128) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi22LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717625343/68716691456) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf505InnerLog : WideLogData :=
  innerPair42Data

set_option maxRecDepth 1000000 in
private theorem leaf505LocalValidity :
    LeafFacts leaf505Box leaf505Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf505Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358345728) }) = true
      norm_num [leaf505Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf505CertificateValid :
    WideCertificateValid leaf505Box leaf505Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi22ValidityFacts
    leaf505LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf505CoverageChecked :
    coverageCheck (innerAD leaf505Box) leaf505InnerLog = true := by
  rfl'

private theorem leaf505InnerLogValid :
    leaf505InnerLog.Valid 8 (innerAD leaf505Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint15PositiveFacts.valid leaf505CoverageChecked

private noncomputable def leaf505InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf505InputLogOnePlusV_eq :
    leaf505InputLogOnePlusV = outerEnclosure 24
      (leaf505Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf505RoundedFacts : LeafRoundedFacts 8
    leaf505Certificate.logOnePlusV leaf505InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf505InputLogOnePlusV_eq }

private noncomputable def leaf505Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi22InputQChi innerPair42Input
    leaf505InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf505LowerChecked :
    lowerCheck 24 leaf505Box leaf505Inputs = true := by
  rfl'

private theorem leaf505CoversExact : CoversExact 8
    leaf505Box leaf505Certificate leaf505InnerLog leaf505Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi22RoundedFacts
    innerPair42RoundedFacts leaf505RoundedFacts (by rfl)

private theorem leaf505FlatSound : Sound leaf505Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf505CertificateValid
    leaf505InnerLogValid leaf505CoversExact leaf505LowerChecked

private noncomputable def leaf506Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (9/16), chiHi := (5/8) }

private noncomputable def leaf506Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777271/16777216) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358263808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (26770791/16777216) }, upper := { exponent := 0, mantissa := (109/64) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi22LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717543423/68716527616) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf506InnerLog : WideLogData :=
  innerPair52Data

set_option maxRecDepth 1000000 in
private theorem leaf506LocalValidity :
    LeafFacts leaf506Box leaf506Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf506Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358263808) }) = true
      norm_num [leaf506Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf506CertificateValid :
    WideCertificateValid leaf506Box leaf506Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi22ValidityFacts
    leaf506LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf506CoverageChecked :
    coverageCheck (innerAD leaf506Box) leaf506InnerLog = true := by
  rfl'

private theorem leaf506InnerLogValid :
    leaf506InnerLog.Valid 8 (innerAD leaf506Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint16PositiveFacts.valid leaf506CoverageChecked

private noncomputable def leaf506InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf506InputLogOnePlusV_eq :
    leaf506InputLogOnePlusV = outerEnclosure 24
      (leaf506Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf506RoundedFacts : LeafRoundedFacts 8
    leaf506Certificate.logOnePlusV leaf506InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf506InputLogOnePlusV_eq }

private noncomputable def leaf506Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi22InputQChi innerPair52Input
    leaf506InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf506LowerChecked :
    lowerCheck 24 leaf506Box leaf506Inputs = true := by
  rfl'

private theorem leaf506CoversExact : CoversExact 8
    leaf506Box leaf506Certificate leaf506InnerLog leaf506Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi22RoundedFacts
    innerPair52RoundedFacts leaf506RoundedFacts (by rfl)

private theorem leaf506FlatSound : Sound leaf506Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf506CertificateValid
    leaf506InnerLogValid leaf506CoversExact leaf506LowerChecked

private noncomputable def leaf507Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (1/2), chiHi := (9/16) }

private noncomputable def leaf507Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777271/16777216) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358337536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (26181003/16777216) }, upper := { exponent := 0, mantissa := (427/256) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi21LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717617151/68716675072) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf507InnerLog : WideLogData :=
  innerPair42Data

set_option maxRecDepth 1000000 in
private theorem leaf507LocalValidity :
    LeafFacts leaf507Box leaf507Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf507Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358337536) }) = true
      norm_num [leaf507Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf507CertificateValid :
    WideCertificateValid leaf507Box leaf507Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi21ValidityFacts
    leaf507LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf507CoverageChecked :
    coverageCheck (innerAD leaf507Box) leaf507InnerLog = true := by
  rfl'

private theorem leaf507InnerLogValid :
    leaf507InnerLog.Valid 8 (innerAD leaf507Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint15PositiveFacts.valid leaf507CoverageChecked

private noncomputable def leaf507InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf507InputLogOnePlusV_eq :
    leaf507InputLogOnePlusV = outerEnclosure 24
      (leaf507Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf507RoundedFacts : LeafRoundedFacts 8
    leaf507Certificate.logOnePlusV leaf507InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf507InputLogOnePlusV_eq }

private noncomputable def leaf507Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi21InputQChi innerPair42Input
    leaf507InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf507LowerChecked :
    lowerCheck 24 leaf507Box leaf507Inputs = true := by
  rfl'

private theorem leaf507CoversExact : CoversExact 8
    leaf507Box leaf507Certificate leaf507InnerLog leaf507Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi21RoundedFacts
    innerPair42RoundedFacts leaf507RoundedFacts (by rfl)

private theorem leaf507FlatSound : Sound leaf507Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf507CertificateValid
    leaf507InnerLogValid leaf507CoversExact leaf507LowerChecked

private noncomputable def leaf508Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (1/2), chiHi := (9/16) }

private noncomputable def leaf508Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777273/16777216) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358263808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (26705257/16777216) }, upper := { exponent := 0, mantissa := (109/64) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi21LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717543423/68716527616) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf508InnerLog : WideLogData :=
  innerPair169Data

set_option maxRecDepth 1000000 in
private theorem leaf508LocalValidity :
    LeafFacts leaf508Box leaf508Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf508Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358263808) }) = true
      norm_num [leaf508Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf508CertificateValid :
    WideCertificateValid leaf508Box leaf508Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi21ValidityFacts
    leaf508LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf508CoverageChecked :
    coverageCheck (innerAD leaf508Box) leaf508InnerLog = true := by
  rfl'

private theorem leaf508InnerLogValid :
    leaf508InnerLog.Valid 8 (innerAD leaf508Box) :=
  wideLogDataValid_of_cachedCheck endpoint47PositiveFacts
    endpoint20PositiveFacts.valid leaf508CoverageChecked

private noncomputable def leaf508InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf508InputLogOnePlusV_eq :
    leaf508InputLogOnePlusV = outerEnclosure 24
      (leaf508Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf508RoundedFacts : LeafRoundedFacts 8
    leaf508Certificate.logOnePlusV leaf508InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf508InputLogOnePlusV_eq }

private noncomputable def leaf508Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi21InputQChi innerPair169Input
    leaf508InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf508LowerChecked :
    lowerCheck 24 leaf508Box leaf508Inputs = true := by
  rfl'

private theorem leaf508CoversExact : CoversExact 8
    leaf508Box leaf508Certificate leaf508InnerLog leaf508Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi21RoundedFacts
    innerPair169RoundedFacts leaf508RoundedFacts (by rfl)

private theorem leaf508FlatSound : Sound leaf508Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf508CertificateValid
    leaf508InnerLogValid leaf508CoversExact leaf508LowerChecked

private noncomputable def leaf509Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (9/16), chiHi := (5/8) }

private noncomputable def leaf509Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777273/16777216) }, vSqrt := { lower := (65533/65536), upper := (11453093205/11452727296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (27360577/16777216) }, upper := { exponent := 0, mantissa := (223/128) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi22LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (22905820501/22905454592) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf509InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf509LocalValidity :
    LeafFacts leaf509Box leaf509Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf509Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (11453093205/11452727296) }) = true
      norm_num [leaf509Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf509CertificateValid :
    WideCertificateValid leaf509Box leaf509Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi22ValidityFacts
    leaf509LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf509CoverageChecked :
    coverageCheck (innerAD leaf509Box) leaf509InnerLog = true := by
  rfl'

private theorem leaf509InnerLogValid :
    leaf509InnerLog.Valid 8 (innerAD leaf509Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf509CoverageChecked

private noncomputable def leaf509InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf509InputLogOnePlusV_eq :
    leaf509InputLogOnePlusV = outerEnclosure 24
      (leaf509Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf509RoundedFacts : LeafRoundedFacts 8
    leaf509Certificate.logOnePlusV leaf509InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf509InputLogOnePlusV_eq }

private noncomputable def leaf509Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi22InputQChi innerPair57Input
    leaf509InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf509LowerChecked :
    lowerCheck 24 leaf509Box leaf509Inputs = true := by
  rfl'

private theorem leaf509CoversExact : CoversExact 8
    leaf509Box leaf509Certificate leaf509InnerLog leaf509Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi22RoundedFacts
    innerPair57RoundedFacts leaf509RoundedFacts (by rfl)

private theorem leaf509FlatSound : Sound leaf509Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf509CertificateValid
    leaf509InnerLogValid leaf509CoversExact leaf509LowerChecked

private noncomputable def leaf510Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (9/16), chiHi := (5/8) }

private noncomputable def leaf510Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777275/16777216) }, vSqrt := { lower := (65533/65536), upper := (2021134095/2021064704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (27950363/16777216) }, upper := { exponent := 0, mantissa := (57/32) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi22LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (4042198799/4042129408) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf510InnerLog : WideLogData :=
  innerPair59Data

set_option maxRecDepth 1000000 in
private theorem leaf510LocalValidity :
    LeafFacts leaf510Box leaf510Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf510Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (2021134095/2021064704) }) = true
      norm_num [leaf510Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf510CertificateValid :
    WideCertificateValid leaf510Box leaf510Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi22ValidityFacts
    leaf510LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf510CoverageChecked :
    coverageCheck (innerAD leaf510Box) leaf510InnerLog = true := by
  rfl'

private theorem leaf510InnerLogValid :
    leaf510InnerLog.Valid 8 (innerAD leaf510Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint21PositiveFacts.valid leaf510CoverageChecked

private noncomputable def leaf510InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf510InputLogOnePlusV_eq :
    leaf510InputLogOnePlusV = outerEnclosure 24
      (leaf510Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf510RoundedFacts : LeafRoundedFacts 8
    leaf510Certificate.logOnePlusV leaf510InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf510InputLogOnePlusV_eq }

private noncomputable def leaf510Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi22InputQChi innerPair59Input
    leaf510InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf510LowerChecked :
    lowerCheck 24 leaf510Box leaf510Inputs = true := by
  rfl'

private theorem leaf510CoversExact : CoversExact 8
    leaf510Box leaf510Certificate leaf510InnerLog leaf510Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi22RoundedFacts
    innerPair59RoundedFacts leaf510RoundedFacts (by rfl)

private theorem leaf510FlatSound : Sound leaf510Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf510CertificateValid
    leaf510InnerLogValid leaf510CoversExact leaf510LowerChecked

private noncomputable def leaf511Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (5/8), chiHi := (11/16) }

private noncomputable def leaf511Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777271/16777216) }, vSqrt := { lower := (65533/65536), upper := (3817697735/3817578496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (27229515/16777216) }, upper := { exponent := 0, mantissa := (443/256) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi23LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (7635276231/7635156992) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf511InnerLog : WideLogData :=
  innerPair52Data

set_option maxRecDepth 1000000 in
private theorem leaf511LocalValidity :
    LeafFacts leaf511Box leaf511Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf511Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (3817697735/3817578496) }) = true
      norm_num [leaf511Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf511CertificateValid :
    WideCertificateValid leaf511Box leaf511Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi23ValidityFacts
    leaf511LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf511CoverageChecked :
    coverageCheck (innerAD leaf511Box) leaf511InnerLog = true := by
  rfl'

private theorem leaf511InnerLogValid :
    leaf511InnerLog.Valid 8 (innerAD leaf511Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint16PositiveFacts.valid leaf511CoverageChecked

private noncomputable def leaf511InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf511InputLogOnePlusV_eq :
    leaf511InputLogOnePlusV = outerEnclosure 24
      (leaf511Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf511RoundedFacts : LeafRoundedFacts 8
    leaf511Certificate.logOnePlusV leaf511InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf511InputLogOnePlusV_eq }

private noncomputable def leaf511Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi23InputQChi innerPair52Input
    leaf511InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf511LowerChecked :
    lowerCheck 24 leaf511Box leaf511Inputs = true := by
  rfl'

private theorem leaf511CoversExact : CoversExact 8
    leaf511Box leaf511Certificate leaf511InnerLog leaf511Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi23RoundedFacts
    innerPair52RoundedFacts leaf511RoundedFacts (by rfl)

private theorem leaf511FlatSound : Sound leaf511Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf511CertificateValid
    leaf511InnerLogValid leaf511CoversExact leaf511LowerChecked

private noncomputable def leaf512Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (5/8), chiHi := (11/16) }

private noncomputable def leaf512Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777273/16777216) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358116352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (27884833/16777216) }, upper := { exponent := 0, mantissa := (227/128) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi23LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717395967/68716232704) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf512InnerLog : WideLogData :=
  innerPair59Data

set_option maxRecDepth 1000000 in
private theorem leaf512LocalValidity :
    LeafFacts leaf512Box leaf512Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf512Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358116352) }) = true
      norm_num [leaf512Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf512CertificateValid :
    WideCertificateValid leaf512Box leaf512Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi23ValidityFacts
    leaf512LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf512CoverageChecked :
    coverageCheck (innerAD leaf512Box) leaf512InnerLog = true := by
  rfl'

private theorem leaf512InnerLogValid :
    leaf512InnerLog.Valid 8 (innerAD leaf512Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint21PositiveFacts.valid leaf512CoverageChecked

private noncomputable def leaf512InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf512InputLogOnePlusV_eq :
    leaf512InputLogOnePlusV = outerEnclosure 24
      (leaf512Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf512RoundedFacts : LeafRoundedFacts 8
    leaf512Certificate.logOnePlusV leaf512InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf512InputLogOnePlusV_eq }

private noncomputable def leaf512Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi23InputQChi innerPair59Input
    leaf512InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf512LowerChecked :
    lowerCheck 24 leaf512Box leaf512Inputs = true := by
  rfl'

private theorem leaf512CoversExact : CoversExact 8
    leaf512Box leaf512Certificate leaf512InnerLog leaf512Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi23RoundedFacts
    innerPair59RoundedFacts leaf512RoundedFacts (by rfl)

private theorem leaf512FlatSound : Sound leaf512Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf512CertificateValid
    leaf512InnerLogValid leaf512CoversExact leaf512LowerChecked

private noncomputable def leaf513Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (17/16), chiLo := (11/16), chiHi := (3/4) }

private noncomputable def leaf513Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777273/16777216) }, vSqrt := { lower := (65533/65536), upper := (6871855923/6871613440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (28278025/16777216) }, upper := { exponent := 0, mantissa := (115/64) } }, logOuter := sk18LogOuterCertificate, logK := sk18LogKCertificate, logChi := chi24LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (13743469363/13743226880) } }, logDArg := sk18LogDArgCertificate }

private noncomputable def leaf513InnerLog : WideLogData :=
  innerPair59Data

set_option maxRecDepth 1000000 in
private theorem leaf513LocalValidity :
    LeafFacts leaf513Box leaf513Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf513Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (6871855923/6871613440) }) = true
      norm_num [leaf513Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf513CertificateValid :
    WideCertificateValid leaf513Box leaf513Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk18ValidityFacts chi24ValidityFacts
    leaf513LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf513CoverageChecked :
    coverageCheck (innerAD leaf513Box) leaf513InnerLog = true := by
  rfl'

private theorem leaf513InnerLogValid :
    leaf513InnerLog.Valid 8 (innerAD leaf513Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint21PositiveFacts.valid leaf513CoverageChecked

private noncomputable def leaf513InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf513InputLogOnePlusV_eq :
    leaf513InputLogOnePlusV = outerEnclosure 24
      (leaf513Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf513RoundedFacts : LeafRoundedFacts 8
    leaf513Certificate.logOnePlusV leaf513InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf513InputLogOnePlusV_eq }

private noncomputable def leaf513Inputs : Inputs :=
  inputsOfCaches globalInput sk18RoundedInputs
    chi24InputQChi innerPair59Input
    leaf513InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf513LowerChecked :
    lowerCheck 24 leaf513Box leaf513Inputs = true := by
  rfl'

private theorem leaf513CoversExact : CoversExact 8
    leaf513Box leaf513Certificate leaf513InnerLog leaf513Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk18RoundedFacts chi24RoundedFacts
    innerPair59RoundedFacts leaf513RoundedFacts (by rfl)

private theorem leaf513FlatSound : Sound leaf513Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf513CertificateValid
    leaf513InnerLogValid leaf513CoversExact leaf513LowerChecked

private noncomputable def leaf514Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (17/16), kHi := (9/8), chiLo := (11/16), chiHi := (3/4) }

private noncomputable def leaf514Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777275/16777216) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34357968896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (28998875/16777216) }, upper := { exponent := 0, mantissa := (59/32) } }, logOuter := sk19LogOuterCertificate, logK := sk19LogKCertificate, logChi := chi24LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717248511/68715937792) } }, logDArg := sk19LogDArgCertificate }

private noncomputable def leaf514InnerLog : WideLogData :=
  innerPair67Data

set_option maxRecDepth 1000000 in
private theorem leaf514LocalValidity :
    LeafFacts leaf514Box leaf514Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf514Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34357968896) }) = true
      norm_num [leaf514Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf514CertificateValid :
    WideCertificateValid leaf514Box leaf514Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk19ValidityFacts chi24ValidityFacts
    leaf514LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf514CoverageChecked :
    coverageCheck (innerAD leaf514Box) leaf514InnerLog = true := by
  rfl'

private theorem leaf514InnerLogValid :
    leaf514InnerLog.Valid 8 (innerAD leaf514Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint22PositiveFacts.valid leaf514CoverageChecked

private noncomputable def leaf514InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf514InputLogOnePlusV_eq :
    leaf514InputLogOnePlusV = outerEnclosure 24
      (leaf514Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf514RoundedFacts : LeafRoundedFacts 8
    leaf514Certificate.logOnePlusV leaf514InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf514InputLogOnePlusV_eq }

private noncomputable def leaf514Inputs : Inputs :=
  inputsOfCaches globalInput sk19RoundedInputs
    chi24InputQChi innerPair67Input
    leaf514InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf514LowerChecked :
    lowerCheck 24 leaf514Box leaf514Inputs = true := by
  rfl'

private theorem leaf514CoversExact : CoversExact 8
    leaf514Box leaf514Certificate leaf514InnerLog leaf514Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk19RoundedFacts chi24RoundedFacts
    innerPair67RoundedFacts leaf514RoundedFacts (by rfl)

private theorem leaf514FlatSound : Sound leaf514Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf514CertificateValid
    leaf514InnerLogValid leaf514CoversExact leaf514LowerChecked

private noncomputable def leaf515Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (5/8), chiHi := (11/16) }

private noncomputable def leaf515Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777275/16777216) }, vSqrt := { lower := (65533/65536), upper := (6871855923/6871605248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (28540151/16777216) }, upper := { exponent := 0, mantissa := (465/256) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi23LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (13743461171/13743210496) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf515InnerLog : WideLogData :=
  innerPair67Data

set_option maxRecDepth 1000000 in
private theorem leaf515LocalValidity :
    LeafFacts leaf515Box leaf515Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf515Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (6871855923/6871605248) }) = true
      norm_num [leaf515Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf515CertificateValid :
    WideCertificateValid leaf515Box leaf515Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi23ValidityFacts
    leaf515LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf515CoverageChecked :
    coverageCheck (innerAD leaf515Box) leaf515InnerLog = true := by
  rfl'

private theorem leaf515InnerLogValid :
    leaf515InnerLog.Valid 8 (innerAD leaf515Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint22PositiveFacts.valid leaf515CoverageChecked

private noncomputable def leaf515InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629387/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf515InputLogOnePlusV_eq :
    leaf515InputLogOnePlusV = outerEnclosure 24
      (leaf515Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf515RoundedFacts : LeafRoundedFacts 8
    leaf515Certificate.logOnePlusV leaf515InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf515InputLogOnePlusV_eq }

private noncomputable def leaf515Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi23InputQChi innerPair67Input
    leaf515InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf515LowerChecked :
    lowerCheck 24 leaf515Box leaf515Inputs = true := by
  rfl'

private theorem leaf515CoversExact : CoversExact 8
    leaf515Box leaf515Certificate leaf515InnerLog leaf515Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi23RoundedFacts
    innerPair67RoundedFacts leaf515RoundedFacts (by rfl)

private theorem leaf515FlatSound : Sound leaf515Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf515CertificateValid
    leaf515InnerLogValid leaf515CoversExact leaf515LowerChecked

private noncomputable def leaf516Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (5/8), chiHi := (11/16) }

private noncomputable def leaf516Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777277/16777216) }, vSqrt := { lower := (65533/65536), upper := (11453093205/11452645376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (29195469/16777216) }, upper := { exponent := 0, mantissa := (119/64) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi23LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (22905738581/22905290752) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf516InnerLog : WideLogData :=
  innerPair67Data

set_option maxRecDepth 1000000 in
private theorem leaf516LocalValidity :
    LeafFacts leaf516Box leaf516Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf516Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (11453093205/11452645376) }) = true
      norm_num [leaf516Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf516CertificateValid :
    WideCertificateValid leaf516Box leaf516Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi23ValidityFacts
    leaf516LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf516CoverageChecked :
    coverageCheck (innerAD leaf516Box) leaf516InnerLog = true := by
  rfl'

private theorem leaf516InnerLogValid :
    leaf516InnerLog.Valid 8 (innerAD leaf516Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint22PositiveFacts.valid leaf516CoverageChecked

private noncomputable def leaf516InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf516InputLogOnePlusV_eq :
    leaf516InputLogOnePlusV = outerEnclosure 24
      (leaf516Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf516RoundedFacts : LeafRoundedFacts 8
    leaf516Certificate.logOnePlusV leaf516InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf516InputLogOnePlusV_eq }

private noncomputable def leaf516Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi23InputQChi innerPair67Input
    leaf516InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf516LowerChecked :
    lowerCheck 24 leaf516Box leaf516Inputs = true := by
  rfl'

private theorem leaf516CoversExact : CoversExact 8
    leaf516Box leaf516Certificate leaf516InnerLog leaf516Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi23RoundedFacts
    innerPair67RoundedFacts leaf516RoundedFacts (by rfl)

private theorem leaf516FlatSound : Sound leaf516Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf516CertificateValid
    leaf516InnerLogValid leaf516CoversExact leaf516LowerChecked

private noncomputable def leaf517Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (19/16), chiLo := (11/16), chiHi := (3/4) }

private noncomputable def leaf517Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777277/16777216) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34357870592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (29719725/16777216) }, upper := { exponent := 0, mantissa := (121/64) } }, logOuter := sk21LogOuterCertificate, logK := sk21LogKCertificate, logChi := chi24LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717150207/68715741184) } }, logDArg := sk21LogDArgCertificate }

private noncomputable def leaf517InnerLog : WideLogData :=
  innerPair73Data

set_option maxRecDepth 1000000 in
private theorem leaf517LocalValidity :
    LeafFacts leaf517Box leaf517Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf517Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34357870592) }) = true
      norm_num [leaf517Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf517CertificateValid :
    WideCertificateValid leaf517Box leaf517Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk21ValidityFacts chi24ValidityFacts
    leaf517LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf517CoverageChecked :
    coverageCheck (innerAD leaf517Box) leaf517InnerLog = true := by
  rfl'

private theorem leaf517InnerLogValid :
    leaf517InnerLog.Valid 8 (innerAD leaf517Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint23PositiveFacts.valid leaf517CoverageChecked

private noncomputable def leaf517InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629425/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf517InputLogOnePlusV_eq :
    leaf517InputLogOnePlusV = outerEnclosure 24
      (leaf517Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf517RoundedFacts : LeafRoundedFacts 8
    leaf517Certificate.logOnePlusV leaf517InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf517InputLogOnePlusV_eq }

private noncomputable def leaf517Inputs : Inputs :=
  inputsOfCaches globalInput sk21RoundedInputs
    chi24InputQChi innerPair73Input
    leaf517InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf517LowerChecked :
    lowerCheck 24 leaf517Box leaf517Inputs = true := by
  rfl'

private theorem leaf517CoversExact : CoversExact 8
    leaf517Box leaf517Certificate leaf517InnerLog leaf517Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk21RoundedFacts chi24RoundedFacts
    innerPair73RoundedFacts leaf517RoundedFacts (by rfl)

private theorem leaf517FlatSound : Sound leaf517Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf517CertificateValid
    leaf517InnerLogValid leaf517CoversExact leaf517LowerChecked

private noncomputable def leaf518Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/16), kHi := (5/4), chiLo := (11/16), chiHi := (3/4) }

private noncomputable def leaf518Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777279/16777216) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34357772288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (30440575/16777216) }, upper := { exponent := 0, mantissa := (31/16) } }, logOuter := sk22LogOuterCertificate, logK := sk22LogKCertificate, logChi := chi24LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717051903/68715544576) } }, logDArg := sk22LogDArgCertificate }

private noncomputable def leaf518InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf518LocalValidity :
    LeafFacts leaf518Box leaf518Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf518Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34357772288) }) = true
      norm_num [leaf518Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf518CertificateValid :
    WideCertificateValid leaf518Box leaf518Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk22ValidityFacts chi24ValidityFacts
    leaf518LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf518CoverageChecked :
    coverageCheck (innerAD leaf518Box) leaf518InnerLog = true := by
  rfl'

private theorem leaf518InnerLogValid :
    leaf518InnerLog.Valid 8 (innerAD leaf518Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf518CoverageChecked

private noncomputable def leaf518InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf518InputLogOnePlusV_eq :
    leaf518InputLogOnePlusV = outerEnclosure 24
      (leaf518Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf518RoundedFacts : LeafRoundedFacts 8
    leaf518Certificate.logOnePlusV leaf518InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf518InputLogOnePlusV_eq }

private noncomputable def leaf518Inputs : Inputs :=
  inputsOfCaches globalInput sk22RoundedInputs
    chi24InputQChi innerPair92Input
    leaf518InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf518LowerChecked :
    lowerCheck 24 leaf518Box leaf518Inputs = true := by
  rfl'

private theorem leaf518CoversExact : CoversExact 8
    leaf518Box leaf518Certificate leaf518InnerLog leaf518Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk22RoundedFacts chi24RoundedFacts
    innerPair92RoundedFacts leaf518RoundedFacts (by rfl)

private theorem leaf518FlatSound : Sound leaf518Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf518CertificateValid
    leaf518InnerLogValid leaf518CoversExact leaf518LowerChecked

private noncomputable def leaf519Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (1/2), chiHi := (17/32) }

private noncomputable def leaf519Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554507/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358276096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (54491831/33554432) }, upper := { exponent := 0, mantissa := (869/512) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi70LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717555711/68716552192) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf519InnerLog : WideLogData :=
  innerPair52Data

set_option maxRecDepth 1000000 in
private theorem leaf519LocalValidity :
    LeafFacts leaf519Box leaf519Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf519Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358276096) }) = true
      norm_num [leaf519Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf519CertificateValid :
    WideCertificateValid leaf519Box leaf519Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi70ValidityFacts
    leaf519LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf519CoverageChecked :
    coverageCheck (innerAD leaf519Box) leaf519InnerLog = true := by
  rfl'

private theorem leaf519InnerLogValid :
    leaf519InnerLog.Valid 8 (innerAD leaf519Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint16PositiveFacts.valid leaf519CoverageChecked

private noncomputable def leaf519InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf519InputLogOnePlusV_eq :
    leaf519InputLogOnePlusV = outerEnclosure 24
      (leaf519Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf519RoundedFacts : LeafRoundedFacts 8
    leaf519Certificate.logOnePlusV leaf519InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf519InputLogOnePlusV_eq }

private noncomputable def leaf519Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi70InputQChi innerPair52Input
    leaf519InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf519LowerChecked :
    lowerCheck 24 leaf519Box leaf519Inputs = true := by
  rfl'

private theorem leaf519CoversExact : CoversExact 8
    leaf519Box leaf519Certificate leaf519InnerLog leaf519Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi70RoundedFacts
    innerPair52RoundedFacts leaf519RoundedFacts (by rfl)

private theorem leaf519FlatSound : Sound leaf519Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf519CertificateValid
    leaf519InnerLogValid leaf519CoversExact leaf519LowerChecked

private noncomputable def leaf520Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (17/32), chiHi := (9/16) }

private noncomputable def leaf520Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554509/33554432) }, vSqrt := { lower := (65533/65536), upper := (6871855923/6871638016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (55802469/33554432) }, upper := { exponent := 0, mantissa := (445/256) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi71LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (13743493939/13743276032) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf520InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf520LocalValidity :
    LeafFacts leaf520Box leaf520Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf520Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (6871855923/6871638016) }) = true
      norm_num [leaf520Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf520CertificateValid :
    WideCertificateValid leaf520Box leaf520Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi71ValidityFacts
    leaf520LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf520CoverageChecked :
    coverageCheck (innerAD leaf520Box) leaf520InnerLog = true := by
  rfl'

private theorem leaf520InnerLogValid :
    leaf520InnerLog.Valid 8 (innerAD leaf520Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf520CoverageChecked

private noncomputable def leaf520InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf520InputLogOnePlusV_eq :
    leaf520InputLogOnePlusV = outerEnclosure 24
      (leaf520Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf520RoundedFacts : LeafRoundedFacts 8
    leaf520Certificate.logOnePlusV leaf520InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf520InputLogOnePlusV_eq }

private noncomputable def leaf520Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi71InputQChi innerPair57Input
    leaf520InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf520LowerChecked :
    lowerCheck 24 leaf520Box leaf520Inputs = true := by
  rfl'

private theorem leaf520CoversExact : CoversExact 8
    leaf520Box leaf520Certificate leaf520InnerLog leaf520Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi71RoundedFacts
    innerPair57RoundedFacts leaf520RoundedFacts (by rfl)

private theorem leaf520FlatSound : Sound leaf520Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf520CertificateValid
    leaf520InnerLogValid leaf520CoversExact leaf520LowerChecked

private noncomputable def leaf521Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (1/2), chiHi := (17/32) }

private noncomputable def leaf521Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554509/33554432) }, vSqrt := { lower := (65533/65536), upper := (3817697735/3817578496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (55540341/33554432) }, upper := { exponent := 0, mantissa := (443/256) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi70LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (7635276231/7635156992) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf521InnerLog : WideLogData :=
  innerPair57Data

set_option maxRecDepth 1000000 in
private theorem leaf521LocalValidity :
    LeafFacts leaf521Box leaf521Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf521Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (3817697735/3817578496) }) = true
      norm_num [leaf521Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf521CertificateValid :
    WideCertificateValid leaf521Box leaf521Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi70ValidityFacts
    leaf521LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf521CoverageChecked :
    coverageCheck (innerAD leaf521Box) leaf521InnerLog = true := by
  rfl'

private theorem leaf521InnerLogValid :
    leaf521InnerLog.Valid 8 (innerAD leaf521Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint16PositiveFacts.valid leaf521CoverageChecked

private noncomputable def leaf521InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf521InputLogOnePlusV_eq :
    leaf521InputLogOnePlusV = outerEnclosure 24
      (leaf521Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf521RoundedFacts : LeafRoundedFacts 8
    leaf521Certificate.logOnePlusV leaf521InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf521InputLogOnePlusV_eq }

private noncomputable def leaf521Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi70InputQChi innerPair57Input
    leaf521InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf521LowerChecked :
    lowerCheck 24 leaf521Box leaf521Inputs = true := by
  rfl'

private theorem leaf521CoversExact : CoversExact 8
    leaf521Box leaf521Certificate leaf521InnerLog leaf521Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi70RoundedFacts
    innerPair57RoundedFacts leaf521RoundedFacts (by rfl)

private theorem leaf521FlatSound : Sound leaf521Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf521CertificateValid
    leaf521InnerLogValid leaf521CoversExact leaf521LowerChecked

private noncomputable def leaf522Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (17/32), chiHi := (9/16) }

private noncomputable def leaf522Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554511/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358116352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (56916511/33554432) }, upper := { exponent := 0, mantissa := (227/128) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi71LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717395967/68716232704) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf522InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf522LocalValidity :
    LeafFacts leaf522Box leaf522Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf522Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358116352) }) = true
      norm_num [leaf522Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf522CertificateValid :
    WideCertificateValid leaf522Box leaf522Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi71ValidityFacts
    leaf522LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf522CoverageChecked :
    coverageCheck (innerAD leaf522Box) leaf522InnerLog = true := by
  rfl'

private theorem leaf522InnerLogValid :
    leaf522InnerLog.Valid 8 (innerAD leaf522Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf522CoverageChecked

private noncomputable def leaf522InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf522InputLogOnePlusV_eq :
    leaf522InputLogOnePlusV = outerEnclosure 24
      (leaf522Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf522RoundedFacts : LeafRoundedFacts 8
    leaf522Certificate.logOnePlusV leaf522InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf522InputLogOnePlusV_eq }

private noncomputable def leaf522Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi71InputQChi innerPair66Input
    leaf522InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf522LowerChecked :
    lowerCheck 24 leaf522Box leaf522Inputs = true := by
  rfl'

private theorem leaf522CoversExact : CoversExact 8
    leaf522Box leaf522Certificate leaf522InnerLog leaf522Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi71RoundedFacts
    innerPair66RoundedFacts leaf522RoundedFacts (by rfl)

private theorem leaf522FlatSound : Sound leaf522Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf522CertificateValid
    leaf522InnerLogValid leaf522CoversExact leaf522LowerChecked

private noncomputable def leaf523Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (9/16), chiHi := (5/8) }

private noncomputable def leaf523Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777277/16777216) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358018048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (28540149/16777216) }, upper := { exponent := 0, mantissa := (233/128) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi22LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717297663/68716036096) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf523InnerLog : WideLogData :=
  innerPair69Data

set_option maxRecDepth 1000000 in
private theorem leaf523LocalValidity :
    LeafFacts leaf523Box leaf523Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf523Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358018048) }) = true
      norm_num [leaf523Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf523CertificateValid :
    WideCertificateValid leaf523Box leaf523Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi22ValidityFacts
    leaf523LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf523CoverageChecked :
    coverageCheck (innerAD leaf523Box) leaf523InnerLog = true := by
  rfl'

private theorem leaf523InnerLogValid :
    leaf523InnerLog.Valid 8 (innerAD leaf523Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint64PositiveFacts.valid leaf523CoverageChecked

private noncomputable def leaf523InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf523InputLogOnePlusV_eq :
    leaf523InputLogOnePlusV = outerEnclosure 24
      (leaf523Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf523RoundedFacts : LeafRoundedFacts 8
    leaf523Certificate.logOnePlusV leaf523InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf523InputLogOnePlusV_eq }

private noncomputable def leaf523Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi22InputQChi innerPair69Input
    leaf523InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf523LowerChecked :
    lowerCheck 24 leaf523Box leaf523Inputs = true := by
  rfl'

private theorem leaf523CoversExact : CoversExact 8
    leaf523Box leaf523Certificate leaf523InnerLog leaf523Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi22RoundedFacts
    innerPair69RoundedFacts leaf523RoundedFacts (by rfl)

private theorem leaf523FlatSound : Sound leaf523Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf523CertificateValid
    leaf523InnerLogValid leaf523CoversExact leaf523LowerChecked

private noncomputable def leaf524Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (9/16), chiHi := (19/32) }

private noncomputable def leaf524Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554513/33554432) }, vSqrt := { lower := (65533/65536), upper := (6871855923/6871605248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (58292681/33554432) }, upper := { exponent := 0, mantissa := (465/256) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi72LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (13743461171/13743210496) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf524InnerLog : WideLogData :=
  innerPair67Data

set_option maxRecDepth 1000000 in
private theorem leaf524LocalValidity :
    LeafFacts leaf524Box leaf524Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf524Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (6871855923/6871605248) }) = true
      norm_num [leaf524Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf524CertificateValid :
    WideCertificateValid leaf524Box leaf524Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi72ValidityFacts
    leaf524LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf524CoverageChecked :
    coverageCheck (innerAD leaf524Box) leaf524InnerLog = true := by
  rfl'

private theorem leaf524InnerLogValid :
    leaf524InnerLog.Valid 8 (innerAD leaf524Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint22PositiveFacts.valid leaf524CoverageChecked

private noncomputable def leaf524InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629387/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf524InputLogOnePlusV_eq :
    leaf524InputLogOnePlusV = outerEnclosure 24
      (leaf524Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf524RoundedFacts : LeafRoundedFacts 8
    leaf524Certificate.logOnePlusV leaf524InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf524InputLogOnePlusV_eq }

private noncomputable def leaf524Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi72InputQChi innerPair67Input
    leaf524InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf524LowerChecked :
    lowerCheck 24 leaf524Box leaf524Inputs = true := by
  rfl'

private theorem leaf524CoversExact : CoversExact 8
    leaf524Box leaf524Certificate leaf524InnerLog leaf524Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi72RoundedFacts
    innerPair67RoundedFacts leaf524RoundedFacts (by rfl)

private theorem leaf524FlatSound : Sound leaf524Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf524CertificateValid
    leaf524InnerLogValid leaf524CoversExact leaf524LowerChecked

private noncomputable def leaf525Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (19/32), chiHi := (5/8) }

private noncomputable def leaf525Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554515/33554432) }, vSqrt := { lower := (65533/65536), upper := (11453093205/11452645376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (59668851/33554432) }, upper := { exponent := 0, mantissa := (119/64) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi73LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (22905738581/22905290752) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf525InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf525LocalValidity :
    LeafFacts leaf525Box leaf525Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf525Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (11453093205/11452645376) }) = true
      norm_num [leaf525Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf525CertificateValid :
    WideCertificateValid leaf525Box leaf525Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi73ValidityFacts
    leaf525LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf525CoverageChecked :
    coverageCheck (innerAD leaf525Box) leaf525InnerLog = true := by
  rfl'

private theorem leaf525InnerLogValid :
    leaf525InnerLog.Valid 8 (innerAD leaf525Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf525CoverageChecked

private noncomputable def leaf525InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf525InputLogOnePlusV_eq :
    leaf525InputLogOnePlusV = outerEnclosure 24
      (leaf525Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf525RoundedFacts : LeafRoundedFacts 8
    leaf525Certificate.logOnePlusV leaf525InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf525InputLogOnePlusV_eq }

private noncomputable def leaf525Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi73InputQChi innerPair72Input
    leaf525InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf525LowerChecked :
    lowerCheck 24 leaf525Box leaf525Inputs = true := by
  rfl'

private theorem leaf525CoversExact : CoversExact 8
    leaf525Box leaf525Certificate leaf525InnerLog leaf525Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi73RoundedFacts
    innerPair72RoundedFacts leaf525RoundedFacts (by rfl)

private theorem leaf525FlatSound : Sound leaf525Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf525CertificateValid
    leaf525InnerLogValid leaf525CoversExact leaf525LowerChecked

private noncomputable def leaf526Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (1/2), chiHi := (17/32) }

private noncomputable def leaf526Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554511/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358136832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (56588851/33554432) }, upper := { exponent := 0, mantissa := (903/512) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi70LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717416447/68716273664) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf526InnerLog : WideLogData :=
  innerPair59Data

set_option maxRecDepth 1000000 in
private theorem leaf526LocalValidity :
    LeafFacts leaf526Box leaf526Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf526Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358136832) }) = true
      norm_num [leaf526Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf526CertificateValid :
    WideCertificateValid leaf526Box leaf526Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi70ValidityFacts
    leaf526LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf526CoverageChecked :
    coverageCheck (innerAD leaf526Box) leaf526InnerLog = true := by
  rfl'

private theorem leaf526InnerLogValid :
    leaf526InnerLog.Valid 8 (innerAD leaf526Box) :=
  wideLogDataValid_of_cachedCheck endpoint14PositiveFacts
    endpoint21PositiveFacts.valid leaf526CoverageChecked

private noncomputable def leaf526InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (726835/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf526InputLogOnePlusV_eq :
    leaf526InputLogOnePlusV = outerEnclosure 24
      (leaf526Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf526RoundedFacts : LeafRoundedFacts 8
    leaf526Certificate.logOnePlusV leaf526InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf526InputLogOnePlusV_eq }

private noncomputable def leaf526Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi70InputQChi innerPair59Input
    leaf526InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf526LowerChecked :
    lowerCheck 24 leaf526Box leaf526Inputs = true := by
  rfl'

private theorem leaf526CoversExact : CoversExact 8
    leaf526Box leaf526Certificate leaf526InnerLog leaf526Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi70RoundedFacts
    innerPair59RoundedFacts leaf526RoundedFacts (by rfl)

private theorem leaf526FlatSound : Sound leaf526Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf526CertificateValid
    leaf526InnerLogValid leaf526CoversExact leaf526LowerChecked

private noncomputable def leaf527Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (17/32), chiHi := (9/16) }

private noncomputable def leaf527Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554513/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34358042624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (58030553/33554432) }, upper := { exponent := 0, mantissa := (463/256) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi71LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717322239/68716085248) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf527InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf527LocalValidity :
    LeafFacts leaf527Box leaf527Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf527Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34358042624) }) = true
      norm_num [leaf527Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf527CertificateValid :
    WideCertificateValid leaf527Box leaf527Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi71ValidityFacts
    leaf527LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf527CoverageChecked :
    coverageCheck (innerAD leaf527Box) leaf527InnerLog = true := by
  rfl'

private theorem leaf527InnerLogValid :
    leaf527InnerLog.Valid 8 (innerAD leaf527Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf527CoverageChecked

private noncomputable def leaf527InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629383/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf527InputLogOnePlusV_eq :
    leaf527InputLogOnePlusV = outerEnclosure 24
      (leaf527Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf527RoundedFacts : LeafRoundedFacts 8
    leaf527Certificate.logOnePlusV leaf527InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf527InputLogOnePlusV_eq }

private noncomputable def leaf527Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi71InputQChi innerPair66Input
    leaf527InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf527LowerChecked :
    lowerCheck 24 leaf527Box leaf527Inputs = true := by
  rfl'

private theorem leaf527CoversExact : CoversExact 8
    leaf527Box leaf527Certificate leaf527InnerLog leaf527Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi71RoundedFacts
    innerPair66RoundedFacts leaf527RoundedFacts (by rfl)

private theorem leaf527FlatSound : Sound leaf527Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf527CertificateValid
    leaf527InnerLogValid leaf527CoversExact leaf527LowerChecked

private noncomputable def leaf528Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (1/2), chiHi := (17/32) }

private noncomputable def leaf528Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554513/33554432) }, vSqrt := { lower := (16383/16384), upper := (6871855923/6871613440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (57637361/33554432) }, upper := { exponent := 0, mantissa := (115/64) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi70LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (13743469363/13743226880) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf528InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf528LocalValidity :
    LeafFacts leaf528Box leaf528Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf528Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (6871855923/6871613440) }) = true
      norm_num [leaf528Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf528CertificateValid :
    WideCertificateValid leaf528Box leaf528Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi70ValidityFacts
    leaf528LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf528CoverageChecked :
    coverageCheck (innerAD leaf528Box) leaf528InnerLog = true := by
  rfl'

private theorem leaf528InnerLogValid :
    leaf528InnerLog.Valid 8 (innerAD leaf528Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf528CoverageChecked

private noncomputable def leaf528InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf528InputLogOnePlusV_eq :
    leaf528InputLogOnePlusV = outerEnclosure 24
      (leaf528Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf528RoundedFacts : LeafRoundedFacts 8
    leaf528Certificate.logOnePlusV leaf528InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf528InputLogOnePlusV_eq }

private noncomputable def leaf528Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi70InputQChi innerPair66Input
    leaf528InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf528LowerChecked :
    lowerCheck 24 leaf528Box leaf528Inputs = true := by
  rfl'

private theorem leaf528CoversExact : CoversExact 8
    leaf528Box leaf528Certificate leaf528InnerLog leaf528Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi70RoundedFacts
    innerPair66RoundedFacts leaf528RoundedFacts (by rfl)

private theorem leaf528FlatSound : Sound leaf528Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf528CertificateValid
    leaf528InnerLogValid leaf528CoversExact leaf528LowerChecked

private noncomputable def leaf529Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (17/32), chiHi := (9/16) }

private noncomputable def leaf529Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554515/33554432) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357968896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (59144595/33554432) }, upper := { exponent := 0, mantissa := (59/32) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi71LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717248511/68715937792) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf529InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf529LocalValidity :
    LeafFacts leaf529Box leaf529Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf529Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357968896) }) = true
      norm_num [leaf529Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf529CertificateValid :
    WideCertificateValid leaf529Box leaf529Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi71ValidityFacts
    leaf529LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf529CoverageChecked :
    coverageCheck (innerAD leaf529Box) leaf529InnerLog = true := by
  rfl'

private theorem leaf529InnerLogValid :
    leaf529InnerLog.Valid 8 (innerAD leaf529Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf529CoverageChecked

private noncomputable def leaf529InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf529InputLogOnePlusV_eq :
    leaf529InputLogOnePlusV = outerEnclosure 24
      (leaf529Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf529RoundedFacts : LeafRoundedFacts 8
    leaf529Certificate.logOnePlusV leaf529InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf529InputLogOnePlusV_eq }

private noncomputable def leaf529Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi71InputQChi innerPair72Input
    leaf529InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf529LowerChecked :
    lowerCheck 24 leaf529Box leaf529Inputs = true := by
  rfl'

private theorem leaf529CoversExact : CoversExact 8
    leaf529Box leaf529Certificate leaf529InnerLog leaf529Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi71RoundedFacts
    innerPair72RoundedFacts leaf529RoundedFacts (by rfl)

private theorem leaf529FlatSound : Sound leaf529Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf529CertificateValid
    leaf529InnerLogValid leaf529CoversExact leaf529LowerChecked

private noncomputable def leaf530Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (9/16), chiHi := (19/32) }

private noncomputable def leaf530Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554515/33554432) }, vSqrt := { lower := (65533/65536), upper := (3817697735/3817549824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (59472255/33554432) }, upper := { exponent := 0, mantissa := (949/512) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi72LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (7635247559/7635099648) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf530InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf530LocalValidity :
    LeafFacts leaf530Box leaf530Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf530Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (3817697735/3817549824) }) = true
      norm_num [leaf530Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf530CertificateValid :
    WideCertificateValid leaf530Box leaf530Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi72ValidityFacts
    leaf530LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf530CoverageChecked :
    coverageCheck (innerAD leaf530Box) leaf530InnerLog = true := by
  rfl'

private theorem leaf530InnerLogValid :
    leaf530InnerLog.Valid 8 (innerAD leaf530Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf530CoverageChecked

private noncomputable def leaf530InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf530InputLogOnePlusV_eq :
    leaf530InputLogOnePlusV = outerEnclosure 24
      (leaf530Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf530RoundedFacts : LeafRoundedFacts 8
    leaf530Certificate.logOnePlusV leaf530InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf530InputLogOnePlusV_eq }

private noncomputable def leaf530Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi72InputQChi innerPair72Input
    leaf530InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf530LowerChecked :
    lowerCheck 24 leaf530Box leaf530Inputs = true := by
  rfl'

private theorem leaf530CoversExact : CoversExact 8
    leaf530Box leaf530Certificate leaf530InnerLog leaf530Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi72RoundedFacts
    innerPair72RoundedFacts leaf530RoundedFacts (by rfl)

private theorem leaf530FlatSound : Sound leaf530Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf530CertificateValid
    leaf530InnerLogValid leaf530CoversExact leaf530LowerChecked

private noncomputable def leaf531Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (19/32), chiHi := (5/8) }

private noncomputable def leaf531Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554517/33554432) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34357854208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (60913957/33554432) }, upper := { exponent := 0, mantissa := (243/128) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi73LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717133823/68715708416) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf531InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf531LocalValidity :
    LeafFacts leaf531Box leaf531Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf531Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34357854208) }) = true
      norm_num [leaf531Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf531CertificateValid :
    WideCertificateValid leaf531Box leaf531Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi73ValidityFacts
    leaf531LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf531CoverageChecked :
    coverageCheck (innerAD leaf531Box) leaf531InnerLog = true := by
  rfl'

private theorem leaf531InnerLogValid :
    leaf531InnerLog.Valid 8 (innerAD leaf531Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf531CoverageChecked

private noncomputable def leaf531InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf531InputLogOnePlusV_eq :
    leaf531InputLogOnePlusV = outerEnclosure 24
      (leaf531Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf531RoundedFacts : LeafRoundedFacts 8
    leaf531Certificate.logOnePlusV leaf531InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf531InputLogOnePlusV_eq }

private noncomputable def leaf531Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi73InputQChi innerPair92Input
    leaf531InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf531LowerChecked :
    lowerCheck 24 leaf531Box leaf531Inputs = true := by
  rfl'

private theorem leaf531CoversExact : CoversExact 8
    leaf531Box leaf531Certificate leaf531InnerLog leaf531Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi73RoundedFacts
    innerPair92RoundedFacts leaf531RoundedFacts (by rfl)

private theorem leaf531FlatSound : Sound leaf531Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf531CertificateValid
    leaf531InnerLogValid leaf531CoversExact leaf531LowerChecked

private noncomputable def leaf532Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (9/16), chiHi := (19/32) }

private noncomputable def leaf532Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554517/33554432) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357870592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (60651829/33554432) }, upper := { exponent := 0, mantissa := (121/64) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi72LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717150207/68715741184) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf532InnerLog : WideLogData :=
  innerPair73Data

set_option maxRecDepth 1000000 in
private theorem leaf532LocalValidity :
    LeafFacts leaf532Box leaf532Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf532Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357870592) }) = true
      norm_num [leaf532Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf532CertificateValid :
    WideCertificateValid leaf532Box leaf532Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi72ValidityFacts
    leaf532LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf532CoverageChecked :
    coverageCheck (innerAD leaf532Box) leaf532InnerLog = true := by
  rfl'

private theorem leaf532InnerLogValid :
    leaf532InnerLog.Valid 8 (innerAD leaf532Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint23PositiveFacts.valid leaf532CoverageChecked

private noncomputable def leaf532InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629425/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf532InputLogOnePlusV_eq :
    leaf532InputLogOnePlusV = outerEnclosure 24
      (leaf532Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf532RoundedFacts : LeafRoundedFacts 8
    leaf532Certificate.logOnePlusV leaf532InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf532InputLogOnePlusV_eq }

private noncomputable def leaf532Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi72InputQChi innerPair73Input
    leaf532InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf532LowerChecked :
    lowerCheck 24 leaf532Box leaf532Inputs = true := by
  rfl'

private theorem leaf532CoversExact : CoversExact 8
    leaf532Box leaf532Certificate leaf532InnerLog leaf532Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi72RoundedFacts
    innerPair73RoundedFacts leaf532RoundedFacts (by rfl)

private theorem leaf532FlatSound : Sound leaf532Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf532CertificateValid
    leaf532InnerLogValid leaf532CoversExact leaf532LowerChecked

private noncomputable def leaf533Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (19/32), chiHi := (5/8) }

private noncomputable def leaf533Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554519/33554432) }, vSqrt := { lower := (16383/16384), upper := (34359279615/34357772288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (62159063/33554432) }, upper := { exponent := 0, mantissa := (31/16) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi73LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (68717051903/68715544576) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf533InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf533LocalValidity :
    LeafFacts leaf533Box leaf533Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf533Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (34359279615/34357772288) }) = true
      norm_num [leaf533Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf533CertificateValid :
    WideCertificateValid leaf533Box leaf533Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi73ValidityFacts
    leaf533LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf533CoverageChecked :
    coverageCheck (innerAD leaf533Box) leaf533InnerLog = true := by
  rfl'

private theorem leaf533InnerLogValid :
    leaf533InnerLog.Valid 8 (innerAD leaf533Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf533CoverageChecked

private noncomputable def leaf533InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf533InputLogOnePlusV_eq :
    leaf533InputLogOnePlusV = outerEnclosure 24
      (leaf533Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf533RoundedFacts : LeafRoundedFacts 8
    leaf533Certificate.logOnePlusV leaf533InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf533InputLogOnePlusV_eq }

private noncomputable def leaf533Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi73InputQChi innerPair92Input
    leaf533InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf533LowerChecked :
    lowerCheck 24 leaf533Box leaf533Inputs = true := by
  rfl'

private theorem leaf533CoversExact : CoversExact 8
    leaf533Box leaf533Certificate leaf533InnerLog leaf533Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi73RoundedFacts
    innerPair92RoundedFacts leaf533RoundedFacts (by rfl)

private theorem leaf533FlatSound : Sound leaf533Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf533CertificateValid
    leaf533InnerLogValid leaf533CoversExact leaf533LowerChecked

private noncomputable def leaf534Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (5/8), chiHi := (11/16) }

private noncomputable def leaf534Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777279/16777216) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34357846016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (29850787/16777216) }, upper := { exponent := 0, mantissa := (487/256) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi23LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717125631/68715692032) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf534InnerLog : WideLogData :=
  innerPair73Data

set_option maxRecDepth 1000000 in
private theorem leaf534LocalValidity :
    LeafFacts leaf534Box leaf534Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf534Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34357846016) }) = true
      norm_num [leaf534Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf534CertificateValid :
    WideCertificateValid leaf534Box leaf534Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi23ValidityFacts
    leaf534LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf534CoverageChecked :
    coverageCheck (innerAD leaf534Box) leaf534InnerLog = true := by
  rfl'

private theorem leaf534InnerLogValid :
    leaf534InnerLog.Valid 8 (innerAD leaf534Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint23PositiveFacts.valid leaf534CoverageChecked

private noncomputable def leaf534InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf534InputLogOnePlusV_eq :
    leaf534InputLogOnePlusV = outerEnclosure 24
      (leaf534Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf534RoundedFacts : LeafRoundedFacts 8
    leaf534Certificate.logOnePlusV leaf534InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf534InputLogOnePlusV_eq }

private noncomputable def leaf534Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi23InputQChi innerPair73Input
    leaf534InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf534LowerChecked :
    lowerCheck 24 leaf534Box leaf534Inputs = true := by
  rfl'

private theorem leaf534CoversExact : CoversExact 8
    leaf534Box leaf534Certificate leaf534InnerLog leaf534Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi23RoundedFacts
    innerPair73RoundedFacts leaf534RoundedFacts (by rfl)

private theorem leaf534FlatSound : Sound leaf534Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf534CertificateValid
    leaf534InnerLogValid leaf534CoversExact leaf534LowerChecked

private noncomputable def leaf535Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (5/8), chiHi := (11/16) }

private noncomputable def leaf535Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777281/16777216) }, vSqrt := { lower := (65533/65536), upper := (34359279615/34357755904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (30506105/16777216) }, upper := { exponent := 0, mantissa := (249/128) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi23LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (68717035519/68715511808) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf535InnerLog : WideLogData :=
  innerPair97Data

set_option maxRecDepth 1000000 in
private theorem leaf535LocalValidity :
    LeafFacts leaf535Box leaf535Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf535Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (34359279615/34357755904) }) = true
      norm_num [leaf535Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf535CertificateValid :
    WideCertificateValid leaf535Box leaf535Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi23ValidityFacts
    leaf535LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf535CoverageChecked :
    coverageCheck (innerAD leaf535Box) leaf535InnerLog = true := by
  rfl'

private theorem leaf535InnerLogValid :
    leaf535InnerLog.Valid 8 (innerAD leaf535Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint71PositiveFacts.valid leaf535CoverageChecked

private noncomputable def leaf535InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629453/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf535InputLogOnePlusV_eq :
    leaf535InputLogOnePlusV = outerEnclosure 24
      (leaf535Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf535RoundedFacts : LeafRoundedFacts 8
    leaf535Certificate.logOnePlusV leaf535InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf535InputLogOnePlusV_eq }

private noncomputable def leaf535Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi23InputQChi innerPair97Input
    leaf535InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf535LowerChecked :
    lowerCheck 24 leaf535Box leaf535Inputs = true := by
  rfl'

private theorem leaf535CoversExact : CoversExact 8
    leaf535Box leaf535Certificate leaf535InnerLog leaf535Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi23RoundedFacts
    innerPair97RoundedFacts leaf535RoundedFacts (by rfl)

private theorem leaf535FlatSound : Sound leaf535Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf535CertificateValid
    leaf535InnerLogValid leaf535CoversExact leaf535LowerChecked

private noncomputable def leaf536Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (11/16), chiHi := (3/4) }

private noncomputable def leaf536Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777281/16777216) }, vSqrt := { lower := (65533/65536), upper := (554173473/554156032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (31161425/16777216) }, upper := { exponent := 0, mantissa := (127/64) } }, logOuter := sk25LogOuterCertificate, logK := sk25LogKCertificate, logChi := chi24LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (1108329505/1108312064) } }, logDArg := sk25LogDArgCertificate }

private noncomputable def leaf536InnerLog : WideLogData :=
  innerPair93Data

set_option maxRecDepth 1000000 in
private theorem leaf536LocalValidity :
    LeafFacts leaf536Box leaf536Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf536Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (554173473/554156032) }) = true
      norm_num [leaf536Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf536CertificateValid :
    WideCertificateValid leaf536Box leaf536Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk25ValidityFacts chi24ValidityFacts
    leaf536LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf536CoverageChecked :
    coverageCheck (innerAD leaf536Box) leaf536InnerLog = true := by
  rfl'

private theorem leaf536InnerLogValid :
    leaf536InnerLog.Valid 8 (innerAD leaf536Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint24PositiveFacts.valid leaf536CoverageChecked

private noncomputable def leaf536InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf536InputLogOnePlusV_eq :
    leaf536InputLogOnePlusV = outerEnclosure 24
      (leaf536Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf536RoundedFacts : LeafRoundedFacts 8
    leaf536Certificate.logOnePlusV leaf536InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf536InputLogOnePlusV_eq }

private noncomputable def leaf536Inputs : Inputs :=
  inputsOfCaches globalInput sk25RoundedInputs
    chi24InputQChi innerPair93Input
    leaf536InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf536LowerChecked :
    lowerCheck 24 leaf536Box leaf536Inputs = true := by
  rfl'

private theorem leaf536CoversExact : CoversExact 8
    leaf536Box leaf536Certificate leaf536InnerLog leaf536Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk25RoundedFacts chi24RoundedFacts
    innerPair93RoundedFacts leaf536RoundedFacts (by rfl)

private theorem leaf536FlatSound : Sound leaf536Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf536CertificateValid
    leaf536InnerLogValid leaf536CoversExact leaf536LowerChecked

private noncomputable def leaf537Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (11/16), chiHi := (3/4) }

private noncomputable def leaf537Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777283/16777216) }, vSqrt := { lower := (65533/65536), upper := (17179377663/17178787840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (31882275/16777216) }, upper := { exponent := 1, mantissa := (65/64) } }, logOuter := sk26LogOuterCertificate, logK := sk26LogKCertificate, logChi := chi24LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131069/65536) }, upper := { exponent := 1, mantissa := (34358165503/34357575680) } }, logDArg := sk26LogDArgCertificate }

private noncomputable def leaf537InnerLog : WideLogData :=
  innerPair104Data

set_option maxRecDepth 1000000 in
private theorem leaf537LocalValidity :
    LeafFacts leaf537Box leaf537Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf537Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65533/65536), upper := (17179377663/17178787840) }) = true
      norm_num [leaf537Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf537CertificateValid :
    WideCertificateValid leaf537Box leaf537Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk26ValidityFacts chi24ValidityFacts
    leaf537LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf537CoverageChecked :
    coverageCheck (innerAD leaf537Box) leaf537InnerLog = true := by
  rfl'

private theorem leaf537InnerLogValid :
    leaf537InnerLog.Valid 8 (innerAD leaf537Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint72PositiveFacts.valid leaf537CoverageChecked

private noncomputable def leaf537InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628695/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf537InputLogOnePlusV_eq :
    leaf537InputLogOnePlusV = outerEnclosure 24
      (leaf537Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf537RoundedFacts : LeafRoundedFacts 8
    leaf537Certificate.logOnePlusV leaf537InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf537InputLogOnePlusV_eq }

private noncomputable def leaf537Inputs : Inputs :=
  inputsOfCaches globalInput sk26RoundedInputs
    chi24InputQChi innerPair104Input
    leaf537InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf537LowerChecked :
    lowerCheck 24 leaf537Box leaf537Inputs = true := by
  rfl'

private theorem leaf537CoversExact : CoversExact 8
    leaf537Box leaf537Certificate leaf537InnerLog leaf537Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk26RoundedFacts chi24RoundedFacts
    innerPair104RoundedFacts leaf537RoundedFacts (by rfl)

private theorem leaf537FlatSound : Sound leaf537Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf537CertificateValid
    leaf537InnerLogValid leaf537CoversExact leaf537LowerChecked

private noncomputable def leaf538Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (5/8), chiHi := (11/16) }

private noncomputable def leaf538Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (16777283/16777216) }, vSqrt := { lower := (16383/16384), upper := (5726459221/5726277632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (31161423/16777216) }, upper := { exponent := 0, mantissa := (509/256) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi23LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (11452736853/11452555264) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf538InnerLog : WideLogData :=
  innerPair93Data

set_option maxRecDepth 1000000 in
private theorem leaf538LocalValidity :
    LeafFacts leaf538Box leaf538Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf538Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (5726459221/5726277632) }) = true
      norm_num [leaf538Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf538CertificateValid :
    WideCertificateValid leaf538Box leaf538Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi23ValidityFacts
    leaf538LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf538CoverageChecked :
    coverageCheck (innerAD leaf538Box) leaf538InnerLog = true := by
  rfl'

private theorem leaf538InnerLogValid :
    leaf538InnerLog.Valid 8 (innerAD leaf538Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint24PositiveFacts.valid leaf538CoverageChecked

private noncomputable def leaf538InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf538InputLogOnePlusV_eq :
    leaf538InputLogOnePlusV = outerEnclosure 24
      (leaf538Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf538RoundedFacts : LeafRoundedFacts 8
    leaf538Certificate.logOnePlusV leaf538InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf538InputLogOnePlusV_eq }

private noncomputable def leaf538Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi23InputQChi innerPair93Input
    leaf538InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf538LowerChecked :
    lowerCheck 24 leaf538Box leaf538Inputs = true := by
  rfl'

private theorem leaf538CoversExact : CoversExact 8
    leaf538Box leaf538Certificate leaf538InnerLog leaf538Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi23RoundedFacts
    innerPair93RoundedFacts leaf538RoundedFacts (by rfl)

private theorem leaf538FlatSound : Sound leaf538Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf538CertificateValid
    leaf538InnerLogValid leaf538CoversExact leaf538LowerChecked

private noncomputable def leaf539Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (5/8), chiHi := (21/32) }

private noncomputable def leaf539Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (33554521/33554432) }, vSqrt := { lower := (16383/16384), upper := (554173473/554156032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (63666297/33554432) }, upper := { exponent := 0, mantissa := (127/64) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi74LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (1108329505/1108312064) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf539InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf539LocalValidity :
    LeafFacts leaf539Box leaf539Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf539Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (554173473/554156032) }) = true
      norm_num [leaf539Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf539CertificateValid :
    WideCertificateValid leaf539Box leaf539Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi74ValidityFacts
    leaf539LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf539CoverageChecked :
    coverageCheck (innerAD leaf539Box) leaf539InnerLog = true := by
  rfl'

private theorem leaf539InnerLogValid :
    leaf539InnerLog.Valid 8 (innerAD leaf539Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf539CoverageChecked

private noncomputable def leaf539InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf539InputLogOnePlusV_eq :
    leaf539InputLogOnePlusV = outerEnclosure 24
      (leaf539Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf539RoundedFacts : LeafRoundedFacts 8
    leaf539Certificate.logOnePlusV leaf539InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf539InputLogOnePlusV_eq }

private noncomputable def leaf539Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi74InputQChi innerPair101Input
    leaf539InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf539LowerChecked :
    lowerCheck 24 leaf539Box leaf539Inputs = true := by
  rfl'

private theorem leaf539CoversExact : CoversExact 8
    leaf539Box leaf539Certificate leaf539InnerLog leaf539Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi74RoundedFacts
    innerPair101RoundedFacts leaf539RoundedFacts (by rfl)

private theorem leaf539FlatSound : Sound leaf539Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf539CertificateValid
    leaf539InnerLogValid leaf539CoversExact leaf539LowerChecked

private noncomputable def leaf540Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (21/32), chiHi := (11/16) }

private noncomputable def leaf540Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (33554523/33554432) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178787840) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (65173531/33554432) }, upper := { exponent := 1, mantissa := (65/64) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi75LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358165503/34357575680) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf540InnerLog : WideLogData :=
  innerPair110Data

set_option maxRecDepth 1000000 in
private theorem leaf540LocalValidity :
    LeafFacts leaf540Box leaf540Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf540Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178787840) }) = true
      norm_num [leaf540Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf540CertificateValid :
    WideCertificateValid leaf540Box leaf540Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi75ValidityFacts
    leaf540LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf540CoverageChecked :
    coverageCheck (innerAD leaf540Box) leaf540InnerLog = true := by
  rfl'

private theorem leaf540InnerLogValid :
    leaf540InnerLog.Valid 8 (innerAD leaf540Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint72PositiveFacts.valid leaf540CoverageChecked

private noncomputable def leaf540InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf540InputLogOnePlusV_eq :
    leaf540InputLogOnePlusV = outerEnclosure 24
      (leaf540Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf540RoundedFacts : LeafRoundedFacts 8
    leaf540Certificate.logOnePlusV leaf540InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf540InputLogOnePlusV_eq }

private noncomputable def leaf540Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi75InputQChi innerPair110Input
    leaf540InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf540LowerChecked :
    lowerCheck 24 leaf540Box leaf540Inputs = true := by
  rfl'

private theorem leaf540CoversExact : CoversExact 8
    leaf540Box leaf540Certificate leaf540InnerLog leaf540Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi75RoundedFacts
    innerPair110RoundedFacts leaf540RoundedFacts (by rfl)

private theorem leaf540FlatSound : Sound leaf540Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf540CertificateValid
    leaf540InnerLogValid leaf540CoversExact leaf540LowerChecked

private noncomputable def leaf541Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (11/16), chiHi := (3/4) }

private noncomputable def leaf541Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777285/16777216) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178738688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (32603125/16777216) }, upper := { exponent := 1, mantissa := (133/128) } }, logOuter := sk27LogOuterCertificate, logK := sk27LogKCertificate, logChi := chi24LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358116351/34357477376) } }, logDArg := sk27LogDArgCertificate }

private noncomputable def leaf541InnerLog : WideLogData :=
  innerPair111Data

set_option maxRecDepth 1000000 in
private theorem leaf541LocalValidity :
    LeafFacts leaf541Box leaf541Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf541Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178738688) }) = true
      norm_num [leaf541Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf541CertificateValid :
    WideCertificateValid leaf541Box leaf541Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk27ValidityFacts chi24ValidityFacts
    leaf541LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf541CoverageChecked :
    coverageCheck (innerAD leaf541Box) leaf541InnerLog = true := by
  rfl'

private theorem leaf541InnerLogValid :
    leaf541InnerLog.Valid 8 (innerAD leaf541Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint73PositiveFacts.valid leaf541CoverageChecked

private noncomputable def leaf541InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf541InputLogOnePlusV_eq :
    leaf541InputLogOnePlusV = outerEnclosure 24
      (leaf541Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf541RoundedFacts : LeafRoundedFacts 8
    leaf541Certificate.logOnePlusV leaf541InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf541InputLogOnePlusV_eq }

private noncomputable def leaf541Inputs : Inputs :=
  inputsOfCaches globalInput sk27RoundedInputs
    chi24InputQChi innerPair111Input
    leaf541InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf541LowerChecked :
    lowerCheck 24 leaf541Box leaf541Inputs = true := by
  rfl'

private theorem leaf541CoversExact : CoversExact 8
    leaf541Box leaf541Certificate leaf541InnerLog leaf541Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk27RoundedFacts chi24RoundedFacts
    innerPair111RoundedFacts leaf541RoundedFacts (by rfl)

private theorem leaf541FlatSound : Sound leaf541Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf541CertificateValid
    leaf541InnerLogValid leaf541CoversExact leaf541LowerChecked

private noncomputable def leaf542Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (11/16), chiHi := (3/4) }

private noncomputable def leaf542Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65533/65536), upper := (16777287/16777216) }, vSqrt := { lower := (16383/16384), upper := (17179377663/17178689536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (33323975/16777216) }, upper := { exponent := 1, mantissa := (17/16) } }, logOuter := sk28LogOuterCertificate, logK := sk28LogKCertificate, logChi := chi24LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (34358067199/34357379072) } }, logDArg := sk28LogDArgCertificate }

private noncomputable def leaf542InnerLog : WideLogData :=
  innerPair111Data

set_option maxRecDepth 1000000 in
private theorem leaf542LocalValidity :
    LeafFacts leaf542Box leaf542Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf542Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (17179377663/17178689536) }) = true
      norm_num [leaf542Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf542CertificateValid :
    WideCertificateValid leaf542Box leaf542Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk28ValidityFacts chi24ValidityFacts
    leaf542LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf542CoverageChecked :
    coverageCheck (innerAD leaf542Box) leaf542InnerLog = true := by
  rfl'

private theorem leaf542InnerLogValid :
    leaf542InnerLog.Valid 8 (innerAD leaf542Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint73PositiveFacts.valid leaf542CoverageChecked

private noncomputable def leaf542InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf542InputLogOnePlusV_eq :
    leaf542InputLogOnePlusV = outerEnclosure 24
      (leaf542Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf542RoundedFacts : LeafRoundedFacts 8
    leaf542Certificate.logOnePlusV leaf542InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf542InputLogOnePlusV_eq }

private noncomputable def leaf542Inputs : Inputs :=
  inputsOfCaches globalInput sk28RoundedInputs
    chi24InputQChi innerPair111Input
    leaf542InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf542LowerChecked :
    lowerCheck 24 leaf542Box leaf542Inputs = true := by
  rfl'

private theorem leaf542CoversExact : CoversExact 8
    leaf542Box leaf542Certificate leaf542InnerLog leaf542Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk28RoundedFacts chi24RoundedFacts
    innerPair111RoundedFacts leaf542RoundedFacts (by rfl)

private theorem leaf542FlatSound : Sound leaf542Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf542CertificateValid
    leaf542InnerLogValid leaf542CoversExact leaf542LowerChecked

private noncomputable def component12Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component12Node0_sound : Sound component12Node0Box :=
  sound_of_literal_split component12Node0Box leaf503Box leaf504Box
    .k (17/16) (by rfl) (by rfl)
    leaf503FlatSound leaf504FlatSound

private noncomputable def component12Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component12Node1_sound : Sound component12Node1Box :=
  sound_of_literal_split component12Node1Box leaf505Box leaf506Box
    .k (17/16) (by rfl) (by rfl)
    leaf505FlatSound leaf506FlatSound

private noncomputable def component12Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component12Node2_sound : Sound component12Node2Box :=
  sound_of_literal_split component12Node2Box component12Node0Box component12Node1Box
    .chi (9/16) (by rfl) (by rfl)
    component12Node0_sound component12Node1_sound

private noncomputable def component12Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component12Node3_sound : Sound component12Node3Box :=
  sound_of_literal_split component12Node3Box leaf507Box leaf508Box
    .k (19/16) (by rfl) (by rfl)
    leaf507FlatSound leaf508FlatSound

private noncomputable def component12Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component12Node4_sound : Sound component12Node4Box :=
  sound_of_literal_split component12Node4Box leaf509Box leaf510Box
    .k (19/16) (by rfl) (by rfl)
    leaf509FlatSound leaf510FlatSound

private noncomputable def component12Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component12Node5_sound : Sound component12Node5Box :=
  sound_of_literal_split component12Node5Box component12Node3Box component12Node4Box
    .chi (9/16) (by rfl) (by rfl)
    component12Node3_sound component12Node4_sound

private noncomputable def component12Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (5/4), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component12Node6_sound : Sound component12Node6Box :=
  sound_of_literal_split component12Node6Box component12Node2Box component12Node5Box
    .k (9/8) (by rfl) (by rfl)
    component12Node2_sound component12Node5_sound

private noncomputable def component12Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component12Node7_sound : Sound component12Node7Box :=
  sound_of_literal_split component12Node7Box leaf511Box leaf512Box
    .k (17/16) (by rfl) (by rfl)
    leaf511FlatSound leaf512FlatSound

private noncomputable def component12Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component12Node8_sound : Sound component12Node8Box :=
  sound_of_literal_split component12Node8Box leaf513Box leaf514Box
    .k (17/16) (by rfl) (by rfl)
    leaf513FlatSound leaf514FlatSound

private noncomputable def component12Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (9/8), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component12Node9_sound : Sound component12Node9Box :=
  sound_of_literal_split component12Node9Box component12Node7Box component12Node8Box
    .chi (11/16) (by rfl) (by rfl)
    component12Node7_sound component12Node8_sound

private noncomputable def component12Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component12Node10_sound : Sound component12Node10Box :=
  sound_of_literal_split component12Node10Box leaf515Box leaf516Box
    .k (19/16) (by rfl) (by rfl)
    leaf515FlatSound leaf516FlatSound

private noncomputable def component12Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component12Node11_sound : Sound component12Node11Box :=
  sound_of_literal_split component12Node11Box leaf517Box leaf518Box
    .k (19/16) (by rfl) (by rfl)
    leaf517FlatSound leaf518FlatSound

private noncomputable def component12Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/8), kHi := (5/4), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component12Node12_sound : Sound component12Node12Box :=
  sound_of_literal_split component12Node12Box component12Node10Box component12Node11Box
    .chi (11/16) (by rfl) (by rfl)
    component12Node10_sound component12Node11_sound

private noncomputable def component12Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (5/4), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component12Node13_sound : Sound component12Node13Box :=
  sound_of_literal_split component12Node13Box component12Node9Box component12Node12Box
    .k (9/8) (by rfl) (by rfl)
    component12Node9_sound component12Node12_sound

private noncomputable def component12Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (5/4), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component12Node14_sound : Sound component12Node14Box :=
  sound_of_literal_split component12Node14Box component12Node6Box component12Node13Box
    .chi (5/8) (by rfl) (by rfl)
    component12Node6_sound component12Node13_sound

private noncomputable def component12Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (21/16), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component12Node15_sound : Sound component12Node15Box :=
  sound_of_literal_split component12Node15Box leaf519Box leaf520Box
    .chi (17/32) (by rfl) (by rfl)
    leaf519FlatSound leaf520FlatSound

private noncomputable def component12Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component12Node16_sound : Sound component12Node16Box :=
  sound_of_literal_split component12Node16Box leaf521Box leaf522Box
    .chi (17/32) (by rfl) (by rfl)
    leaf521FlatSound leaf522FlatSound

private noncomputable def component12Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component12Node17_sound : Sound component12Node17Box :=
  sound_of_literal_split component12Node17Box component12Node15Box component12Node16Box
    .k (21/16) (by rfl) (by rfl)
    component12Node15_sound component12Node16_sound

private noncomputable def component12Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (21/16), kHi := (11/8), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component12Node18_sound : Sound component12Node18Box :=
  sound_of_literal_split component12Node18Box leaf524Box leaf525Box
    .chi (19/32) (by rfl) (by rfl)
    leaf524FlatSound leaf525FlatSound

private noncomputable def component12Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component12Node19_sound : Sound component12Node19Box :=
  sound_of_literal_split component12Node19Box leaf523Box component12Node18Box
    .k (21/16) (by rfl) (by rfl)
    leaf523FlatSound component12Node18_sound

private noncomputable def component12Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component12Node20_sound : Sound component12Node20Box :=
  sound_of_literal_split component12Node20Box component12Node17Box component12Node19Box
    .chi (9/16) (by rfl) (by rfl)
    component12Node17_sound component12Node19_sound

private noncomputable def component12Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component12Node21_sound : Sound component12Node21Box :=
  sound_of_literal_split component12Node21Box leaf526Box leaf527Box
    .chi (17/32) (by rfl) (by rfl)
    leaf526FlatSound leaf527FlatSound

private noncomputable def component12Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component12Node22_sound : Sound component12Node22Box :=
  sound_of_literal_split component12Node22Box leaf528Box leaf529Box
    .chi (17/32) (by rfl) (by rfl)
    leaf528FlatSound leaf529FlatSound

private noncomputable def component12Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (1/2), chiHi := (9/16) }

set_option maxRecDepth 1000000 in
private theorem component12Node23_sound : Sound component12Node23Box :=
  sound_of_literal_split component12Node23Box component12Node21Box component12Node22Box
    .k (23/16) (by rfl) (by rfl)
    component12Node21_sound component12Node22_sound

private noncomputable def component12Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (23/16), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component12Node24_sound : Sound component12Node24Box :=
  sound_of_literal_split component12Node24Box leaf530Box leaf531Box
    .chi (19/32) (by rfl) (by rfl)
    leaf530FlatSound leaf531FlatSound

private noncomputable def component12Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component12Node25_sound : Sound component12Node25Box :=
  sound_of_literal_split component12Node25Box leaf532Box leaf533Box
    .chi (19/32) (by rfl) (by rfl)
    leaf532FlatSound leaf533FlatSound

private noncomputable def component12Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (9/16), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component12Node26_sound : Sound component12Node26Box :=
  sound_of_literal_split component12Node26Box component12Node24Box component12Node25Box
    .k (23/16) (by rfl) (by rfl)
    component12Node24_sound component12Node25_sound

private noncomputable def component12Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component12Node27_sound : Sound component12Node27Box :=
  sound_of_literal_split component12Node27Box component12Node23Box component12Node26Box
    .chi (9/16) (by rfl) (by rfl)
    component12Node23_sound component12Node26_sound

private noncomputable def component12Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (3/2), chiLo := (1/2), chiHi := (5/8) }

set_option maxRecDepth 1000000 in
private theorem component12Node28_sound : Sound component12Node28Box :=
  sound_of_literal_split component12Node28Box component12Node20Box component12Node27Box
    .k (11/8) (by rfl) (by rfl)
    component12Node20_sound component12Node27_sound

private noncomputable def component12Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component12Node29_sound : Sound component12Node29Box :=
  sound_of_literal_split component12Node29Box leaf534Box leaf535Box
    .k (21/16) (by rfl) (by rfl)
    leaf534FlatSound leaf535FlatSound

private noncomputable def component12Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component12Node30_sound : Sound component12Node30Box :=
  sound_of_literal_split component12Node30Box leaf536Box leaf537Box
    .k (21/16) (by rfl) (by rfl)
    leaf536FlatSound leaf537FlatSound

private noncomputable def component12Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (11/8), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component12Node31_sound : Sound component12Node31Box :=
  sound_of_literal_split component12Node31Box component12Node29Box component12Node30Box
    .chi (11/16) (by rfl) (by rfl)
    component12Node29_sound component12Node30_sound

private noncomputable def component12Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (23/16), kHi := (3/2), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component12Node32_sound : Sound component12Node32Box :=
  sound_of_literal_split component12Node32Box leaf539Box leaf540Box
    .chi (21/32) (by rfl) (by rfl)
    leaf539FlatSound leaf540FlatSound

private noncomputable def component12Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component12Node33_sound : Sound component12Node33Box :=
  sound_of_literal_split component12Node33Box leaf538Box component12Node32Box
    .k (23/16) (by rfl) (by rfl)
    leaf538FlatSound component12Node32_sound

private noncomputable def component12Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component12Node34_sound : Sound component12Node34Box :=
  sound_of_literal_split component12Node34Box leaf541Box leaf542Box
    .k (23/16) (by rfl) (by rfl)
    leaf541FlatSound leaf542FlatSound

private noncomputable def component12Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (11/8), kHi := (3/2), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component12Node35_sound : Sound component12Node35Box :=
  sound_of_literal_split component12Node35Box component12Node33Box component12Node34Box
    .chi (11/16) (by rfl) (by rfl)
    component12Node33_sound component12Node34_sound

private noncomputable def component12Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (3/2), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component12Node36_sound : Sound component12Node36Box :=
  sound_of_literal_split component12Node36Box component12Node31Box component12Node35Box
    .k (11/8) (by rfl) (by rfl)
    component12Node31_sound component12Node35_sound

private noncomputable def component12Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (5/4), kHi := (3/2), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component12Node37_sound : Sound component12Node37Box :=
  sound_of_literal_split component12Node37Box component12Node28Box component12Node36Box
    .chi (5/8) (by rfl) (by rfl)
    component12Node28_sound component12Node36_sound

noncomputable def component12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (1), kHi := (3/2), chiLo := (1/2), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
theorem component12_sound : Sound component12Box :=
  sound_of_literal_split component12Box component12Node14Box component12Node37Box
    .k (5/4) (by rfl) (by rfl)
    component12Node14_sound component12Node37_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
