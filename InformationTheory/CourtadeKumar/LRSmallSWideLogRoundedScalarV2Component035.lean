import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
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

private noncomputable def leaf1503Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1503Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871171/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134215103) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (700405759/536870912) }, upper := { exponent := 0, mantissa := (10817/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432959/268430206) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf1503InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1503LocalValidity :
    LeafFacts leaf1503Box leaf1503Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1503Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134215103) }) = true
      norm_num [leaf1503Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1503CertificateValid :
    WideCertificateValid leaf1503Box leaf1503Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi131ValidityFacts
    leaf1503LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1503CoverageChecked :
    coverageCheck (innerAD leaf1503Box) leaf1503InnerLog = true := by
  rfl'

private theorem leaf1503InnerLogValid :
    leaf1503InnerLog.Valid 8 (innerAD leaf1503Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1503CoverageChecked

private noncomputable def leaf1503InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1503InputLogOnePlusV_eq :
    leaf1503InputLogOnePlusV = outerEnclosure 24
      (leaf1503Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1503RoundedFacts : LeafRoundedFacts 8
    leaf1503Certificate.logOnePlusV leaf1503InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1503InputLogOnePlusV_eq }

private noncomputable def leaf1503Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi131InputQChi innerPair17Input
    leaf1503InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1503LowerChecked :
    lowerCheck 24 leaf1503Box leaf1503Inputs = true := by
  rfl'

private theorem leaf1503CoversExact : CoversExact 8
    leaf1503Box leaf1503Certificate leaf1503InnerLog leaf1503Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi131RoundedFacts
    innerPair17RoundedFacts leaf1503RoundedFacts (by rfl)

private theorem leaf1503FlatSound : Sound leaf1503Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1503CertificateValid
    leaf1503InnerLogValid leaf1503CoversExact leaf1503LowerChecked

private noncomputable def leaf1504Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1504Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871173/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107539) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (701978525/536870912) }, upper := { exponent := 0, mantissa := (5421/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216467/134215078) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf1504InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1504LocalValidity :
    LeafFacts leaf1504Box leaf1504Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1504Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107539) }) = true
      norm_num [leaf1504Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1504CertificateValid :
    WideCertificateValid leaf1504Box leaf1504Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi131ValidityFacts
    leaf1504LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1504CoverageChecked :
    coverageCheck (innerAD leaf1504Box) leaf1504InnerLog = true := by
  rfl'

private theorem leaf1504InnerLogValid :
    leaf1504InnerLog.Valid 8 (innerAD leaf1504Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1504CoverageChecked

private noncomputable def leaf1504InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1504InputLogOnePlusV_eq :
    leaf1504InputLogOnePlusV = outerEnclosure 24
      (leaf1504Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1504RoundedFacts : LeafRoundedFacts 8
    leaf1504Certificate.logOnePlusV leaf1504InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1504InputLogOnePlusV_eq }

private noncomputable def leaf1504Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi131InputQChi innerPair17Input
    leaf1504InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1504LowerChecked :
    lowerCheck 24 leaf1504Box leaf1504Inputs = true := by
  rfl'

private theorem leaf1504CoversExact : CoversExact 8
    leaf1504Box leaf1504Certificate leaf1504InnerLog leaf1504Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi131RoundedFacts
    innerPair17RoundedFacts leaf1504RoundedFacts (by rfl)

private theorem leaf1504FlatSound : Sound leaf1504Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1504CertificateValid
    leaf1504InnerLogValid leaf1504CoversExact leaf1504LowerChecked

private noncomputable def leaf1505Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1505Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871173/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107499) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (707221085/536870912) }, upper := { exponent := 0, mantissa := (5461/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216427/134214998) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf1505InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1505LocalValidity :
    LeafFacts leaf1505Box leaf1505Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1505Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107499) }) = true
      norm_num [leaf1505Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1505CertificateValid :
    WideCertificateValid leaf1505Box leaf1505Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi132ValidityFacts
    leaf1505LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1505CoverageChecked :
    coverageCheck (innerAD leaf1505Box) leaf1505InnerLog = true := by
  rfl'

private theorem leaf1505InnerLogValid :
    leaf1505InnerLog.Valid 8 (innerAD leaf1505Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1505CoverageChecked

private noncomputable def leaf1505InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1505InputLogOnePlusV_eq :
    leaf1505InputLogOnePlusV = outerEnclosure 24
      (leaf1505Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1505RoundedFacts : LeafRoundedFacts 8
    leaf1505Certificate.logOnePlusV leaf1505InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1505InputLogOnePlusV_eq }

private noncomputable def leaf1505Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi132InputQChi innerPair21Input
    leaf1505InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1505LowerChecked :
    lowerCheck 24 leaf1505Box leaf1505Inputs = true := by
  rfl'

private theorem leaf1505CoversExact : CoversExact 8
    leaf1505Box leaf1505Certificate leaf1505InnerLog leaf1505Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi132RoundedFacts
    innerPair21RoundedFacts leaf1505RoundedFacts (by rfl)

private theorem leaf1505FlatSound : Sound leaf1505Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1505CertificateValid
    leaf1505InnerLogValid leaf1505CoversExact leaf1505LowerChecked

private noncomputable def leaf1506Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1506Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871175/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553743) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (708859383/536870912) }, upper := { exponent := 0, mantissa := (2737/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108207/67107486) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf1506InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1506LocalValidity :
    LeafFacts leaf1506Box leaf1506Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1506Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553743) }) = true
      norm_num [leaf1506Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1506CertificateValid :
    WideCertificateValid leaf1506Box leaf1506Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi132ValidityFacts
    leaf1506LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1506CoverageChecked :
    coverageCheck (innerAD leaf1506Box) leaf1506InnerLog = true := by
  rfl'

private theorem leaf1506InnerLogValid :
    leaf1506InnerLog.Valid 8 (innerAD leaf1506Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1506CoverageChecked

private noncomputable def leaf1506InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1506InputLogOnePlusV_eq :
    leaf1506InputLogOnePlusV = outerEnclosure 24
      (leaf1506Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1506RoundedFacts : LeafRoundedFacts 8
    leaf1506Certificate.logOnePlusV leaf1506InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1506InputLogOnePlusV_eq }

private noncomputable def leaf1506Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi132InputQChi innerPair21Input
    leaf1506InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1506LowerChecked :
    lowerCheck 24 leaf1506Box leaf1506Inputs = true := by
  rfl'

private theorem leaf1506CoversExact : CoversExact 8
    leaf1506Box leaf1506Certificate leaf1506InnerLog leaf1506Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi132RoundedFacts
    innerPair21RoundedFacts leaf1506RoundedFacts (by rfl)

private theorem leaf1506FlatSound : Sound leaf1506Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1506CertificateValid
    leaf1506InnerLogValid leaf1506CoversExact leaf1506LowerChecked

private noncomputable def leaf1507Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1507Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871175/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214893) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (714036411/536870912) }, upper := { exponent := 0, mantissa := (11027/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432749/268429786) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf1507InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1507LocalValidity :
    LeafFacts leaf1507Box leaf1507Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1507Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214893) }) = true
      norm_num [leaf1507Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1507CertificateValid :
    WideCertificateValid leaf1507Box leaf1507Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi149ValidityFacts
    leaf1507LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1507CoverageChecked :
    coverageCheck (innerAD leaf1507Box) leaf1507InnerLog = true := by
  rfl'

private theorem leaf1507InnerLogValid :
    leaf1507InnerLog.Valid 8 (innerAD leaf1507Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1507CoverageChecked

private noncomputable def leaf1507InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814633/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1507InputLogOnePlusV_eq :
    leaf1507InputLogOnePlusV = outerEnclosure 24
      (leaf1507Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1507RoundedFacts : LeafRoundedFacts 8
    leaf1507Certificate.logOnePlusV leaf1507InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1507InputLogOnePlusV_eq }

private noncomputable def leaf1507Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi149InputQChi innerPair21Input
    leaf1507InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1507LowerChecked :
    lowerCheck 24 leaf1507Box leaf1507Inputs = true := by
  rfl'

private theorem leaf1507CoversExact : CoversExact 8
    leaf1507Box leaf1507Certificate leaf1507InnerLog leaf1507Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi149RoundedFacts
    innerPair21RoundedFacts leaf1507RoundedFacts (by rfl)

private theorem leaf1507FlatSound : Sound leaf1507Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1507CertificateValid
    leaf1507InnerLogValid leaf1507CoversExact leaf1507LowerChecked

private noncomputable def leaf1508Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1508Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871177/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107433) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (715740241/536870912) }, upper := { exponent := 0, mantissa := (5527/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216361/134214866) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf1508InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1508LocalValidity :
    LeafFacts leaf1508Box leaf1508Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1508Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107433) }) = true
      norm_num [leaf1508Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1508CertificateValid :
    WideCertificateValid leaf1508Box leaf1508Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi149ValidityFacts
    leaf1508LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1508CoverageChecked :
    coverageCheck (innerAD leaf1508Box) leaf1508InnerLog = true := by
  rfl'

private theorem leaf1508InnerLogValid :
    leaf1508InnerLog.Valid 8 (innerAD leaf1508Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1508CoverageChecked

private noncomputable def leaf1508InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1508InputLogOnePlusV_eq :
    leaf1508InputLogOnePlusV = outerEnclosure 24
      (leaf1508Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1508RoundedFacts : LeafRoundedFacts 8
    leaf1508Certificate.logOnePlusV leaf1508InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1508InputLogOnePlusV_eq }

private noncomputable def leaf1508Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi149InputQChi innerPair21Input
    leaf1508InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1508LowerChecked :
    lowerCheck 24 leaf1508Box leaf1508Inputs = true := by
  rfl'

private theorem leaf1508CoversExact : CoversExact 8
    leaf1508Box leaf1508Certificate leaf1508InnerLog leaf1508Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi149RoundedFacts
    innerPair21RoundedFacts leaf1508RoundedFacts (by rfl)

private theorem leaf1508FlatSound : Sound leaf1508Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1508CertificateValid
    leaf1508InnerLogValid leaf1508CoversExact leaf1508LowerChecked

private noncomputable def leaf1509Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1509Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871177/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553697) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (720851737/536870912) }, upper := { exponent := 0, mantissa := (2783/2048) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108161/67107394) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf1509InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1509LocalValidity :
    LeafFacts leaf1509Box leaf1509Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1509Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553697) }) = true
      norm_num [leaf1509Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1509CertificateValid :
    WideCertificateValid leaf1509Box leaf1509Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi150ValidityFacts
    leaf1509LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1509CoverageChecked :
    coverageCheck (innerAD leaf1509Box) leaf1509InnerLog = true := by
  rfl'

private theorem leaf1509InnerLogValid :
    leaf1509InnerLog.Valid 8 (innerAD leaf1509Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1509CoverageChecked

private noncomputable def leaf1509InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1509InputLogOnePlusV_eq :
    leaf1509InputLogOnePlusV = outerEnclosure 24
      (leaf1509Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1509RoundedFacts : LeafRoundedFacts 8
    leaf1509Certificate.logOnePlusV leaf1509InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1509InputLogOnePlusV_eq }

private noncomputable def leaf1509Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi150InputQChi innerPair21Input
    leaf1509InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1509LowerChecked :
    lowerCheck 24 leaf1509Box leaf1509Inputs = true := by
  rfl'

private theorem leaf1509CoversExact : CoversExact 8
    leaf1509Box leaf1509Certificate leaf1509InnerLog leaf1509Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi150RoundedFacts
    innerPair21RoundedFacts leaf1509RoundedFacts (by rfl)

private theorem leaf1509FlatSound : Sound leaf1509Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1509CertificateValid
    leaf1509InnerLogValid leaf1509CoversExact leaf1509LowerChecked

private noncomputable def leaf1510Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1510Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871179/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776845) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (722621099/536870912) }, upper := { exponent := 0, mantissa := (1395/1024) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554077/33553690) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf1510InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1510LocalValidity :
    LeafFacts leaf1510Box leaf1510Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1510Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776845) }) = true
      norm_num [leaf1510Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1510CertificateValid :
    WideCertificateValid leaf1510Box leaf1510Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi150ValidityFacts
    leaf1510LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1510CoverageChecked :
    coverageCheck (innerAD leaf1510Box) leaf1510InnerLog = true := by
  rfl'

private theorem leaf1510InnerLogValid :
    leaf1510InnerLog.Valid 8 (innerAD leaf1510Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1510CoverageChecked

private noncomputable def leaf1510InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814637/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1510InputLogOnePlusV_eq :
    leaf1510InputLogOnePlusV = outerEnclosure 24
      (leaf1510Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1510RoundedFacts : LeafRoundedFacts 8
    leaf1510Certificate.logOnePlusV leaf1510InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1510InputLogOnePlusV_eq }

private noncomputable def leaf1510Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi150InputQChi innerPair21Input
    leaf1510InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1510LowerChecked :
    lowerCheck 24 leaf1510Box leaf1510Inputs = true := by
  rfl'

private theorem leaf1510CoversExact : CoversExact 8
    leaf1510Box leaf1510Certificate leaf1510InnerLog leaf1510Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi150RoundedFacts
    innerPair21RoundedFacts leaf1510RoundedFacts (by rfl)

private theorem leaf1510FlatSound : Sound leaf1510Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1510CertificateValid
    leaf1510InnerLogValid leaf1510CoversExact leaf1510LowerChecked

private noncomputable def leaf1511Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1511Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871175/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134215053) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (703551291/536870912) }, upper := { exponent := 0, mantissa := (10867/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432909/268430106) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf1511InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf1511LocalValidity :
    LeafFacts leaf1511Box leaf1511Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1511Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134215053) }) = true
      norm_num [leaf1511Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1511CertificateValid :
    WideCertificateValid leaf1511Box leaf1511Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi131ValidityFacts
    leaf1511LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1511CoverageChecked :
    coverageCheck (innerAD leaf1511Box) leaf1511InnerLog = true := by
  rfl'

private theorem leaf1511InnerLogValid :
    leaf1511InnerLog.Valid 8 (innerAD leaf1511Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf1511CoverageChecked

private noncomputable def leaf1511InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453657/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1511InputLogOnePlusV_eq :
    leaf1511InputLogOnePlusV = outerEnclosure 24
      (leaf1511Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1511RoundedFacts : LeafRoundedFacts 8
    leaf1511Certificate.logOnePlusV leaf1511InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1511InputLogOnePlusV_eq }

private noncomputable def leaf1511Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi131InputQChi innerPair17Input
    leaf1511InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1511LowerChecked :
    lowerCheck 24 leaf1511Box leaf1511Inputs = true := by
  rfl'

private theorem leaf1511CoversExact : CoversExact 8
    leaf1511Box leaf1511Certificate leaf1511InnerLog leaf1511Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi131RoundedFacts
    innerPair17RoundedFacts leaf1511RoundedFacts (by rfl)

private theorem leaf1511FlatSound : Sound leaf1511Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1511CertificateValid
    leaf1511InnerLogValid leaf1511CoversExact leaf1511LowerChecked

private noncomputable def leaf1512Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1512Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871177/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553757) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (705124057/536870912) }, upper := { exponent := 0, mantissa := (2723/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108221/67107514) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf1512InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1512LocalValidity :
    LeafFacts leaf1512Box leaf1512Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1512Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553757) }) = true
      norm_num [leaf1512Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1512CertificateValid :
    WideCertificateValid leaf1512Box leaf1512Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi131ValidityFacts
    leaf1512LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1512CoverageChecked :
    coverageCheck (innerAD leaf1512Box) leaf1512InnerLog = true := by
  rfl'

private theorem leaf1512InnerLogValid :
    leaf1512InnerLog.Valid 8 (innerAD leaf1512Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1512CoverageChecked

private noncomputable def leaf1512InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1512InputLogOnePlusV_eq :
    leaf1512InputLogOnePlusV = outerEnclosure 24
      (leaf1512Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1512RoundedFacts : LeafRoundedFacts 8
    leaf1512Certificate.logOnePlusV leaf1512InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1512InputLogOnePlusV_eq }

private noncomputable def leaf1512Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi131InputQChi innerPair21Input
    leaf1512InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1512LowerChecked :
    lowerCheck 24 leaf1512Box leaf1512Inputs = true := by
  rfl'

private theorem leaf1512CoversExact : CoversExact 8
    leaf1512Box leaf1512Certificate leaf1512InnerLog leaf1512Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi131RoundedFacts
    innerPair21RoundedFacts leaf1512RoundedFacts (by rfl)

private theorem leaf1512FlatSound : Sound leaf1512Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1512CertificateValid
    leaf1512InnerLogValid leaf1512CoversExact leaf1512LowerChecked

private noncomputable def leaf1513Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1513Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871177/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107473) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (710497681/536870912) }, upper := { exponent := 0, mantissa := (5487/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216401/134214946) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf1513InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1513LocalValidity :
    LeafFacts leaf1513Box leaf1513Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1513Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107473) }) = true
      norm_num [leaf1513Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1513CertificateValid :
    WideCertificateValid leaf1513Box leaf1513Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi132ValidityFacts
    leaf1513LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1513CoverageChecked :
    coverageCheck (innerAD leaf1513Box) leaf1513InnerLog = true := by
  rfl'

private theorem leaf1513InnerLogValid :
    leaf1513InnerLog.Valid 8 (innerAD leaf1513Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1513CoverageChecked

private noncomputable def leaf1513InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1513InputLogOnePlusV_eq :
    leaf1513InputLogOnePlusV = outerEnclosure 24
      (leaf1513Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1513RoundedFacts : LeafRoundedFacts 8
    leaf1513Certificate.logOnePlusV leaf1513InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1513InputLogOnePlusV_eq }

private noncomputable def leaf1513Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi132InputQChi innerPair21Input
    leaf1513InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1513LowerChecked :
    lowerCheck 24 leaf1513Box leaf1513Inputs = true := by
  rfl'

private theorem leaf1513CoversExact : CoversExact 8
    leaf1513Box leaf1513Certificate leaf1513InnerLog leaf1513Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi132RoundedFacts
    innerPair21RoundedFacts leaf1513RoundedFacts (by rfl)

private theorem leaf1513FlatSound : Sound leaf1513Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1513CertificateValid
    leaf1513InnerLogValid leaf1513CoversExact leaf1513LowerChecked

private noncomputable def leaf1514Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1514Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871179/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776865) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (712135979/536870912) }, upper := { exponent := 0, mantissa := (1375/1024) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554097/33553730) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf1514InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1514LocalValidity :
    LeafFacts leaf1514Box leaf1514Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1514Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776865) }) = true
      norm_num [leaf1514Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1514CertificateValid :
    WideCertificateValid leaf1514Box leaf1514Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi132ValidityFacts
    leaf1514LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1514CoverageChecked :
    coverageCheck (innerAD leaf1514Box) leaf1514InnerLog = true := by
  rfl'

private theorem leaf1514InnerLogValid :
    leaf1514InnerLog.Valid 8 (innerAD leaf1514Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1514CoverageChecked

private noncomputable def leaf1514InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726829/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1514InputLogOnePlusV_eq :
    leaf1514InputLogOnePlusV = outerEnclosure 24
      (leaf1514Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1514RoundedFacts : LeafRoundedFacts 8
    leaf1514Certificate.logOnePlusV leaf1514InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1514InputLogOnePlusV_eq }

private noncomputable def leaf1514Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi132InputQChi innerPair21Input
    leaf1514InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1514LowerChecked :
    lowerCheck 24 leaf1514Box leaf1514Inputs = true := by
  rfl'

private theorem leaf1514CoversExact : CoversExact 8
    leaf1514Box leaf1514Certificate leaf1514InnerLog leaf1514Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi132RoundedFacts
    innerPair21RoundedFacts leaf1514RoundedFacts (by rfl)

private theorem leaf1514FlatSound : Sound leaf1514Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1514CertificateValid
    leaf1514InnerLogValid leaf1514CoversExact leaf1514LowerChecked

private noncomputable def leaf1515Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1515Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871179/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214839) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (717444071/536870912) }, upper := { exponent := 0, mantissa := (11081/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432695/268429678) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf1515InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1515LocalValidity :
    LeafFacts leaf1515Box leaf1515Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1515Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214839) }) = true
      norm_num [leaf1515Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1515CertificateValid :
    WideCertificateValid leaf1515Box leaf1515Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi149ValidityFacts
    leaf1515LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1515CoverageChecked :
    coverageCheck (innerAD leaf1515Box) leaf1515InnerLog = true := by
  rfl'

private theorem leaf1515InnerLogValid :
    leaf1515InnerLog.Valid 8 (innerAD leaf1515Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1515CoverageChecked

private noncomputable def leaf1515InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1515InputLogOnePlusV_eq :
    leaf1515InputLogOnePlusV = outerEnclosure 24
      (leaf1515Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1515RoundedFacts : LeafRoundedFacts 8
    leaf1515Certificate.logOnePlusV leaf1515InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1515InputLogOnePlusV_eq }

private noncomputable def leaf1515Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi149InputQChi innerPair21Input
    leaf1515InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1515LowerChecked :
    lowerCheck 24 leaf1515Box leaf1515Inputs = true := by
  rfl'

private theorem leaf1515CoversExact : CoversExact 8
    leaf1515Box leaf1515Certificate leaf1515InnerLog leaf1515Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi149RoundedFacts
    innerPair21RoundedFacts leaf1515RoundedFacts (by rfl)

private theorem leaf1515FlatSound : Sound leaf1515Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1515CertificateValid
    leaf1515InnerLogValid leaf1515CoversExact leaf1515LowerChecked

private noncomputable def leaf1516Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1516Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871181/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553703) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (719147901/536870912) }, upper := { exponent := 0, mantissa := (2777/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108167/67107406) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf1516InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1516LocalValidity :
    LeafFacts leaf1516Box leaf1516Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1516Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553703) }) = true
      norm_num [leaf1516Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1516CertificateValid :
    WideCertificateValid leaf1516Box leaf1516Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi149ValidityFacts
    leaf1516LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1516CoverageChecked :
    coverageCheck (innerAD leaf1516Box) leaf1516InnerLog = true := by
  rfl'

private theorem leaf1516InnerLogValid :
    leaf1516InnerLog.Valid 8 (innerAD leaf1516Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1516CoverageChecked

private noncomputable def leaf1516InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1516InputLogOnePlusV_eq :
    leaf1516InputLogOnePlusV = outerEnclosure 24
      (leaf1516Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1516RoundedFacts : LeafRoundedFacts 8
    leaf1516Certificate.logOnePlusV leaf1516InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1516InputLogOnePlusV_eq }

private noncomputable def leaf1516Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi149InputQChi innerPair21Input
    leaf1516InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1516LowerChecked :
    lowerCheck 24 leaf1516Box leaf1516Inputs = true := by
  rfl'

private theorem leaf1516CoversExact : CoversExact 8
    leaf1516Box leaf1516Certificate leaf1516InnerLog leaf1516Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi149RoundedFacts
    innerPair21RoundedFacts leaf1516RoundedFacts (by rfl)

private theorem leaf1516FlatSound : Sound leaf1516Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1516CertificateValid
    leaf1516InnerLogValid leaf1516CoversExact leaf1516LowerChecked

private noncomputable def leaf1517Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1517Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871181/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553683) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (724390461/536870912) }, upper := { exponent := 0, mantissa := (2797/2048) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108147/67107366) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf1517InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1517LocalValidity :
    LeafFacts leaf1517Box leaf1517Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1517Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553683) }) = true
      norm_num [leaf1517Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1517CertificateValid :
    WideCertificateValid leaf1517Box leaf1517Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi150ValidityFacts
    leaf1517LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1517CoverageChecked :
    coverageCheck (innerAD leaf1517Box) leaf1517InnerLog = true := by
  rfl'

private theorem leaf1517InnerLogValid :
    leaf1517InnerLog.Valid 8 (innerAD leaf1517Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1517CoverageChecked

private noncomputable def leaf1517InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1517InputLogOnePlusV_eq :
    leaf1517InputLogOnePlusV = outerEnclosure 24
      (leaf1517Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1517RoundedFacts : LeafRoundedFacts 8
    leaf1517Certificate.logOnePlusV leaf1517InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1517InputLogOnePlusV_eq }

private noncomputable def leaf1517Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi150InputQChi innerPair21Input
    leaf1517InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1517LowerChecked :
    lowerCheck 24 leaf1517Box leaf1517Inputs = true := by
  rfl'

private theorem leaf1517CoversExact : CoversExact 8
    leaf1517Box leaf1517Certificate leaf1517InnerLog leaf1517Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi150RoundedFacts
    innerPair21RoundedFacts leaf1517RoundedFacts (by rfl)

private theorem leaf1517FlatSound : Sound leaf1517Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1517CertificateValid
    leaf1517InnerLogValid leaf1517CoversExact leaf1517LowerChecked

private noncomputable def leaf1518Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1518Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871183/536870912) }, vSqrt := { lower := (65529/65536), upper := (8388616/8388419) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (726159823/536870912) }, upper := { exponent := 0, mantissa := (701/512) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16777035/16776838) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf1518InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1518LocalValidity :
    LeafFacts leaf1518Box leaf1518Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1518Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8388616/8388419) }) = true
      norm_num [leaf1518Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1518CertificateValid :
    WideCertificateValid leaf1518Box leaf1518Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi150ValidityFacts
    leaf1518LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1518CoverageChecked :
    coverageCheck (innerAD leaf1518Box) leaf1518InnerLog = true := by
  rfl'

private theorem leaf1518InnerLogValid :
    leaf1518InnerLog.Valid 8 (innerAD leaf1518Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1518CoverageChecked

private noncomputable def leaf1518InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814639/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1518InputLogOnePlusV_eq :
    leaf1518InputLogOnePlusV = outerEnclosure 24
      (leaf1518Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1518RoundedFacts : LeafRoundedFacts 8
    leaf1518Certificate.logOnePlusV leaf1518InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1518InputLogOnePlusV_eq }

private noncomputable def leaf1518Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi150InputQChi innerPair21Input
    leaf1518InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1518LowerChecked :
    lowerCheck 24 leaf1518Box leaf1518Inputs = true := by
  rfl'

private theorem leaf1518CoversExact : CoversExact 8
    leaf1518Box leaf1518Certificate leaf1518InnerLog leaf1518Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi150RoundedFacts
    innerPair21RoundedFacts leaf1518RoundedFacts (by rfl)

private theorem leaf1518FlatSound : Sound leaf1518Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1518CertificateValid
    leaf1518InnerLogValid leaf1518CoversExact leaf1518LowerChecked

private noncomputable def leaf1519Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1519Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435695/268435456) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107289) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (363817043/268435456) }, upper := { exponent := 0, mantissa := (5671/4096) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216217/134214578) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf1519InnerLog : WideLogData :=
  innerPair142Data

set_option maxRecDepth 1000000 in
private theorem leaf1519LocalValidity :
    LeafFacts leaf1519Box leaf1519Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1519Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107289) }) = true
      norm_num [leaf1519Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1519CertificateValid :
    WideCertificateValid leaf1519Box leaf1519Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi98ValidityFacts
    leaf1519LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1519CoverageChecked :
    coverageCheck (innerAD leaf1519Box) leaf1519InnerLog = true := by
  rfl'

private theorem leaf1519InnerLogValid :
    leaf1519InnerLog.Valid 8 (innerAD leaf1519Box) :=
  wideLogDataValid_of_cachedCheck endpoint37PositiveFacts
    endpoint34PositiveFacts.valid leaf1519CoverageChecked

private noncomputable def leaf1519InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1519InputLogOnePlusV_eq :
    leaf1519InputLogOnePlusV = outerEnclosure 24
      (leaf1519Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1519RoundedFacts : LeafRoundedFacts 8
    leaf1519Certificate.logOnePlusV leaf1519InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1519InputLogOnePlusV_eq }

private noncomputable def leaf1519Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi98InputQChi innerPair142Input
    leaf1519InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1519LowerChecked :
    lowerCheck 24 leaf1519Box leaf1519Inputs = true := by
  rfl'

private theorem leaf1519CoversExact : CoversExact 8
    leaf1519Box leaf1519Certificate leaf1519InnerLog leaf1519Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi98RoundedFacts
    innerPair142RoundedFacts leaf1519RoundedFacts (by rfl)

private theorem leaf1519FlatSound : Sound leaf1519Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1519CertificateValid
    leaf1519InnerLogValid leaf1519CoversExact leaf1519LowerChecked

private noncomputable def leaf1520Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (7/64), chiHi := (15/128) }

private noncomputable def leaf1520Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (268435697/268435456) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553637) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (364734489/268435456) }, upper := { exponent := 0, mantissa := (2843/2048) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi98LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108101/67107274) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf1520InnerLog : WideLogData :=
  innerPair142Data

set_option maxRecDepth 1000000 in
private theorem leaf1520LocalValidity :
    LeafFacts leaf1520Box leaf1520Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1520Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553637) }) = true
      norm_num [leaf1520Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1520CertificateValid :
    WideCertificateValid leaf1520Box leaf1520Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi98ValidityFacts
    leaf1520LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1520CoverageChecked :
    coverageCheck (innerAD leaf1520Box) leaf1520InnerLog = true := by
  rfl'

private theorem leaf1520InnerLogValid :
    leaf1520InnerLog.Valid 8 (innerAD leaf1520Box) :=
  wideLogDataValid_of_cachedCheck endpoint37PositiveFacts
    endpoint34PositiveFacts.valid leaf1520CoverageChecked

private noncomputable def leaf1520InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629287/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1520InputLogOnePlusV_eq :
    leaf1520InputLogOnePlusV = outerEnclosure 24
      (leaf1520Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1520RoundedFacts : LeafRoundedFacts 8
    leaf1520Certificate.logOnePlusV leaf1520InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1520InputLogOnePlusV_eq }

private noncomputable def leaf1520Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi98InputQChi innerPair142Input
    leaf1520InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1520LowerChecked :
    lowerCheck 24 leaf1520Box leaf1520Inputs = true := by
  rfl'

private theorem leaf1520CoversExact : CoversExact 8
    leaf1520Box leaf1520Certificate leaf1520InnerLog leaf1520Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi98RoundedFacts
    innerPair142RoundedFacts leaf1520RoundedFacts (by rfl)

private theorem leaf1520FlatSound : Sound leaf1520Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1520CertificateValid
    leaf1520InnerLogValid leaf1520CoversExact leaf1520LowerChecked

private noncomputable def leaf1521Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (15/128), chiHi := (31/256) }

private noncomputable def leaf1521Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871183/536870912) }, vSqrt := { lower := (65529/65536), upper := (7895168/7894969) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (741297715/536870912) }, upper := { exponent := 0, mantissa := (11447/8192) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi153LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (15790137/15789938) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf1521InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1521LocalValidity :
    LeafFacts leaf1521Box leaf1521Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1521Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (7895168/7894969) }) = true
      norm_num [leaf1521Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1521CertificateValid :
    WideCertificateValid leaf1521Box leaf1521Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi153ValidityFacts
    leaf1521LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1521CoverageChecked :
    coverageCheck (innerAD leaf1521Box) leaf1521InnerLog = true := by
  rfl'

private theorem leaf1521InnerLogValid :
    leaf1521InnerLog.Valid 8 (innerAD leaf1521Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1521CoverageChecked

private noncomputable def leaf1521InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907323/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1521InputLogOnePlusV_eq :
    leaf1521InputLogOnePlusV = outerEnclosure 24
      (leaf1521Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1521RoundedFacts : LeafRoundedFacts 8
    leaf1521Certificate.logOnePlusV leaf1521InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1521InputLogOnePlusV_eq }

private noncomputable def leaf1521Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi153InputQChi innerPair26Input
    leaf1521InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1521LowerChecked :
    lowerCheck 24 leaf1521Box leaf1521Inputs = true := by
  rfl'

private theorem leaf1521CoversExact : CoversExact 8
    leaf1521Box leaf1521Certificate leaf1521InnerLog leaf1521Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi153RoundedFacts
    innerPair26RoundedFacts leaf1521RoundedFacts (by rfl)

private theorem leaf1521FlatSound : Sound leaf1521Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1521CertificateValid
    leaf1521InnerLogValid leaf1521CoversExact leaf1521LowerChecked

private noncomputable def leaf1522Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (31/256), chiHi := (1/8) }

private noncomputable def leaf1522Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (65529/65536), upper := (4194308/4194199) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (748113041/536870912) }, upper := { exponent := 0, mantissa := (361/256) } }, logOuter := sk141LogOuterCertificate, logK := sk141LogKCertificate, logChi := chi154LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388507/8388398) } }, logDArg := sk141LogDArgCertificate }

private noncomputable def leaf1522InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1522LocalValidity :
    LeafFacts leaf1522Box leaf1522Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1522Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194308/4194199) }) = true
      norm_num [leaf1522Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1522CertificateValid :
    WideCertificateValid leaf1522Box leaf1522Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk141ValidityFacts chi154ValidityFacts
    leaf1522LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1522CoverageChecked :
    coverageCheck (innerAD leaf1522Box) leaf1522InnerLog = true := by
  rfl'

private theorem leaf1522InnerLogValid :
    leaf1522InnerLog.Valid 8 (innerAD leaf1522Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1522CoverageChecked

private noncomputable def leaf1522InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1522InputLogOnePlusV_eq :
    leaf1522InputLogOnePlusV = outerEnclosure 24
      (leaf1522Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1522RoundedFacts : LeafRoundedFacts 8
    leaf1522Certificate.logOnePlusV leaf1522InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1522InputLogOnePlusV_eq }

private noncomputable def leaf1522Inputs : Inputs :=
  inputsOfCaches globalInput sk141RoundedInputs
    chi154InputQChi innerPair26Input
    leaf1522InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1522LowerChecked :
    lowerCheck 24 leaf1522Box leaf1522Inputs = true := by
  rfl'

private theorem leaf1522CoversExact : CoversExact 8
    leaf1522Box leaf1522Certificate leaf1522InnerLog leaf1522Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk141RoundedFacts chi154RoundedFacts
    innerPair26RoundedFacts leaf1522RoundedFacts (by rfl)

private theorem leaf1522FlatSound : Sound leaf1522Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1522CertificateValid
    leaf1522InnerLogValid leaf1522CoversExact leaf1522LowerChecked

private noncomputable def leaf1523Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (15/128), chiHi := (31/256) }

private noncomputable def leaf1523Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107221) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (743263673/536870912) }, upper := { exponent := 0, mantissa := (5739/4096) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi153LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216149/134214442) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf1523InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1523LocalValidity :
    LeafFacts leaf1523Box leaf1523Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1523Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107221) }) = true
      norm_num [leaf1523Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1523CertificateValid :
    WideCertificateValid leaf1523Box leaf1523Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi153ValidityFacts
    leaf1523LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1523CoverageChecked :
    coverageCheck (innerAD leaf1523Box) leaf1523InnerLog = true := by
  rfl'

private theorem leaf1523InnerLogValid :
    leaf1523InnerLog.Valid 8 (innerAD leaf1523Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1523CoverageChecked

private noncomputable def leaf1523InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814647/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1523InputLogOnePlusV_eq :
    leaf1523InputLogOnePlusV = outerEnclosure 24
      (leaf1523Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1523RoundedFacts : LeafRoundedFacts 8
    leaf1523Certificate.logOnePlusV leaf1523InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1523InputLogOnePlusV_eq }

private noncomputable def leaf1523Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi153InputQChi innerPair26Input
    leaf1523InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1523LowerChecked :
    lowerCheck 24 leaf1523Box leaf1523Inputs = true := by
  rfl'

private theorem leaf1523CoversExact : CoversExact 8
    leaf1523Box leaf1523Certificate leaf1523InnerLog leaf1523Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi153RoundedFacts
    innerPair26RoundedFacts leaf1523RoundedFacts (by rfl)

private theorem leaf1523FlatSound : Sound leaf1523Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1523CertificateValid
    leaf1523InnerLogValid leaf1523CoversExact leaf1523LowerChecked

private noncomputable def leaf1524Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (31/256), chiHi := (1/8) }

private noncomputable def leaf1524Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (65529/65536), upper := (2097154/2097099) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (750144531/536870912) }, upper := { exponent := 0, mantissa := (181/128) } }, logOuter := sk142LogOuterCertificate, logK := sk142LogKCertificate, logChi := chi154LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4194253/4194198) } }, logDArg := sk142LogDArgCertificate }

private noncomputable def leaf1524InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1524LocalValidity :
    LeafFacts leaf1524Box leaf1524Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1524Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2097154/2097099) }) = true
      norm_num [leaf1524Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1524CertificateValid :
    WideCertificateValid leaf1524Box leaf1524Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk142ValidityFacts chi154ValidityFacts
    leaf1524LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1524CoverageChecked :
    coverageCheck (innerAD leaf1524Box) leaf1524InnerLog = true := by
  rfl'

private theorem leaf1524InnerLogValid :
    leaf1524InnerLog.Valid 8 (innerAD leaf1524Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1524CoverageChecked

private noncomputable def leaf1524InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629301/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1524InputLogOnePlusV_eq :
    leaf1524InputLogOnePlusV = outerEnclosure 24
      (leaf1524Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1524RoundedFacts : LeafRoundedFacts 8
    leaf1524Certificate.logOnePlusV leaf1524InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1524InputLogOnePlusV_eq }

private noncomputable def leaf1524Inputs : Inputs :=
  inputsOfCaches globalInput sk142RoundedInputs
    chi154InputQChi innerPair26Input
    leaf1524InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1524LowerChecked :
    lowerCheck 24 leaf1524Box leaf1524Inputs = true := by
  rfl'

private theorem leaf1524CoversExact : CoversExact 8
    leaf1524Box leaf1524Certificate leaf1524InnerLog leaf1524Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk142RoundedFacts chi154RoundedFacts
    innerPair26RoundedFacts leaf1524RoundedFacts (by rfl)

private theorem leaf1524FlatSound : Sound leaf1524Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1524CertificateValid
    leaf1524InnerLogValid leaf1524CoversExact leaf1524LowerChecked

private noncomputable def leaf1525Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1525Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871183/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214625) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (731336851/536870912) }, upper := { exponent := 0, mantissa := (11295/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432481/268429250) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf1525InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1525LocalValidity :
    LeafFacts leaf1525Box leaf1525Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1525Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214625) }) = true
      norm_num [leaf1525Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1525CertificateValid :
    WideCertificateValid leaf1525Box leaf1525Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi155ValidityFacts
    leaf1525LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1525CoverageChecked :
    coverageCheck (innerAD leaf1525Box) leaf1525InnerLog = true := by
  rfl'

private theorem leaf1525InnerLogValid :
    leaf1525InnerLog.Valid 8 (innerAD leaf1525Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1525CoverageChecked

private noncomputable def leaf1525InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629283/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1525InputLogOnePlusV_eq :
    leaf1525InputLogOnePlusV = outerEnclosure 24
      (leaf1525Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1525RoundedFacts : LeafRoundedFacts 8
    leaf1525Certificate.logOnePlusV leaf1525InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1525InputLogOnePlusV_eq }

private noncomputable def leaf1525Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi155InputQChi innerPair22Input
    leaf1525InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1525LowerChecked :
    lowerCheck 24 leaf1525Box leaf1525Inputs = true := by
  rfl'

private theorem leaf1525CoversExact : CoversExact 8
    leaf1525Box leaf1525Certificate leaf1525InnerLog leaf1525Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi155RoundedFacts
    innerPair22RoundedFacts leaf1525RoundedFacts (by rfl)

private theorem leaf1525FlatSound : Sound leaf1525Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1525CertificateValid
    leaf1525InnerLogValid leaf1525CoversExact leaf1525LowerChecked

private noncomputable def leaf1526Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1526Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553649) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (733171745/536870912) }, upper := { exponent := 0, mantissa := (2831/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108113/67107298) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf1526InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1526LocalValidity :
    LeafFacts leaf1526Box leaf1526Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1526Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553649) }) = true
      norm_num [leaf1526Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1526CertificateValid :
    WideCertificateValid leaf1526Box leaf1526Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi155ValidityFacts
    leaf1526LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1526CoverageChecked :
    coverageCheck (innerAD leaf1526Box) leaf1526InnerLog = true := by
  rfl'

private theorem leaf1526InnerLogValid :
    leaf1526InnerLog.Valid 8 (innerAD leaf1526Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1526CoverageChecked

private noncomputable def leaf1526InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907321/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1526InputLogOnePlusV_eq :
    leaf1526InputLogOnePlusV = outerEnclosure 24
      (leaf1526Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1526RoundedFacts : LeafRoundedFacts 8
    leaf1526Certificate.logOnePlusV leaf1526InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1526InputLogOnePlusV_eq }

private noncomputable def leaf1526Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi155InputQChi innerPair22Input
    leaf1526InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1526LowerChecked :
    lowerCheck 24 leaf1526Box leaf1526Inputs = true := by
  rfl'

private theorem leaf1526CoversExact : CoversExact 8
    leaf1526Box leaf1526Certificate leaf1526InnerLog leaf1526Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi155RoundedFacts
    innerPair22RoundedFacts leaf1526RoundedFacts (by rfl)

private theorem leaf1526FlatSound : Sound leaf1526Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1526CertificateValid
    leaf1526InnerLogValid leaf1526CoversExact leaf1526LowerChecked

private noncomputable def leaf1527Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (29/256), chiHi := (15/128) }

private noncomputable def leaf1527Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107259) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (738283241/536870912) }, upper := { exponent := 0, mantissa := (5701/4096) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi156LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216187/134214518) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf1527InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1527LocalValidity :
    LeafFacts leaf1527Box leaf1527Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1527Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107259) }) = true
      norm_num [leaf1527Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1527CertificateValid :
    WideCertificateValid leaf1527Box leaf1527Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi156ValidityFacts
    leaf1527LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1527CoverageChecked :
    coverageCheck (innerAD leaf1527Box) leaf1527InnerLog = true := by
  rfl'

private theorem leaf1527InnerLogValid :
    leaf1527InnerLog.Valid 8 (innerAD leaf1527Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1527CoverageChecked

private noncomputable def leaf1527InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1527InputLogOnePlusV_eq :
    leaf1527InputLogOnePlusV = outerEnclosure 24
      (leaf1527Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1527RoundedFacts : LeafRoundedFacts 8
    leaf1527Certificate.logOnePlusV leaf1527InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1527InputLogOnePlusV_eq }

private noncomputable def leaf1527Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi156InputQChi innerPair26Input
    leaf1527InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1527LowerChecked :
    lowerCheck 24 leaf1527Box leaf1527Inputs = true := by
  rfl'

private theorem leaf1527CoversExact : CoversExact 8
    leaf1527Box leaf1527Certificate leaf1527InnerLog leaf1527Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi156RoundedFacts
    innerPair26RoundedFacts leaf1527RoundedFacts (by rfl)

private theorem leaf1527FlatSound : Sound leaf1527Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1527CertificateValid
    leaf1527InnerLogValid leaf1527CoversExact leaf1527LowerChecked

private noncomputable def leaf1528Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (29/256), chiHi := (15/128) }

private noncomputable def leaf1528Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776811) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (740183667/536870912) }, upper := { exponent := 0, mantissa := (1429/1024) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi156LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554043/33553622) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf1528InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1528LocalValidity :
    LeafFacts leaf1528Box leaf1528Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1528Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776811) }) = true
      norm_num [leaf1528Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1528CertificateValid :
    WideCertificateValid leaf1528Box leaf1528Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi156ValidityFacts
    leaf1528LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1528CoverageChecked :
    coverageCheck (innerAD leaf1528Box) leaf1528InnerLog = true := by
  rfl'

private theorem leaf1528InnerLogValid :
    leaf1528InnerLog.Valid 8 (innerAD leaf1528Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1528CoverageChecked

private noncomputable def leaf1528InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629291/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1528InputLogOnePlusV_eq :
    leaf1528InputLogOnePlusV = outerEnclosure 24
      (leaf1528Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1528RoundedFacts : LeafRoundedFacts 8
    leaf1528Certificate.logOnePlusV leaf1528InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1528InputLogOnePlusV_eq }

private noncomputable def leaf1528Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi156InputQChi innerPair26Input
    leaf1528InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1528LowerChecked :
    lowerCheck 24 leaf1528Box leaf1528Inputs = true := by
  rfl'

private theorem leaf1528CoversExact : CoversExact 8
    leaf1528Box leaf1528Certificate leaf1528InnerLog leaf1528Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi156RoundedFacts
    innerPair26RoundedFacts leaf1528RoundedFacts (by rfl)

private theorem leaf1528FlatSound : Sound leaf1528Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1528CertificateValid
    leaf1528InnerLogValid leaf1528CoversExact leaf1528LowerChecked

private noncomputable def leaf1529Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (15/128), chiHi := (31/256) }

private noncomputable def leaf1529Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214411) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (745229631/536870912) }, upper := { exponent := 0, mantissa := (11509/8192) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi153LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432267/268428822) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf1529InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1529LocalValidity :
    LeafFacts leaf1529Box leaf1529Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1529Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214411) }) = true
      norm_num [leaf1529Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1529CertificateValid :
    WideCertificateValid leaf1529Box leaf1529Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi153ValidityFacts
    leaf1529LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1529CoverageChecked :
    coverageCheck (innerAD leaf1529Box) leaf1529InnerLog = true := by
  rfl'

private theorem leaf1529InnerLogValid :
    leaf1529InnerLog.Valid 8 (innerAD leaf1529Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1529CoverageChecked

private noncomputable def leaf1529InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726831/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1529InputLogOnePlusV_eq :
    leaf1529InputLogOnePlusV = outerEnclosure 24
      (leaf1529Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1529RoundedFacts : LeafRoundedFacts 8
    leaf1529Certificate.logOnePlusV leaf1529InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1529InputLogOnePlusV_eq }

private noncomputable def leaf1529Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi153InputQChi innerPair26Input
    leaf1529InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1529LowerChecked :
    lowerCheck 24 leaf1529Box leaf1529Inputs = true := by
  rfl'

private theorem leaf1529CoversExact : CoversExact 8
    leaf1529Box leaf1529Certificate leaf1529InnerLog leaf1529Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi153RoundedFacts
    innerPair26RoundedFacts leaf1529RoundedFacts (by rfl)

private theorem leaf1529FlatSound : Sound leaf1529Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1529CertificateValid
    leaf1529InnerLogValid leaf1529CoversExact leaf1529LowerChecked

private noncomputable def leaf1530Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (31/256), chiHi := (1/8) }

private noncomputable def leaf1530Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (65529/65536), upper := (4194308/4194197) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (752176021/536870912) }, upper := { exponent := 0, mantissa := (363/256) } }, logOuter := sk143LogOuterCertificate, logK := sk143LogKCertificate, logChi := chi154LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388505/8388394) } }, logDArg := sk143LogDArgCertificate }

private noncomputable def leaf1530InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1530LocalValidity :
    LeafFacts leaf1530Box leaf1530Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1530Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194308/4194197) }) = true
      norm_num [leaf1530Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1530CertificateValid :
    WideCertificateValid leaf1530Box leaf1530Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk143ValidityFacts chi154ValidityFacts
    leaf1530LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1530CoverageChecked :
    coverageCheck (innerAD leaf1530Box) leaf1530InnerLog = true := by
  rfl'

private theorem leaf1530InnerLogValid :
    leaf1530InnerLog.Valid 8 (innerAD leaf1530Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1530CoverageChecked

private noncomputable def leaf1530InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629303/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1530InputLogOnePlusV_eq :
    leaf1530InputLogOnePlusV = outerEnclosure 24
      (leaf1530Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1530RoundedFacts : LeafRoundedFacts 8
    leaf1530Certificate.logOnePlusV leaf1530InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1530InputLogOnePlusV_eq }

private noncomputable def leaf1530Inputs : Inputs :=
  inputsOfCaches globalInput sk143RoundedInputs
    chi154InputQChi innerPair26Input
    leaf1530InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1530LowerChecked :
    lowerCheck 24 leaf1530Box leaf1530Inputs = true := by
  rfl'

private theorem leaf1530CoversExact : CoversExact 8
    leaf1530Box leaf1530Certificate leaf1530InnerLog leaf1530Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk143RoundedFacts chi154RoundedFacts
    innerPair26RoundedFacts leaf1530RoundedFacts (by rfl)

private theorem leaf1530FlatSound : Sound leaf1530Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1530CertificateValid
    leaf1530InnerLogValid leaf1530CoversExact leaf1530LowerChecked

private noncomputable def leaf1531Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (15/128), chiHi := (31/256) }

private noncomputable def leaf1531Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553595) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (747195589/536870912) }, upper := { exponent := 0, mantissa := (2885/2048) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi153LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108059/67107190) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf1531InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1531LocalValidity :
    LeafFacts leaf1531Box leaf1531Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1531Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553595) }) = true
      norm_num [leaf1531Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1531CertificateValid :
    WideCertificateValid leaf1531Box leaf1531Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi153ValidityFacts
    leaf1531LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1531CoverageChecked :
    coverageCheck (innerAD leaf1531Box) leaf1531InnerLog = true := by
  rfl'

private theorem leaf1531InnerLogValid :
    leaf1531InnerLog.Valid 8 (innerAD leaf1531Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1531CoverageChecked

private noncomputable def leaf1531InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814649/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1531InputLogOnePlusV_eq :
    leaf1531InputLogOnePlusV = outerEnclosure 24
      (leaf1531Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1531RoundedFacts : LeafRoundedFacts 8
    leaf1531Certificate.logOnePlusV leaf1531InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1531InputLogOnePlusV_eq }

private noncomputable def leaf1531Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi153InputQChi innerPair26Input
    leaf1531InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1531LowerChecked :
    lowerCheck 24 leaf1531Box leaf1531Inputs = true := by
  rfl'

private theorem leaf1531CoversExact : CoversExact 8
    leaf1531Box leaf1531Certificate leaf1531InnerLog leaf1531Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi153RoundedFacts
    innerPair26RoundedFacts leaf1531RoundedFacts (by rfl)

private theorem leaf1531FlatSound : Sound leaf1531Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1531CertificateValid
    leaf1531InnerLogValid leaf1531CoversExact leaf1531LowerChecked

private noncomputable def leaf1532Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (31/256), chiHi := (1/8) }

private noncomputable def leaf1532Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (65529/65536), upper := (1048577/1048549) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (754207511/536870912) }, upper := { exponent := 0, mantissa := (91/64) } }, logOuter := sk144LogOuterCertificate, logK := sk144LogKCertificate, logChi := chi154LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1048563/1048549) } }, logDArg := sk144LogDArgCertificate }

private noncomputable def leaf1532InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1532LocalValidity :
    LeafFacts leaf1532Box leaf1532Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1532Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1048577/1048549) }) = true
      norm_num [leaf1532Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1532CertificateValid :
    WideCertificateValid leaf1532Box leaf1532Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk144ValidityFacts chi154ValidityFacts
    leaf1532LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1532CoverageChecked :
    coverageCheck (innerAD leaf1532Box) leaf1532InnerLog = true := by
  rfl'

private theorem leaf1532InnerLogValid :
    leaf1532InnerLog.Valid 8 (innerAD leaf1532Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1532CoverageChecked

private noncomputable def leaf1532InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629305/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1532InputLogOnePlusV_eq :
    leaf1532InputLogOnePlusV = outerEnclosure 24
      (leaf1532Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1532RoundedFacts : LeafRoundedFacts 8
    leaf1532Certificate.logOnePlusV leaf1532InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1532InputLogOnePlusV_eq }

private noncomputable def leaf1532Inputs : Inputs :=
  inputsOfCaches globalInput sk144RoundedInputs
    chi154InputQChi innerPair26Input
    leaf1532InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1532LowerChecked :
    lowerCheck 24 leaf1532Box leaf1532Inputs = true := by
  rfl'

private theorem leaf1532CoversExact : CoversExact 8
    leaf1532Box leaf1532Certificate leaf1532InnerLog leaf1532Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk144RoundedFacts chi154RoundedFacts
    innerPair26RoundedFacts leaf1532RoundedFacts (by rfl)

private theorem leaf1532FlatSound : Sound leaf1532Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1532CertificateValid
    leaf1532InnerLogValid leaf1532CoversExact leaf1532LowerChecked

private noncomputable def leaf1533Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1533Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871179/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134215003) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (706696823/536870912) }, upper := { exponent := 0, mantissa := (10917/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432859/268430006) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf1533InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1533LocalValidity :
    LeafFacts leaf1533Box leaf1533Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1533Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134215003) }) = true
      norm_num [leaf1533Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1533CertificateValid :
    WideCertificateValid leaf1533Box leaf1533Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi131ValidityFacts
    leaf1533LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1533CoverageChecked :
    coverageCheck (innerAD leaf1533Box) leaf1533InnerLog = true := by
  rfl'

private theorem leaf1533InnerLogValid :
    leaf1533InnerLog.Valid 8 (innerAD leaf1533Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1533CoverageChecked

private noncomputable def leaf1533InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1533InputLogOnePlusV_eq :
    leaf1533InputLogOnePlusV = outerEnclosure 24
      (leaf1533Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1533RoundedFacts : LeafRoundedFacts 8
    leaf1533Certificate.logOnePlusV leaf1533InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1533InputLogOnePlusV_eq }

private noncomputable def leaf1533Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi131InputQChi innerPair21Input
    leaf1533InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1533LowerChecked :
    lowerCheck 24 leaf1533Box leaf1533Inputs = true := by
  rfl'

private theorem leaf1533CoversExact : CoversExact 8
    leaf1533Box leaf1533Certificate leaf1533InnerLog leaf1533Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi131RoundedFacts
    innerPair21RoundedFacts leaf1533RoundedFacts (by rfl)

private theorem leaf1533FlatSound : Sound leaf1533Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1533CertificateValid
    leaf1533InnerLogValid leaf1533CoversExact leaf1533LowerChecked

private noncomputable def leaf1534Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1534Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871181/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107489) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (708269589/536870912) }, upper := { exponent := 0, mantissa := (5471/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216417/134214978) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf1534InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1534LocalValidity :
    LeafFacts leaf1534Box leaf1534Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1534Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107489) }) = true
      norm_num [leaf1534Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1534CertificateValid :
    WideCertificateValid leaf1534Box leaf1534Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi131ValidityFacts
    leaf1534LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1534CoverageChecked :
    coverageCheck (innerAD leaf1534Box) leaf1534InnerLog = true := by
  rfl'

private theorem leaf1534InnerLogValid :
    leaf1534InnerLog.Valid 8 (innerAD leaf1534Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1534CoverageChecked

private noncomputable def leaf1534InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1534InputLogOnePlusV_eq :
    leaf1534InputLogOnePlusV = outerEnclosure 24
      (leaf1534Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1534RoundedFacts : LeafRoundedFacts 8
    leaf1534Certificate.logOnePlusV leaf1534InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1534InputLogOnePlusV_eq }

private noncomputable def leaf1534Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi131InputQChi innerPair21Input
    leaf1534InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1534LowerChecked :
    lowerCheck 24 leaf1534Box leaf1534Inputs = true := by
  rfl'

private theorem leaf1534CoversExact : CoversExact 8
    leaf1534Box leaf1534Certificate leaf1534InnerLog leaf1534Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi131RoundedFacts
    innerPair21RoundedFacts leaf1534RoundedFacts (by rfl)

private theorem leaf1534FlatSound : Sound leaf1534Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1534CertificateValid
    leaf1534InnerLogValid leaf1534CoversExact leaf1534LowerChecked

private noncomputable def leaf1535Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1535Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871181/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107447) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (713774277/536870912) }, upper := { exponent := 0, mantissa := (5513/4096) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216375/134214894) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf1535InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1535LocalValidity :
    LeafFacts leaf1535Box leaf1535Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1535Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107447) }) = true
      norm_num [leaf1535Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1535CertificateValid :
    WideCertificateValid leaf1535Box leaf1535Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi132ValidityFacts
    leaf1535LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1535CoverageChecked :
    coverageCheck (innerAD leaf1535Box) leaf1535InnerLog = true := by
  rfl'

private theorem leaf1535InnerLogValid :
    leaf1535InnerLog.Valid 8 (innerAD leaf1535Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1535CoverageChecked

private noncomputable def leaf1535InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814633/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1535InputLogOnePlusV_eq :
    leaf1535InputLogOnePlusV = outerEnclosure 24
      (leaf1535Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1535RoundedFacts : LeafRoundedFacts 8
    leaf1535Certificate.logOnePlusV leaf1535InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1535InputLogOnePlusV_eq }

private noncomputable def leaf1535Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi132InputQChi innerPair21Input
    leaf1535InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1535LowerChecked :
    lowerCheck 24 leaf1535Box leaf1535Inputs = true := by
  rfl'

private theorem leaf1535CoversExact : CoversExact 8
    leaf1535Box leaf1535Certificate leaf1535InnerLog leaf1535Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi132RoundedFacts
    innerPair21RoundedFacts leaf1535RoundedFacts (by rfl)

private theorem leaf1535FlatSound : Sound leaf1535Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1535CertificateValid
    leaf1535InnerLogValid leaf1535CoversExact leaf1535LowerChecked

private noncomputable def leaf1536Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1536Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871183/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553717) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (715412575/536870912) }, upper := { exponent := 0, mantissa := (2763/2048) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108181/67107434) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf1536InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1536LocalValidity :
    LeafFacts leaf1536Box leaf1536Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1536Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553717) }) = true
      norm_num [leaf1536Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1536CertificateValid :
    WideCertificateValid leaf1536Box leaf1536Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi132ValidityFacts
    leaf1536LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1536CoverageChecked :
    coverageCheck (innerAD leaf1536Box) leaf1536InnerLog = true := by
  rfl'

private theorem leaf1536InnerLogValid :
    leaf1536InnerLog.Valid 8 (innerAD leaf1536Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1536CoverageChecked

private noncomputable def leaf1536InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629267/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1536InputLogOnePlusV_eq :
    leaf1536InputLogOnePlusV = outerEnclosure 24
      (leaf1536Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1536RoundedFacts : LeafRoundedFacts 8
    leaf1536Certificate.logOnePlusV leaf1536InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1536InputLogOnePlusV_eq }

private noncomputable def leaf1536Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi132InputQChi innerPair21Input
    leaf1536InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1536LowerChecked :
    lowerCheck 24 leaf1536Box leaf1536Inputs = true := by
  rfl'

private theorem leaf1536CoversExact : CoversExact 8
    leaf1536Box leaf1536Certificate leaf1536InnerLog leaf1536Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi132RoundedFacts
    innerPair21RoundedFacts leaf1536RoundedFacts (by rfl)

private theorem leaf1536FlatSound : Sound leaf1536Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1536CertificateValid
    leaf1536InnerLogValid leaf1536CoversExact leaf1536LowerChecked

private noncomputable def leaf1537Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1537Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871183/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214953) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (709842355/536870912) }, upper := { exponent := 0, mantissa := (10967/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432809/268429906) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf1537InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1537LocalValidity :
    LeafFacts leaf1537Box leaf1537Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1537Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214953) }) = true
      norm_num [leaf1537Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1537CertificateValid :
    WideCertificateValid leaf1537Box leaf1537Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi131ValidityFacts
    leaf1537LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1537CoverageChecked :
    coverageCheck (innerAD leaf1537Box) leaf1537InnerLog = true := by
  rfl'

private theorem leaf1537InnerLogValid :
    leaf1537InnerLog.Valid 8 (innerAD leaf1537Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1537CoverageChecked

private noncomputable def leaf1537InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814631/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1537InputLogOnePlusV_eq :
    leaf1537InputLogOnePlusV = outerEnclosure 24
      (leaf1537Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1537RoundedFacts : LeafRoundedFacts 8
    leaf1537Certificate.logOnePlusV leaf1537InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1537InputLogOnePlusV_eq }

private noncomputable def leaf1537Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi131InputQChi innerPair21Input
    leaf1537InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1537LowerChecked :
    lowerCheck 24 leaf1537Box leaf1537Inputs = true := by
  rfl'

private theorem leaf1537CoversExact : CoversExact 8
    leaf1537Box leaf1537Certificate leaf1537InnerLog leaf1537Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi131RoundedFacts
    innerPair21RoundedFacts leaf1537RoundedFacts (by rfl)

private theorem leaf1537FlatSound : Sound leaf1537Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1537CertificateValid
    leaf1537InnerLogValid leaf1537CoversExact leaf1537LowerChecked

private noncomputable def leaf1538Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (3/32), chiHi := (25/256) }

private noncomputable def leaf1538Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388433) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (711415121/536870912) }, upper := { exponent := 0, mantissa := (687/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi131LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777049/16776866) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf1538InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1538LocalValidity :
    LeafFacts leaf1538Box leaf1538Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1538Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388433) }) = true
      norm_num [leaf1538Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1538CertificateValid :
    WideCertificateValid leaf1538Box leaf1538Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi131ValidityFacts
    leaf1538LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1538CoverageChecked :
    coverageCheck (innerAD leaf1538Box) leaf1538InnerLog = true := by
  rfl'

private theorem leaf1538InnerLogValid :
    leaf1538InnerLog.Valid 8 (innerAD leaf1538Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1538CoverageChecked

private noncomputable def leaf1538InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726829/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf1538InputLogOnePlusV_eq :
    leaf1538InputLogOnePlusV = outerEnclosure 24
      (leaf1538Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1538RoundedFacts : LeafRoundedFacts 8
    leaf1538Certificate.logOnePlusV leaf1538InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1538InputLogOnePlusV_eq }

private noncomputable def leaf1538Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi131InputQChi innerPair21Input
    leaf1538InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1538LowerChecked :
    lowerCheck 24 leaf1538Box leaf1538Inputs = true := by
  rfl'

private theorem leaf1538CoversExact : CoversExact 8
    leaf1538Box leaf1538Certificate leaf1538InnerLog leaf1538Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi131RoundedFacts
    innerPair21RoundedFacts leaf1538RoundedFacts (by rfl)

private theorem leaf1538FlatSound : Sound leaf1538Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1538CertificateValid
    leaf1538InnerLogValid leaf1538CoversExact leaf1538LowerChecked

private noncomputable def leaf1539Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1539Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107421) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (717050873/536870912) }, upper := { exponent := 0, mantissa := (5539/4096) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216349/134214842) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf1539InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1539LocalValidity :
    LeafFacts leaf1539Box leaf1539Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1539Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107421) }) = true
      norm_num [leaf1539Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1539CertificateValid :
    WideCertificateValid leaf1539Box leaf1539Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi132ValidityFacts
    leaf1539LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1539CoverageChecked :
    coverageCheck (innerAD leaf1539Box) leaf1539InnerLog = true := by
  rfl'

private theorem leaf1539InnerLogValid :
    leaf1539InnerLog.Valid 8 (innerAD leaf1539Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1539CoverageChecked

private noncomputable def leaf1539InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1539InputLogOnePlusV_eq :
    leaf1539InputLogOnePlusV = outerEnclosure 24
      (leaf1539Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1539RoundedFacts : LeafRoundedFacts 8
    leaf1539Certificate.logOnePlusV leaf1539InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1539InputLogOnePlusV_eq }

private noncomputable def leaf1539Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi132InputQChi innerPair21Input
    leaf1539InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1539LowerChecked :
    lowerCheck 24 leaf1539Box leaf1539Inputs = true := by
  rfl'

private theorem leaf1539CoversExact : CoversExact 8
    leaf1539Box leaf1539Certificate leaf1539InnerLog leaf1539Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi132RoundedFacts
    innerPair21RoundedFacts leaf1539RoundedFacts (by rfl)

private theorem leaf1539FlatSound : Sound leaf1539Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1539CertificateValid
    leaf1539InnerLogValid leaf1539CoversExact leaf1539LowerChecked

private noncomputable def leaf1540Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (25/256), chiHi := (13/128) }

private noncomputable def leaf1540Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (8191/8192), upper := (4194308/4194213) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (718689171/536870912) }, upper := { exponent := 0, mantissa := (347/256) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi132LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388521/8388426) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf1540InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1540LocalValidity :
    LeafFacts leaf1540Box leaf1540Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1540Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194308/4194213) }) = true
      norm_num [leaf1540Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1540CertificateValid :
    WideCertificateValid leaf1540Box leaf1540Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi132ValidityFacts
    leaf1540LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1540CoverageChecked :
    coverageCheck (innerAD leaf1540Box) leaf1540InnerLog = true := by
  rfl'

private theorem leaf1540InnerLogValid :
    leaf1540InnerLog.Valid 8 (innerAD leaf1540Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1540CoverageChecked

private noncomputable def leaf1540InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629271/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1540InputLogOnePlusV_eq :
    leaf1540InputLogOnePlusV = outerEnclosure 24
      (leaf1540Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1540RoundedFacts : LeafRoundedFacts 8
    leaf1540Certificate.logOnePlusV leaf1540InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1540InputLogOnePlusV_eq }

private noncomputable def leaf1540Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi132InputQChi innerPair21Input
    leaf1540InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1540LowerChecked :
    lowerCheck 24 leaf1540Box leaf1540Inputs = true := by
  rfl'

private theorem leaf1540CoversExact : CoversExact 8
    leaf1540Box leaf1540Certificate leaf1540InnerLog leaf1540Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi132RoundedFacts
    innerPair21RoundedFacts leaf1540RoundedFacts (by rfl)

private theorem leaf1540FlatSound : Sound leaf1540Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1540CertificateValid
    leaf1540InnerLogValid leaf1540CoversExact leaf1540LowerChecked

private noncomputable def leaf1541Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1541Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871183/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214785) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (720851731/536870912) }, upper := { exponent := 0, mantissa := (11135/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432641/268429570) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf1541InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1541LocalValidity :
    LeafFacts leaf1541Box leaf1541Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1541Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214785) }) = true
      norm_num [leaf1541Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1541CertificateValid :
    WideCertificateValid leaf1541Box leaf1541Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi149ValidityFacts
    leaf1541LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1541CoverageChecked :
    coverageCheck (innerAD leaf1541Box) leaf1541InnerLog = true := by
  rfl'

private theorem leaf1541InnerLogValid :
    leaf1541InnerLog.Valid 8 (innerAD leaf1541Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1541CoverageChecked

private noncomputable def leaf1541InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1541InputLogOnePlusV_eq :
    leaf1541InputLogOnePlusV = outerEnclosure 24
      (leaf1541Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1541RoundedFacts : LeafRoundedFacts 8
    leaf1541Certificate.logOnePlusV leaf1541InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1541InputLogOnePlusV_eq }

private noncomputable def leaf1541Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi149InputQChi innerPair21Input
    leaf1541InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1541LowerChecked :
    lowerCheck 24 leaf1541Box leaf1541Inputs = true := by
  rfl'

private theorem leaf1541CoversExact : CoversExact 8
    leaf1541Box leaf1541Certificate leaf1541InnerLog leaf1541Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi149RoundedFacts
    innerPair21RoundedFacts leaf1541RoundedFacts (by rfl)

private theorem leaf1541FlatSound : Sound leaf1541Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1541CertificateValid
    leaf1541InnerLogValid leaf1541CoversExact leaf1541LowerChecked

private noncomputable def leaf1542Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1542Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107379) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (722555561/536870912) }, upper := { exponent := 0, mantissa := (5581/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216307/134214758) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf1542InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1542LocalValidity :
    LeafFacts leaf1542Box leaf1542Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1542Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107379) }) = true
      norm_num [leaf1542Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1542CertificateValid :
    WideCertificateValid leaf1542Box leaf1542Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi149ValidityFacts
    leaf1542LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1542CoverageChecked :
    coverageCheck (innerAD leaf1542Box) leaf1542InnerLog = true := by
  rfl'

private theorem leaf1542InnerLogValid :
    leaf1542InnerLog.Valid 8 (innerAD leaf1542Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1542CoverageChecked

private noncomputable def leaf1542InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814637/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1542InputLogOnePlusV_eq :
    leaf1542InputLogOnePlusV = outerEnclosure 24
      (leaf1542Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1542RoundedFacts : LeafRoundedFacts 8
    leaf1542Certificate.logOnePlusV leaf1542InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1542InputLogOnePlusV_eq }

private noncomputable def leaf1542Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi149InputQChi innerPair21Input
    leaf1542InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1542LowerChecked :
    lowerCheck 24 leaf1542Box leaf1542Inputs = true := by
  rfl'

private theorem leaf1542CoversExact : CoversExact 8
    leaf1542Box leaf1542Certificate leaf1542InnerLog leaf1542Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi149RoundedFacts
    innerPair21RoundedFacts leaf1542RoundedFacts (by rfl)

private theorem leaf1542FlatSound : Sound leaf1542Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1542CertificateValid
    leaf1542InnerLogValid leaf1542CoversExact leaf1542LowerChecked

private noncomputable def leaf1543Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1543Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871185/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553669) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (727929185/536870912) }, upper := { exponent := 0, mantissa := (2811/2048) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108133/67107338) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf1543InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1543LocalValidity :
    LeafFacts leaf1543Box leaf1543Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1543Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553669) }) = true
      norm_num [leaf1543Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1543CertificateValid :
    WideCertificateValid leaf1543Box leaf1543Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi150ValidityFacts
    leaf1543LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1543CoverageChecked :
    coverageCheck (innerAD leaf1543Box) leaf1543InnerLog = true := by
  rfl'

private theorem leaf1543InnerLogValid :
    leaf1543InnerLog.Valid 8 (innerAD leaf1543Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1543CoverageChecked

private noncomputable def leaf1543InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1543InputLogOnePlusV_eq :
    leaf1543InputLogOnePlusV = outerEnclosure 24
      (leaf1543Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1543RoundedFacts : LeafRoundedFacts 8
    leaf1543Certificate.logOnePlusV leaf1543InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1543InputLogOnePlusV_eq }

private noncomputable def leaf1543Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi150InputQChi innerPair21Input
    leaf1543InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1543LowerChecked :
    lowerCheck 24 leaf1543Box leaf1543Inputs = true := by
  rfl'

private theorem leaf1543CoversExact : CoversExact 8
    leaf1543Box leaf1543Certificate leaf1543InnerLog leaf1543Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi150RoundedFacts
    innerPair21RoundedFacts leaf1543RoundedFacts (by rfl)

private theorem leaf1543FlatSound : Sound leaf1543Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1543CertificateValid
    leaf1543InnerLogValid leaf1543CoversExact leaf1543LowerChecked

private noncomputable def leaf1544Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1544Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (65529/65536), upper := (16777232/16776831) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (729698547/536870912) }, upper := { exponent := 0, mantissa := (1409/1024) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (33554063/33553662) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf1544InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1544LocalValidity :
    LeafFacts leaf1544Box leaf1544Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1544Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (16777232/16776831) }) = true
      norm_num [leaf1544Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1544CertificateValid :
    WideCertificateValid leaf1544Box leaf1544Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi150ValidityFacts
    leaf1544LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1544CoverageChecked :
    coverageCheck (innerAD leaf1544Box) leaf1544InnerLog = true := by
  rfl'

private theorem leaf1544InnerLogValid :
    leaf1544InnerLog.Valid 8 (innerAD leaf1544Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1544CoverageChecked

private noncomputable def leaf1544InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629281/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1544InputLogOnePlusV_eq :
    leaf1544InputLogOnePlusV = outerEnclosure 24
      (leaf1544Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1544RoundedFacts : LeafRoundedFacts 8
    leaf1544Certificate.logOnePlusV leaf1544InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1544InputLogOnePlusV_eq }

private noncomputable def leaf1544Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi150InputQChi innerPair22Input
    leaf1544InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1544LowerChecked :
    lowerCheck 24 leaf1544Box leaf1544Inputs = true := by
  rfl'

private theorem leaf1544CoversExact : CoversExact 8
    leaf1544Box leaf1544Certificate leaf1544InnerLog leaf1544Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi150RoundedFacts
    innerPair22RoundedFacts leaf1544RoundedFacts (by rfl)

private theorem leaf1544FlatSound : Sound leaf1544Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1544CertificateValid
    leaf1544InnerLogValid leaf1544CoversExact leaf1544LowerChecked

private noncomputable def leaf1545Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1545Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214731) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (724259391/536870912) }, upper := { exponent := 0, mantissa := (11189/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432587/268429462) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf1545InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1545LocalValidity :
    LeafFacts leaf1545Box leaf1545Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1545Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214731) }) = true
      norm_num [leaf1545Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1545CertificateValid :
    WideCertificateValid leaf1545Box leaf1545Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi149ValidityFacts
    leaf1545LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1545CoverageChecked :
    coverageCheck (innerAD leaf1545Box) leaf1545InnerLog = true := by
  rfl'

private theorem leaf1545InnerLogValid :
    leaf1545InnerLog.Valid 8 (innerAD leaf1545Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1545CoverageChecked

private noncomputable def leaf1545InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907319/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1545InputLogOnePlusV_eq :
    leaf1545InputLogOnePlusV = outerEnclosure 24
      (leaf1545Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1545RoundedFacts : LeafRoundedFacts 8
    leaf1545Certificate.logOnePlusV leaf1545InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1545InputLogOnePlusV_eq }

private noncomputable def leaf1545Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi149InputQChi innerPair21Input
    leaf1545InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1545LowerChecked :
    lowerCheck 24 leaf1545Box leaf1545Inputs = true := by
  rfl'

private theorem leaf1545CoversExact : CoversExact 8
    leaf1545Box leaf1545Certificate leaf1545InnerLog leaf1545Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi149RoundedFacts
    innerPair21RoundedFacts leaf1545RoundedFacts (by rfl)

private theorem leaf1545FlatSound : Sound leaf1545Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1545CertificateValid
    leaf1545InnerLogValid leaf1545CoversExact leaf1545LowerChecked

private noncomputable def leaf1546Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (13/128), chiHi := (27/256) }

private noncomputable def leaf1546Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388419) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (725963221/536870912) }, upper := { exponent := 0, mantissa := (701/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi149LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777035/16776838) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf1546InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf1546LocalValidity :
    LeafFacts leaf1546Box leaf1546Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1546Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388419) }) = true
      norm_num [leaf1546Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1546CertificateValid :
    WideCertificateValid leaf1546Box leaf1546Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi149ValidityFacts
    leaf1546LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1546CoverageChecked :
    coverageCheck (innerAD leaf1546Box) leaf1546InnerLog = true := by
  rfl'

private theorem leaf1546InnerLogValid :
    leaf1546InnerLog.Valid 8 (innerAD leaf1546Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf1546CoverageChecked

private noncomputable def leaf1546InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814639/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1546InputLogOnePlusV_eq :
    leaf1546InputLogOnePlusV = outerEnclosure 24
      (leaf1546Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1546RoundedFacts : LeafRoundedFacts 8
    leaf1546Certificate.logOnePlusV leaf1546InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1546InputLogOnePlusV_eq }

private noncomputable def leaf1546Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi149InputQChi innerPair21Input
    leaf1546InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1546LowerChecked :
    lowerCheck 24 leaf1546Box leaf1546Inputs = true := by
  rfl'

private theorem leaf1546CoversExact : CoversExact 8
    leaf1546Box leaf1546Certificate leaf1546InnerLog leaf1546Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi149RoundedFacts
    innerPair21RoundedFacts leaf1546RoundedFacts (by rfl)

private theorem leaf1546FlatSound : Sound leaf1546Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1546CertificateValid
    leaf1546InnerLogValid leaf1546CoversExact leaf1546LowerChecked

private noncomputable def leaf1547Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1547Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553655) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (731467909/536870912) }, upper := { exponent := 0, mantissa := (2825/2048) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108119/67107310) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf1547InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1547LocalValidity :
    LeafFacts leaf1547Box leaf1547Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1547Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553655) }) = true
      norm_num [leaf1547Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1547CertificateValid :
    WideCertificateValid leaf1547Box leaf1547Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi150ValidityFacts
    leaf1547LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1547CoverageChecked :
    coverageCheck (innerAD leaf1547Box) leaf1547InnerLog = true := by
  rfl'

private theorem leaf1547InnerLogValid :
    leaf1547InnerLog.Valid 8 (innerAD leaf1547Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1547CoverageChecked

private noncomputable def leaf1547InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629283/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1547InputLogOnePlusV_eq :
    leaf1547InputLogOnePlusV = outerEnclosure 24
      (leaf1547Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1547RoundedFacts : LeafRoundedFacts 8
    leaf1547Certificate.logOnePlusV leaf1547InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1547InputLogOnePlusV_eq }

private noncomputable def leaf1547Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi150InputQChi innerPair22Input
    leaf1547InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1547LowerChecked :
    lowerCheck 24 leaf1547Box leaf1547Inputs = true := by
  rfl'

private theorem leaf1547CoversExact : CoversExact 8
    leaf1547Box leaf1547Certificate leaf1547InnerLog leaf1547Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi150RoundedFacts
    innerPair22RoundedFacts leaf1547RoundedFacts (by rfl)

private theorem leaf1547FlatSound : Sound leaf1547Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1547CertificateValid
    leaf1547InnerLogValid leaf1547CoversExact leaf1547LowerChecked

private noncomputable def leaf1548Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (27/256), chiHi := (7/64) }

private noncomputable def leaf1548Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (8191/8192), upper := (123362/123359) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (733237271/536870912) }, upper := { exponent := 0, mantissa := (177/128) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi150LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (246721/246718) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf1548InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1548LocalValidity :
    LeafFacts leaf1548Box leaf1548Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1548Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (123362/123359) }) = true
      norm_num [leaf1548Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1548CertificateValid :
    WideCertificateValid leaf1548Box leaf1548Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi150ValidityFacts
    leaf1548LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1548CoverageChecked :
    coverageCheck (innerAD leaf1548Box) leaf1548InnerLog = true := by
  rfl'

private theorem leaf1548InnerLogValid :
    leaf1548InnerLog.Valid 8 (innerAD leaf1548Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1548CoverageChecked

private noncomputable def leaf1548InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629285/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1548InputLogOnePlusV_eq :
    leaf1548InputLogOnePlusV = outerEnclosure 24
      (leaf1548Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1548RoundedFacts : LeafRoundedFacts 8
    leaf1548Certificate.logOnePlusV leaf1548InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1548InputLogOnePlusV_eq }

private noncomputable def leaf1548Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi150InputQChi innerPair22Input
    leaf1548InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1548LowerChecked :
    lowerCheck 24 leaf1548Box leaf1548Inputs = true := by
  rfl'

private theorem leaf1548CoversExact : CoversExact 8
    leaf1548Box leaf1548Certificate leaf1548InnerLog leaf1548Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi150RoundedFacts
    innerPair22RoundedFacts leaf1548RoundedFacts (by rfl)

private theorem leaf1548FlatSound : Sound leaf1548Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1548CertificateValid
    leaf1548InnerLogValid leaf1548CoversExact leaf1548LowerChecked

private noncomputable def leaf1549Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1549Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871187/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214567) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (735006639/536870912) }, upper := { exponent := 0, mantissa := (11353/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432423/268429134) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf1549InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1549LocalValidity :
    LeafFacts leaf1549Box leaf1549Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1549Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214567) }) = true
      norm_num [leaf1549Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1549CertificateValid :
    WideCertificateValid leaf1549Box leaf1549Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi155ValidityFacts
    leaf1549LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1549CoverageChecked :
    coverageCheck (innerAD leaf1549Box) leaf1549InnerLog = true := by
  rfl'

private theorem leaf1549InnerLogValid :
    leaf1549InnerLog.Valid 8 (innerAD leaf1549Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1549CoverageChecked

private noncomputable def leaf1549InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1549InputLogOnePlusV_eq :
    leaf1549InputLogOnePlusV = outerEnclosure 24
      (leaf1549Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1549RoundedFacts : LeafRoundedFacts 8
    leaf1549Certificate.logOnePlusV leaf1549InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1549InputLogOnePlusV_eq }

private noncomputable def leaf1549Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi155InputQChi innerPair22Input
    leaf1549InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1549LowerChecked :
    lowerCheck 24 leaf1549Box leaf1549Inputs = true := by
  rfl'

private theorem leaf1549CoversExact : CoversExact 8
    leaf1549Box leaf1549Certificate leaf1549InnerLog leaf1549Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi155RoundedFacts
    innerPair22RoundedFacts leaf1549RoundedFacts (by rfl)

private theorem leaf1549FlatSound : Sound leaf1549Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1549CertificateValid
    leaf1549InnerLogValid leaf1549CoversExact leaf1549LowerChecked

private noncomputable def leaf1550Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1550Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107269) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (736841533/536870912) }, upper := { exponent := 0, mantissa := (5691/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216197/134214538) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf1550InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf1550LocalValidity :
    LeafFacts leaf1550Box leaf1550Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1550Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107269) }) = true
      norm_num [leaf1550Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1550CertificateValid :
    WideCertificateValid leaf1550Box leaf1550Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi155ValidityFacts
    leaf1550LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1550CoverageChecked :
    coverageCheck (innerAD leaf1550Box) leaf1550InnerLog = true := by
  rfl'

private theorem leaf1550InnerLogValid :
    leaf1550InnerLog.Valid 8 (innerAD leaf1550Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf1550CoverageChecked

private noncomputable def leaf1550InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453661/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1550InputLogOnePlusV_eq :
    leaf1550InputLogOnePlusV = outerEnclosure 24
      (leaf1550Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1550RoundedFacts : LeafRoundedFacts 8
    leaf1550Certificate.logOnePlusV leaf1550InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1550InputLogOnePlusV_eq }

private noncomputable def leaf1550Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi155InputQChi innerPair22Input
    leaf1550InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1550LowerChecked :
    lowerCheck 24 leaf1550Box leaf1550Inputs = true := by
  rfl'

private theorem leaf1550CoversExact : CoversExact 8
    leaf1550Box leaf1550Certificate leaf1550InnerLog leaf1550Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi155RoundedFacts
    innerPair22RoundedFacts leaf1550RoundedFacts (by rfl)

private theorem leaf1550FlatSound : Sound leaf1550Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1550CertificateValid
    leaf1550InnerLogValid leaf1550CoversExact leaf1550LowerChecked

private noncomputable def leaf1551Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (29/256), chiHi := (15/128) }

private noncomputable def leaf1551Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871189/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107229) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (742084093/536870912) }, upper := { exponent := 0, mantissa := (5731/4096) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi156LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216157/134214458) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf1551InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1551LocalValidity :
    LeafFacts leaf1551Box leaf1551Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1551Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107229) }) = true
      norm_num [leaf1551Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1551CertificateValid :
    WideCertificateValid leaf1551Box leaf1551Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi156ValidityFacts
    leaf1551LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1551CoverageChecked :
    coverageCheck (innerAD leaf1551Box) leaf1551InnerLog = true := by
  rfl'

private theorem leaf1551InnerLogValid :
    leaf1551InnerLog.Valid 8 (innerAD leaf1551Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1551CoverageChecked

private noncomputable def leaf1551InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1551InputLogOnePlusV_eq :
    leaf1551InputLogOnePlusV = outerEnclosure 24
      (leaf1551Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1551RoundedFacts : LeafRoundedFacts 8
    leaf1551Certificate.logOnePlusV leaf1551InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1551InputLogOnePlusV_eq }

private noncomputable def leaf1551Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi156InputQChi innerPair26Input
    leaf1551InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1551LowerChecked :
    lowerCheck 24 leaf1551Box leaf1551Inputs = true := by
  rfl'

private theorem leaf1551CoversExact : CoversExact 8
    leaf1551Box leaf1551Certificate leaf1551InnerLog leaf1551Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi156RoundedFacts
    innerPair26RoundedFacts leaf1551RoundedFacts (by rfl)

private theorem leaf1551FlatSound : Sound leaf1551Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1551CertificateValid
    leaf1551InnerLogValid leaf1551CoversExact leaf1551LowerChecked

private noncomputable def leaf1552Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (29/256), chiHi := (15/128) }

private noncomputable def leaf1552Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (65529/65536), upper := (33554464/33553607) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (743984519/536870912) }, upper := { exponent := 0, mantissa := (2873/2048) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi156LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (67108071/67107214) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf1552InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1552LocalValidity :
    LeafFacts leaf1552Box leaf1552Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1552Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (33554464/33553607) }) = true
      norm_num [leaf1552Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1552CertificateValid :
    WideCertificateValid leaf1552Box leaf1552Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi156ValidityFacts
    leaf1552LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1552CoverageChecked :
    coverageCheck (innerAD leaf1552Box) leaf1552InnerLog = true := by
  rfl'

private theorem leaf1552InnerLogValid :
    leaf1552InnerLog.Valid 8 (innerAD leaf1552Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1552CoverageChecked

private noncomputable def leaf1552InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629295/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1552InputLogOnePlusV_eq :
    leaf1552InputLogOnePlusV = outerEnclosure 24
      (leaf1552Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1552RoundedFacts : LeafRoundedFacts 8
    leaf1552Certificate.logOnePlusV leaf1552InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1552InputLogOnePlusV_eq }

private noncomputable def leaf1552Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi156InputQChi innerPair26Input
    leaf1552InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1552LowerChecked :
    lowerCheck 24 leaf1552Box leaf1552Inputs = true := by
  rfl'

private theorem leaf1552CoversExact : CoversExact 8
    leaf1552Box leaf1552Certificate leaf1552InnerLog leaf1552Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi156RoundedFacts
    innerPair26RoundedFacts leaf1552RoundedFacts (by rfl)

private theorem leaf1552FlatSound : Sound leaf1552Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1552CertificateValid
    leaf1552InnerLogValid leaf1552CoversExact leaf1552LowerChecked

private noncomputable def leaf1553Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (15/128), chiHi := (31/256) }

private noncomputable def leaf1553Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214349) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (749161547/536870912) }, upper := { exponent := 0, mantissa := (11571/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi153LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432205/268428698) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf1553InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1553LocalValidity :
    LeafFacts leaf1553Box leaf1553Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1553Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214349) }) = true
      norm_num [leaf1553Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1553CertificateValid :
    WideCertificateValid leaf1553Box leaf1553Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi153ValidityFacts
    leaf1553LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1553CoverageChecked :
    coverageCheck (innerAD leaf1553Box) leaf1553InnerLog = true := by
  rfl'

private theorem leaf1553InnerLogValid :
    leaf1553InnerLog.Valid 8 (innerAD leaf1553Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1553CoverageChecked

private noncomputable def leaf1553InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907325/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1553InputLogOnePlusV_eq :
    leaf1553InputLogOnePlusV = outerEnclosure 24
      (leaf1553Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1553RoundedFacts : LeafRoundedFacts 8
    leaf1553Certificate.logOnePlusV leaf1553InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1553InputLogOnePlusV_eq }

private noncomputable def leaf1553Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi153InputQChi innerPair26Input
    leaf1553InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1553LowerChecked :
    lowerCheck 24 leaf1553Box leaf1553Inputs = true := by
  rfl'

private theorem leaf1553CoversExact : CoversExact 8
    leaf1553Box leaf1553Certificate leaf1553InnerLog leaf1553Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi153RoundedFacts
    innerPair26RoundedFacts leaf1553RoundedFacts (by rfl)

private theorem leaf1553FlatSound : Sound leaf1553Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1553CertificateValid
    leaf1553InnerLogValid leaf1553CoversExact leaf1553LowerChecked

private noncomputable def leaf1554Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (31/256), chiHi := (1/8) }

private noncomputable def leaf1554Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (65529/65536), upper := (4194308/4194195) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (756239001/536870912) }, upper := { exponent := 0, mantissa := (365/256) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi154LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388503/8388390) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf1554InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1554LocalValidity :
    LeafFacts leaf1554Box leaf1554Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1554Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194308/4194195) }) = true
      norm_num [leaf1554Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1554CertificateValid :
    WideCertificateValid leaf1554Box leaf1554Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi154ValidityFacts
    leaf1554LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1554CoverageChecked :
    coverageCheck (innerAD leaf1554Box) leaf1554InnerLog = true := by
  rfl'

private theorem leaf1554InnerLogValid :
    leaf1554InnerLog.Valid 8 (innerAD leaf1554Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1554CoverageChecked

private noncomputable def leaf1554InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1554InputLogOnePlusV_eq :
    leaf1554InputLogOnePlusV = outerEnclosure 24
      (leaf1554Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1554RoundedFacts : LeafRoundedFacts 8
    leaf1554Certificate.logOnePlusV leaf1554InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1554InputLogOnePlusV_eq }

private noncomputable def leaf1554Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi154InputQChi innerPair26Input
    leaf1554InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1554LowerChecked :
    lowerCheck 24 leaf1554Box leaf1554Inputs = true := by
  rfl'

private theorem leaf1554CoversExact : CoversExact 8
    leaf1554Box leaf1554Certificate leaf1554InnerLog leaf1554Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi154RoundedFacts
    innerPair26RoundedFacts leaf1554RoundedFacts (by rfl)

private theorem leaf1554FlatSound : Sound leaf1554Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1554CertificateValid
    leaf1554InnerLogValid leaf1554CoversExact leaf1554LowerChecked

private noncomputable def leaf1555Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (15/128), chiHi := (31/256) }

private noncomputable def leaf1555Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107159) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (751127505/536870912) }, upper := { exponent := 0, mantissa := (5801/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi153LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216087/134214318) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf1555InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1555LocalValidity :
    LeafFacts leaf1555Box leaf1555Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1555Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107159) }) = true
      norm_num [leaf1555Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1555CertificateValid :
    WideCertificateValid leaf1555Box leaf1555Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi153ValidityFacts
    leaf1555LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1555CoverageChecked :
    coverageCheck (innerAD leaf1555Box) leaf1555InnerLog = true := by
  rfl'

private theorem leaf1555InnerLogValid :
    leaf1555InnerLog.Valid 8 (innerAD leaf1555Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1555CoverageChecked

private noncomputable def leaf1555InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814651/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1555InputLogOnePlusV_eq :
    leaf1555InputLogOnePlusV = outerEnclosure 24
      (leaf1555Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1555RoundedFacts : LeafRoundedFacts 8
    leaf1555Certificate.logOnePlusV leaf1555InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1555InputLogOnePlusV_eq }

private noncomputable def leaf1555Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi153InputQChi innerPair26Input
    leaf1555InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1555LowerChecked :
    lowerCheck 24 leaf1555Box leaf1555Inputs = true := by
  rfl'

private theorem leaf1555CoversExact : CoversExact 8
    leaf1555Box leaf1555Certificate leaf1555InnerLog leaf1555Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi153RoundedFacts
    innerPair26RoundedFacts leaf1555RoundedFacts (by rfl)

private theorem leaf1555FlatSound : Sound leaf1555Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1555CertificateValid
    leaf1555InnerLogValid leaf1555CoversExact leaf1555LowerChecked

private noncomputable def leaf1556Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (31/256), chiHi := (1/8) }

private noncomputable def leaf1556Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (65529/65536), upper := (2097154/2097097) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (758270491/536870912) }, upper := { exponent := 0, mantissa := (183/128) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi154LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (4194251/4194194) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf1556InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1556LocalValidity :
    LeafFacts leaf1556Box leaf1556Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1556Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2097154/2097097) }) = true
      norm_num [leaf1556Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1556CertificateValid :
    WideCertificateValid leaf1556Box leaf1556Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi154ValidityFacts
    leaf1556LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1556CoverageChecked :
    coverageCheck (innerAD leaf1556Box) leaf1556InnerLog = true := by
  rfl'

private theorem leaf1556InnerLogValid :
    leaf1556InnerLog.Valid 8 (innerAD leaf1556Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1556CoverageChecked

private noncomputable def leaf1556InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629309/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1556InputLogOnePlusV_eq :
    leaf1556InputLogOnePlusV = outerEnclosure 24
      (leaf1556Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1556RoundedFacts : LeafRoundedFacts 8
    leaf1556Certificate.logOnePlusV leaf1556InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1556InputLogOnePlusV_eq }

private noncomputable def leaf1556Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi154InputQChi innerPair26Input
    leaf1556InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1556LowerChecked :
    lowerCheck 24 leaf1556Box leaf1556Inputs = true := by
  rfl'

private theorem leaf1556CoversExact : CoversExact 8
    leaf1556Box leaf1556Certificate leaf1556InnerLog leaf1556Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi154RoundedFacts
    innerPair26RoundedFacts leaf1556RoundedFacts (by rfl)

private theorem leaf1556FlatSound : Sound leaf1556Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1556CertificateValid
    leaf1556InnerLogValid leaf1556CoversExact leaf1556LowerChecked

private noncomputable def leaf1557Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1557Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871191/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214509) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (738676427/536870912) }, upper := { exponent := 0, mantissa := (11411/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432365/268429018) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf1557InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1557LocalValidity :
    LeafFacts leaf1557Box leaf1557Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1557Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214509) }) = true
      norm_num [leaf1557Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1557CertificateValid :
    WideCertificateValid leaf1557Box leaf1557Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi155ValidityFacts
    leaf1557LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1557CoverageChecked :
    coverageCheck (innerAD leaf1557Box) leaf1557InnerLog = true := by
  rfl'

private theorem leaf1557InnerLogValid :
    leaf1557InnerLog.Valid 8 (innerAD leaf1557Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1557CoverageChecked

private noncomputable def leaf1557InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814645/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1557InputLogOnePlusV_eq :
    leaf1557InputLogOnePlusV = outerEnclosure 24
      (leaf1557Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1557RoundedFacts : LeafRoundedFacts 8
    leaf1557Certificate.logOnePlusV leaf1557InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1557InputLogOnePlusV_eq }

private noncomputable def leaf1557Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi155InputQChi innerPair26Input
    leaf1557InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1557LowerChecked :
    lowerCheck 24 leaf1557Box leaf1557Inputs = true := by
  rfl'

private theorem leaf1557CoversExact : CoversExact 8
    leaf1557Box leaf1557Certificate leaf1557InnerLog leaf1557Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi155RoundedFacts
    innerPair26RoundedFacts leaf1557RoundedFacts (by rfl)

private theorem leaf1557FlatSound : Sound leaf1557Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1557CertificateValid
    leaf1557InnerLogValid leaf1557CoversExact leaf1557LowerChecked

private noncomputable def leaf1558Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (7/64), chiHi := (29/256) }

private noncomputable def leaf1558Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388405) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (740511321/536870912) }, upper := { exponent := 0, mantissa := (715/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi155LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777021/16776810) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf1558InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1558LocalValidity :
    LeafFacts leaf1558Box leaf1558Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1558Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388405) }) = true
      norm_num [leaf1558Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1558CertificateValid :
    WideCertificateValid leaf1558Box leaf1558Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi155ValidityFacts
    leaf1558LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1558CoverageChecked :
    coverageCheck (innerAD leaf1558Box) leaf1558InnerLog = true := by
  rfl'

private theorem leaf1558InnerLogValid :
    leaf1558InnerLog.Valid 8 (innerAD leaf1558Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1558CoverageChecked

private noncomputable def leaf1558InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907323/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf1558InputLogOnePlusV_eq :
    leaf1558InputLogOnePlusV = outerEnclosure 24
      (leaf1558Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1558RoundedFacts : LeafRoundedFacts 8
    leaf1558Certificate.logOnePlusV leaf1558InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1558InputLogOnePlusV_eq }

private noncomputable def leaf1558Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi155InputQChi innerPair26Input
    leaf1558InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1558LowerChecked :
    lowerCheck 24 leaf1558Box leaf1558Inputs = true := by
  rfl'

private theorem leaf1558CoversExact : CoversExact 8
    leaf1558Box leaf1558Certificate leaf1558InnerLog leaf1558Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi155RoundedFacts
    innerPair26RoundedFacts leaf1558RoundedFacts (by rfl)

private theorem leaf1558FlatSound : Sound leaf1558Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1558CertificateValid
    leaf1558InnerLogValid leaf1558CoversExact leaf1558LowerChecked

private noncomputable def leaf1559Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (29/256), chiHi := (15/128) }

private noncomputable def leaf1559Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871193/536870912) }, vSqrt := { lower := (65529/65536), upper := (67108928/67107199) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (745884945/536870912) }, upper := { exponent := 0, mantissa := (5761/4096) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi156LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (134216127/134214398) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf1559InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1559LocalValidity :
    LeafFacts leaf1559Box leaf1559Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1559Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (67108928/67107199) }) = true
      norm_num [leaf1559Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1559CertificateValid :
    WideCertificateValid leaf1559Box leaf1559Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi156ValidityFacts
    leaf1559LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1559CoverageChecked :
    coverageCheck (innerAD leaf1559Box) leaf1559InnerLog = true := by
  rfl'

private theorem leaf1559InnerLogValid :
    leaf1559InnerLog.Valid 8 (innerAD leaf1559Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1559CoverageChecked

private noncomputable def leaf1559InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1559InputLogOnePlusV_eq :
    leaf1559InputLogOnePlusV = outerEnclosure 24
      (leaf1559Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1559RoundedFacts : LeafRoundedFacts 8
    leaf1559Certificate.logOnePlusV leaf1559InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1559InputLogOnePlusV_eq }

private noncomputable def leaf1559Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi156InputQChi innerPair26Input
    leaf1559InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1559LowerChecked :
    lowerCheck 24 leaf1559Box leaf1559Inputs = true := by
  rfl'

private theorem leaf1559CoversExact : CoversExact 8
    leaf1559Box leaf1559Certificate leaf1559InnerLog leaf1559Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi156RoundedFacts
    innerPair26RoundedFacts leaf1559RoundedFacts (by rfl)

private theorem leaf1559FlatSound : Sound leaf1559Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1559CertificateValid
    leaf1559InnerLogValid leaf1559CoversExact leaf1559LowerChecked

private noncomputable def leaf1560Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (29/256), chiHi := (15/128) }

private noncomputable def leaf1560Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (8191/8192), upper := (4194308/4194199) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (747785371/536870912) }, upper := { exponent := 0, mantissa := (361/256) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi156LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (8388507/8388398) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf1560InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1560LocalValidity :
    LeafFacts leaf1560Box leaf1560Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1560Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (4194308/4194199) }) = true
      norm_num [leaf1560Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1560CertificateValid :
    WideCertificateValid leaf1560Box leaf1560Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi156ValidityFacts
    leaf1560LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1560CoverageChecked :
    coverageCheck (innerAD leaf1560Box) leaf1560InnerLog = true := by
  rfl'

private theorem leaf1560InnerLogValid :
    leaf1560InnerLog.Valid 8 (innerAD leaf1560Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1560CoverageChecked

private noncomputable def leaf1560InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1560InputLogOnePlusV_eq :
    leaf1560InputLogOnePlusV = outerEnclosure 24
      (leaf1560Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1560RoundedFacts : LeafRoundedFacts 8
    leaf1560Certificate.logOnePlusV leaf1560InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1560InputLogOnePlusV_eq }

private noncomputable def leaf1560Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi156InputQChi innerPair26Input
    leaf1560InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1560LowerChecked :
    lowerCheck 24 leaf1560Box leaf1560Inputs = true := by
  rfl'

private theorem leaf1560CoversExact : CoversExact 8
    leaf1560Box leaf1560Certificate leaf1560InnerLog leaf1560Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi156RoundedFacts
    innerPair26RoundedFacts leaf1560RoundedFacts (by rfl)

private theorem leaf1560FlatSound : Sound leaf1560Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1560CertificateValid
    leaf1560InnerLogValid leaf1560CoversExact leaf1560LowerChecked

private noncomputable def leaf1561Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (15/128), chiHi := (31/256) }

private noncomputable def leaf1561Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871195/536870912) }, vSqrt := { lower := (65529/65536), upper := (134217856/134214287) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (753093463/536870912) }, upper := { exponent := 0, mantissa := (11633/8192) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi153LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (268432143/268428574) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf1561InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1561LocalValidity :
    LeafFacts leaf1561Box leaf1561Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1561Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (134217856/134214287) }) = true
      norm_num [leaf1561Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1561CertificateValid :
    WideCertificateValid leaf1561Box leaf1561Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi153ValidityFacts
    leaf1561LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1561CoverageChecked :
    coverageCheck (innerAD leaf1561Box) leaf1561InnerLog = true := by
  rfl'

private theorem leaf1561InnerLogValid :
    leaf1561InnerLog.Valid 8 (innerAD leaf1561Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1561CoverageChecked

private noncomputable def leaf1561InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453663/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf1561InputLogOnePlusV_eq :
    leaf1561InputLogOnePlusV = outerEnclosure 24
      (leaf1561Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1561RoundedFacts : LeafRoundedFacts 8
    leaf1561Certificate.logOnePlusV leaf1561InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1561InputLogOnePlusV_eq }

private noncomputable def leaf1561Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi153InputQChi innerPair26Input
    leaf1561InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1561LowerChecked :
    lowerCheck 24 leaf1561Box leaf1561Inputs = true := by
  rfl'

private theorem leaf1561CoversExact : CoversExact 8
    leaf1561Box leaf1561Certificate leaf1561InnerLog leaf1561Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi153RoundedFacts
    innerPair26RoundedFacts leaf1561RoundedFacts (by rfl)

private theorem leaf1561FlatSound : Sound leaf1561Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1561CertificateValid
    leaf1561InnerLogValid leaf1561CoversExact leaf1561LowerChecked

private noncomputable def leaf1562Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (31/256), chiHi := (1/8) }

private noncomputable def leaf1562Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (65529/65536), upper := (4194308/4194193) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (760301981/536870912) }, upper := { exponent := 0, mantissa := (367/256) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi154LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8388501/8388386) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf1562InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1562LocalValidity :
    LeafFacts leaf1562Box leaf1562Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1562Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4194308/4194193) }) = true
      norm_num [leaf1562Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1562CertificateValid :
    WideCertificateValid leaf1562Box leaf1562Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi154ValidityFacts
    leaf1562LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1562CoverageChecked :
    coverageCheck (innerAD leaf1562Box) leaf1562InnerLog = true := by
  rfl'

private theorem leaf1562InnerLogValid :
    leaf1562InnerLog.Valid 8 (innerAD leaf1562Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1562CoverageChecked

private noncomputable def leaf1562InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629311/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1562InputLogOnePlusV_eq :
    leaf1562InputLogOnePlusV = outerEnclosure 24
      (leaf1562Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1562RoundedFacts : LeafRoundedFacts 8
    leaf1562Certificate.logOnePlusV leaf1562InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1562InputLogOnePlusV_eq }

private noncomputable def leaf1562Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi154InputQChi innerPair26Input
    leaf1562InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1562LowerChecked :
    lowerCheck 24 leaf1562Box leaf1562Inputs = true := by
  rfl'

private theorem leaf1562CoversExact : CoversExact 8
    leaf1562Box leaf1562Certificate leaf1562InnerLog leaf1562Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi154RoundedFacts
    innerPair26RoundedFacts leaf1562RoundedFacts (by rfl)

private theorem leaf1562FlatSound : Sound leaf1562Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1562CertificateValid
    leaf1562InnerLogValid leaf1562CoversExact leaf1562LowerChecked

private noncomputable def leaf1563Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (15/128), chiHi := (31/256) }

private noncomputable def leaf1563Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871197/536870912) }, vSqrt := { lower := (8191/8192), upper := (8388616/8388391) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (755059421/536870912) }, upper := { exponent := 0, mantissa := (729/512) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi153LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16777007/16776782) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf1563InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1563LocalValidity :
    LeafFacts leaf1563Box leaf1563Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1563Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8388616/8388391) }) = true
      norm_num [leaf1563Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1563CertificateValid :
    WideCertificateValid leaf1563Box leaf1563Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi153ValidityFacts
    leaf1563LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1563CoverageChecked :
    coverageCheck (innerAD leaf1563Box) leaf1563InnerLog = true := by
  rfl'

private theorem leaf1563InnerLogValid :
    leaf1563InnerLog.Valid 8 (innerAD leaf1563Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1563CoverageChecked

private noncomputable def leaf1563InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814653/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf1563InputLogOnePlusV_eq :
    leaf1563InputLogOnePlusV = outerEnclosure 24
      (leaf1563Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1563RoundedFacts : LeafRoundedFacts 8
    leaf1563Certificate.logOnePlusV leaf1563InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1563InputLogOnePlusV_eq }

private noncomputable def leaf1563Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi153InputQChi innerPair26Input
    leaf1563InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1563LowerChecked :
    lowerCheck 24 leaf1563Box leaf1563Inputs = true := by
  rfl'

private theorem leaf1563CoversExact : CoversExact 8
    leaf1563Box leaf1563Certificate leaf1563InnerLog leaf1563Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi153RoundedFacts
    innerPair26RoundedFacts leaf1563RoundedFacts (by rfl)

private theorem leaf1563FlatSound : Sound leaf1563Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1563CertificateValid
    leaf1563InnerLogValid leaf1563CoversExact leaf1563LowerChecked

private noncomputable def leaf1564Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (31/256), chiHi := (1/8) }

private noncomputable def leaf1564Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (536871199/536870912) }, vSqrt := { lower := (8191/8192), upper := (1048577/1048548) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (762333471/536870912) }, upper := { exponent := 0, mantissa := (23/16) } }, logOuter := sk148LogOuterCertificate, logK := sk148LogKCertificate, logChi := chi154LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2097125/2097096) } }, logDArg := sk148LogDArgCertificate }

private noncomputable def leaf1564InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf1564LocalValidity :
    LeafFacts leaf1564Box leaf1564Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf1564Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1048577/1048548) }) = true
      norm_num [leaf1564Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf1564CertificateValid :
    WideCertificateValid leaf1564Box leaf1564Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk148ValidityFacts chi154ValidityFacts
    leaf1564LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf1564CoverageChecked :
    coverageCheck (innerAD leaf1564Box) leaf1564InnerLog = true := by
  rfl'

private theorem leaf1564InnerLogValid :
    leaf1564InnerLog.Valid 8 (innerAD leaf1564Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf1564CoverageChecked

private noncomputable def leaf1564InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf1564InputLogOnePlusV_eq :
    leaf1564InputLogOnePlusV = outerEnclosure 24
      (leaf1564Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf1564RoundedFacts : LeafRoundedFacts 8
    leaf1564Certificate.logOnePlusV leaf1564InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf1564InputLogOnePlusV_eq }

private noncomputable def leaf1564Inputs : Inputs :=
  inputsOfCaches globalInput sk148RoundedInputs
    chi154InputQChi innerPair26Input
    leaf1564InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf1564LowerChecked :
    lowerCheck 24 leaf1564Box leaf1564Inputs = true := by
  rfl'

private theorem leaf1564CoversExact : CoversExact 8
    leaf1564Box leaf1564Certificate leaf1564InnerLog leaf1564Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk148RoundedFacts chi154RoundedFacts
    innerPair26RoundedFacts leaf1564RoundedFacts (by rfl)

private theorem leaf1564FlatSound : Sound leaf1564Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf1564CertificateValid
    leaf1564InnerLogValid leaf1564CoversExact leaf1564LowerChecked

private noncomputable def component35Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (3/32), chiHi := (25/256) }

set_option maxRecDepth 1000000 in
private theorem component35Node0_sound : Sound component35Node0Box :=
  sound_of_literal_split component35Node0Box leaf1503Box leaf1504Box
    .k (105/32) (by rfl) (by rfl)
    leaf1503FlatSound leaf1504FlatSound

private noncomputable def component35Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (25/256), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component35Node1_sound : Sound component35Node1Box :=
  sound_of_literal_split component35Node1Box leaf1505Box leaf1506Box
    .k (105/32) (by rfl) (by rfl)
    leaf1505FlatSound leaf1506FlatSound

private noncomputable def component35Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component35Node2_sound : Sound component35Node2Box :=
  sound_of_literal_split component35Node2Box component35Node0Box component35Node1Box
    .chi (25/256) (by rfl) (by rfl)
    component35Node0_sound component35Node1_sound

private noncomputable def component35Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (13/128), chiHi := (27/256) }

set_option maxRecDepth 1000000 in
private theorem component35Node3_sound : Sound component35Node3Box :=
  sound_of_literal_split component35Node3Box leaf1507Box leaf1508Box
    .k (105/32) (by rfl) (by rfl)
    leaf1507FlatSound leaf1508FlatSound

private noncomputable def component35Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (27/256), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component35Node4_sound : Sound component35Node4Box :=
  sound_of_literal_split component35Node4Box leaf1509Box leaf1510Box
    .k (105/32) (by rfl) (by rfl)
    leaf1509FlatSound leaf1510FlatSound

private noncomputable def component35Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component35Node5_sound : Sound component35Node5Box :=
  sound_of_literal_split component35Node5Box component35Node3Box component35Node4Box
    .chi (27/256) (by rfl) (by rfl)
    component35Node3_sound component35Node4_sound

private noncomputable def component35Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component35Node6_sound : Sound component35Node6Box :=
  sound_of_literal_split component35Node6Box component35Node2Box component35Node5Box
    .chi (13/128) (by rfl) (by rfl)
    component35Node2_sound component35Node5_sound

private noncomputable def component35Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (3/32), chiHi := (25/256) }

set_option maxRecDepth 1000000 in
private theorem component35Node7_sound : Sound component35Node7Box :=
  sound_of_literal_split component35Node7Box leaf1511Box leaf1512Box
    .k (107/32) (by rfl) (by rfl)
    leaf1511FlatSound leaf1512FlatSound

private noncomputable def component35Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (25/256), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component35Node8_sound : Sound component35Node8Box :=
  sound_of_literal_split component35Node8Box leaf1513Box leaf1514Box
    .k (107/32) (by rfl) (by rfl)
    leaf1513FlatSound leaf1514FlatSound

private noncomputable def component35Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component35Node9_sound : Sound component35Node9Box :=
  sound_of_literal_split component35Node9Box component35Node7Box component35Node8Box
    .chi (25/256) (by rfl) (by rfl)
    component35Node7_sound component35Node8_sound

private noncomputable def component35Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (13/128), chiHi := (27/256) }

set_option maxRecDepth 1000000 in
private theorem component35Node10_sound : Sound component35Node10Box :=
  sound_of_literal_split component35Node10Box leaf1515Box leaf1516Box
    .k (107/32) (by rfl) (by rfl)
    leaf1515FlatSound leaf1516FlatSound

private noncomputable def component35Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (27/256), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component35Node11_sound : Sound component35Node11Box :=
  sound_of_literal_split component35Node11Box leaf1517Box leaf1518Box
    .k (107/32) (by rfl) (by rfl)
    leaf1517FlatSound leaf1518FlatSound

private noncomputable def component35Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component35Node12_sound : Sound component35Node12Box :=
  sound_of_literal_split component35Node12Box component35Node10Box component35Node11Box
    .chi (27/256) (by rfl) (by rfl)
    component35Node10_sound component35Node11_sound

private noncomputable def component35Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component35Node13_sound : Sound component35Node13Box :=
  sound_of_literal_split component35Node13Box component35Node9Box component35Node12Box
    .chi (13/128) (by rfl) (by rfl)
    component35Node9_sound component35Node12_sound

private noncomputable def component35Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component35Node14_sound : Sound component35Node14Box :=
  sound_of_literal_split component35Node14Box component35Node6Box component35Node13Box
    .k (53/16) (by rfl) (by rfl)
    component35Node6_sound component35Node13_sound

private noncomputable def component35Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component35Node15_sound : Sound component35Node15Box :=
  sound_of_literal_split component35Node15Box leaf1519Box leaf1520Box
    .k (105/32) (by rfl) (by rfl)
    leaf1519FlatSound leaf1520FlatSound

private noncomputable def component35Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (105/32), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node16_sound : Sound component35Node16Box :=
  sound_of_literal_split component35Node16Box leaf1521Box leaf1522Box
    .chi (31/256) (by rfl) (by rfl)
    leaf1521FlatSound leaf1522FlatSound

private noncomputable def component35Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (105/32), kHi := (53/16), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node17_sound : Sound component35Node17Box :=
  sound_of_literal_split component35Node17Box leaf1523Box leaf1524Box
    .chi (31/256) (by rfl) (by rfl)
    leaf1523FlatSound leaf1524FlatSound

private noncomputable def component35Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node18_sound : Sound component35Node18Box :=
  sound_of_literal_split component35Node18Box component35Node16Box component35Node17Box
    .k (105/32) (by rfl) (by rfl)
    component35Node16_sound component35Node17_sound

private noncomputable def component35Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node19_sound : Sound component35Node19Box :=
  sound_of_literal_split component35Node19Box component35Node15Box component35Node18Box
    .chi (15/128) (by rfl) (by rfl)
    component35Node15_sound component35Node18_sound

private noncomputable def component35Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (7/64), chiHi := (29/256) }

set_option maxRecDepth 1000000 in
private theorem component35Node20_sound : Sound component35Node20Box :=
  sound_of_literal_split component35Node20Box leaf1525Box leaf1526Box
    .k (107/32) (by rfl) (by rfl)
    leaf1525FlatSound leaf1526FlatSound

private noncomputable def component35Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (29/256), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component35Node21_sound : Sound component35Node21Box :=
  sound_of_literal_split component35Node21Box leaf1527Box leaf1528Box
    .k (107/32) (by rfl) (by rfl)
    leaf1527FlatSound leaf1528FlatSound

private noncomputable def component35Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component35Node22_sound : Sound component35Node22Box :=
  sound_of_literal_split component35Node22Box component35Node20Box component35Node21Box
    .chi (29/256) (by rfl) (by rfl)
    component35Node20_sound component35Node21_sound

private noncomputable def component35Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (107/32), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node23_sound : Sound component35Node23Box :=
  sound_of_literal_split component35Node23Box leaf1529Box leaf1530Box
    .chi (31/256) (by rfl) (by rfl)
    leaf1529FlatSound leaf1530FlatSound

private noncomputable def component35Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (107/32), kHi := (27/8), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node24_sound : Sound component35Node24Box :=
  sound_of_literal_split component35Node24Box leaf1531Box leaf1532Box
    .chi (31/256) (by rfl) (by rfl)
    leaf1531FlatSound leaf1532FlatSound

private noncomputable def component35Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node25_sound : Sound component35Node25Box :=
  sound_of_literal_split component35Node25Box component35Node23Box component35Node24Box
    .k (107/32) (by rfl) (by rfl)
    component35Node23_sound component35Node24_sound

private noncomputable def component35Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node26_sound : Sound component35Node26Box :=
  sound_of_literal_split component35Node26Box component35Node22Box component35Node25Box
    .chi (15/128) (by rfl) (by rfl)
    component35Node22_sound component35Node25_sound

private noncomputable def component35Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node27_sound : Sound component35Node27Box :=
  sound_of_literal_split component35Node27Box component35Node19Box component35Node26Box
    .k (53/16) (by rfl) (by rfl)
    component35Node19_sound component35Node26_sound

private noncomputable def component35Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node28_sound : Sound component35Node28Box :=
  sound_of_literal_split component35Node28Box component35Node14Box component35Node27Box
    .chi (7/64) (by rfl) (by rfl)
    component35Node14_sound component35Node27_sound

private noncomputable def component35Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (3/32), chiHi := (25/256) }

set_option maxRecDepth 1000000 in
private theorem component35Node29_sound : Sound component35Node29Box :=
  sound_of_literal_split component35Node29Box leaf1533Box leaf1534Box
    .k (109/32) (by rfl) (by rfl)
    leaf1533FlatSound leaf1534FlatSound

private noncomputable def component35Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (25/256), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component35Node30_sound : Sound component35Node30Box :=
  sound_of_literal_split component35Node30Box leaf1535Box leaf1536Box
    .k (109/32) (by rfl) (by rfl)
    leaf1535FlatSound leaf1536FlatSound

private noncomputable def component35Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component35Node31_sound : Sound component35Node31Box :=
  sound_of_literal_split component35Node31Box component35Node29Box component35Node30Box
    .chi (25/256) (by rfl) (by rfl)
    component35Node29_sound component35Node30_sound

private noncomputable def component35Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (3/32), chiHi := (25/256) }

set_option maxRecDepth 1000000 in
private theorem component35Node32_sound : Sound component35Node32Box :=
  sound_of_literal_split component35Node32Box leaf1537Box leaf1538Box
    .k (111/32) (by rfl) (by rfl)
    leaf1537FlatSound leaf1538FlatSound

private noncomputable def component35Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (25/256), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component35Node33_sound : Sound component35Node33Box :=
  sound_of_literal_split component35Node33Box leaf1539Box leaf1540Box
    .k (111/32) (by rfl) (by rfl)
    leaf1539FlatSound leaf1540FlatSound

private noncomputable def component35Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component35Node34_sound : Sound component35Node34Box :=
  sound_of_literal_split component35Node34Box component35Node32Box component35Node33Box
    .chi (25/256) (by rfl) (by rfl)
    component35Node32_sound component35Node33_sound

private noncomputable def component35Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (3/32), chiHi := (13/128) }

set_option maxRecDepth 1000000 in
private theorem component35Node35_sound : Sound component35Node35Box :=
  sound_of_literal_split component35Node35Box component35Node31Box component35Node34Box
    .k (55/16) (by rfl) (by rfl)
    component35Node31_sound component35Node34_sound

private noncomputable def component35Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (13/128), chiHi := (27/256) }

set_option maxRecDepth 1000000 in
private theorem component35Node36_sound : Sound component35Node36Box :=
  sound_of_literal_split component35Node36Box leaf1541Box leaf1542Box
    .k (109/32) (by rfl) (by rfl)
    leaf1541FlatSound leaf1542FlatSound

private noncomputable def component35Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (27/256), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component35Node37_sound : Sound component35Node37Box :=
  sound_of_literal_split component35Node37Box leaf1543Box leaf1544Box
    .k (109/32) (by rfl) (by rfl)
    leaf1543FlatSound leaf1544FlatSound

private noncomputable def component35Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component35Node38_sound : Sound component35Node38Box :=
  sound_of_literal_split component35Node38Box component35Node36Box component35Node37Box
    .chi (27/256) (by rfl) (by rfl)
    component35Node36_sound component35Node37_sound

private noncomputable def component35Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (13/128), chiHi := (27/256) }

set_option maxRecDepth 1000000 in
private theorem component35Node39_sound : Sound component35Node39Box :=
  sound_of_literal_split component35Node39Box leaf1545Box leaf1546Box
    .k (111/32) (by rfl) (by rfl)
    leaf1545FlatSound leaf1546FlatSound

private noncomputable def component35Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (27/256), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component35Node40_sound : Sound component35Node40Box :=
  sound_of_literal_split component35Node40Box leaf1547Box leaf1548Box
    .k (111/32) (by rfl) (by rfl)
    leaf1547FlatSound leaf1548FlatSound

private noncomputable def component35Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component35Node41_sound : Sound component35Node41Box :=
  sound_of_literal_split component35Node41Box component35Node39Box component35Node40Box
    .chi (27/256) (by rfl) (by rfl)
    component35Node39_sound component35Node40_sound

private noncomputable def component35Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (13/128), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component35Node42_sound : Sound component35Node42Box :=
  sound_of_literal_split component35Node42Box component35Node38Box component35Node41Box
    .k (55/16) (by rfl) (by rfl)
    component35Node38_sound component35Node41_sound

private noncomputable def component35Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (3/32), chiHi := (7/64) }

set_option maxRecDepth 1000000 in
private theorem component35Node43_sound : Sound component35Node43Box :=
  sound_of_literal_split component35Node43Box component35Node35Box component35Node42Box
    .chi (13/128) (by rfl) (by rfl)
    component35Node35_sound component35Node42_sound

private noncomputable def component35Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (7/64), chiHi := (29/256) }

set_option maxRecDepth 1000000 in
private theorem component35Node44_sound : Sound component35Node44Box :=
  sound_of_literal_split component35Node44Box leaf1549Box leaf1550Box
    .k (109/32) (by rfl) (by rfl)
    leaf1549FlatSound leaf1550FlatSound

private noncomputable def component35Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (29/256), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component35Node45_sound : Sound component35Node45Box :=
  sound_of_literal_split component35Node45Box leaf1551Box leaf1552Box
    .k (109/32) (by rfl) (by rfl)
    leaf1551FlatSound leaf1552FlatSound

private noncomputable def component35Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component35Node46_sound : Sound component35Node46Box :=
  sound_of_literal_split component35Node46Box component35Node44Box component35Node45Box
    .chi (29/256) (by rfl) (by rfl)
    component35Node44_sound component35Node45_sound

private noncomputable def component35Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node47_sound : Sound component35Node47Box :=
  sound_of_literal_split component35Node47Box leaf1553Box leaf1554Box
    .chi (31/256) (by rfl) (by rfl)
    leaf1553FlatSound leaf1554FlatSound

private noncomputable def component35Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node48_sound : Sound component35Node48Box :=
  sound_of_literal_split component35Node48Box leaf1555Box leaf1556Box
    .chi (31/256) (by rfl) (by rfl)
    leaf1555FlatSound leaf1556FlatSound

private noncomputable def component35Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node49_sound : Sound component35Node49Box :=
  sound_of_literal_split component35Node49Box component35Node47Box component35Node48Box
    .k (109/32) (by rfl) (by rfl)
    component35Node47_sound component35Node48_sound

private noncomputable def component35Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node50_sound : Sound component35Node50Box :=
  sound_of_literal_split component35Node50Box component35Node46Box component35Node49Box
    .chi (15/128) (by rfl) (by rfl)
    component35Node46_sound component35Node49_sound

private noncomputable def component35Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (7/64), chiHi := (29/256) }

set_option maxRecDepth 1000000 in
private theorem component35Node51_sound : Sound component35Node51Box :=
  sound_of_literal_split component35Node51Box leaf1557Box leaf1558Box
    .k (111/32) (by rfl) (by rfl)
    leaf1557FlatSound leaf1558FlatSound

private noncomputable def component35Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (29/256), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component35Node52_sound : Sound component35Node52Box :=
  sound_of_literal_split component35Node52Box leaf1559Box leaf1560Box
    .k (111/32) (by rfl) (by rfl)
    leaf1559FlatSound leaf1560FlatSound

private noncomputable def component35Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (7/64), chiHi := (15/128) }

set_option maxRecDepth 1000000 in
private theorem component35Node53_sound : Sound component35Node53Box :=
  sound_of_literal_split component35Node53Box component35Node51Box component35Node52Box
    .chi (29/256) (by rfl) (by rfl)
    component35Node51_sound component35Node52_sound

private noncomputable def component35Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node54_sound : Sound component35Node54Box :=
  sound_of_literal_split component35Node54Box leaf1561Box leaf1562Box
    .chi (31/256) (by rfl) (by rfl)
    leaf1561FlatSound leaf1562FlatSound

private noncomputable def component35Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node55_sound : Sound component35Node55Box :=
  sound_of_literal_split component35Node55Box leaf1563Box leaf1564Box
    .chi (31/256) (by rfl) (by rfl)
    leaf1563FlatSound leaf1564FlatSound

private noncomputable def component35Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (15/128), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node56_sound : Sound component35Node56Box :=
  sound_of_literal_split component35Node56Box component35Node54Box component35Node55Box
    .k (111/32) (by rfl) (by rfl)
    component35Node54_sound component35Node55_sound

private noncomputable def component35Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node57_sound : Sound component35Node57Box :=
  sound_of_literal_split component35Node57Box component35Node53Box component35Node56Box
    .chi (15/128) (by rfl) (by rfl)
    component35Node53_sound component35Node56_sound

private noncomputable def component35Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (7/64), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node58_sound : Sound component35Node58Box :=
  sound_of_literal_split component35Node58Box component35Node50Box component35Node57Box
    .k (55/16) (by rfl) (by rfl)
    component35Node50_sound component35Node57_sound

private noncomputable def component35Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
private theorem component35Node59_sound : Sound component35Node59Box :=
  sound_of_literal_split component35Node59Box component35Node43Box component35Node58Box
    .chi (7/64) (by rfl) (by rfl)
    component35Node43_sound component35Node58_sound

noncomputable def component35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (3/32), chiHi := (1/8) }

set_option maxRecDepth 1000000 in
theorem component35_sound : Sound component35Box :=
  sound_of_literal_split component35Box component35Node28Box component35Node59Box
    .k (27/8) (by rfl) (by rfl)
    component35Node28_sound component35Node59_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
