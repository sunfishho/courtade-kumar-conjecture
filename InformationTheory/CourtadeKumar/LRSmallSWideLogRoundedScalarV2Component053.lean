import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
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

private noncomputable def leaf2453Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf2453Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742371/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432620544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1866383583/1073741824) }, upper := { exponent := 0, mantissa := (28753/16384) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869542399/274865241088) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2453InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf2453LocalValidity :
    LeafFacts leaf2453Box leaf2453Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2453Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432620544) }) = true
      norm_num [leaf2453Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2453CertificateValid :
    WideCertificateValid leaf2453Box leaf2453Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi201ValidityFacts
    leaf2453LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2453CoverageChecked :
    coverageCheck (innerAD leaf2453Box) leaf2453InnerLog = true := by
  rfl'

private theorem leaf2453InnerLogValid :
    leaf2453InnerLog.Valid 8 (innerAD leaf2453Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf2453CoverageChecked

private noncomputable def leaf2453InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2453InputLogOnePlusV_eq :
    leaf2453InputLogOnePlusV = outerEnclosure 24
      (leaf2453Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2453RoundedFacts : LeafRoundedFacts 8
    leaf2453Certificate.logOnePlusV leaf2453InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2453InputLogOnePlusV_eq }

private noncomputable def leaf2453Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi201InputQChi innerPair66Input
    leaf2453InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2453LowerChecked :
    lowerCheck 24 leaf2453Box leaf2453Inputs = true := by
  rfl'

private theorem leaf2453CoversExact : CoversExact 8
    leaf2453Box leaf2453Certificate leaf2453InnerLog leaf2453Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi201RoundedFacts
    innerPair66RoundedFacts leaf2453RoundedFacts (by rfl)

private theorem leaf2453FlatSound : Sound leaf2453Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2453CertificateValid
    leaf2453InnerLogValid leaf2453CoversExact leaf2453LowerChecked

private noncomputable def leaf2454Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf2454Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (65529/65536), upper := (1616904963/1616854016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1870053373/1073741824) }, upper := { exponent := 0, mantissa := (14405/8192) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (3233758979/3233708032) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2454InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf2454LocalValidity :
    LeafFacts leaf2454Box leaf2454Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2454Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1616904963/1616854016) }) = true
      norm_num [leaf2454Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2454CertificateValid :
    WideCertificateValid leaf2454Box leaf2454Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi201ValidityFacts
    leaf2454LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2454CoverageChecked :
    coverageCheck (innerAD leaf2454Box) leaf2454InnerLog = true := by
  rfl'

private theorem leaf2454InnerLogValid :
    leaf2454InnerLog.Valid 8 (innerAD leaf2454Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf2454CoverageChecked

private noncomputable def leaf2454InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2454InputLogOnePlusV_eq :
    leaf2454InputLogOnePlusV = outerEnclosure 24
      (leaf2454Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2454RoundedFacts : LeafRoundedFacts 8
    leaf2454Certificate.logOnePlusV leaf2454InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2454InputLogOnePlusV_eq }

private noncomputable def leaf2454Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi201InputQChi innerPair66Input
    leaf2454InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2454LowerChecked :
    lowerCheck 24 leaf2454Box leaf2454Inputs = true := by
  rfl'

private theorem leaf2454CoversExact : CoversExact 8
    leaf2454Box leaf2454Certificate leaf2454InnerLog leaf2454Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi201RoundedFacts
    innerPair66RoundedFacts leaf2454RoundedFacts (by rfl)

private theorem leaf2454FlatSound : Sound leaf2454Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2454CertificateValid
    leaf2454InnerLogValid leaf2454CoversExact leaf2454LowerChecked

private noncomputable def leaf2455Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf2455Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742373/1073741824) }, vSqrt := { lower := (65529/65536), upper := (9162461457/9162167296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1880538493/1073741824) }, upper := { exponent := 0, mantissa := (14485/8192) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (18324628753/18324334592) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2455InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2455LocalValidity :
    LeafFacts leaf2455Box leaf2455Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2455Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (9162461457/9162167296) }) = true
      norm_num [leaf2455Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2455CertificateValid :
    WideCertificateValid leaf2455Box leaf2455Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi202ValidityFacts
    leaf2455LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2455CoverageChecked :
    coverageCheck (innerAD leaf2455Box) leaf2455InnerLog = true := by
  rfl'

private theorem leaf2455InnerLogValid :
    leaf2455InnerLog.Valid 8 (innerAD leaf2455Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2455CoverageChecked

private noncomputable def leaf2455InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2455InputLogOnePlusV_eq :
    leaf2455InputLogOnePlusV = outerEnclosure 24
      (leaf2455Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2455RoundedFacts : LeafRoundedFacts 8
    leaf2455Certificate.logOnePlusV leaf2455InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2455InputLogOnePlusV_eq }

private noncomputable def leaf2455Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi202InputQChi innerPair71Input
    leaf2455InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2455LowerChecked :
    lowerCheck 24 leaf2455Box leaf2455Inputs = true := by
  rfl'

private theorem leaf2455CoversExact : CoversExact 8
    leaf2455Box leaf2455Certificate leaf2455InnerLog leaf2455Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi202RoundedFacts
    innerPair71RoundedFacts leaf2455RoundedFacts (by rfl)

private theorem leaf2455FlatSound : Sound leaf2455Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2455CertificateValid
    leaf2455InnerLogValid leaf2455CoversExact leaf2455LowerChecked

private noncomputable def leaf2456Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf2456Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432479744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1884273815/1073741824) }, upper := { exponent := 0, mantissa := (7257/4096) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869401599/274864959488) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2456InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2456LocalValidity :
    LeafFacts leaf2456Box leaf2456Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2456Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432479744) }) = true
      norm_num [leaf2456Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2456CertificateValid :
    WideCertificateValid leaf2456Box leaf2456Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi202ValidityFacts
    leaf2456LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2456CoverageChecked :
    coverageCheck (innerAD leaf2456Box) leaf2456InnerLog = true := by
  rfl'

private theorem leaf2456InnerLogValid :
    leaf2456InnerLog.Valid 8 (innerAD leaf2456Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2456CoverageChecked

private noncomputable def leaf2456InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2456InputLogOnePlusV_eq :
    leaf2456InputLogOnePlusV = outerEnclosure 24
      (leaf2456Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2456RoundedFacts : LeafRoundedFacts 8
    leaf2456Certificate.logOnePlusV leaf2456InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2456InputLogOnePlusV_eq }

private noncomputable def leaf2456Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi202InputQChi innerPair71Input
    leaf2456InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2456LowerChecked :
    lowerCheck 24 leaf2456Box leaf2456Inputs = true := by
  rfl'

private theorem leaf2456CoversExact : CoversExact 8
    leaf2456Box leaf2456Certificate leaf2456InnerLog leaf2456Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi202RoundedFacts
    innerPair71RoundedFacts leaf2456RoundedFacts (by rfl)

private theorem leaf2456FlatSound : Sound leaf2456Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2456CertificateValid
    leaf2456InnerLogValid leaf2456CoversExact leaf2456LowerChecked

private noncomputable def leaf2457Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf2457Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432562176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1873723163/1073741824) }, upper := { exponent := 0, mantissa := (28867/16384) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869484031/274865124352) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2457InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf2457LocalValidity :
    LeafFacts leaf2457Box leaf2457Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2457Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432562176) }) = true
      norm_num [leaf2457Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2457CertificateValid :
    WideCertificateValid leaf2457Box leaf2457Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi201ValidityFacts
    leaf2457LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2457CoverageChecked :
    coverageCheck (innerAD leaf2457Box) leaf2457InnerLog = true := by
  rfl'

private theorem leaf2457InnerLogValid :
    leaf2457InnerLog.Valid 8 (innerAD leaf2457Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf2457CoverageChecked

private noncomputable def leaf2457InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2457InputLogOnePlusV_eq :
    leaf2457InputLogOnePlusV = outerEnclosure 24
      (leaf2457Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2457RoundedFacts : LeafRoundedFacts 8
    leaf2457Certificate.logOnePlusV leaf2457InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2457InputLogOnePlusV_eq }

private noncomputable def leaf2457Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi201InputQChi innerPair66Input
    leaf2457InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2457LowerChecked :
    lowerCheck 24 leaf2457Box leaf2457Inputs = true := by
  rfl'

private theorem leaf2457CoversExact : CoversExact 8
    leaf2457Box leaf2457Certificate leaf2457InnerLog leaf2457Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi201RoundedFacts
    innerPair66RoundedFacts leaf2457RoundedFacts (by rfl)

private theorem leaf2457FlatSound : Sound leaf2457Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2457CertificateValid
    leaf2457InnerLogValid leaf2457CoversExact leaf2457LowerChecked

private noncomputable def leaf2458Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf2458Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432532992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1877392953/1073741824) }, upper := { exponent := 0, mantissa := (7231/4096) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869454847/274865065984) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2458InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf2458LocalValidity :
    LeafFacts leaf2458Box leaf2458Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2458Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432532992) }) = true
      norm_num [leaf2458Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2458CertificateValid :
    WideCertificateValid leaf2458Box leaf2458Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi201ValidityFacts
    leaf2458LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2458CoverageChecked :
    coverageCheck (innerAD leaf2458Box) leaf2458InnerLog = true := by
  rfl'

private theorem leaf2458InnerLogValid :
    leaf2458InnerLog.Valid 8 (innerAD leaf2458Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf2458CoverageChecked

private noncomputable def leaf2458InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2458InputLogOnePlusV_eq :
    leaf2458InputLogOnePlusV = outerEnclosure 24
      (leaf2458Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2458RoundedFacts : LeafRoundedFacts 8
    leaf2458Certificate.logOnePlusV leaf2458InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2458InputLogOnePlusV_eq }

private noncomputable def leaf2458Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi201InputQChi innerPair66Input
    leaf2458InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2458LowerChecked :
    lowerCheck 24 leaf2458Box leaf2458Inputs = true := by
  rfl'

private theorem leaf2458CoversExact : CoversExact 8
    leaf2458Box leaf2458Certificate leaf2458InnerLog leaf2458Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi201RoundedFacts
    innerPair66RoundedFacts leaf2458RoundedFacts (by rfl)

private theorem leaf2458FlatSound : Sound leaf2458Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2458CertificateValid
    leaf2458InnerLogValid leaf2458CoversExact leaf2458LowerChecked

private noncomputable def leaf2459Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf2459Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432450048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1888009137/1073741824) }, upper := { exponent := 0, mantissa := (14543/8192) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869371903/274864900096) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2459InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2459LocalValidity :
    LeafFacts leaf2459Box leaf2459Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2459Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432450048) }) = true
      norm_num [leaf2459Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2459CertificateValid :
    WideCertificateValid leaf2459Box leaf2459Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi202ValidityFacts
    leaf2459LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2459CoverageChecked :
    coverageCheck (innerAD leaf2459Box) leaf2459InnerLog = true := by
  rfl'

private theorem leaf2459InnerLogValid :
    leaf2459InnerLog.Valid 8 (innerAD leaf2459Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2459CoverageChecked

private noncomputable def leaf2459InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2459InputLogOnePlusV_eq :
    leaf2459InputLogOnePlusV = outerEnclosure 24
      (leaf2459Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2459RoundedFacts : LeafRoundedFacts 8
    leaf2459Certificate.logOnePlusV leaf2459InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2459InputLogOnePlusV_eq }

private noncomputable def leaf2459Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi202InputQChi innerPair71Input
    leaf2459InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2459LowerChecked :
    lowerCheck 24 leaf2459Box leaf2459Inputs = true := by
  rfl'

private theorem leaf2459CoversExact : CoversExact 8
    leaf2459Box leaf2459Certificate leaf2459InnerLog leaf2459Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi202RoundedFacts
    innerPair71RoundedFacts leaf2459RoundedFacts (by rfl)

private theorem leaf2459FlatSound : Sound leaf2459Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2459CertificateValid
    leaf2459InnerLogValid leaf2459CoversExact leaf2459LowerChecked

private noncomputable def leaf2460Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf2460Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (65529/65536), upper := (15270769095/15270268928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1891744459/1073741824) }, upper := { exponent := 0, mantissa := (3643/2048) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (30541038023/30540537856) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2460InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2460LocalValidity :
    LeafFacts leaf2460Box leaf2460Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2460Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (15270769095/15270268928) }) = true
      norm_num [leaf2460Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2460CertificateValid :
    WideCertificateValid leaf2460Box leaf2460Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi202ValidityFacts
    leaf2460LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2460CoverageChecked :
    coverageCheck (innerAD leaf2460Box) leaf2460InnerLog = true := by
  rfl'

private theorem leaf2460InnerLogValid :
    leaf2460InnerLog.Valid 8 (innerAD leaf2460Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2460CoverageChecked

private noncomputable def leaf2460InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2460InputLogOnePlusV_eq :
    leaf2460InputLogOnePlusV = outerEnclosure 24
      (leaf2460Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2460RoundedFacts : LeafRoundedFacts 8
    leaf2460Certificate.logOnePlusV leaf2460InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2460InputLogOnePlusV_eq }

private noncomputable def leaf2460Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi202InputQChi innerPair71Input
    leaf2460InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2460LowerChecked :
    lowerCheck 24 leaf2460Box leaf2460Inputs = true := by
  rfl'

private theorem leaf2460CoversExact : CoversExact 8
    leaf2460Box leaf2460Certificate leaf2460InnerLog leaf2460Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi202RoundedFacts
    innerPair71RoundedFacts leaf2460RoundedFacts (by rfl)

private theorem leaf2460FlatSound : Sound leaf2460Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2460CertificateValid
    leaf2460InnerLogValid leaf2460CoversExact leaf2460LowerChecked

private noncomputable def leaf2461Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf2461Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742375/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432398336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1894693403/1073741824) }, upper := { exponent := 0, mantissa := (29187/16384) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869320191/274864796672) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2461InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2461LocalValidity :
    LeafFacts leaf2461Box leaf2461Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2461Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432398336) }) = true
      norm_num [leaf2461Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2461CertificateValid :
    WideCertificateValid leaf2461Box leaf2461Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi199ValidityFacts
    leaf2461LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2461CoverageChecked :
    coverageCheck (innerAD leaf2461Box) leaf2461InnerLog = true := by
  rfl'

private theorem leaf2461InnerLogValid :
    leaf2461InnerLog.Valid 8 (innerAD leaf2461Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2461CoverageChecked

private noncomputable def leaf2461InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629357/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2461InputLogOnePlusV_eq :
    leaf2461InputLogOnePlusV = outerEnclosure 24
      (leaf2461Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2461RoundedFacts : LeafRoundedFacts 8
    leaf2461Certificate.logOnePlusV leaf2461InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2461InputLogOnePlusV_eq }

private noncomputable def leaf2461Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi199InputQChi innerPair71Input
    leaf2461InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2461LowerChecked :
    lowerCheck 24 leaf2461Box leaf2461Inputs = true := by
  rfl'

private theorem leaf2461CoversExact : CoversExact 8
    leaf2461Box leaf2461Certificate leaf2461InnerLog leaf2461Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi199RoundedFacts
    innerPair71RoundedFacts leaf2461RoundedFacts (by rfl)

private theorem leaf2461FlatSound : Sound leaf2461Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2461CertificateValid
    leaf2461InnerLogValid leaf2461CoversExact leaf2461LowerChecked

private noncomputable def leaf2462Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf2462Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810789376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1898494257/1073741824) }, upper := { exponent := 0, mantissa := (14623/8192) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623096661/91621578752) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2462InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2462LocalValidity :
    LeafFacts leaf2462Box leaf2462Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2462Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810789376) }) = true
      norm_num [leaf2462Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2462CertificateValid :
    WideCertificateValid leaf2462Box leaf2462Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi199ValidityFacts
    leaf2462LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2462CoverageChecked :
    coverageCheck (innerAD leaf2462Box) leaf2462InnerLog = true := by
  rfl'

private theorem leaf2462InnerLogValid :
    leaf2462InnerLog.Valid 8 (innerAD leaf2462Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2462CoverageChecked

private noncomputable def leaf2462InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2462InputLogOnePlusV_eq :
    leaf2462InputLogOnePlusV = outerEnclosure 24
      (leaf2462Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2462RoundedFacts : LeafRoundedFacts 8
    leaf2462Certificate.logOnePlusV leaf2462InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2462InputLogOnePlusV_eq }

private noncomputable def leaf2462Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi199InputQChi innerPair71Input
    leaf2462InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2462LowerChecked :
    lowerCheck 24 leaf2462Box leaf2462Inputs = true := by
  rfl'

private theorem leaf2462CoversExact : CoversExact 8
    leaf2462Box leaf2462Certificate leaf2462InnerLog leaf2462Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi199RoundedFacts
    innerPair71RoundedFacts leaf2462RoundedFacts (by rfl)

private theorem leaf2462FlatSound : Sound leaf2462Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2462CertificateValid
    leaf2462InnerLogValid leaf2462CoversExact leaf2462LowerChecked

private noncomputable def leaf2463Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf2463Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742377/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432287232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1908848313/1073741824) }, upper := { exponent := 0, mantissa := (7351/4096) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869209087/274864574464) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2463InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2463LocalValidity :
    LeafFacts leaf2463Box leaf2463Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2463Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432287232) }) = true
      norm_num [leaf2463Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2463CertificateValid :
    WideCertificateValid leaf2463Box leaf2463Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi200ValidityFacts
    leaf2463LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2463CoverageChecked :
    coverageCheck (innerAD leaf2463Box) leaf2463InnerLog = true := by
  rfl'

private theorem leaf2463InnerLogValid :
    leaf2463InnerLog.Valid 8 (innerAD leaf2463Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2463CoverageChecked

private noncomputable def leaf2463InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907341/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2463InputLogOnePlusV_eq :
    leaf2463InputLogOnePlusV = outerEnclosure 24
      (leaf2463Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2463RoundedFacts : LeafRoundedFacts 8
    leaf2463Certificate.logOnePlusV leaf2463InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2463InputLogOnePlusV_eq }

private noncomputable def leaf2463Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi200InputQChi innerPair71Input
    leaf2463InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2463LowerChecked :
    lowerCheck 24 leaf2463Box leaf2463Inputs = true := by
  rfl'

private theorem leaf2463CoversExact : CoversExact 8
    leaf2463Box leaf2463Certificate leaf2463InnerLog leaf2463Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi200RoundedFacts
    innerPair71RoundedFacts leaf2463RoundedFacts (by rfl)

private theorem leaf2463FlatSound : Sound leaf2463Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2463CertificateValid
    leaf2463InnerLogValid leaf2463CoversExact leaf2463LowerChecked

private noncomputable def leaf2464Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf2464Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432256512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1912714699/1073741824) }, upper := { exponent := 0, mantissa := (3683/2048) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869178367/274864513024) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2464InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2464LocalValidity :
    LeafFacts leaf2464Box leaf2464Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2464Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432256512) }) = true
      norm_num [leaf2464Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2464CertificateValid :
    WideCertificateValid leaf2464Box leaf2464Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi200ValidityFacts
    leaf2464LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2464CoverageChecked :
    coverageCheck (innerAD leaf2464Box) leaf2464InnerLog = true := by
  rfl'

private theorem leaf2464InnerLogValid :
    leaf2464InnerLog.Valid 8 (innerAD leaf2464Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2464CoverageChecked

private noncomputable def leaf2464InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2464InputLogOnePlusV_eq :
    leaf2464InputLogOnePlusV = outerEnclosure 24
      (leaf2464Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2464RoundedFacts : LeafRoundedFacts 8
    leaf2464Certificate.logOnePlusV leaf2464InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2464InputLogOnePlusV_eq }

private noncomputable def leaf2464Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi200InputQChi innerPair71Input
    leaf2464InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2464LowerChecked :
    lowerCheck 24 leaf2464Box leaf2464Inputs = true := by
  rfl'

private theorem leaf2464CoversExact : CoversExact 8
    leaf2464Box leaf2464Certificate leaf2464InnerLog leaf2464Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi200RoundedFacts
    innerPair71RoundedFacts leaf2464RoundedFacts (by rfl)

private theorem leaf2464FlatSound : Sound leaf2464Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2464CertificateValid
    leaf2464InnerLogValid leaf2464CoversExact leaf2464LowerChecked

private noncomputable def leaf2465Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf2465Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486467584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1902295111/1073741824) }, upper := { exponent := 0, mantissa := (29305/16384) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973851955/54972935168) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2465InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2465LocalValidity :
    LeafFacts leaf2465Box leaf2465Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2465Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486467584) }) = true
      norm_num [leaf2465Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2465CertificateValid :
    WideCertificateValid leaf2465Box leaf2465Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi199ValidityFacts
    leaf2465LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2465CoverageChecked :
    coverageCheck (innerAD leaf2465Box) leaf2465InnerLog = true := by
  rfl'

private theorem leaf2465InnerLogValid :
    leaf2465InnerLog.Valid 8 (innerAD leaf2465Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2465CoverageChecked

private noncomputable def leaf2465InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2465InputLogOnePlusV_eq :
    leaf2465InputLogOnePlusV = outerEnclosure 24
      (leaf2465Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2465RoundedFacts : LeafRoundedFacts 8
    leaf2465Certificate.logOnePlusV leaf2465InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2465InputLogOnePlusV_eq }

private noncomputable def leaf2465Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi199InputQChi innerPair71Input
    leaf2465InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2465LowerChecked :
    lowerCheck 24 leaf2465Box leaf2465Inputs = true := by
  rfl'

private theorem leaf2465CoversExact : CoversExact 8
    leaf2465Box leaf2465Certificate leaf2465InnerLog leaf2465Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi199RoundedFacts
    innerPair71RoundedFacts leaf2465RoundedFacts (by rfl)

private theorem leaf2465FlatSound : Sound leaf2465Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2465CertificateValid
    leaf2465InnerLogValid leaf2465CoversExact leaf2465LowerChecked

private noncomputable def leaf2466Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf2466Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432307712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1906095965/1073741824) }, upper := { exponent := 0, mantissa := (7341/4096) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869229567/274864615424) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2466InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2466LocalValidity :
    LeafFacts leaf2466Box leaf2466Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2466Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432307712) }) = true
      norm_num [leaf2466Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2466CertificateValid :
    WideCertificateValid leaf2466Box leaf2466Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi199ValidityFacts
    leaf2466LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2466CoverageChecked :
    coverageCheck (innerAD leaf2466Box) leaf2466InnerLog = true := by
  rfl'

private theorem leaf2466InnerLogValid :
    leaf2466InnerLog.Valid 8 (innerAD leaf2466Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2466CoverageChecked

private noncomputable def leaf2466InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814681/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2466InputLogOnePlusV_eq :
    leaf2466InputLogOnePlusV = outerEnclosure 24
      (leaf2466Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2466RoundedFacts : LeafRoundedFacts 8
    leaf2466Certificate.logOnePlusV leaf2466InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2466InputLogOnePlusV_eq }

private noncomputable def leaf2466Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi199InputQChi innerPair71Input
    leaf2466InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2466LowerChecked :
    lowerCheck 24 leaf2466Box leaf2466Inputs = true := by
  rfl'

private theorem leaf2466CoversExact : CoversExact 8
    leaf2466Box leaf2466Certificate leaf2466InnerLog leaf2466Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi199RoundedFacts
    innerPair71RoundedFacts leaf2466RoundedFacts (by rfl)

private theorem leaf2466FlatSound : Sound leaf2466Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2466CertificateValid
    leaf2466InnerLogValid leaf2466CoversExact leaf2466LowerChecked

private noncomputable def leaf2467Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf2467Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (65529/65536), upper := (8084524815/8084248576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1916581085/1073741824) }, upper := { exponent := 0, mantissa := (7381/4096) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16168773391/16168497152) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2467InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2467LocalValidity :
    LeafFacts leaf2467Box leaf2467Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2467Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8084524815/8084248576) }) = true
      norm_num [leaf2467Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2467CertificateValid :
    WideCertificateValid leaf2467Box leaf2467Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi200ValidityFacts
    leaf2467LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2467CoverageChecked :
    coverageCheck (innerAD leaf2467Box) leaf2467InnerLog = true := by
  rfl'

private theorem leaf2467InnerLogValid :
    leaf2467InnerLog.Valid 8 (innerAD leaf2467Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2467CoverageChecked

private noncomputable def leaf2467InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629367/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2467InputLogOnePlusV_eq :
    leaf2467InputLogOnePlusV = outerEnclosure 24
      (leaf2467Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2467RoundedFacts : LeafRoundedFacts 8
    leaf2467Certificate.logOnePlusV leaf2467InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2467InputLogOnePlusV_eq }

private noncomputable def leaf2467Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi200InputQChi innerPair71Input
    leaf2467InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2467LowerChecked :
    lowerCheck 24 leaf2467Box leaf2467Inputs = true := by
  rfl'

private theorem leaf2467CoversExact : CoversExact 8
    leaf2467Box leaf2467Certificate leaf2467InnerLog leaf2467Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi200RoundedFacts
    innerPair71RoundedFacts leaf2467RoundedFacts (by rfl)

private theorem leaf2467FlatSound : Sound leaf2467Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2467CertificateValid
    leaf2467InnerLogValid leaf2467CoversExact leaf2467LowerChecked

private noncomputable def leaf2468Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf2468Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432195072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1920447471/1073741824) }, upper := { exponent := 0, mantissa := (1849/1024) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869116927/274864390144) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2468InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2468LocalValidity :
    LeafFacts leaf2468Box leaf2468Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2468Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432195072) }) = true
      norm_num [leaf2468Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2468CertificateValid :
    WideCertificateValid leaf2468Box leaf2468Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi200ValidityFacts
    leaf2468LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2468CoverageChecked :
    coverageCheck (innerAD leaf2468Box) leaf2468InnerLog = true := by
  rfl'

private theorem leaf2468InnerLogValid :
    leaf2468InnerLog.Valid 8 (innerAD leaf2468Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2468CoverageChecked

private noncomputable def leaf2468InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2468InputLogOnePlusV_eq :
    leaf2468InputLogOnePlusV = outerEnclosure 24
      (leaf2468Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2468RoundedFacts : LeafRoundedFacts 8
    leaf2468Certificate.logOnePlusV leaf2468InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2468InputLogOnePlusV_eq }

private noncomputable def leaf2468Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi200InputQChi innerPair71Input
    leaf2468InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2468LowerChecked :
    lowerCheck 24 leaf2468Box leaf2468Inputs = true := by
  rfl'

private theorem leaf2468CoversExact : CoversExact 8
    leaf2468Box leaf2468Certificate leaf2468InnerLog leaf2468Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi200RoundedFacts
    innerPair71RoundedFacts leaf2468RoundedFacts (by rfl)

private theorem leaf2468FlatSound : Sound leaf2468Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2468CertificateValid
    leaf2468InnerLogValid leaf2468CoversExact leaf2468LowerChecked

private noncomputable def leaf2469Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf2469Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432503808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1881062743/1073741824) }, upper := { exponent := 0, mantissa := (28981/16384) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869425663/274865007616) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2469InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2469LocalValidity :
    LeafFacts leaf2469Box leaf2469Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2469Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432503808) }) = true
      norm_num [leaf2469Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2469CertificateValid :
    WideCertificateValid leaf2469Box leaf2469Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi201ValidityFacts
    leaf2469LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2469CoverageChecked :
    coverageCheck (innerAD leaf2469Box) leaf2469InnerLog = true := by
  rfl'

private theorem leaf2469InnerLogValid :
    leaf2469InnerLog.Valid 8 (innerAD leaf2469Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2469CoverageChecked

private noncomputable def leaf2469InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2469InputLogOnePlusV_eq :
    leaf2469InputLogOnePlusV = outerEnclosure 24
      (leaf2469Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2469RoundedFacts : LeafRoundedFacts 8
    leaf2469Certificate.logOnePlusV leaf2469InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2469InputLogOnePlusV_eq }

private noncomputable def leaf2469Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi201InputQChi innerPair71Input
    leaf2469InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2469LowerChecked :
    lowerCheck 24 leaf2469Box leaf2469Inputs = true := by
  rfl'

private theorem leaf2469CoversExact : CoversExact 8
    leaf2469Box leaf2469Certificate leaf2469InnerLog leaf2469Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi201RoundedFacts
    innerPair71RoundedFacts leaf2469RoundedFacts (by rfl)

private theorem leaf2469FlatSound : Sound leaf2469Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2469CertificateValid
    leaf2469InnerLogValid leaf2469CoversExact leaf2469LowerChecked

private noncomputable def leaf2470Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf2470Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432474624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1884732533/1073741824) }, upper := { exponent := 0, mantissa := (14519/8192) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869396479/274864949248) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2470InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2470LocalValidity :
    LeafFacts leaf2470Box leaf2470Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2470Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432474624) }) = true
      norm_num [leaf2470Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2470CertificateValid :
    WideCertificateValid leaf2470Box leaf2470Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi201ValidityFacts
    leaf2470LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2470CoverageChecked :
    coverageCheck (innerAD leaf2470Box) leaf2470InnerLog = true := by
  rfl'

private theorem leaf2470InnerLogValid :
    leaf2470InnerLog.Valid 8 (innerAD leaf2470Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2470CoverageChecked

private noncomputable def leaf2470InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2470InputLogOnePlusV_eq :
    leaf2470InputLogOnePlusV = outerEnclosure 24
      (leaf2470Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2470RoundedFacts : LeafRoundedFacts 8
    leaf2470Certificate.logOnePlusV leaf2470InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2470InputLogOnePlusV_eq }

private noncomputable def leaf2470Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi201InputQChi innerPair71Input
    leaf2470InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2470LowerChecked :
    lowerCheck 24 leaf2470Box leaf2470Inputs = true := by
  rfl'

private theorem leaf2470CoversExact : CoversExact 8
    leaf2470Box leaf2470Certificate leaf2470InnerLog leaf2470Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi201RoundedFacts
    innerPair71RoundedFacts leaf2470RoundedFacts (by rfl)

private theorem leaf2470FlatSound : Sound leaf2470Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2470CertificateValid
    leaf2470InnerLogValid leaf2470CoversExact leaf2470LowerChecked

private noncomputable def leaf2471Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf2471Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432390656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1895479781/1073741824) }, upper := { exponent := 0, mantissa := (14601/8192) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869312511/274864781312) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2471InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2471LocalValidity :
    LeafFacts leaf2471Box leaf2471Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2471Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432390656) }) = true
      norm_num [leaf2471Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2471CertificateValid :
    WideCertificateValid leaf2471Box leaf2471Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi202ValidityFacts
    leaf2471LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2471CoverageChecked :
    coverageCheck (innerAD leaf2471Box) leaf2471InnerLog = true := by
  rfl'

private theorem leaf2471InnerLogValid :
    leaf2471InnerLog.Valid 8 (innerAD leaf2471Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2471CoverageChecked

private noncomputable def leaf2471InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629357/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2471InputLogOnePlusV_eq :
    leaf2471InputLogOnePlusV = outerEnclosure 24
      (leaf2471Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2471RoundedFacts : LeafRoundedFacts 8
    leaf2471Certificate.logOnePlusV leaf2471InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2471InputLogOnePlusV_eq }

private noncomputable def leaf2471Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi202InputQChi innerPair71Input
    leaf2471InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2471LowerChecked :
    lowerCheck 24 leaf2471Box leaf2471Inputs = true := by
  rfl'

private theorem leaf2471CoversExact : CoversExact 8
    leaf2471Box leaf2471Certificate leaf2471InnerLog leaf2471Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi202RoundedFacts
    innerPair71RoundedFacts leaf2471RoundedFacts (by rfl)

private theorem leaf2471FlatSound : Sound leaf2471Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2471CertificateValid
    leaf2471InnerLogValid leaf2471CoversExact leaf2471LowerChecked

private noncomputable def leaf2472Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf2472Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486472192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1899215103/1073741824) }, upper := { exponent := 0, mantissa := (7315/4096) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973856563/54972944384) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2472InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2472LocalValidity :
    LeafFacts leaf2472Box leaf2472Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2472Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486472192) }) = true
      norm_num [leaf2472Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2472CertificateValid :
    WideCertificateValid leaf2472Box leaf2472Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi202ValidityFacts
    leaf2472LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2472CoverageChecked :
    coverageCheck (innerAD leaf2472Box) leaf2472InnerLog = true := by
  rfl'

private theorem leaf2472InnerLogValid :
    leaf2472InnerLog.Valid 8 (innerAD leaf2472Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2472CoverageChecked

private noncomputable def leaf2472InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2472InputLogOnePlusV_eq :
    leaf2472InputLogOnePlusV = outerEnclosure 24
      (leaf2472Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2472RoundedFacts : LeafRoundedFacts 8
    leaf2472Certificate.logOnePlusV leaf2472InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2472InputLogOnePlusV_eq }

private noncomputable def leaf2472Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi202InputQChi innerPair71Input
    leaf2472InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2472LowerChecked :
    lowerCheck 24 leaf2472Box leaf2472Inputs = true := by
  rfl'

private theorem leaf2472CoversExact : CoversExact 8
    leaf2472Box leaf2472Certificate leaf2472InnerLog leaf2472Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi202RoundedFacts
    innerPair71RoundedFacts leaf2472RoundedFacts (by rfl)

private theorem leaf2472FlatSound : Sound leaf2472Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2472CertificateValid
    leaf2472InnerLogValid leaf2472CoversExact leaf2472LowerChecked

private noncomputable def leaf2473Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf2473Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486489088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1888402323/1073741824) }, upper := { exponent := 0, mantissa := (29095/16384) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973873459/54972978176) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2473InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2473LocalValidity :
    LeafFacts leaf2473Box leaf2473Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2473Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486489088) }) = true
      norm_num [leaf2473Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2473CertificateValid :
    WideCertificateValid leaf2473Box leaf2473Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi201ValidityFacts
    leaf2473LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2473CoverageChecked :
    coverageCheck (innerAD leaf2473Box) leaf2473InnerLog = true := by
  rfl'

private theorem leaf2473InnerLogValid :
    leaf2473InnerLog.Valid 8 (innerAD leaf2473Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2473CoverageChecked

private noncomputable def leaf2473InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2473InputLogOnePlusV_eq :
    leaf2473InputLogOnePlusV = outerEnclosure 24
      (leaf2473Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2473RoundedFacts : LeafRoundedFacts 8
    leaf2473Certificate.logOnePlusV leaf2473InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2473InputLogOnePlusV_eq }

private noncomputable def leaf2473Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi201InputQChi innerPair71Input
    leaf2473InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2473LowerChecked :
    lowerCheck 24 leaf2473Box leaf2473Inputs = true := by
  rfl'

private theorem leaf2473CoversExact : CoversExact 8
    leaf2473Box leaf2473Certificate leaf2473InnerLog leaf2473Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi201RoundedFacts
    innerPair71RoundedFacts leaf2473RoundedFacts (by rfl)

private theorem leaf2473FlatSound : Sound leaf2473Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2473CertificateValid
    leaf2473InnerLogValid leaf2473CoversExact leaf2473LowerChecked

private noncomputable def leaf2474Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf2474Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432416256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1892072113/1073741824) }, upper := { exponent := 0, mantissa := (911/512) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869338111/274864832512) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2474InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2474LocalValidity :
    LeafFacts leaf2474Box leaf2474Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2474Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432416256) }) = true
      norm_num [leaf2474Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2474CertificateValid :
    WideCertificateValid leaf2474Box leaf2474Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi201ValidityFacts
    leaf2474LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2474CoverageChecked :
    coverageCheck (innerAD leaf2474Box) leaf2474InnerLog = true := by
  rfl'

private theorem leaf2474InnerLogValid :
    leaf2474InnerLog.Valid 8 (innerAD leaf2474Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2474CoverageChecked

private noncomputable def leaf2474InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2474InputLogOnePlusV_eq :
    leaf2474InputLogOnePlusV = outerEnclosure 24
      (leaf2474Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2474RoundedFacts : LeafRoundedFacts 8
    leaf2474Certificate.logOnePlusV leaf2474InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2474InputLogOnePlusV_eq }

private noncomputable def leaf2474Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi201InputQChi innerPair71Input
    leaf2474InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2474LowerChecked :
    lowerCheck 24 leaf2474Box leaf2474Inputs = true := by
  rfl'

private theorem leaf2474CoversExact : CoversExact 8
    leaf2474Box leaf2474Certificate leaf2474InnerLog leaf2474Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi201RoundedFacts
    innerPair71RoundedFacts leaf2474RoundedFacts (by rfl)

private theorem leaf2474FlatSound : Sound leaf2474Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2474CertificateValid
    leaf2474InnerLogValid leaf2474CoversExact leaf2474LowerChecked

private noncomputable def leaf2475Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf2475Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810777088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1902950425/1073741824) }, upper := { exponent := 0, mantissa := (14659/8192) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623084373/91621554176) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2475InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2475LocalValidity :
    LeafFacts leaf2475Box leaf2475Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2475Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810777088) }) = true
      norm_num [leaf2475Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2475CertificateValid :
    WideCertificateValid leaf2475Box leaf2475Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi202ValidityFacts
    leaf2475LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2475CoverageChecked :
    coverageCheck (innerAD leaf2475Box) leaf2475InnerLog = true := by
  rfl'

private theorem leaf2475InnerLogValid :
    leaf2475InnerLog.Valid 8 (innerAD leaf2475Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2475CoverageChecked

private noncomputable def leaf2475InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2475InputLogOnePlusV_eq :
    leaf2475InputLogOnePlusV = outerEnclosure 24
      (leaf2475Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2475RoundedFacts : LeafRoundedFacts 8
    leaf2475Certificate.logOnePlusV leaf2475InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2475InputLogOnePlusV_eq }

private noncomputable def leaf2475Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi202InputQChi innerPair71Input
    leaf2475InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2475LowerChecked :
    lowerCheck 24 leaf2475Box leaf2475Inputs = true := by
  rfl'

private theorem leaf2475CoversExact : CoversExact 8
    leaf2475Box leaf2475Certificate leaf2475InnerLog leaf2475Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi202RoundedFacts
    innerPair71RoundedFacts leaf2475RoundedFacts (by rfl)

private theorem leaf2475FlatSound : Sound leaf2475Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2475CertificateValid
    leaf2475InnerLogValid leaf2475CoversExact leaf2475LowerChecked

private noncomputable def leaf2476Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf2476Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432301568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1906685747/1073741824) }, upper := { exponent := 0, mantissa := (459/256) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869223423/274864603136) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2476InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2476LocalValidity :
    LeafFacts leaf2476Box leaf2476Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2476Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432301568) }) = true
      norm_num [leaf2476Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2476CertificateValid :
    WideCertificateValid leaf2476Box leaf2476Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi202ValidityFacts
    leaf2476LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2476CoverageChecked :
    coverageCheck (innerAD leaf2476Box) leaf2476InnerLog = true := by
  rfl'

private theorem leaf2476InnerLogValid :
    leaf2476InnerLog.Valid 8 (innerAD leaf2476Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2476CoverageChecked

private noncomputable def leaf2476InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2476InputLogOnePlusV_eq :
    leaf2476InputLogOnePlusV = outerEnclosure 24
      (leaf2476Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2476RoundedFacts : LeafRoundedFacts 8
    leaf2476Certificate.logOnePlusV leaf2476InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2476InputLogOnePlusV_eq }

private noncomputable def leaf2476Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi202InputQChi innerPair71Input
    leaf2476InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2476LowerChecked :
    lowerCheck 24 leaf2476Box leaf2476Inputs = true := by
  rfl'

private theorem leaf2476CoversExact : CoversExact 8
    leaf2476Box leaf2476Certificate leaf2476InnerLog leaf2476Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi202RoundedFacts
    innerPair71RoundedFacts leaf2476RoundedFacts (by rfl)

private theorem leaf2476FlatSound : Sound leaf2476Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2476CertificateValid
    leaf2476InnerLogValid leaf2476CoversExact leaf2476LowerChecked

private noncomputable def leaf2477Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf2477Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (65529/65536), upper := (5090256365/5090084352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1909896819/1073741824) }, upper := { exponent := 0, mantissa := (29423/16384) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (10180340717/10180168704) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2477InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2477LocalValidity :
    LeafFacts leaf2477Box leaf2477Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2477Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5090256365/5090084352) }) = true
      norm_num [leaf2477Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2477CertificateValid :
    WideCertificateValid leaf2477Box leaf2477Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi199ValidityFacts
    leaf2477LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2477CoverageChecked :
    coverageCheck (innerAD leaf2477Box) leaf2477InnerLog = true := by
  rfl'

private theorem leaf2477InnerLogValid :
    leaf2477InnerLog.Valid 8 (innerAD leaf2477Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2477CoverageChecked

private noncomputable def leaf2477InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907341/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2477InputLogOnePlusV_eq :
    leaf2477InputLogOnePlusV = outerEnclosure 24
      (leaf2477Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2477RoundedFacts : LeafRoundedFacts 8
    leaf2477Certificate.logOnePlusV leaf2477InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2477InputLogOnePlusV_eq }

private noncomputable def leaf2477Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi199InputQChi innerPair71Input
    leaf2477InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2477LowerChecked :
    lowerCheck 24 leaf2477Box leaf2477Inputs = true := by
  rfl'

private theorem leaf2477CoversExact : CoversExact 8
    leaf2477Box leaf2477Certificate leaf2477InnerLog leaf2477Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi199RoundedFacts
    innerPair71RoundedFacts leaf2477RoundedFacts (by rfl)

private theorem leaf2477FlatSound : Sound leaf2477Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2477CertificateValid
    leaf2477InnerLogValid leaf2477CoversExact leaf2477LowerChecked

private noncomputable def leaf2478Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf2478Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432247296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1913697673/1073741824) }, upper := { exponent := 0, mantissa := (14741/8192) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869169151/274864494592) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2478InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2478LocalValidity :
    LeafFacts leaf2478Box leaf2478Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2478Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432247296) }) = true
      norm_num [leaf2478Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2478CertificateValid :
    WideCertificateValid leaf2478Box leaf2478Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi199ValidityFacts
    leaf2478LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2478CoverageChecked :
    coverageCheck (innerAD leaf2478Box) leaf2478InnerLog = true := by
  rfl'

private theorem leaf2478InnerLogValid :
    leaf2478InnerLog.Valid 8 (innerAD leaf2478Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2478CoverageChecked

private noncomputable def leaf2478InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2478InputLogOnePlusV_eq :
    leaf2478InputLogOnePlusV = outerEnclosure 24
      (leaf2478Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2478RoundedFacts : LeafRoundedFacts 8
    leaf2478Certificate.logOnePlusV leaf2478InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2478InputLogOnePlusV_eq }

private noncomputable def leaf2478Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi199InputQChi innerPair71Input
    leaf2478InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2478LowerChecked :
    lowerCheck 24 leaf2478Box leaf2478Inputs = true := by
  rfl'

private theorem leaf2478CoversExact : CoversExact 8
    leaf2478Box leaf2478Certificate leaf2478InnerLog leaf2478Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi199RoundedFacts
    innerPair71RoundedFacts leaf2478RoundedFacts (by rfl)

private theorem leaf2478FlatSound : Sound leaf2478Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2478CertificateValid
    leaf2478InnerLogValid leaf2478CoversExact leaf2478LowerChecked

private noncomputable def leaf2479Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf2479Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432164352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1924313857/1073741824) }, upper := { exponent := 0, mantissa := (7411/4096) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869086207/274864328704) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2479InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2479LocalValidity :
    LeafFacts leaf2479Box leaf2479Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2479Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432164352) }) = true
      norm_num [leaf2479Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2479CertificateValid :
    WideCertificateValid leaf2479Box leaf2479Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi200ValidityFacts
    leaf2479LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2479CoverageChecked :
    coverageCheck (innerAD leaf2479Box) leaf2479InnerLog = true := by
  rfl'

private theorem leaf2479InnerLogValid :
    leaf2479InnerLog.Valid 8 (innerAD leaf2479Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2479CoverageChecked

private noncomputable def leaf2479InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629371/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2479InputLogOnePlusV_eq :
    leaf2479InputLogOnePlusV = outerEnclosure 24
      (leaf2479Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2479RoundedFacts : LeafRoundedFacts 8
    leaf2479Certificate.logOnePlusV leaf2479InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2479InputLogOnePlusV_eq }

private noncomputable def leaf2479Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi200InputQChi innerPair71Input
    leaf2479InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2479LowerChecked :
    lowerCheck 24 leaf2479Box leaf2479Inputs = true := by
  rfl'

private theorem leaf2479CoversExact : CoversExact 8
    leaf2479Box leaf2479Certificate leaf2479InnerLog leaf2479Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi200RoundedFacts
    innerPair71RoundedFacts leaf2479RoundedFacts (by rfl)

private theorem leaf2479FlatSound : Sound leaf2479Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2479CertificateValid
    leaf2479InnerLogValid leaf2479CoversExact leaf2479LowerChecked

private noncomputable def leaf2480Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf2480Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432133632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1928180243/1073741824) }, upper := { exponent := 0, mantissa := (3713/2048) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869055487/274864267264) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2480InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf2480LocalValidity :
    LeafFacts leaf2480Box leaf2480Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2480Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432133632) }) = true
      norm_num [leaf2480Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2480CertificateValid :
    WideCertificateValid leaf2480Box leaf2480Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi200ValidityFacts
    leaf2480LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2480CoverageChecked :
    coverageCheck (innerAD leaf2480Box) leaf2480InnerLog = true := by
  rfl'

private theorem leaf2480InnerLogValid :
    leaf2480InnerLog.Valid 8 (innerAD leaf2480Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf2480CoverageChecked

private noncomputable def leaf2480InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2480InputLogOnePlusV_eq :
    leaf2480InputLogOnePlusV = outerEnclosure 24
      (leaf2480Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2480RoundedFacts : LeafRoundedFacts 8
    leaf2480Certificate.logOnePlusV leaf2480InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2480InputLogOnePlusV_eq }

private noncomputable def leaf2480Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi200InputQChi innerPair72Input
    leaf2480InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2480LowerChecked :
    lowerCheck 24 leaf2480Box leaf2480Inputs = true := by
  rfl'

private theorem leaf2480CoversExact : CoversExact 8
    leaf2480Box leaf2480Certificate leaf2480InnerLog leaf2480Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi200RoundedFacts
    innerPair72RoundedFacts leaf2480RoundedFacts (by rfl)

private theorem leaf2480FlatSound : Sound leaf2480Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2480CertificateValid
    leaf2480InnerLogValid leaf2480CoversExact leaf2480LowerChecked

private noncomputable def leaf2481Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf2481Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (65529/65536), upper := (8084524815/8084248064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1917498527/1073741824) }, upper := { exponent := 0, mantissa := (29541/16384) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16168772879/16168496128) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2481InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2481LocalValidity :
    LeafFacts leaf2481Box leaf2481Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2481Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8084524815/8084248064) }) = true
      norm_num [leaf2481Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2481CertificateValid :
    WideCertificateValid leaf2481Box leaf2481Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi199ValidityFacts
    leaf2481LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2481CoverageChecked :
    coverageCheck (innerAD leaf2481Box) leaf2481InnerLog = true := by
  rfl'

private theorem leaf2481InnerLogValid :
    leaf2481InnerLog.Valid 8 (innerAD leaf2481Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2481CoverageChecked

private noncomputable def leaf2481InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2481InputLogOnePlusV_eq :
    leaf2481InputLogOnePlusV = outerEnclosure 24
      (leaf2481Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2481RoundedFacts : LeafRoundedFacts 8
    leaf2481Certificate.logOnePlusV leaf2481InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2481InputLogOnePlusV_eq }

private noncomputable def leaf2481Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi199InputQChi innerPair71Input
    leaf2481InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2481LowerChecked :
    lowerCheck 24 leaf2481Box leaf2481Inputs = true := by
  rfl'

private theorem leaf2481CoversExact : CoversExact 8
    leaf2481Box leaf2481Certificate leaf2481InnerLog leaf2481Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi199RoundedFacts
    innerPair71RoundedFacts leaf2481RoundedFacts (by rfl)

private theorem leaf2481FlatSound : Sound leaf2481Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2481CertificateValid
    leaf2481InnerLogValid leaf2481CoversExact leaf2481LowerChecked

private noncomputable def leaf2482Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf2482Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162145792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1921299381/1073741824) }, upper := { exponent := 0, mantissa := (925/512) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324607249/18324291584) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2482InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2482LocalValidity :
    LeafFacts leaf2482Box leaf2482Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2482Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162145792) }) = true
      norm_num [leaf2482Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2482CertificateValid :
    WideCertificateValid leaf2482Box leaf2482Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi199ValidityFacts
    leaf2482LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2482CoverageChecked :
    coverageCheck (innerAD leaf2482Box) leaf2482InnerLog = true := by
  rfl'

private theorem leaf2482InnerLogValid :
    leaf2482InnerLog.Valid 8 (innerAD leaf2482Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2482CoverageChecked

private noncomputable def leaf2482InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2482InputLogOnePlusV_eq :
    leaf2482InputLogOnePlusV = outerEnclosure 24
      (leaf2482Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2482RoundedFacts : LeafRoundedFacts 8
    leaf2482Certificate.logOnePlusV leaf2482InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2482InputLogOnePlusV_eq }

private noncomputable def leaf2482Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi199InputQChi innerPair71Input
    leaf2482InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2482LowerChecked :
    lowerCheck 24 leaf2482Box leaf2482Inputs = true := by
  rfl'

private theorem leaf2482CoversExact : CoversExact 8
    leaf2482Box leaf2482Certificate leaf2482InnerLog leaf2482Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi199RoundedFacts
    innerPair71RoundedFacts leaf2482RoundedFacts (by rfl)

private theorem leaf2482FlatSound : Sound leaf2482Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2482CertificateValid
    leaf2482InnerLogValid leaf2482CoversExact leaf2482LowerChecked

private noncomputable def leaf2483Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf2483Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432102912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1932046629/1073741824) }, upper := { exponent := 0, mantissa := (7441/4096) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869024767/274864205824) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2483InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf2483LocalValidity :
    LeafFacts leaf2483Box leaf2483Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2483Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432102912) }) = true
      norm_num [leaf2483Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2483CertificateValid :
    WideCertificateValid leaf2483Box leaf2483Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi200ValidityFacts
    leaf2483LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2483CoverageChecked :
    coverageCheck (innerAD leaf2483Box) leaf2483InnerLog = true := by
  rfl'

private theorem leaf2483InnerLogValid :
    leaf2483InnerLog.Valid 8 (innerAD leaf2483Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf2483CoverageChecked

private noncomputable def leaf2483InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2483InputLogOnePlusV_eq :
    leaf2483InputLogOnePlusV = outerEnclosure 24
      (leaf2483Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2483RoundedFacts : LeafRoundedFacts 8
    leaf2483Certificate.logOnePlusV leaf2483InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2483InputLogOnePlusV_eq }

private noncomputable def leaf2483Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi200InputQChi innerPair72Input
    leaf2483InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2483LowerChecked :
    lowerCheck 24 leaf2483Box leaf2483Inputs = true := by
  rfl'

private theorem leaf2483CoversExact : CoversExact 8
    leaf2483Box leaf2483Certificate leaf2483InnerLog leaf2483Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi200RoundedFacts
    innerPair72RoundedFacts leaf2483RoundedFacts (by rfl)

private theorem leaf2483FlatSound : Sound leaf2483Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2483CertificateValid
    leaf2483InnerLogValid leaf2483CoversExact leaf2483LowerChecked

private noncomputable def leaf2484Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf2484Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432072192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1935913015/1073741824) }, upper := { exponent := 0, mantissa := (233/128) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868994047/274864144384) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2484InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf2484LocalValidity :
    LeafFacts leaf2484Box leaf2484Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2484Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432072192) }) = true
      norm_num [leaf2484Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2484CertificateValid :
    WideCertificateValid leaf2484Box leaf2484Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi200ValidityFacts
    leaf2484LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2484CoverageChecked :
    coverageCheck (innerAD leaf2484Box) leaf2484InnerLog = true := by
  rfl'

private theorem leaf2484InnerLogValid :
    leaf2484InnerLog.Valid 8 (innerAD leaf2484Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf2484CoverageChecked

private noncomputable def leaf2484InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2484InputLogOnePlusV_eq :
    leaf2484InputLogOnePlusV = outerEnclosure 24
      (leaf2484Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2484RoundedFacts : LeafRoundedFacts 8
    leaf2484Certificate.logOnePlusV leaf2484InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2484InputLogOnePlusV_eq }

private noncomputable def leaf2484Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi200InputQChi innerPair72Input
    leaf2484InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2484LowerChecked :
    lowerCheck 24 leaf2484Box leaf2484Inputs = true := by
  rfl'

private theorem leaf2484CoversExact : CoversExact 8
    leaf2484Box leaf2484Certificate leaf2484InnerLog leaf2484Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi200RoundedFacts
    innerPair72RoundedFacts leaf2484RoundedFacts (by rfl)

private theorem leaf2484FlatSound : Sound leaf2484Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2484CertificateValid
    leaf2484InnerLogValid leaf2484CoversExact leaf2484LowerChecked

private noncomputable def leaf2485Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf2485Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742379/1073741824) }, vSqrt := { lower := (65529/65536), upper := (15270769095/15270241792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1923003223/1073741824) }, upper := { exponent := 0, mantissa := (29621/16384) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (30541010887/30540483584) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2485InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2485LocalValidity :
    LeafFacts leaf2485Box leaf2485Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2485Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (15270769095/15270241792) }) = true
      norm_num [leaf2485Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2485CertificateValid :
    WideCertificateValid leaf2485Box leaf2485Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi191ValidityFacts
    leaf2485LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2485CoverageChecked :
    coverageCheck (innerAD leaf2485Box) leaf2485InnerLog = true := by
  rfl'

private theorem leaf2485InnerLogValid :
    leaf2485InnerLog.Valid 8 (innerAD leaf2485Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2485CoverageChecked

private noncomputable def leaf2485InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2485InputLogOnePlusV_eq :
    leaf2485InputLogOnePlusV = outerEnclosure 24
      (leaf2485Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2485RoundedFacts : LeafRoundedFacts 8
    leaf2485Certificate.logOnePlusV leaf2485InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2485InputLogOnePlusV_eq }

private noncomputable def leaf2485Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi191InputQChi innerPair71Input
    leaf2485InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2485LowerChecked :
    lowerCheck 24 leaf2485Box leaf2485Inputs = true := by
  rfl'

private theorem leaf2485CoversExact : CoversExact 8
    leaf2485Box leaf2485Certificate leaf2485InnerLog leaf2485Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi191RoundedFacts
    innerPair71RoundedFacts leaf2485RoundedFacts (by rfl)

private theorem leaf2485FlatSound : Sound leaf2485Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2485CertificateValid
    leaf2485InnerLogValid leaf2485CoversExact leaf2485LowerChecked

private noncomputable def leaf2486Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf2486Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432144896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1926935141/1073741824) }, upper := { exponent := 0, mantissa := (14841/8192) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869066751/274864289792) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2486InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf2486LocalValidity :
    LeafFacts leaf2486Box leaf2486Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2486Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432144896) }) = true
      norm_num [leaf2486Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2486CertificateValid :
    WideCertificateValid leaf2486Box leaf2486Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi191ValidityFacts
    leaf2486LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2486CoverageChecked :
    coverageCheck (innerAD leaf2486Box) leaf2486InnerLog = true := by
  rfl'

private theorem leaf2486InnerLogValid :
    leaf2486InnerLog.Valid 8 (innerAD leaf2486Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf2486CoverageChecked

private noncomputable def leaf2486InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2486InputLogOnePlusV_eq :
    leaf2486InputLogOnePlusV = outerEnclosure 24
      (leaf2486Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2486RoundedFacts : LeafRoundedFacts 8
    leaf2486Certificate.logOnePlusV leaf2486InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2486InputLogOnePlusV_eq }

private noncomputable def leaf2486Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi191InputQChi innerPair71Input
    leaf2486InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2486LowerChecked :
    lowerCheck 24 leaf2486Box leaf2486Inputs = true := by
  rfl'

private theorem leaf2486CoversExact : CoversExact 8
    leaf2486Box leaf2486Certificate leaf2486InnerLog leaf2486Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi191RoundedFacts
    innerPair71RoundedFacts leaf2486RoundedFacts (by rfl)

private theorem leaf2486FlatSound : Sound leaf2486Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2486CertificateValid
    leaf2486InnerLogValid leaf2486CoversExact leaf2486LowerChecked

private noncomputable def leaf2487Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf2487Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742381/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432065024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1937158133/1073741824) }, upper := { exponent := 0, mantissa := (14919/8192) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868986879/274864130048) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2487InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf2487LocalValidity :
    LeafFacts leaf2487Box leaf2487Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2487Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432065024) }) = true
      norm_num [leaf2487Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2487CertificateValid :
    WideCertificateValid leaf2487Box leaf2487Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi192ValidityFacts
    leaf2487LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2487CoverageChecked :
    coverageCheck (innerAD leaf2487Box) leaf2487InnerLog = true := by
  rfl'

private theorem leaf2487InnerLogValid :
    leaf2487InnerLog.Valid 8 (innerAD leaf2487Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf2487CoverageChecked

private noncomputable def leaf2487InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2487InputLogOnePlusV_eq :
    leaf2487InputLogOnePlusV = outerEnclosure 24
      (leaf2487Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2487RoundedFacts : LeafRoundedFacts 8
    leaf2487Certificate.logOnePlusV leaf2487InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2487InputLogOnePlusV_eq }

private noncomputable def leaf2487Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi192InputQChi innerPair72Input
    leaf2487InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2487LowerChecked :
    lowerCheck 24 leaf2487Box leaf2487Inputs = true := by
  rfl'

private theorem leaf2487CoversExact : CoversExact 8
    leaf2487Box leaf2487Certificate leaf2487InnerLog leaf2487Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi192RoundedFacts
    innerPair72RoundedFacts leaf2487RoundedFacts (by rfl)

private theorem leaf2487FlatSound : Sound leaf2487Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2487CertificateValid
    leaf2487InnerLogValid leaf2487CoversExact leaf2487LowerChecked

private noncomputable def leaf2488Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf2488Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (65529/65536), upper := (3054153819/3054045184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1941155583/1073741824) }, upper := { exponent := 0, mantissa := (7475/4096) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (6108199003/6108090368) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2488InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf2488LocalValidity :
    LeafFacts leaf2488Box leaf2488Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2488Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (3054153819/3054045184) }) = true
      norm_num [leaf2488Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2488CertificateValid :
    WideCertificateValid leaf2488Box leaf2488Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi192ValidityFacts
    leaf2488LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2488CoverageChecked :
    coverageCheck (innerAD leaf2488Box) leaf2488InnerLog = true := by
  rfl'

private theorem leaf2488InnerLogValid :
    leaf2488InnerLog.Valid 8 (innerAD leaf2488Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf2488CoverageChecked

private noncomputable def leaf2488InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2488InputLogOnePlusV_eq :
    leaf2488InputLogOnePlusV = outerEnclosure 24
      (leaf2488Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2488RoundedFacts : LeafRoundedFacts 8
    leaf2488Certificate.logOnePlusV leaf2488InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2488InputLogOnePlusV_eq }

private noncomputable def leaf2488Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi192InputQChi innerPair72Input
    leaf2488InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2488LowerChecked :
    lowerCheck 24 leaf2488Box leaf2488Inputs = true := by
  rfl'

private theorem leaf2488CoversExact : CoversExact 8
    leaf2488Box leaf2488Certificate leaf2488InnerLog leaf2488Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi192RoundedFacts
    innerPair72RoundedFacts leaf2488RoundedFacts (by rfl)

private theorem leaf2488FlatSound : Sound leaf2488Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2488CertificateValid
    leaf2488InnerLogValid leaf2488CoversExact leaf2488LowerChecked

private noncomputable def leaf2489Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf2489Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432113664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1930867059/1073741824) }, upper := { exponent := 0, mantissa := (29743/16384) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274869035519/274864227328) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2489InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf2489LocalValidity :
    LeafFacts leaf2489Box leaf2489Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2489Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432113664) }) = true
      norm_num [leaf2489Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2489CertificateValid :
    WideCertificateValid leaf2489Box leaf2489Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi191ValidityFacts
    leaf2489LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2489CoverageChecked :
    coverageCheck (innerAD leaf2489Box) leaf2489InnerLog = true := by
  rfl'

private theorem leaf2489InnerLogValid :
    leaf2489InnerLog.Valid 8 (innerAD leaf2489Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf2489CoverageChecked

private noncomputable def leaf2489InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814687/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2489InputLogOnePlusV_eq :
    leaf2489InputLogOnePlusV = outerEnclosure 24
      (leaf2489Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2489RoundedFacts : LeafRoundedFacts 8
    leaf2489Certificate.logOnePlusV leaf2489InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2489InputLogOnePlusV_eq }

private noncomputable def leaf2489Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi191InputQChi innerPair72Input
    leaf2489InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2489LowerChecked :
    lowerCheck 24 leaf2489Box leaf2489Inputs = true := by
  rfl'

private theorem leaf2489CoversExact : CoversExact 8
    leaf2489Box leaf2489Certificate leaf2489InnerLog leaf2489Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi191RoundedFacts
    innerPair72RoundedFacts leaf2489RoundedFacts (by rfl)

private theorem leaf2489FlatSound : Sound leaf2489Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2489CertificateValid
    leaf2489InnerLogValid leaf2489CoversExact leaf2489LowerChecked

private noncomputable def leaf2490Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf2490Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810694144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1934798977/1073741824) }, upper := { exponent := 0, mantissa := (7451/4096) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91623001429/91621388288) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2490InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf2490LocalValidity :
    LeafFacts leaf2490Box leaf2490Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2490Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810694144) }) = true
      norm_num [leaf2490Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2490CertificateValid :
    WideCertificateValid leaf2490Box leaf2490Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi191ValidityFacts
    leaf2490LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2490CoverageChecked :
    coverageCheck (innerAD leaf2490Box) leaf2490InnerLog = true := by
  rfl'

private theorem leaf2490InnerLogValid :
    leaf2490InnerLog.Valid 8 (innerAD leaf2490Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf2490CoverageChecked

private noncomputable def leaf2490InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (181709/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf2490InputLogOnePlusV_eq :
    leaf2490InputLogOnePlusV = outerEnclosure 24
      (leaf2490Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2490RoundedFacts : LeafRoundedFacts 8
    leaf2490Certificate.logOnePlusV leaf2490InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2490InputLogOnePlusV_eq }

private noncomputable def leaf2490Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi191InputQChi innerPair72Input
    leaf2490InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2490LowerChecked :
    lowerCheck 24 leaf2490Box leaf2490Inputs = true := by
  rfl'

private theorem leaf2490CoversExact : CoversExact 8
    leaf2490Box leaf2490Certificate leaf2490InnerLog leaf2490Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi191RoundedFacts
    innerPair72RoundedFacts leaf2490RoundedFacts (by rfl)

private theorem leaf2490FlatSound : Sound leaf2490Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2490CertificateValid
    leaf2490InnerLogValid leaf2490CoversExact leaf2490LowerChecked

private noncomputable def leaf2491Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf2491Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432001536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1945153033/1073741824) }, upper := { exponent := 0, mantissa := (14981/8192) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868923391/274864003072) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2491InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf2491LocalValidity :
    LeafFacts leaf2491Box leaf2491Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2491Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432001536) }) = true
      norm_num [leaf2491Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2491CertificateValid :
    WideCertificateValid leaf2491Box leaf2491Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi192ValidityFacts
    leaf2491LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2491CoverageChecked :
    coverageCheck (innerAD leaf2491Box) leaf2491InnerLog = true := by
  rfl'

private theorem leaf2491InnerLogValid :
    leaf2491InnerLog.Valid 8 (innerAD leaf2491Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf2491CoverageChecked

private noncomputable def leaf2491InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2491InputLogOnePlusV_eq :
    leaf2491InputLogOnePlusV = outerEnclosure 24
      (leaf2491Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2491RoundedFacts : LeafRoundedFacts 8
    leaf2491Certificate.logOnePlusV leaf2491InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2491InputLogOnePlusV_eq }

private noncomputable def leaf2491Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi192InputQChi innerPair72Input
    leaf2491InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2491LowerChecked :
    lowerCheck 24 leaf2491Box leaf2491Inputs = true := by
  rfl'

private theorem leaf2491CoversExact : CoversExact 8
    leaf2491Box leaf2491Certificate leaf2491InnerLog leaf2491Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi192RoundedFacts
    innerPair72RoundedFacts leaf2491RoundedFacts (by rfl)

private theorem leaf2491FlatSound : Sound leaf2491Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2491CertificateValid
    leaf2491InnerLogValid leaf2491CoversExact leaf2491LowerChecked

private noncomputable def leaf2492Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf2492Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431969792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1949150483/1073741824) }, upper := { exponent := 0, mantissa := (3753/2048) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868891647/274863939584) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2492InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2492LocalValidity :
    LeafFacts leaf2492Box leaf2492Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2492Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431969792) }) = true
      norm_num [leaf2492Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2492CertificateValid :
    WideCertificateValid leaf2492Box leaf2492Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi192ValidityFacts
    leaf2492LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2492CoverageChecked :
    coverageCheck (innerAD leaf2492Box) leaf2492InnerLog = true := by
  rfl'

private theorem leaf2492InnerLogValid :
    leaf2492InnerLog.Valid 8 (innerAD leaf2492Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2492CoverageChecked

private noncomputable def leaf2492InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629383/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2492InputLogOnePlusV_eq :
    leaf2492InputLogOnePlusV = outerEnclosure 24
      (leaf2492Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2492RoundedFacts : LeafRoundedFacts 8
    leaf2492Certificate.logOnePlusV leaf2492InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2492InputLogOnePlusV_eq }

private noncomputable def leaf2492Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi192InputQChi innerPair91Input
    leaf2492InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2492LowerChecked :
    lowerCheck 24 leaf2492Box leaf2492Inputs = true := by
  rfl'

private theorem leaf2492CoversExact : CoversExact 8
    leaf2492Box leaf2492Certificate leaf2492InnerLog leaf2492Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi192RoundedFacts
    innerPair91RoundedFacts leaf2492RoundedFacts (by rfl)

private theorem leaf2492FlatSound : Sound leaf2492Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2492CertificateValid
    leaf2492InnerLogValid leaf2492CoversExact leaf2492LowerChecked

private noncomputable def leaf2493Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf2493Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742383/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486390784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1951313043/1073741824) }, upper := { exponent := 0, mantissa := (30055/16384) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973775155/54972781568) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2493InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2493LocalValidity :
    LeafFacts leaf2493Box leaf2493Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2493Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486390784) }) = true
      norm_num [leaf2493Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2493CertificateValid :
    WideCertificateValid leaf2493Box leaf2493Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi189ValidityFacts
    leaf2493LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2493CoverageChecked :
    coverageCheck (innerAD leaf2493Box) leaf2493InnerLog = true := by
  rfl'

private theorem leaf2493InnerLogValid :
    leaf2493InnerLog.Valid 8 (innerAD leaf2493Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2493CoverageChecked

private noncomputable def leaf2493InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2493InputLogOnePlusV_eq :
    leaf2493InputLogOnePlusV = outerEnclosure 24
      (leaf2493Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2493RoundedFacts : LeafRoundedFacts 8
    leaf2493Certificate.logOnePlusV leaf2493InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2493InputLogOnePlusV_eq }

private noncomputable def leaf2493Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi189InputQChi innerPair91Input
    leaf2493InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2493LowerChecked :
    lowerCheck 24 leaf2493Box leaf2493Inputs = true := by
  rfl'

private theorem leaf2493CoversExact : CoversExact 8
    leaf2493Box leaf2493Certificate leaf2493InnerLog leaf2493Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi189RoundedFacts
    innerPair91RoundedFacts leaf2493RoundedFacts (by rfl)

private theorem leaf2493FlatSound : Sound leaf2493Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2493CertificateValid
    leaf2493InnerLogValid leaf2493CoversExact leaf2493LowerChecked

private noncomputable def leaf2494Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf2494Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431921664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1955376025/1073741824) }, upper := { exponent := 0, mantissa := (15059/8192) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868843519/274863843328) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2494InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2494LocalValidity :
    LeafFacts leaf2494Box leaf2494Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2494Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431921664) }) = true
      norm_num [leaf2494Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2494CertificateValid :
    WideCertificateValid leaf2494Box leaf2494Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi189ValidityFacts
    leaf2494LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2494CoverageChecked :
    coverageCheck (innerAD leaf2494Box) leaf2494InnerLog = true := by
  rfl'

private theorem leaf2494InnerLogValid :
    leaf2494InnerLog.Valid 8 (innerAD leaf2494Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2494CoverageChecked

private noncomputable def leaf2494InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2494InputLogOnePlusV_eq :
    leaf2494InputLogOnePlusV = outerEnclosure 24
      (leaf2494Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2494RoundedFacts : LeafRoundedFacts 8
    leaf2494Certificate.logOnePlusV leaf2494InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2494InputLogOnePlusV_eq }

private noncomputable def leaf2494Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi189InputQChi innerPair91Input
    leaf2494InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2494LowerChecked :
    lowerCheck 24 leaf2494Box leaf2494Inputs = true := by
  rfl'

private theorem leaf2494CoversExact : CoversExact 8
    leaf2494Box leaf2494Certificate leaf2494InnerLog leaf2494Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi189RoundedFacts
    innerPair91RoundedFacts leaf2494RoundedFacts (by rfl)

private theorem leaf2494FlatSound : Sound leaf2494Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2494CertificateValid
    leaf2494InnerLogValid leaf2494CoversExact leaf2494LowerChecked

private noncomputable def leaf2495Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf2495Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742385/1073741824) }, vSqrt := { lower := (65529/65536), upper := (2694841605/2694742016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1965467953/1073741824) }, upper := { exponent := 0, mantissa := (473/256) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5389583621/5389484032) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf2495InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2495LocalValidity :
    LeafFacts leaf2495Box leaf2495Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2495Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2694841605/2694742016) }) = true
      norm_num [leaf2495Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2495CertificateValid :
    WideCertificateValid leaf2495Box leaf2495Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi190ValidityFacts
    leaf2495LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2495CoverageChecked :
    coverageCheck (innerAD leaf2495Box) leaf2495InnerLog = true := by
  rfl'

private theorem leaf2495InnerLogValid :
    leaf2495InnerLog.Valid 8 (innerAD leaf2495Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2495CoverageChecked

private noncomputable def leaf2495InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2495InputLogOnePlusV_eq :
    leaf2495InputLogOnePlusV = outerEnclosure 24
      (leaf2495Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2495RoundedFacts : LeafRoundedFacts 8
    leaf2495Certificate.logOnePlusV leaf2495InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2495InputLogOnePlusV_eq }

private noncomputable def leaf2495Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi190InputQChi innerPair91Input
    leaf2495InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2495LowerChecked :
    lowerCheck 24 leaf2495Box leaf2495Inputs = true := by
  rfl'

private theorem leaf2495CoversExact : CoversExact 8
    leaf2495Box leaf2495Certificate leaf2495InnerLog leaf2495Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi190RoundedFacts
    innerPair91RoundedFacts leaf2495RoundedFacts (by rfl)

private theorem leaf2495FlatSound : Sound leaf2495Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2495CertificateValid
    leaf2495InnerLogValid leaf2495CoversExact leaf2495LowerChecked

private noncomputable def leaf2496Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf2496Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431810048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1969596467/1073741824) }, upper := { exponent := 0, mantissa := (237/128) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868731903/274863620096) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf2496InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2496LocalValidity :
    LeafFacts leaf2496Box leaf2496Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2496Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431810048) }) = true
      norm_num [leaf2496Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2496CertificateValid :
    WideCertificateValid leaf2496Box leaf2496Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi190ValidityFacts
    leaf2496LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2496CoverageChecked :
    coverageCheck (innerAD leaf2496Box) leaf2496InnerLog = true := by
  rfl'

private theorem leaf2496InnerLogValid :
    leaf2496InnerLog.Valid 8 (innerAD leaf2496Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2496CoverageChecked

private noncomputable def leaf2496InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2496InputLogOnePlusV_eq :
    leaf2496InputLogOnePlusV = outerEnclosure 24
      (leaf2496Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2496RoundedFacts : LeafRoundedFacts 8
    leaf2496Certificate.logOnePlusV leaf2496InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2496InputLogOnePlusV_eq }

private noncomputable def leaf2496Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi190InputQChi innerPair91Input
    leaf2496InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2496LowerChecked :
    lowerCheck 24 leaf2496Box leaf2496Inputs = true := by
  rfl'

private theorem leaf2496CoversExact : CoversExact 8
    leaf2496Box leaf2496Certificate leaf2496InnerLog leaf2496Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi190RoundedFacts
    innerPair91RoundedFacts leaf2496RoundedFacts (by rfl)

private theorem leaf2496FlatSound : Sound leaf2496Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2496CertificateValid
    leaf2496InnerLogValid leaf2496CoversExact leaf2496LowerChecked

private noncomputable def leaf2497Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf2497Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431889408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1959439007/1073741824) }, upper := { exponent := 0, mantissa := (30181/16384) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868811263/274863778816) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2497InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2497LocalValidity :
    LeafFacts leaf2497Box leaf2497Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2497Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431889408) }) = true
      norm_num [leaf2497Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2497CertificateValid :
    WideCertificateValid leaf2497Box leaf2497Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi189ValidityFacts
    leaf2497LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2497CoverageChecked :
    coverageCheck (innerAD leaf2497Box) leaf2497InnerLog = true := by
  rfl'

private theorem leaf2497InnerLogValid :
    leaf2497InnerLog.Valid 8 (innerAD leaf2497Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2497CoverageChecked

private noncomputable def leaf2497InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2497InputLogOnePlusV_eq :
    leaf2497InputLogOnePlusV = outerEnclosure 24
      (leaf2497Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2497RoundedFacts : LeafRoundedFacts 8
    leaf2497Certificate.logOnePlusV leaf2497InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2497InputLogOnePlusV_eq }

private noncomputable def leaf2497Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi189InputQChi innerPair91Input
    leaf2497InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2497LowerChecked :
    lowerCheck 24 leaf2497Box leaf2497Inputs = true := by
  rfl'

private theorem leaf2497CoversExact : CoversExact 8
    leaf2497Box leaf2497Certificate leaf2497InnerLog leaf2497Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi189RoundedFacts
    innerPair91RoundedFacts leaf2497RoundedFacts (by rfl)

private theorem leaf2497FlatSound : Sound leaf2497Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2497CertificateValid
    leaf2497InnerLogValid leaf2497CoversExact leaf2497LowerChecked

private noncomputable def leaf2498Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf2498Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431857152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1963501989/1073741824) }, upper := { exponent := 0, mantissa := (7561/4096) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868779007/274863714304) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2498InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2498LocalValidity :
    LeafFacts leaf2498Box leaf2498Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2498Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431857152) }) = true
      norm_num [leaf2498Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2498CertificateValid :
    WideCertificateValid leaf2498Box leaf2498Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi189ValidityFacts
    leaf2498LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2498CoverageChecked :
    coverageCheck (innerAD leaf2498Box) leaf2498InnerLog = true := by
  rfl'

private theorem leaf2498InnerLogValid :
    leaf2498InnerLog.Valid 8 (innerAD leaf2498Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2498CoverageChecked

private noncomputable def leaf2498InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814695/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2498InputLogOnePlusV_eq :
    leaf2498InputLogOnePlusV = outerEnclosure 24
      (leaf2498Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2498RoundedFacts : LeafRoundedFacts 8
    leaf2498Certificate.logOnePlusV leaf2498InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2498InputLogOnePlusV_eq }

private noncomputable def leaf2498Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi189InputQChi innerPair91Input
    leaf2498InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2498LowerChecked :
    lowerCheck 24 leaf2498Box leaf2498Inputs = true := by
  rfl'

private theorem leaf2498CoversExact : CoversExact 8
    leaf2498Box leaf2498Certificate leaf2498InnerLog leaf2498Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi189RoundedFacts
    innerPair91RoundedFacts leaf2498RoundedFacts (by rfl)

private theorem leaf2498FlatSound : Sound leaf2498Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2498CertificateValid
    leaf2498InnerLogValid leaf2498CoversExact leaf2498LowerChecked

private noncomputable def leaf2499Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf2499Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486355456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1973724981/1073741824) }, upper := { exponent := 0, mantissa := (475/256) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973739827/54972710912) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf2499InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2499LocalValidity :
    LeafFacts leaf2499Box leaf2499Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2499Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486355456) }) = true
      norm_num [leaf2499Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2499CertificateValid :
    WideCertificateValid leaf2499Box leaf2499Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi190ValidityFacts
    leaf2499LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2499CoverageChecked :
    coverageCheck (innerAD leaf2499Box) leaf2499InnerLog = true := by
  rfl'

private theorem leaf2499InnerLogValid :
    leaf2499InnerLog.Valid 8 (innerAD leaf2499Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2499CoverageChecked

private noncomputable def leaf2499InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629395/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2499InputLogOnePlusV_eq :
    leaf2499InputLogOnePlusV = outerEnclosure 24
      (leaf2499Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2499RoundedFacts : LeafRoundedFacts 8
    leaf2499Certificate.logOnePlusV leaf2499InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2499InputLogOnePlusV_eq }

private noncomputable def leaf2499Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi190InputQChi innerPair91Input
    leaf2499InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2499LowerChecked :
    lowerCheck 24 leaf2499Box leaf2499Inputs = true := by
  rfl'

private theorem leaf2499CoversExact : CoversExact 8
    leaf2499Box leaf2499Certificate leaf2499InnerLog leaf2499Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi190RoundedFacts
    innerPair91RoundedFacts leaf2499RoundedFacts (by rfl)

private theorem leaf2499FlatSound : Sound leaf2499Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2499CertificateValid
    leaf2499InnerLogValid leaf2499CoversExact leaf2499LowerChecked

private noncomputable def leaf2500Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf2500Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810581504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1977853495/1073741824) }, upper := { exponent := 0, mantissa := (119/64) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91622888789/91621163008) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf2500InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2500LocalValidity :
    LeafFacts leaf2500Box leaf2500Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2500Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810581504) }) = true
      norm_num [leaf2500Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2500CertificateValid :
    WideCertificateValid leaf2500Box leaf2500Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi190ValidityFacts
    leaf2500LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2500CoverageChecked :
    coverageCheck (innerAD leaf2500Box) leaf2500InnerLog = true := by
  rfl'

private theorem leaf2500InnerLogValid :
    leaf2500InnerLog.Valid 8 (innerAD leaf2500Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2500CoverageChecked

private noncomputable def leaf2500InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2500InputLogOnePlusV_eq :
    leaf2500InputLogOnePlusV = outerEnclosure 24
      (leaf2500Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2500RoundedFacts : LeafRoundedFacts 8
    leaf2500Certificate.logOnePlusV leaf2500InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2500InputLogOnePlusV_eq }

private noncomputable def leaf2500Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi190InputQChi innerPair91Input
    leaf2500InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2500LowerChecked :
    lowerCheck 24 leaf2500Box leaf2500Inputs = true := by
  rfl'

private theorem leaf2500CoversExact : CoversExact 8
    leaf2500Box leaf2500Certificate leaf2500InnerLog leaf2500Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi190RoundedFacts
    innerPair91RoundedFacts leaf2500RoundedFacts (by rfl)

private theorem leaf2500FlatSound : Sound leaf2500Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2500CertificateValid
    leaf2500InnerLogValid leaf2500CoversExact leaf2500LowerChecked

private noncomputable def leaf2501Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf2501Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486410240) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1938730895/1073741824) }, upper := { exponent := 0, mantissa := (29865/16384) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973794611/54972820480) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2501InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf2501LocalValidity :
    LeafFacts leaf2501Box leaf2501Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2501Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486410240) }) = true
      norm_num [leaf2501Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2501CertificateValid :
    WideCertificateValid leaf2501Box leaf2501Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi191ValidityFacts
    leaf2501LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2501CoverageChecked :
    coverageCheck (innerAD leaf2501Box) leaf2501InnerLog = true := by
  rfl'

private theorem leaf2501InnerLogValid :
    leaf2501InnerLog.Valid 8 (innerAD leaf2501Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf2501CoverageChecked

private noncomputable def leaf2501InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814689/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2501InputLogOnePlusV_eq :
    leaf2501InputLogOnePlusV = outerEnclosure 24
      (leaf2501Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2501RoundedFacts : LeafRoundedFacts 8
    leaf2501Certificate.logOnePlusV leaf2501InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2501InputLogOnePlusV_eq }

private noncomputable def leaf2501Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi191InputQChi innerPair72Input
    leaf2501InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2501LowerChecked :
    lowerCheck 24 leaf2501Box leaf2501Inputs = true := by
  rfl'

private theorem leaf2501CoversExact : CoversExact 8
    leaf2501Box leaf2501Certificate leaf2501InnerLog leaf2501Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi191RoundedFacts
    innerPair72RoundedFacts leaf2501RoundedFacts (by rfl)

private theorem leaf2501FlatSound : Sound leaf2501Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2501CertificateValid
    leaf2501InnerLogValid leaf2501CoversExact leaf2501LowerChecked

private noncomputable def leaf2502Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf2502Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137432019968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1942662813/1073741824) }, upper := { exponent := 0, mantissa := (14963/8192) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868941823/274864039936) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2502InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf2502LocalValidity :
    LeafFacts leaf2502Box leaf2502Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2502Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137432019968) }) = true
      norm_num [leaf2502Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2502CertificateValid :
    WideCertificateValid leaf2502Box leaf2502Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi191ValidityFacts
    leaf2502LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2502CoverageChecked :
    coverageCheck (innerAD leaf2502Box) leaf2502InnerLog = true := by
  rfl'

private theorem leaf2502InnerLogValid :
    leaf2502InnerLog.Valid 8 (innerAD leaf2502Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf2502CoverageChecked

private noncomputable def leaf2502InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2502InputLogOnePlusV_eq :
    leaf2502InputLogOnePlusV = outerEnclosure 24
      (leaf2502Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2502RoundedFacts : LeafRoundedFacts 8
    leaf2502Certificate.logOnePlusV leaf2502InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2502InputLogOnePlusV_eq }

private noncomputable def leaf2502Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi191InputQChi innerPair72Input
    leaf2502InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2502LowerChecked :
    lowerCheck 24 leaf2502Box leaf2502Inputs = true := by
  rfl'

private theorem leaf2502CoversExact : CoversExact 8
    leaf2502Box leaf2502Certificate leaf2502InnerLog leaf2502Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi191RoundedFacts
    innerPair72RoundedFacts leaf2502RoundedFacts (by rfl)

private theorem leaf2502FlatSound : Sound leaf2502Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2502CertificateValid
    leaf2502InnerLogValid leaf2502CoversExact leaf2502LowerChecked

private noncomputable def leaf2503Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf2503Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810646016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1953147933/1073741824) }, upper := { exponent := 0, mantissa := (15043/8192) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91622953301/91621292032) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2503InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2503LocalValidity :
    LeafFacts leaf2503Box leaf2503Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2503Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810646016) }) = true
      norm_num [leaf2503Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2503CertificateValid :
    WideCertificateValid leaf2503Box leaf2503Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi192ValidityFacts
    leaf2503LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2503CoverageChecked :
    coverageCheck (innerAD leaf2503Box) leaf2503InnerLog = true := by
  rfl'

private theorem leaf2503InnerLogValid :
    leaf2503InnerLog.Valid 8 (innerAD leaf2503Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2503CoverageChecked

private noncomputable def leaf2503InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2503InputLogOnePlusV_eq :
    leaf2503InputLogOnePlusV = outerEnclosure 24
      (leaf2503Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2503RoundedFacts : LeafRoundedFacts 8
    leaf2503Certificate.logOnePlusV leaf2503InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2503InputLogOnePlusV_eq }

private noncomputable def leaf2503Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi192InputQChi innerPair91Input
    leaf2503InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2503LowerChecked :
    lowerCheck 24 leaf2503Box leaf2503Inputs = true := by
  rfl'

private theorem leaf2503CoversExact : CoversExact 8
    leaf2503Box leaf2503Certificate leaf2503InnerLog leaf2503Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi192RoundedFacts
    innerPair91RoundedFacts leaf2503RoundedFacts (by rfl)

private theorem leaf2503FlatSound : Sound leaf2503Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2503CertificateValid
    leaf2503InnerLogValid leaf2503CoversExact leaf2503LowerChecked

private noncomputable def leaf2504Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf2504Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431906304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1957145383/1073741824) }, upper := { exponent := 0, mantissa := (7537/4096) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868828159/274863812608) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2504InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2504LocalValidity :
    LeafFacts leaf2504Box leaf2504Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2504Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431906304) }) = true
      norm_num [leaf2504Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2504CertificateValid :
    WideCertificateValid leaf2504Box leaf2504Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi192ValidityFacts
    leaf2504LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2504CoverageChecked :
    coverageCheck (innerAD leaf2504Box) leaf2504InnerLog = true := by
  rfl'

private theorem leaf2504InnerLogValid :
    leaf2504InnerLog.Valid 8 (innerAD leaf2504Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2504CoverageChecked

private noncomputable def leaf2504InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629387/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2504InputLogOnePlusV_eq :
    leaf2504InputLogOnePlusV = outerEnclosure 24
      (leaf2504Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2504RoundedFacts : LeafRoundedFacts 8
    leaf2504Certificate.logOnePlusV leaf2504InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2504InputLogOnePlusV_eq }

private noncomputable def leaf2504Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi192InputQChi innerPair91Input
    leaf2504InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2504LowerChecked :
    lowerCheck 24 leaf2504Box leaf2504Inputs = true := by
  rfl'

private theorem leaf2504CoversExact : CoversExact 8
    leaf2504Box leaf2504Certificate leaf2504InnerLog leaf2504Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi192RoundedFacts
    innerPair91RoundedFacts leaf2504RoundedFacts (by rfl)

private theorem leaf2504FlatSound : Sound leaf2504Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2504CertificateValid
    leaf2504InnerLogValid leaf2504CoversExact leaf2504LowerChecked

private noncomputable def leaf2505Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf2505Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810662912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1946594731/1073741824) }, upper := { exponent := 0, mantissa := (29987/16384) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91622970197/91621325824) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2505InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2505LocalValidity :
    LeafFacts leaf2505Box leaf2505Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2505Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810662912) }) = true
      norm_num [leaf2505Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2505CertificateValid :
    WideCertificateValid leaf2505Box leaf2505Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi191ValidityFacts
    leaf2505LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2505CoverageChecked :
    coverageCheck (innerAD leaf2505Box) leaf2505InnerLog = true := by
  rfl'

private theorem leaf2505InnerLogValid :
    leaf2505InnerLog.Valid 8 (innerAD leaf2505Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2505CoverageChecked

private noncomputable def leaf2505InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814691/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2505InputLogOnePlusV_eq :
    leaf2505InputLogOnePlusV = outerEnclosure 24
      (leaf2505Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2505RoundedFacts : LeafRoundedFacts 8
    leaf2505Certificate.logOnePlusV leaf2505InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2505InputLogOnePlusV_eq }

private noncomputable def leaf2505Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi191InputQChi innerPair91Input
    leaf2505InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2505LowerChecked :
    lowerCheck 24 leaf2505Box leaf2505Inputs = true := by
  rfl'

private theorem leaf2505CoversExact : CoversExact 8
    leaf2505Box leaf2505Certificate leaf2505InnerLog leaf2505Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi191RoundedFacts
    innerPair91RoundedFacts leaf2505RoundedFacts (by rfl)

private theorem leaf2505FlatSound : Sound leaf2505Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2505CertificateValid
    leaf2505InnerLogValid leaf2505CoversExact leaf2505LowerChecked

private noncomputable def leaf2506Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf2506Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431957504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1950526649/1073741824) }, upper := { exponent := 0, mantissa := (939/512) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868879359/274863915008) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2506InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2506LocalValidity :
    LeafFacts leaf2506Box leaf2506Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2506Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431957504) }) = true
      norm_num [leaf2506Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2506CertificateValid :
    WideCertificateValid leaf2506Box leaf2506Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi191ValidityFacts
    leaf2506LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2506CoverageChecked :
    coverageCheck (innerAD leaf2506Box) leaf2506InnerLog = true := by
  rfl'

private theorem leaf2506InnerLogValid :
    leaf2506InnerLog.Valid 8 (innerAD leaf2506Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2506CoverageChecked

private noncomputable def leaf2506InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2506InputLogOnePlusV_eq :
    leaf2506InputLogOnePlusV = outerEnclosure 24
      (leaf2506Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2506RoundedFacts : LeafRoundedFacts 8
    leaf2506Certificate.logOnePlusV leaf2506InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2506InputLogOnePlusV_eq }

private noncomputable def leaf2506Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi191InputQChi innerPair91Input
    leaf2506InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2506LowerChecked :
    lowerCheck 24 leaf2506Box leaf2506Inputs = true := by
  rfl'

private theorem leaf2506CoversExact : CoversExact 8
    leaf2506Box leaf2506Certificate leaf2506InnerLog leaf2506Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi191RoundedFacts
    innerPair91RoundedFacts leaf2506RoundedFacts (by rfl)

private theorem leaf2506FlatSound : Sound leaf2506Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2506CertificateValid
    leaf2506InnerLogValid leaf2506CoversExact leaf2506LowerChecked

private noncomputable def leaf2507Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf2507Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486374912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1961142833/1073741824) }, upper := { exponent := 0, mantissa := (15105/8192) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973759283/54972749824) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2507InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2507LocalValidity :
    LeafFacts leaf2507Box leaf2507Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2507Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486374912) }) = true
      norm_num [leaf2507Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2507CertificateValid :
    WideCertificateValid leaf2507Box leaf2507Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi192ValidityFacts
    leaf2507LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2507CoverageChecked :
    coverageCheck (innerAD leaf2507Box) leaf2507InnerLog = true := by
  rfl'

private theorem leaf2507InnerLogValid :
    leaf2507InnerLog.Valid 8 (innerAD leaf2507Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2507CoverageChecked

private noncomputable def leaf2507InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2507InputLogOnePlusV_eq :
    leaf2507InputLogOnePlusV = outerEnclosure 24
      (leaf2507Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2507RoundedFacts : LeafRoundedFacts 8
    leaf2507Certificate.logOnePlusV leaf2507InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2507InputLogOnePlusV_eq }

private noncomputable def leaf2507Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi192InputQChi innerPair91Input
    leaf2507InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2507LowerChecked :
    lowerCheck 24 leaf2507Box leaf2507Inputs = true := by
  rfl'

private theorem leaf2507CoversExact : CoversExact 8
    leaf2507Box leaf2507Certificate leaf2507InnerLog leaf2507Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi192RoundedFacts
    innerPair91RoundedFacts leaf2507RoundedFacts (by rfl)

private theorem leaf2507FlatSound : Sound leaf2507Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2507CertificateValid
    leaf2507InnerLogValid leaf2507CoversExact leaf2507LowerChecked

private noncomputable def leaf2508Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf2508Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (2694841605/2694742016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1965140283/1073741824) }, upper := { exponent := 0, mantissa := (473/256) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5389583621/5389484032) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2508InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2508LocalValidity :
    LeafFacts leaf2508Box leaf2508Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2508Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2694841605/2694742016) }) = true
      norm_num [leaf2508Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2508CertificateValid :
    WideCertificateValid leaf2508Box leaf2508Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi192ValidityFacts
    leaf2508LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2508CoverageChecked :
    coverageCheck (innerAD leaf2508Box) leaf2508InnerLog = true := by
  rfl'

private theorem leaf2508InnerLogValid :
    leaf2508InnerLog.Valid 8 (innerAD leaf2508Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2508CoverageChecked

private noncomputable def leaf2508InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2508InputLogOnePlusV_eq :
    leaf2508InputLogOnePlusV = outerEnclosure 24
      (leaf2508Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2508RoundedFacts : LeafRoundedFacts 8
    leaf2508Certificate.logOnePlusV leaf2508InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2508InputLogOnePlusV_eq }

private noncomputable def leaf2508Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi192InputQChi innerPair91Input
    leaf2508InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2508LowerChecked :
    lowerCheck 24 leaf2508Box leaf2508Inputs = true := by
  rfl'

private theorem leaf2508CoversExact : CoversExact 8
    leaf2508Box leaf2508Certificate leaf2508InnerLog leaf2508Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi192RoundedFacts
    innerPair91RoundedFacts leaf2508RoundedFacts (by rfl)

private theorem leaf2508FlatSound : Sound leaf2508Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2508CertificateValid
    leaf2508InnerLogValid leaf2508CoversExact leaf2508LowerChecked

private noncomputable def leaf2509Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf2509Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431824896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1967564971/1073741824) }, upper := { exponent := 0, mantissa := (30307/16384) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868746751/274863649792) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2509InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2509LocalValidity :
    LeafFacts leaf2509Box leaf2509Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2509Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431824896) }) = true
      norm_num [leaf2509Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2509CertificateValid :
    WideCertificateValid leaf2509Box leaf2509Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi189ValidityFacts
    leaf2509LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2509CoverageChecked :
    coverageCheck (innerAD leaf2509Box) leaf2509InnerLog = true := by
  rfl'

private theorem leaf2509InnerLogValid :
    leaf2509InnerLog.Valid 8 (innerAD leaf2509Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2509CoverageChecked

private noncomputable def leaf2509InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726837/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2509InputLogOnePlusV_eq :
    leaf2509InputLogOnePlusV = outerEnclosure 24
      (leaf2509Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2509RoundedFacts : LeafRoundedFacts 8
    leaf2509Certificate.logOnePlusV leaf2509InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2509InputLogOnePlusV_eq }

private noncomputable def leaf2509Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi189InputQChi innerPair91Input
    leaf2509InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2509LowerChecked :
    lowerCheck 24 leaf2509Box leaf2509Inputs = true := by
  rfl'

private theorem leaf2509CoversExact : CoversExact 8
    leaf2509Box leaf2509Certificate leaf2509InnerLog leaf2509Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi189RoundedFacts
    innerPair91RoundedFacts leaf2509RoundedFacts (by rfl)

private theorem leaf2509FlatSound : Sound leaf2509Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2509CertificateValid
    leaf2509InnerLogValid leaf2509CoversExact leaf2509LowerChecked

private noncomputable def leaf2510Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf2510Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486358528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1971627953/1073741824) }, upper := { exponent := 0, mantissa := (15185/8192) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973742899/54972717056) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2510InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2510LocalValidity :
    LeafFacts leaf2510Box leaf2510Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2510Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486358528) }) = true
      norm_num [leaf2510Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2510CertificateValid :
    WideCertificateValid leaf2510Box leaf2510Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi189ValidityFacts
    leaf2510LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2510CoverageChecked :
    coverageCheck (innerAD leaf2510Box) leaf2510InnerLog = true := by
  rfl'

private theorem leaf2510InnerLogValid :
    leaf2510InnerLog.Valid 8 (innerAD leaf2510Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2510CoverageChecked

private noncomputable def leaf2510InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814697/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2510InputLogOnePlusV_eq :
    leaf2510InputLogOnePlusV = outerEnclosure 24
      (leaf2510Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2510RoundedFacts : LeafRoundedFacts 8
    leaf2510Certificate.logOnePlusV leaf2510InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2510InputLogOnePlusV_eq }

private noncomputable def leaf2510Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi189InputQChi innerPair91Input
    leaf2510InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2510LowerChecked :
    lowerCheck 24 leaf2510Box leaf2510Inputs = true := by
  rfl'

private theorem leaf2510CoversExact : CoversExact 8
    leaf2510Box leaf2510Certificate leaf2510InnerLog leaf2510Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi189RoundedFacts
    innerPair91RoundedFacts leaf2510RoundedFacts (by rfl)

private theorem leaf2510FlatSound : Sound leaf2510Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2510CertificateValid
    leaf2510InnerLogValid leaf2510CoversExact leaf2510LowerChecked

private noncomputable def leaf2511Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf2511Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431711744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1981982009/1073741824) }, upper := { exponent := 0, mantissa := (477/256) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868633599/274863423488) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf2511InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2511LocalValidity :
    LeafFacts leaf2511Box leaf2511Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2511Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431711744) }) = true
      norm_num [leaf2511Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2511CertificateValid :
    WideCertificateValid leaf2511Box leaf2511Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi190ValidityFacts
    leaf2511LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2511CoverageChecked :
    coverageCheck (innerAD leaf2511Box) leaf2511InnerLog = true := by
  rfl'

private theorem leaf2511InnerLogValid :
    leaf2511InnerLog.Valid 8 (innerAD leaf2511Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2511CoverageChecked

private noncomputable def leaf2511InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2511InputLogOnePlusV_eq :
    leaf2511InputLogOnePlusV = outerEnclosure 24
      (leaf2511Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2511RoundedFacts : LeafRoundedFacts 8
    leaf2511Certificate.logOnePlusV leaf2511InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2511InputLogOnePlusV_eq }

private noncomputable def leaf2511Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi190InputQChi innerPair91Input
    leaf2511InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2511LowerChecked :
    lowerCheck 24 leaf2511Box leaf2511Inputs = true := by
  rfl'

private theorem leaf2511CoversExact : CoversExact 8
    leaf2511Box leaf2511Certificate leaf2511InnerLog leaf2511Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi190RoundedFacts
    innerPair91RoundedFacts leaf2511RoundedFacts (by rfl)

private theorem leaf2511FlatSound : Sound leaf2511Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2511CertificateValid
    leaf2511InnerLogValid leaf2511CoversExact leaf2511LowerChecked

private noncomputable def leaf2512Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf2512Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431678976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1986110523/1073741824) }, upper := { exponent := 0, mantissa := (239/128) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868600831/274863357952) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf2512InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2512LocalValidity :
    LeafFacts leaf2512Box leaf2512Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2512Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431678976) }) = true
      norm_num [leaf2512Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2512CertificateValid :
    WideCertificateValid leaf2512Box leaf2512Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi190ValidityFacts
    leaf2512LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2512CoverageChecked :
    coverageCheck (innerAD leaf2512Box) leaf2512InnerLog = true := by
  rfl'

private theorem leaf2512InnerLogValid :
    leaf2512InnerLog.Valid 8 (innerAD leaf2512Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2512CoverageChecked

private noncomputable def leaf2512InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2512InputLogOnePlusV_eq :
    leaf2512InputLogOnePlusV = outerEnclosure 24
      (leaf2512Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2512RoundedFacts : LeafRoundedFacts 8
    leaf2512Certificate.logOnePlusV leaf2512InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2512InputLogOnePlusV_eq }

private noncomputable def leaf2512Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi190InputQChi innerPair91Input
    leaf2512InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2512LowerChecked :
    lowerCheck 24 leaf2512Box leaf2512Inputs = true := by
  rfl'

private theorem leaf2512CoversExact : CoversExact 8
    leaf2512Box leaf2512Certificate leaf2512InnerLog leaf2512Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi190RoundedFacts
    innerPair91RoundedFacts leaf2512RoundedFacts (by rfl)

private theorem leaf2512FlatSound : Sound leaf2512Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2512CertificateValid
    leaf2512InnerLogValid leaf2512CoversExact leaf2512LowerChecked

private noncomputable def leaf2513Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf2513Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431760384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1975690935/1073741824) }, upper := { exponent := 0, mantissa := (30433/16384) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868682239/274863520768) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2513InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2513LocalValidity :
    LeafFacts leaf2513Box leaf2513Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2513Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431760384) }) = true
      norm_num [leaf2513Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2513CertificateValid :
    WideCertificateValid leaf2513Box leaf2513Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi189ValidityFacts
    leaf2513LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2513CoverageChecked :
    coverageCheck (innerAD leaf2513Box) leaf2513InnerLog = true := by
  rfl'

private theorem leaf2513InnerLogValid :
    leaf2513InnerLog.Valid 8 (innerAD leaf2513Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2513CoverageChecked

private noncomputable def leaf2513InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2513InputLogOnePlusV_eq :
    leaf2513InputLogOnePlusV = outerEnclosure 24
      (leaf2513Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2513RoundedFacts : LeafRoundedFacts 8
    leaf2513Certificate.logOnePlusV leaf2513InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2513InputLogOnePlusV_eq }

private noncomputable def leaf2513Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi189InputQChi innerPair91Input
    leaf2513InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2513LowerChecked :
    lowerCheck 24 leaf2513Box leaf2513Inputs = true := by
  rfl'

private theorem leaf2513CoversExact : CoversExact 8
    leaf2513Box leaf2513Certificate leaf2513InnerLog leaf2513Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi189RoundedFacts
    innerPair91RoundedFacts leaf2513RoundedFacts (by rfl)

private theorem leaf2513FlatSound : Sound leaf2513Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2513CertificateValid
    leaf2513InnerLogValid leaf2513CoversExact leaf2513LowerChecked

private noncomputable def leaf2514Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf2514Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431728128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1979753917/1073741824) }, upper := { exponent := 0, mantissa := (953/512) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868649983/274863456256) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2514InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2514LocalValidity :
    LeafFacts leaf2514Box leaf2514Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2514Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431728128) }) = true
      norm_num [leaf2514Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2514CertificateValid :
    WideCertificateValid leaf2514Box leaf2514Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi189ValidityFacts
    leaf2514LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2514CoverageChecked :
    coverageCheck (innerAD leaf2514Box) leaf2514InnerLog = true := by
  rfl'

private theorem leaf2514InnerLogValid :
    leaf2514InnerLog.Valid 8 (innerAD leaf2514Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2514CoverageChecked

private noncomputable def leaf2514InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814699/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2514InputLogOnePlusV_eq :
    leaf2514InputLogOnePlusV = outerEnclosure 24
      (leaf2514Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2514RoundedFacts : LeafRoundedFacts 8
    leaf2514Certificate.logOnePlusV leaf2514InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2514InputLogOnePlusV_eq }

private noncomputable def leaf2514Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi189InputQChi innerPair91Input
    leaf2514InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2514LowerChecked :
    lowerCheck 24 leaf2514Box leaf2514Inputs = true := by
  rfl'

private theorem leaf2514CoversExact : CoversExact 8
    leaf2514Box leaf2514Certificate leaf2514InnerLog leaf2514Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi189RoundedFacts
    innerPair91RoundedFacts leaf2514RoundedFacts (by rfl)

private theorem leaf2514FlatSound : Sound leaf2514Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2514CertificateValid
    leaf2514InnerLogValid leaf2514CoversExact leaf2514LowerChecked

private noncomputable def leaf2515Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf2515Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (65529/65536), upper := (15270769095/15270182912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1990239037/1073741824) }, upper := { exponent := 0, mantissa := (479/256) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (30540952007/30540365824) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf2515InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2515LocalValidity :
    LeafFacts leaf2515Box leaf2515Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2515Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (15270769095/15270182912) }) = true
      norm_num [leaf2515Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2515CertificateValid :
    WideCertificateValid leaf2515Box leaf2515Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi190ValidityFacts
    leaf2515LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2515CoverageChecked :
    coverageCheck (innerAD leaf2515Box) leaf2515InnerLog = true := by
  rfl'

private theorem leaf2515InnerLogValid :
    leaf2515InnerLog.Valid 8 (innerAD leaf2515Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2515CoverageChecked

private noncomputable def leaf2515InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2515InputLogOnePlusV_eq :
    leaf2515InputLogOnePlusV = outerEnclosure 24
      (leaf2515Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2515RoundedFacts : LeafRoundedFacts 8
    leaf2515Certificate.logOnePlusV leaf2515InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2515InputLogOnePlusV_eq }

private noncomputable def leaf2515Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi190InputQChi innerPair91Input
    leaf2515InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2515LowerChecked :
    lowerCheck 24 leaf2515Box leaf2515Inputs = true := by
  rfl'

private theorem leaf2515CoversExact : CoversExact 8
    leaf2515Box leaf2515Certificate leaf2515InnerLog leaf2515Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi190RoundedFacts
    innerPair91RoundedFacts leaf2515RoundedFacts (by rfl)

private theorem leaf2515FlatSound : Sound leaf2515Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2515CertificateValid
    leaf2515InnerLogValid leaf2515CoversExact leaf2515LowerChecked

private noncomputable def leaf2516Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf2516Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486322688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1994367551/1073741824) }, upper := { exponent := 0, mantissa := (15/8) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973707059/54972645376) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf2516InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf2516LocalValidity :
    LeafFacts leaf2516Box leaf2516Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2516Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486322688) }) = true
      norm_num [leaf2516Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2516CertificateValid :
    WideCertificateValid leaf2516Box leaf2516Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi190ValidityFacts
    leaf2516LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2516CoverageChecked :
    coverageCheck (innerAD leaf2516Box) leaf2516InnerLog = true := by
  rfl'

private theorem leaf2516InnerLogValid :
    leaf2516InnerLog.Valid 8 (innerAD leaf2516Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf2516CoverageChecked

private noncomputable def leaf2516InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2516InputLogOnePlusV_eq :
    leaf2516InputLogOnePlusV = outerEnclosure 24
      (leaf2516Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2516RoundedFacts : LeafRoundedFacts 8
    leaf2516Certificate.logOnePlusV leaf2516InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2516InputLogOnePlusV_eq }

private noncomputable def leaf2516Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi190InputQChi innerPair91Input
    leaf2516InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2516LowerChecked :
    lowerCheck 24 leaf2516Box leaf2516Inputs = true := by
  rfl'

private theorem leaf2516CoversExact : CoversExact 8
    leaf2516Box leaf2516Certificate leaf2516InnerLog leaf2516Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi190RoundedFacts
    innerPair91RoundedFacts leaf2516RoundedFacts (by rfl)

private theorem leaf2516FlatSound : Sound leaf2516Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2516CertificateValid
    leaf2516InnerLogValid leaf2516CoversExact leaf2516LowerChecked

private noncomputable def component53Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component53Node0_sound : Sound component53Node0Box :=
  sound_of_literal_split component53Node0Box leaf2453Box leaf2454Box
    .k (217/64) (by rfl) (by rfl)
    leaf2453FlatSound leaf2454FlatSound

private noncomputable def component53Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node1_sound : Sound component53Node1Box :=
  sound_of_literal_split component53Node1Box leaf2455Box leaf2456Box
    .k (217/64) (by rfl) (by rfl)
    leaf2455FlatSound leaf2456FlatSound

private noncomputable def component53Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node2_sound : Sound component53Node2Box :=
  sound_of_literal_split component53Node2Box component53Node0Box component53Node1Box
    .chi (57/256) (by rfl) (by rfl)
    component53Node0_sound component53Node1_sound

private noncomputable def component53Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component53Node3_sound : Sound component53Node3Box :=
  sound_of_literal_split component53Node3Box leaf2457Box leaf2458Box
    .k (219/64) (by rfl) (by rfl)
    leaf2457FlatSound leaf2458FlatSound

private noncomputable def component53Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node4_sound : Sound component53Node4Box :=
  sound_of_literal_split component53Node4Box leaf2459Box leaf2460Box
    .k (219/64) (by rfl) (by rfl)
    leaf2459FlatSound leaf2460FlatSound

private noncomputable def component53Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node5_sound : Sound component53Node5Box :=
  sound_of_literal_split component53Node5Box component53Node3Box component53Node4Box
    .chi (57/256) (by rfl) (by rfl)
    component53Node3_sound component53Node4_sound

private noncomputable def component53Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node6_sound : Sound component53Node6Box :=
  sound_of_literal_split component53Node6Box component53Node2Box component53Node5Box
    .k (109/32) (by rfl) (by rfl)
    component53Node2_sound component53Node5_sound

private noncomputable def component53Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component53Node7_sound : Sound component53Node7Box :=
  sound_of_literal_split component53Node7Box leaf2461Box leaf2462Box
    .k (217/64) (by rfl) (by rfl)
    leaf2461FlatSound leaf2462FlatSound

private noncomputable def component53Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component53Node8_sound : Sound component53Node8Box :=
  sound_of_literal_split component53Node8Box leaf2463Box leaf2464Box
    .k (217/64) (by rfl) (by rfl)
    leaf2463FlatSound leaf2464FlatSound

private noncomputable def component53Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component53Node9_sound : Sound component53Node9Box :=
  sound_of_literal_split component53Node9Box component53Node7Box component53Node8Box
    .chi (59/256) (by rfl) (by rfl)
    component53Node7_sound component53Node8_sound

private noncomputable def component53Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component53Node10_sound : Sound component53Node10Box :=
  sound_of_literal_split component53Node10Box leaf2465Box leaf2466Box
    .k (219/64) (by rfl) (by rfl)
    leaf2465FlatSound leaf2466FlatSound

private noncomputable def component53Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component53Node11_sound : Sound component53Node11Box :=
  sound_of_literal_split component53Node11Box leaf2467Box leaf2468Box
    .k (219/64) (by rfl) (by rfl)
    leaf2467FlatSound leaf2468FlatSound

private noncomputable def component53Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component53Node12_sound : Sound component53Node12Box :=
  sound_of_literal_split component53Node12Box component53Node10Box component53Node11Box
    .chi (59/256) (by rfl) (by rfl)
    component53Node10_sound component53Node11_sound

private noncomputable def component53Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component53Node13_sound : Sound component53Node13Box :=
  sound_of_literal_split component53Node13Box component53Node9Box component53Node12Box
    .k (109/32) (by rfl) (by rfl)
    component53Node9_sound component53Node12_sound

private noncomputable def component53Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component53Node14_sound : Sound component53Node14Box :=
  sound_of_literal_split component53Node14Box component53Node6Box component53Node13Box
    .chi (29/128) (by rfl) (by rfl)
    component53Node6_sound component53Node13_sound

private noncomputable def component53Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component53Node15_sound : Sound component53Node15Box :=
  sound_of_literal_split component53Node15Box leaf2469Box leaf2470Box
    .k (221/64) (by rfl) (by rfl)
    leaf2469FlatSound leaf2470FlatSound

private noncomputable def component53Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node16_sound : Sound component53Node16Box :=
  sound_of_literal_split component53Node16Box leaf2471Box leaf2472Box
    .k (221/64) (by rfl) (by rfl)
    leaf2471FlatSound leaf2472FlatSound

private noncomputable def component53Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node17_sound : Sound component53Node17Box :=
  sound_of_literal_split component53Node17Box component53Node15Box component53Node16Box
    .chi (57/256) (by rfl) (by rfl)
    component53Node15_sound component53Node16_sound

private noncomputable def component53Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component53Node18_sound : Sound component53Node18Box :=
  sound_of_literal_split component53Node18Box leaf2473Box leaf2474Box
    .k (223/64) (by rfl) (by rfl)
    leaf2473FlatSound leaf2474FlatSound

private noncomputable def component53Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node19_sound : Sound component53Node19Box :=
  sound_of_literal_split component53Node19Box leaf2475Box leaf2476Box
    .k (223/64) (by rfl) (by rfl)
    leaf2475FlatSound leaf2476FlatSound

private noncomputable def component53Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node20_sound : Sound component53Node20Box :=
  sound_of_literal_split component53Node20Box component53Node18Box component53Node19Box
    .chi (57/256) (by rfl) (by rfl)
    component53Node18_sound component53Node19_sound

private noncomputable def component53Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node21_sound : Sound component53Node21Box :=
  sound_of_literal_split component53Node21Box component53Node17Box component53Node20Box
    .k (111/32) (by rfl) (by rfl)
    component53Node17_sound component53Node20_sound

private noncomputable def component53Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component53Node22_sound : Sound component53Node22Box :=
  sound_of_literal_split component53Node22Box leaf2477Box leaf2478Box
    .k (221/64) (by rfl) (by rfl)
    leaf2477FlatSound leaf2478FlatSound

private noncomputable def component53Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component53Node23_sound : Sound component53Node23Box :=
  sound_of_literal_split component53Node23Box leaf2479Box leaf2480Box
    .k (221/64) (by rfl) (by rfl)
    leaf2479FlatSound leaf2480FlatSound

private noncomputable def component53Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component53Node24_sound : Sound component53Node24Box :=
  sound_of_literal_split component53Node24Box component53Node22Box component53Node23Box
    .chi (59/256) (by rfl) (by rfl)
    component53Node22_sound component53Node23_sound

private noncomputable def component53Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component53Node25_sound : Sound component53Node25Box :=
  sound_of_literal_split component53Node25Box leaf2481Box leaf2482Box
    .k (223/64) (by rfl) (by rfl)
    leaf2481FlatSound leaf2482FlatSound

private noncomputable def component53Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component53Node26_sound : Sound component53Node26Box :=
  sound_of_literal_split component53Node26Box leaf2483Box leaf2484Box
    .k (223/64) (by rfl) (by rfl)
    leaf2483FlatSound leaf2484FlatSound

private noncomputable def component53Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component53Node27_sound : Sound component53Node27Box :=
  sound_of_literal_split component53Node27Box component53Node25Box component53Node26Box
    .chi (59/256) (by rfl) (by rfl)
    component53Node25_sound component53Node26_sound

private noncomputable def component53Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component53Node28_sound : Sound component53Node28Box :=
  sound_of_literal_split component53Node28Box component53Node24Box component53Node27Box
    .k (111/32) (by rfl) (by rfl)
    component53Node24_sound component53Node27_sound

private noncomputable def component53Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component53Node29_sound : Sound component53Node29Box :=
  sound_of_literal_split component53Node29Box component53Node21Box component53Node28Box
    .chi (29/128) (by rfl) (by rfl)
    component53Node21_sound component53Node28_sound

private noncomputable def component53Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component53Node30_sound : Sound component53Node30Box :=
  sound_of_literal_split component53Node30Box component53Node14Box component53Node29Box
    .k (55/16) (by rfl) (by rfl)
    component53Node14_sound component53Node29_sound

private noncomputable def component53Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component53Node31_sound : Sound component53Node31Box :=
  sound_of_literal_split component53Node31Box leaf2485Box leaf2486Box
    .k (217/64) (by rfl) (by rfl)
    leaf2485FlatSound leaf2486FlatSound

private noncomputable def component53Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node32_sound : Sound component53Node32Box :=
  sound_of_literal_split component53Node32Box leaf2487Box leaf2488Box
    .k (217/64) (by rfl) (by rfl)
    leaf2487FlatSound leaf2488FlatSound

private noncomputable def component53Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node33_sound : Sound component53Node33Box :=
  sound_of_literal_split component53Node33Box component53Node31Box component53Node32Box
    .chi (61/256) (by rfl) (by rfl)
    component53Node31_sound component53Node32_sound

private noncomputable def component53Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component53Node34_sound : Sound component53Node34Box :=
  sound_of_literal_split component53Node34Box leaf2489Box leaf2490Box
    .k (219/64) (by rfl) (by rfl)
    leaf2489FlatSound leaf2490FlatSound

private noncomputable def component53Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node35_sound : Sound component53Node35Box :=
  sound_of_literal_split component53Node35Box leaf2491Box leaf2492Box
    .k (219/64) (by rfl) (by rfl)
    leaf2491FlatSound leaf2492FlatSound

private noncomputable def component53Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node36_sound : Sound component53Node36Box :=
  sound_of_literal_split component53Node36Box component53Node34Box component53Node35Box
    .chi (61/256) (by rfl) (by rfl)
    component53Node34_sound component53Node35_sound

private noncomputable def component53Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node37_sound : Sound component53Node37Box :=
  sound_of_literal_split component53Node37Box component53Node33Box component53Node36Box
    .k (109/32) (by rfl) (by rfl)
    component53Node33_sound component53Node36_sound

private noncomputable def component53Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component53Node38_sound : Sound component53Node38Box :=
  sound_of_literal_split component53Node38Box leaf2493Box leaf2494Box
    .k (217/64) (by rfl) (by rfl)
    leaf2493FlatSound leaf2494FlatSound

private noncomputable def component53Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component53Node39_sound : Sound component53Node39Box :=
  sound_of_literal_split component53Node39Box leaf2495Box leaf2496Box
    .k (217/64) (by rfl) (by rfl)
    leaf2495FlatSound leaf2496FlatSound

private noncomputable def component53Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component53Node40_sound : Sound component53Node40Box :=
  sound_of_literal_split component53Node40Box component53Node38Box component53Node39Box
    .chi (63/256) (by rfl) (by rfl)
    component53Node38_sound component53Node39_sound

private noncomputable def component53Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component53Node41_sound : Sound component53Node41Box :=
  sound_of_literal_split component53Node41Box leaf2497Box leaf2498Box
    .k (219/64) (by rfl) (by rfl)
    leaf2497FlatSound leaf2498FlatSound

private noncomputable def component53Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component53Node42_sound : Sound component53Node42Box :=
  sound_of_literal_split component53Node42Box leaf2499Box leaf2500Box
    .k (219/64) (by rfl) (by rfl)
    leaf2499FlatSound leaf2500FlatSound

private noncomputable def component53Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component53Node43_sound : Sound component53Node43Box :=
  sound_of_literal_split component53Node43Box component53Node41Box component53Node42Box
    .chi (63/256) (by rfl) (by rfl)
    component53Node41_sound component53Node42_sound

private noncomputable def component53Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component53Node44_sound : Sound component53Node44Box :=
  sound_of_literal_split component53Node44Box component53Node40Box component53Node43Box
    .k (109/32) (by rfl) (by rfl)
    component53Node40_sound component53Node43_sound

private noncomputable def component53Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component53Node45_sound : Sound component53Node45Box :=
  sound_of_literal_split component53Node45Box component53Node37Box component53Node44Box
    .chi (31/128) (by rfl) (by rfl)
    component53Node37_sound component53Node44_sound

private noncomputable def component53Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component53Node46_sound : Sound component53Node46Box :=
  sound_of_literal_split component53Node46Box leaf2501Box leaf2502Box
    .k (221/64) (by rfl) (by rfl)
    leaf2501FlatSound leaf2502FlatSound

private noncomputable def component53Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node47_sound : Sound component53Node47Box :=
  sound_of_literal_split component53Node47Box leaf2503Box leaf2504Box
    .k (221/64) (by rfl) (by rfl)
    leaf2503FlatSound leaf2504FlatSound

private noncomputable def component53Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node48_sound : Sound component53Node48Box :=
  sound_of_literal_split component53Node48Box component53Node46Box component53Node47Box
    .chi (61/256) (by rfl) (by rfl)
    component53Node46_sound component53Node47_sound

private noncomputable def component53Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component53Node49_sound : Sound component53Node49Box :=
  sound_of_literal_split component53Node49Box leaf2505Box leaf2506Box
    .k (223/64) (by rfl) (by rfl)
    leaf2505FlatSound leaf2506FlatSound

private noncomputable def component53Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node50_sound : Sound component53Node50Box :=
  sound_of_literal_split component53Node50Box leaf2507Box leaf2508Box
    .k (223/64) (by rfl) (by rfl)
    leaf2507FlatSound leaf2508FlatSound

private noncomputable def component53Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node51_sound : Sound component53Node51Box :=
  sound_of_literal_split component53Node51Box component53Node49Box component53Node50Box
    .chi (61/256) (by rfl) (by rfl)
    component53Node49_sound component53Node50_sound

private noncomputable def component53Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component53Node52_sound : Sound component53Node52Box :=
  sound_of_literal_split component53Node52Box component53Node48Box component53Node51Box
    .k (111/32) (by rfl) (by rfl)
    component53Node48_sound component53Node51_sound

private noncomputable def component53Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component53Node53_sound : Sound component53Node53Box :=
  sound_of_literal_split component53Node53Box leaf2509Box leaf2510Box
    .k (221/64) (by rfl) (by rfl)
    leaf2509FlatSound leaf2510FlatSound

private noncomputable def component53Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component53Node54_sound : Sound component53Node54Box :=
  sound_of_literal_split component53Node54Box leaf2511Box leaf2512Box
    .k (221/64) (by rfl) (by rfl)
    leaf2511FlatSound leaf2512FlatSound

private noncomputable def component53Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component53Node55_sound : Sound component53Node55Box :=
  sound_of_literal_split component53Node55Box component53Node53Box component53Node54Box
    .chi (63/256) (by rfl) (by rfl)
    component53Node53_sound component53Node54_sound

private noncomputable def component53Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component53Node56_sound : Sound component53Node56Box :=
  sound_of_literal_split component53Node56Box leaf2513Box leaf2514Box
    .k (223/64) (by rfl) (by rfl)
    leaf2513FlatSound leaf2514FlatSound

private noncomputable def component53Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component53Node57_sound : Sound component53Node57Box :=
  sound_of_literal_split component53Node57Box leaf2515Box leaf2516Box
    .k (223/64) (by rfl) (by rfl)
    leaf2515FlatSound leaf2516FlatSound

private noncomputable def component53Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component53Node58_sound : Sound component53Node58Box :=
  sound_of_literal_split component53Node58Box component53Node56Box component53Node57Box
    .chi (63/256) (by rfl) (by rfl)
    component53Node56_sound component53Node57_sound

private noncomputable def component53Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component53Node59_sound : Sound component53Node59Box :=
  sound_of_literal_split component53Node59Box component53Node55Box component53Node58Box
    .k (111/32) (by rfl) (by rfl)
    component53Node55_sound component53Node58_sound

private noncomputable def component53Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component53Node60_sound : Sound component53Node60Box :=
  sound_of_literal_split component53Node60Box component53Node52Box component53Node59Box
    .chi (31/128) (by rfl) (by rfl)
    component53Node52_sound component53Node59_sound

private noncomputable def component53Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component53Node61_sound : Sound component53Node61Box :=
  sound_of_literal_split component53Node61Box component53Node45Box component53Node60Box
    .k (55/16) (by rfl) (by rfl)
    component53Node45_sound component53Node60_sound

noncomputable def component53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
theorem component53_sound : Sound component53Box :=
  sound_of_literal_split component53Box component53Node30Box component53Node61Box
    .chi (15/64) (by rfl) (by rfl)
    component53Node30_sound component53Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
