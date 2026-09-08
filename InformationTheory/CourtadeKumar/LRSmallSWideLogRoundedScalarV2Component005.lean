import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
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

private noncomputable def leaf209Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (1/8), chiHi := (5/32) }

private noncomputable def leaf209Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (33554491/33554432) }, vSqrt := { lower := (16383/16384), upper := (2796208/2796161) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (39812679/33554432) }, upper := { exponent := 0, mantissa := (637/512) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi25LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (5592369/5592322) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf209InnerLog : WideLogData :=
  innerPair136Data

set_option maxRecDepth 1000000 in
private theorem leaf209LocalValidity :
    LeafFacts leaf209Box leaf209Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf209Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2796208/2796161) }) = true
      norm_num [leaf209Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf209CertificateValid :
    WideCertificateValid leaf209Box leaf209Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi25ValidityFacts
    leaf209LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf209CoverageChecked :
    coverageCheck (innerAD leaf209Box) leaf209InnerLog = true := by
  rfl'

private theorem leaf209InnerLogValid :
    leaf209InnerLog.Valid 8 (innerAD leaf209Box) :=
  wideLogDataValid_of_cachedCheck endpoint32PositiveFacts
    endpoint33PositiveFacts.valid leaf209CoverageChecked

private noncomputable def leaf209InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814611/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf209InputLogOnePlusV_eq :
    leaf209InputLogOnePlusV = outerEnclosure 24
      (leaf209Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf209RoundedFacts : LeafRoundedFacts 8
    leaf209Certificate.logOnePlusV leaf209InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf209InputLogOnePlusV_eq }

private noncomputable def leaf209Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi25InputQChi innerPair136Input
    leaf209InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf209LowerChecked :
    lowerCheck 24 leaf209Box leaf209Inputs = true := by
  rfl'

private theorem leaf209CoversExact : CoversExact 8
    leaf209Box leaf209Certificate leaf209InnerLog leaf209Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi25RoundedFacts
    innerPair136RoundedFacts leaf209RoundedFacts (by rfl)

private theorem leaf209FlatSound : Sound leaf209Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf209CertificateValid
    leaf209InnerLogValid leaf209CoversExact leaf209LowerChecked

private noncomputable def leaf210Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (1/8), chiHi := (9/64) }

private noncomputable def leaf210Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108933/67108864) }, vSqrt := { lower := (16383/16384), upper := (8388624/8388491) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (80182429/67108864) }, upper := { exponent := 0, mantissa := (629/512) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi40LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777115/16776982) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf210InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf210LocalValidity :
    LeafFacts leaf210Box leaf210Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf210Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388624/8388491) }) = true
      norm_num [leaf210Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf210CertificateValid :
    WideCertificateValid leaf210Box leaf210Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi40ValidityFacts
    leaf210LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf210CoverageChecked :
    coverageCheck (innerAD leaf210Box) leaf210InnerLog = true := by
  rfl'

private theorem leaf210InnerLogValid :
    leaf210InnerLog.Valid 8 (innerAD leaf210Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf210CoverageChecked

private noncomputable def leaf210InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814607/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf210InputLogOnePlusV_eq :
    leaf210InputLogOnePlusV = outerEnclosure 24
      (leaf210Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf210RoundedFacts : LeafRoundedFacts 8
    leaf210Certificate.logOnePlusV leaf210InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf210InputLogOnePlusV_eq }

private noncomputable def leaf210Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi40InputQChi innerPair12Input
    leaf210InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf210LowerChecked :
    lowerCheck 24 leaf210Box leaf210Inputs = true := by
  rfl'

private theorem leaf210CoversExact : CoversExact 8
    leaf210Box leaf210Certificate leaf210InnerLog leaf210Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi40RoundedFacts
    innerPair12RoundedFacts leaf210RoundedFacts (by rfl)

private theorem leaf210FlatSound : Sound leaf210Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf210CertificateValid
    leaf210InnerLogValid leaf210CoversExact leaf210LowerChecked

private noncomputable def leaf211Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (9/64), chiHi := (5/32) }

private noncomputable def leaf211Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108935/67108864) }, vSqrt := { lower := (16383/16384), upper := (4194312/4194239) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (81820727/67108864) }, upper := { exponent := 0, mantissa := (321/256) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi41LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388551/8388478) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf211InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf211LocalValidity :
    LeafFacts leaf211Box leaf211Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf211Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194312/4194239) }) = true
      norm_num [leaf211Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf211CertificateValid :
    WideCertificateValid leaf211Box leaf211Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi41ValidityFacts
    leaf211LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf211CoverageChecked :
    coverageCheck (innerAD leaf211Box) leaf211InnerLog = true := by
  rfl'

private theorem leaf211InnerLogValid :
    leaf211InnerLog.Valid 8 (innerAD leaf211Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf211CoverageChecked

private noncomputable def leaf211InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629227/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf211InputLogOnePlusV_eq :
    leaf211InputLogOnePlusV = outerEnclosure 24
      (leaf211Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf211RoundedFacts : LeafRoundedFacts 8
    leaf211Certificate.logOnePlusV leaf211InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf211InputLogOnePlusV_eq }

private noncomputable def leaf211Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi41InputQChi innerPair13Input
    leaf211InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf211LowerChecked :
    lowerCheck 24 leaf211Box leaf211Inputs = true := by
  rfl'

private theorem leaf211CoversExact : CoversExact 8
    leaf211Box leaf211Certificate leaf211InnerLog leaf211Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi41RoundedFacts
    innerPair13RoundedFacts leaf211RoundedFacts (by rfl)

private theorem leaf211FlatSound : Sound leaf211Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf211CertificateValid
    leaf211InnerLogValid leaf211CoversExact leaf211LowerChecked

private noncomputable def leaf212Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf212Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108935/67108864) }, vSqrt := { lower := (16383/16384), upper := (16777248/16776941) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (82803707/67108864) }, upper := { exponent := 0, mantissa := (1299/1024) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554189/33553882) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf212InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf212LocalValidity :
    LeafFacts leaf212Box leaf212Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf212Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777248/16776941) }) = true
      norm_num [leaf212Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf212CertificateValid :
    WideCertificateValid leaf212Box leaf212Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi42ValidityFacts
    leaf212LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf212CoverageChecked :
    coverageCheck (innerAD leaf212Box) leaf212InnerLog = true := by
  rfl'

private theorem leaf212InnerLogValid :
    leaf212InnerLog.Valid 8 (innerAD leaf212Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf212CoverageChecked

private noncomputable def leaf212InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814617/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf212InputLogOnePlusV_eq :
    leaf212InputLogOnePlusV = outerEnclosure 24
      (leaf212Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf212RoundedFacts : LeafRoundedFacts 8
    leaf212Certificate.logOnePlusV leaf212InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf212InputLogOnePlusV_eq }

private noncomputable def leaf212Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi42InputQChi innerPair13Input
    leaf212InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf212LowerChecked :
    lowerCheck 24 leaf212Box leaf212Inputs = true := by
  rfl'

private theorem leaf212CoversExact : CoversExact 8
    leaf212Box leaf212Certificate leaf212InnerLog leaf212Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi42RoundedFacts
    innerPair13RoundedFacts leaf212RoundedFacts (by rfl)

private theorem leaf212FlatSound : Sound leaf212Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf212CertificateValid
    leaf212InnerLogValid leaf212CoversExact leaf212LowerChecked

private noncomputable def leaf213Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf213Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108937/67108864) }, vSqrt := { lower := (16383/16384), upper := (4194312/4194229) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (84376473/67108864) }, upper := { exponent := 0, mantissa := (331/256) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388541/8388458) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf213InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf213LocalValidity :
    LeafFacts leaf213Box leaf213Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf213Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194312/4194229) }) = true
      norm_num [leaf213Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf213CertificateValid :
    WideCertificateValid leaf213Box leaf213Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi43ValidityFacts
    leaf213LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf213CoverageChecked :
    coverageCheck (innerAD leaf213Box) leaf213InnerLog = true := by
  rfl'

private theorem leaf213InnerLogValid :
    leaf213InnerLog.Valid 8 (innerAD leaf213Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf213CoverageChecked

private noncomputable def leaf213InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf213InputLogOnePlusV_eq :
    leaf213InputLogOnePlusV = outerEnclosure 24
      (leaf213Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf213RoundedFacts : LeafRoundedFacts 8
    leaf213Certificate.logOnePlusV leaf213InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf213InputLogOnePlusV_eq }

private noncomputable def leaf213Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi43InputQChi innerPair16Input
    leaf213InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf213LowerChecked :
    lowerCheck 24 leaf213Box leaf213Inputs = true := by
  rfl'

private theorem leaf213CoversExact : CoversExact 8
    leaf213Box leaf213Certificate leaf213InnerLog leaf213Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi43RoundedFacts
    innerPair16RoundedFacts leaf213RoundedFacts (by rfl)

private theorem leaf213FlatSound : Sound leaf213Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf213CertificateValid
    leaf213InnerLogValid leaf213CoversExact leaf213LowerChecked

private noncomputable def leaf214Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf214Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108937/67108864) }, vSqrt := { lower := (16383/16384), upper := (2796208/2796155) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (83459025/67108864) }, upper := { exponent := 0, mantissa := (655/512) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (5592363/5592310) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf214InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf214LocalValidity :
    LeafFacts leaf214Box leaf214Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf214Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2796208/2796155) }) = true
      norm_num [leaf214Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf214CertificateValid :
    WideCertificateValid leaf214Box leaf214Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi42ValidityFacts
    leaf214LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf214CoverageChecked :
    coverageCheck (innerAD leaf214Box) leaf214InnerLog = true := by
  rfl'

private theorem leaf214InnerLogValid :
    leaf214InnerLog.Valid 8 (innerAD leaf214Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf214CoverageChecked

private noncomputable def leaf214InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (1453655/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf214InputLogOnePlusV_eq :
    leaf214InputLogOnePlusV = outerEnclosure 24
      (leaf214Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf214RoundedFacts : LeafRoundedFacts 8
    leaf214Certificate.logOnePlusV leaf214InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf214InputLogOnePlusV_eq }

private noncomputable def leaf214Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi42InputQChi innerPair13Input
    leaf214InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf214LowerChecked :
    lowerCheck 24 leaf214Box leaf214Inputs = true := by
  rfl'

private theorem leaf214CoversExact : CoversExact 8
    leaf214Box leaf214Certificate leaf214InnerLog leaf214Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi42RoundedFacts
    innerPair13RoundedFacts leaf214RoundedFacts (by rfl)

private theorem leaf214FlatSound : Sound leaf214Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf214CertificateValid
    leaf214InnerLogValid leaf214CoversExact leaf214LowerChecked

private noncomputable def leaf215Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf215Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108939/67108864) }, vSqrt := { lower := (16383/16384), upper := (2097156/2097113) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (85097323/67108864) }, upper := { exponent := 0, mantissa := (167/128) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4194269/4194226) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf215InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf215LocalValidity :
    LeafFacts leaf215Box leaf215Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf215Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2097156/2097113) }) = true
      norm_num [leaf215Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf215CertificateValid :
    WideCertificateValid leaf215Box leaf215Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi43ValidityFacts
    leaf215LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf215CoverageChecked :
    coverageCheck (innerAD leaf215Box) leaf215InnerLog = true := by
  rfl'

private theorem leaf215InnerLogValid :
    leaf215InnerLog.Valid 8 (innerAD leaf215Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf215CoverageChecked

private noncomputable def leaf215InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf215InputLogOnePlusV_eq :
    leaf215InputLogOnePlusV = outerEnclosure 24
      (leaf215Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf215RoundedFacts : LeafRoundedFacts 8
    leaf215Certificate.logOnePlusV leaf215InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf215InputLogOnePlusV_eq }

private noncomputable def leaf215Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi43InputQChi innerPair16Input
    leaf215InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf215LowerChecked :
    lowerCheck 24 leaf215Box leaf215Inputs = true := by
  rfl'

private theorem leaf215CoversExact : CoversExact 8
    leaf215Box leaf215Certificate leaf215InnerLog leaf215Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi43RoundedFacts
    innerPair16RoundedFacts leaf215RoundedFacts (by rfl)

private theorem leaf215FlatSound : Sound leaf215Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf215CertificateValid
    leaf215InnerLogValid leaf215CoversExact leaf215LowerChecked

private noncomputable def leaf216Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (1/8), chiHi := (9/64) }

private noncomputable def leaf216Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108935/67108864) }, vSqrt := { lower := (16383/16384), upper := (16777248/16776973) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (80706683/67108864) }, upper := { exponent := 0, mantissa := (1267/1024) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi40LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554221/33553946) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf216InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf216LocalValidity :
    LeafFacts leaf216Box leaf216Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf216Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777248/16776973) }) = true
      norm_num [leaf216Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf216CertificateValid :
    WideCertificateValid leaf216Box leaf216Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi40ValidityFacts
    leaf216LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf216CoverageChecked :
    coverageCheck (innerAD leaf216Box) leaf216InnerLog = true := by
  rfl'

private theorem leaf216InnerLogValid :
    leaf216InnerLog.Valid 8 (innerAD leaf216Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf216CoverageChecked

private noncomputable def leaf216InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814609/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf216InputLogOnePlusV_eq :
    leaf216InputLogOnePlusV = outerEnclosure 24
      (leaf216Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf216RoundedFacts : LeafRoundedFacts 8
    leaf216Certificate.logOnePlusV leaf216InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf216InputLogOnePlusV_eq }

private noncomputable def leaf216Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi40InputQChi innerPair12Input
    leaf216InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf216LowerChecked :
    lowerCheck 24 leaf216Box leaf216Inputs = true := by
  rfl'

private theorem leaf216CoversExact : CoversExact 8
    leaf216Box leaf216Certificate leaf216InnerLog leaf216Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi40RoundedFacts
    innerPair12RoundedFacts leaf216RoundedFacts (by rfl)

private theorem leaf216FlatSound : Sound leaf216Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf216CertificateValid
    leaf216InnerLogValid leaf216CoversExact leaf216LowerChecked

private noncomputable def leaf217Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (9/64), chiHi := (5/32) }

private noncomputable def leaf217Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108937/67108864) }, vSqrt := { lower := (16383/16384), upper := (8388624/8388473) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (82410513/67108864) }, upper := { exponent := 0, mantissa := (647/512) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi41LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777097/16776946) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf217InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf217LocalValidity :
    LeafFacts leaf217Box leaf217Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf217Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388624/8388473) }) = true
      norm_num [leaf217Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf217CertificateValid :
    WideCertificateValid leaf217Box leaf217Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi41ValidityFacts
    leaf217LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf217CoverageChecked :
    coverageCheck (innerAD leaf217Box) leaf217InnerLog = true := by
  rfl'

private theorem leaf217InnerLogValid :
    leaf217InnerLog.Valid 8 (innerAD leaf217Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf217CoverageChecked

private noncomputable def leaf217InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (726827/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf217InputLogOnePlusV_eq :
    leaf217InputLogOnePlusV = outerEnclosure 24
      (leaf217Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf217RoundedFacts : LeafRoundedFacts 8
    leaf217Certificate.logOnePlusV leaf217InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf217InputLogOnePlusV_eq }

private noncomputable def leaf217Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi41InputQChi innerPair13Input
    leaf217InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf217LowerChecked :
    lowerCheck 24 leaf217Box leaf217Inputs = true := by
  rfl'

private theorem leaf217CoversExact : CoversExact 8
    leaf217Box leaf217Certificate leaf217InnerLog leaf217Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi41RoundedFacts
    innerPair13RoundedFacts leaf217RoundedFacts (by rfl)

private theorem leaf217FlatSound : Sound leaf217Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf217CertificateValid
    leaf217InnerLogValid leaf217CoversExact leaf217LowerChecked

private noncomputable def leaf218Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (1/8), chiHi := (9/64) }

private noncomputable def leaf218Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108937/67108864) }, vSqrt := { lower := (16383/16384), upper := (4194312/4194241) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (81230937/67108864) }, upper := { exponent := 0, mantissa := (319/256) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi40LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388553/8388482) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf218InnerLog : WideLogData :=
  innerPair12Data

set_option maxRecDepth 1000000 in
private theorem leaf218LocalValidity :
    LeafFacts leaf218Box leaf218Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf218Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194312/4194241) }) = true
      norm_num [leaf218Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf218CertificateValid :
    WideCertificateValid leaf218Box leaf218Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi40ValidityFacts
    leaf218LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf218CoverageChecked :
    coverageCheck (innerAD leaf218Box) leaf218InnerLog = true := by
  rfl'

private theorem leaf218InnerLogValid :
    leaf218InnerLog.Valid 8 (innerAD leaf218Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint5PositiveFacts.valid leaf218CoverageChecked

private noncomputable def leaf218InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629223/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf218InputLogOnePlusV_eq :
    leaf218InputLogOnePlusV = outerEnclosure 24
      (leaf218Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf218RoundedFacts : LeafRoundedFacts 8
    leaf218Certificate.logOnePlusV leaf218InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf218InputLogOnePlusV_eq }

private noncomputable def leaf218Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi40InputQChi innerPair12Input
    leaf218InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf218LowerChecked :
    lowerCheck 24 leaf218Box leaf218Inputs = true := by
  rfl'

private theorem leaf218CoversExact : CoversExact 8
    leaf218Box leaf218Certificate leaf218InnerLog leaf218Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi40RoundedFacts
    innerPair12RoundedFacts leaf218RoundedFacts (by rfl)

private theorem leaf218FlatSound : Sound leaf218Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf218CertificateValid
    leaf218InnerLogValid leaf218CoversExact leaf218LowerChecked

private noncomputable def leaf219Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (9/64), chiHi := (5/32) }

private noncomputable def leaf219Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108939/67108864) }, vSqrt := { lower := (16383/16384), upper := (699052/699039) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (83000299/67108864) }, upper := { exponent := 0, mantissa := (163/128) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi41LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (1398091/1398078) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf219InnerLog : WideLogData :=
  innerPair13Data

set_option maxRecDepth 1000000 in
private theorem leaf219LocalValidity :
    LeafFacts leaf219Box leaf219Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf219Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (699052/699039) }) = true
      norm_num [leaf219Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf219CertificateValid :
    WideCertificateValid leaf219Box leaf219Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi41ValidityFacts
    leaf219LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf219CoverageChecked :
    coverageCheck (innerAD leaf219Box) leaf219InnerLog = true := by
  rfl'

private theorem leaf219InnerLogValid :
    leaf219InnerLog.Valid 8 (innerAD leaf219Box) :=
  wideLogDataValid_of_cachedCheck endpoint4PositiveFacts
    endpoint6PositiveFacts.valid leaf219CoverageChecked

private noncomputable def leaf219InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629237/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf219InputLogOnePlusV_eq :
    leaf219InputLogOnePlusV = outerEnclosure 24
      (leaf219Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf219RoundedFacts : LeafRoundedFacts 8
    leaf219Certificate.logOnePlusV leaf219InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf219InputLogOnePlusV_eq }

private noncomputable def leaf219Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi41InputQChi innerPair13Input
    leaf219InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf219LowerChecked :
    lowerCheck 24 leaf219Box leaf219Inputs = true := by
  rfl'

private theorem leaf219CoversExact : CoversExact 8
    leaf219Box leaf219Certificate leaf219InnerLog leaf219Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi41RoundedFacts
    innerPair13RoundedFacts leaf219RoundedFacts (by rfl)

private theorem leaf219FlatSound : Sound leaf219Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf219CertificateValid
    leaf219InnerLogValid leaf219CoversExact leaf219LowerChecked

private noncomputable def leaf220Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf220Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108939/67108864) }, vSqrt := { lower := (16383/16384), upper := (16777248/16776919) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (84114343/67108864) }, upper := { exponent := 0, mantissa := (1321/1024) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554167/33553838) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf220InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf220LocalValidity :
    LeafFacts leaf220Box leaf220Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf220Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777248/16776919) }) = true
      norm_num [leaf220Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf220CertificateValid :
    WideCertificateValid leaf220Box leaf220Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi42ValidityFacts
    leaf220LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf220CoverageChecked :
    coverageCheck (innerAD leaf220Box) leaf220InnerLog = true := by
  rfl'

private theorem leaf220InnerLogValid :
    leaf220InnerLog.Valid 8 (innerAD leaf220Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf220CoverageChecked

private noncomputable def leaf220InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf220InputLogOnePlusV_eq :
    leaf220InputLogOnePlusV = outerEnclosure 24
      (leaf220Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf220RoundedFacts : LeafRoundedFacts 8
    leaf220Certificate.logOnePlusV leaf220InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf220InputLogOnePlusV_eq }

private noncomputable def leaf220Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi42InputQChi innerPair16Input
    leaf220InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf220LowerChecked :
    lowerCheck 24 leaf220Box leaf220Inputs = true := by
  rfl'

private theorem leaf220CoversExact : CoversExact 8
    leaf220Box leaf220Certificate leaf220InnerLog leaf220Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi42RoundedFacts
    innerPair16RoundedFacts leaf220RoundedFacts (by rfl)

private theorem leaf220FlatSound : Sound leaf220Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf220CertificateValid
    leaf220InnerLogValid leaf220CoversExact leaf220LowerChecked

private noncomputable def leaf221Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf221Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108941/67108864) }, vSqrt := { lower := (16383/16384), upper := (4194312/4194223) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (85818173/67108864) }, upper := { exponent := 0, mantissa := (337/256) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388535/8388446) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf221InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf221LocalValidity :
    LeafFacts leaf221Box leaf221Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf221Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194312/4194223) }) = true
      norm_num [leaf221Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf221CertificateValid :
    WideCertificateValid leaf221Box leaf221Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi43ValidityFacts
    leaf221LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf221CoverageChecked :
    coverageCheck (innerAD leaf221Box) leaf221InnerLog = true := by
  rfl'

private theorem leaf221InnerLogValid :
    leaf221InnerLog.Valid 8 (innerAD leaf221Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf221CoverageChecked

private noncomputable def leaf221InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf221InputLogOnePlusV_eq :
    leaf221InputLogOnePlusV = outerEnclosure 24
      (leaf221Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf221RoundedFacts : LeafRoundedFacts 8
    leaf221Certificate.logOnePlusV leaf221InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf221InputLogOnePlusV_eq }

private noncomputable def leaf221Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi43InputQChi innerPair17Input
    leaf221InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf221LowerChecked :
    lowerCheck 24 leaf221Box leaf221Inputs = true := by
  rfl'

private theorem leaf221CoversExact : CoversExact 8
    leaf221Box leaf221Certificate leaf221InnerLog leaf221Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi43RoundedFacts
    innerPair17RoundedFacts leaf221RoundedFacts (by rfl)

private theorem leaf221FlatSound : Sound leaf221Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf221CertificateValid
    leaf221InnerLogValid leaf221CoversExact leaf221LowerChecked

private noncomputable def leaf222Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (5/32), chiHi := (11/64) }

private noncomputable def leaf222Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108941/67108864) }, vSqrt := { lower := (16383/16384), upper := (4194312/4194227) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (84769661/67108864) }, upper := { exponent := 0, mantissa := (333/256) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi42LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388539/8388454) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf222InnerLog : WideLogData :=
  innerPair16Data

set_option maxRecDepth 1000000 in
private theorem leaf222LocalValidity :
    LeafFacts leaf222Box leaf222Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf222Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194312/4194227) }) = true
      norm_num [leaf222Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf222CertificateValid :
    WideCertificateValid leaf222Box leaf222Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi42ValidityFacts
    leaf222LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf222CoverageChecked :
    coverageCheck (innerAD leaf222Box) leaf222InnerLog = true := by
  rfl'

private theorem leaf222InnerLogValid :
    leaf222InnerLog.Valid 8 (innerAD leaf222Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint6PositiveFacts.valid leaf222CoverageChecked

private noncomputable def leaf222InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629251/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf222InputLogOnePlusV_eq :
    leaf222InputLogOnePlusV = outerEnclosure 24
      (leaf222Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf222RoundedFacts : LeafRoundedFacts 8
    leaf222Certificate.logOnePlusV leaf222InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf222InputLogOnePlusV_eq }

private noncomputable def leaf222Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi42InputQChi innerPair16Input
    leaf222InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf222LowerChecked :
    lowerCheck 24 leaf222Box leaf222Inputs = true := by
  rfl'

private theorem leaf222CoversExact : CoversExact 8
    leaf222Box leaf222Certificate leaf222InnerLog leaf222Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi42RoundedFacts
    innerPair16RoundedFacts leaf222RoundedFacts (by rfl)

private theorem leaf222FlatSound : Sound leaf222Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf222CertificateValid
    leaf222InnerLogValid leaf222CoversExact leaf222LowerChecked

private noncomputable def leaf223Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (11/64), chiHi := (3/16) }

private noncomputable def leaf223Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108943/67108864) }, vSqrt := { lower := (16383/16384), upper := (1048578/1048555) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (86539023/67108864) }, upper := { exponent := 0, mantissa := (85/64) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi43LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (2097133/2097110) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf223InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf223LocalValidity :
    LeafFacts leaf223Box leaf223Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf223Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1048578/1048555) }) = true
      norm_num [leaf223Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf223CertificateValid :
    WideCertificateValid leaf223Box leaf223Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi43ValidityFacts
    leaf223LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf223CoverageChecked :
    coverageCheck (innerAD leaf223Box) leaf223InnerLog = true := by
  rfl'

private theorem leaf223InnerLogValid :
    leaf223InnerLog.Valid 8 (innerAD leaf223Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf223CoverageChecked

private noncomputable def leaf223InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf223InputLogOnePlusV_eq :
    leaf223InputLogOnePlusV = outerEnclosure 24
      (leaf223Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf223RoundedFacts : LeafRoundedFacts 8
    leaf223Certificate.logOnePlusV leaf223InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf223InputLogOnePlusV_eq }

private noncomputable def leaf223Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi43InputQChi innerPair17Input
    leaf223InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf223LowerChecked :
    lowerCheck 24 leaf223Box leaf223Inputs = true := by
  rfl'

private theorem leaf223CoversExact : CoversExact 8
    leaf223Box leaf223Certificate leaf223InnerLog leaf223Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi43RoundedFacts
    innerPair17RoundedFacts leaf223RoundedFacts (by rfl)

private theorem leaf223FlatSound : Sound leaf223Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf223CertificateValid
    leaf223InnerLogValid leaf223CoversExact leaf223LowerChecked

private noncomputable def leaf224Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf224Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108939/67108864) }, vSqrt := { lower := (16383/16384), upper := (5592416/5592297) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (85949239/67108864) }, upper := { exponent := 0, mantissa := (1349/1024) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (11184713/11184594) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf224InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf224LocalValidity :
    LeafFacts leaf224Box leaf224Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf224Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (5592416/5592297) }) = true
      norm_num [leaf224Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf224CertificateValid :
    WideCertificateValid leaf224Box leaf224Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi34ValidityFacts
    leaf224LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf224CoverageChecked :
    coverageCheck (innerAD leaf224Box) leaf224InnerLog = true := by
  rfl'

private theorem leaf224InnerLogValid :
    leaf224InnerLog.Valid 8 (innerAD leaf224Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf224CoverageChecked

private noncomputable def leaf224InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629259/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf224InputLogOnePlusV_eq :
    leaf224InputLogOnePlusV = outerEnclosure 24
      (leaf224Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf224RoundedFacts : LeafRoundedFacts 8
    leaf224Certificate.logOnePlusV leaf224InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf224InputLogOnePlusV_eq }

private noncomputable def leaf224Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi34InputQChi innerPair17Input
    leaf224InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf224LowerChecked :
    lowerCheck 24 leaf224Box leaf224Inputs = true := by
  rfl'

private theorem leaf224CoversExact : CoversExact 8
    leaf224Box leaf224Certificate leaf224InnerLog leaf224Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi34RoundedFacts
    innerPair17RoundedFacts leaf224RoundedFacts (by rfl)

private theorem leaf224FlatSound : Sound leaf224Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf224CertificateValid
    leaf224InnerLogValid leaf224CoversExact leaf224LowerChecked

private noncomputable def leaf225Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf225Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108941/67108864) }, vSqrt := { lower := (16383/16384), upper := (8388624/8388433) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (87522005/67108864) }, upper := { exponent := 0, mantissa := (687/512) } }, logOuter := sk35LogOuterCertificate, logK := sk35LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777057/16776866) } }, logDArg := sk35LogDArgCertificate }

private noncomputable def leaf225InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf225LocalValidity :
    LeafFacts leaf225Box leaf225Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf225Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388624/8388433) }) = true
      norm_num [leaf225Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf225CertificateValid :
    WideCertificateValid leaf225Box leaf225Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk35ValidityFacts chi35ValidityFacts
    leaf225LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf225CoverageChecked :
    coverageCheck (innerAD leaf225Box) leaf225InnerLog = true := by
  rfl'

private theorem leaf225InnerLogValid :
    leaf225InnerLog.Valid 8 (innerAD leaf225Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf225CoverageChecked

private noncomputable def leaf225InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf225InputLogOnePlusV_eq :
    leaf225InputLogOnePlusV = outerEnclosure 24
      (leaf225Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf225RoundedFacts : LeafRoundedFacts 8
    leaf225Certificate.logOnePlusV leaf225InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf225InputLogOnePlusV_eq }

private noncomputable def leaf225Inputs : Inputs :=
  inputsOfCaches globalInput sk35RoundedInputs
    chi35InputQChi innerPair17Input
    leaf225InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf225LowerChecked :
    lowerCheck 24 leaf225Box leaf225Inputs = true := by
  rfl'

private theorem leaf225CoversExact : CoversExact 8
    leaf225Box leaf225Certificate leaf225InnerLog leaf225Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk35RoundedFacts chi35RoundedFacts
    innerPair17RoundedFacts leaf225RoundedFacts (by rfl)

private theorem leaf225FlatSound : Sound leaf225Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf225CertificateValid
    leaf225InnerLogValid leaf225CoversExact leaf225LowerChecked

private noncomputable def leaf226Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf226Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108941/67108864) }, vSqrt := { lower := (16383/16384), upper := (8388624/8388439) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (86735621/67108864) }, upper := { exponent := 0, mantissa := (681/512) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777063/16776878) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf226InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf226LocalValidity :
    LeafFacts leaf226Box leaf226Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf226Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388624/8388439) }) = true
      norm_num [leaf226Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf226CertificateValid :
    WideCertificateValid leaf226Box leaf226Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi34ValidityFacts
    leaf226LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf226CoverageChecked :
    coverageCheck (innerAD leaf226Box) leaf226InnerLog = true := by
  rfl'

private theorem leaf226InnerLogValid :
    leaf226InnerLog.Valid 8 (innerAD leaf226Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf226CoverageChecked

private noncomputable def leaf226InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814633/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf226InputLogOnePlusV_eq :
    leaf226InputLogOnePlusV = outerEnclosure 24
      (leaf226Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf226RoundedFacts : LeafRoundedFacts 8
    leaf226Certificate.logOnePlusV leaf226InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf226InputLogOnePlusV_eq }

private noncomputable def leaf226Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi34InputQChi innerPair17Input
    leaf226InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf226LowerChecked :
    lowerCheck 24 leaf226Box leaf226Inputs = true := by
  rfl'

private theorem leaf226CoversExact : CoversExact 8
    leaf226Box leaf226Certificate leaf226InnerLog leaf226Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi34RoundedFacts
    innerPair17RoundedFacts leaf226RoundedFacts (by rfl)

private theorem leaf226FlatSound : Sound leaf226Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf226CertificateValid
    leaf226InnerLogValid leaf226CoversExact leaf226LowerChecked

private noncomputable def leaf227Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf227Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108943/67108864) }, vSqrt := { lower := (16383/16384), upper := (1398104/1398071) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (88373919/67108864) }, upper := { exponent := 0, mantissa := (347/256) } }, logOuter := sk36LogOuterCertificate, logK := sk36LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (2796175/2796142) } }, logDArg := sk36LogDArgCertificate }

private noncomputable def leaf227InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf227LocalValidity :
    LeafFacts leaf227Box leaf227Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf227Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1398104/1398071) }) = true
      norm_num [leaf227Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf227CertificateValid :
    WideCertificateValid leaf227Box leaf227Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk36ValidityFacts chi35ValidityFacts
    leaf227LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf227CoverageChecked :
    coverageCheck (innerAD leaf227Box) leaf227InnerLog = true := by
  rfl'

private theorem leaf227InnerLogValid :
    leaf227InnerLog.Valid 8 (innerAD leaf227Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf227CoverageChecked

private noncomputable def leaf227InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf227InputLogOnePlusV_eq :
    leaf227InputLogOnePlusV = outerEnclosure 24
      (leaf227Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf227RoundedFacts : LeafRoundedFacts 8
    leaf227Certificate.logOnePlusV leaf227InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf227InputLogOnePlusV_eq }

private noncomputable def leaf227Inputs : Inputs :=
  inputsOfCaches globalInput sk36RoundedInputs
    chi35InputQChi innerPair21Input
    leaf227InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf227LowerChecked :
    lowerCheck 24 leaf227Box leaf227Inputs = true := by
  rfl'

private theorem leaf227CoversExact : CoversExact 8
    leaf227Box leaf227Certificate leaf227InnerLog leaf227Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk36RoundedFacts chi35RoundedFacts
    innerPair21RoundedFacts leaf227RoundedFacts (by rfl)

private theorem leaf227FlatSound : Sound leaf227Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf227CertificateValid
    leaf227InnerLogValid leaf227CoversExact leaf227LowerChecked

private noncomputable def leaf228Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (49/32), chiLo := (7/32), chiHi := (1/4) }

private noncomputable def leaf228Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108977/67108864) }, vSqrt := { lower := (16383/16384), upper := (123362/123359) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (89094737/67108864) }, upper := { exponent := 0, mantissa := (177/128) } }, logOuter := sk43LogOuterCertificate, logK := sk43LogKCertificate, logChi := chi28LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (246721/246718) } }, logDArg := sk43LogDArgCertificate }

private noncomputable def leaf228InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf228LocalValidity :
    LeafFacts leaf228Box leaf228Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf228Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (123362/123359) }) = true
      norm_num [leaf228Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf228CertificateValid :
    WideCertificateValid leaf228Box leaf228Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk43ValidityFacts chi28ValidityFacts
    leaf228LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf228CoverageChecked :
    coverageCheck (innerAD leaf228Box) leaf228InnerLog = true := by
  rfl'

private theorem leaf228InnerLogValid :
    leaf228InnerLog.Valid 8 (innerAD leaf228Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf228CoverageChecked

private noncomputable def leaf228InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629285/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf228InputLogOnePlusV_eq :
    leaf228InputLogOnePlusV = outerEnclosure 24
      (leaf228Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf228RoundedFacts : LeafRoundedFacts 8
    leaf228Certificate.logOnePlusV leaf228InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf228InputLogOnePlusV_eq }

private noncomputable def leaf228Inputs : Inputs :=
  inputsOfCaches globalInput sk43RoundedInputs
    chi28InputQChi innerPair22Input
    leaf228InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf228LowerChecked :
    lowerCheck 24 leaf228Box leaf228Inputs = true := by
  rfl'

private theorem leaf228CoversExact : CoversExact 8
    leaf228Box leaf228Certificate leaf228InnerLog leaf228Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk43RoundedFacts chi28RoundedFacts
    innerPair22RoundedFacts leaf228RoundedFacts (by rfl)

private theorem leaf228FlatSound : Sound leaf228Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf228CertificateValid
    leaf228InnerLogValid leaf228CoversExact leaf228LowerChecked

private noncomputable def leaf229Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/32), kHi := (25/16), chiLo := (7/32), chiHi := (1/4) }

private noncomputable def leaf229Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108979/67108864) }, vSqrt := { lower := (16383/16384), upper := (1048577/1048551) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (89553459/67108864) }, upper := { exponent := 0, mantissa := (89/64) } }, logOuter := sk44LogOuterCertificate, logK := sk44LogKCertificate, logChi := chi28LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (1048564/1048551) } }, logDArg := sk44LogDArgCertificate }

private noncomputable def leaf229InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf229LocalValidity :
    LeafFacts leaf229Box leaf229Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf229Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1048577/1048551) }) = true
      norm_num [leaf229Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf229CertificateValid :
    WideCertificateValid leaf229Box leaf229Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk44ValidityFacts chi28ValidityFacts
    leaf229LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf229CoverageChecked :
    coverageCheck (innerAD leaf229Box) leaf229InnerLog = true := by
  rfl'

private theorem leaf229InnerLogValid :
    leaf229InnerLog.Valid 8 (innerAD leaf229Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf229CoverageChecked

private noncomputable def leaf229InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629289/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf229InputLogOnePlusV_eq :
    leaf229InputLogOnePlusV = outerEnclosure 24
      (leaf229Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf229RoundedFacts : LeafRoundedFacts 8
    leaf229Certificate.logOnePlusV leaf229InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf229InputLogOnePlusV_eq }

private noncomputable def leaf229Inputs : Inputs :=
  inputsOfCaches globalInput sk44RoundedInputs
    chi28InputQChi innerPair22Input
    leaf229InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf229LowerChecked :
    lowerCheck 24 leaf229Box leaf229Inputs = true := by
  rfl'

private theorem leaf229CoversExact : CoversExact 8
    leaf229Box leaf229Certificate leaf229InnerLog leaf229Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk44RoundedFacts chi28RoundedFacts
    innerPair22RoundedFacts leaf229RoundedFacts (by rfl)

private theorem leaf229FlatSound : Sound leaf229Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf229CertificateValid
    leaf229InnerLogValid leaf229CoversExact leaf229LowerChecked

private noncomputable def leaf230Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (51/32), chiLo := (7/32), chiHi := (1/4) }

private noncomputable def leaf230Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108981/67108864) }, vSqrt := { lower := (16383/16384), upper := (2097154/2097101) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (90012181/67108864) }, upper := { exponent := 0, mantissa := (179/128) } }, logOuter := sk45LogOuterCertificate, logK := sk45LogKCertificate, logChi := chi28LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4194255/4194202) } }, logDArg := sk45LogDArgCertificate }

private noncomputable def leaf230InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf230LocalValidity :
    LeafFacts leaf230Box leaf230Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf230Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2097154/2097101) }) = true
      norm_num [leaf230Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf230CertificateValid :
    WideCertificateValid leaf230Box leaf230Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk45ValidityFacts chi28ValidityFacts
    leaf230LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf230CoverageChecked :
    coverageCheck (innerAD leaf230Box) leaf230InnerLog = true := by
  rfl'

private theorem leaf230InnerLogValid :
    leaf230InnerLog.Valid 8 (innerAD leaf230Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf230CoverageChecked

private noncomputable def leaf230InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf230InputLogOnePlusV_eq :
    leaf230InputLogOnePlusV = outerEnclosure 24
      (leaf230Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf230RoundedFacts : LeafRoundedFacts 8
    leaf230Certificate.logOnePlusV leaf230InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf230InputLogOnePlusV_eq }

private noncomputable def leaf230Inputs : Inputs :=
  inputsOfCaches globalInput sk45RoundedInputs
    chi28InputQChi innerPair22Input
    leaf230InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf230LowerChecked :
    lowerCheck 24 leaf230Box leaf230Inputs = true := by
  rfl'

private theorem leaf230CoversExact : CoversExact 8
    leaf230Box leaf230Certificate leaf230InnerLog leaf230Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk45RoundedFacts chi28RoundedFacts
    innerPair22RoundedFacts leaf230RoundedFacts (by rfl)

private theorem leaf230FlatSound : Sound leaf230Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf230CertificateValid
    leaf230InnerLogValid leaf230CoversExact leaf230LowerChecked

private noncomputable def leaf231Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/32), kHi := (13/8), chiLo := (7/32), chiHi := (1/4) }

private noncomputable def leaf231Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108983/67108864) }, vSqrt := { lower := (16383/16384), upper := (1048577/1048550) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (90470903/67108864) }, upper := { exponent := 0, mantissa := (45/32) } }, logOuter := sk46LogOuterCertificate, logK := sk46LogKCertificate, logChi := chi28LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (2097127/2097100) } }, logDArg := sk46LogDArgCertificate }

private noncomputable def leaf231InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf231LocalValidity :
    LeafFacts leaf231Box leaf231Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf231Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1048577/1048550) }) = true
      norm_num [leaf231Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf231CertificateValid :
    WideCertificateValid leaf231Box leaf231Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk46ValidityFacts chi28ValidityFacts
    leaf231LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf231CoverageChecked :
    coverageCheck (innerAD leaf231Box) leaf231InnerLog = true := by
  rfl'

private theorem leaf231InnerLogValid :
    leaf231InnerLog.Valid 8 (innerAD leaf231Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf231CoverageChecked

private noncomputable def leaf231InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629297/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf231InputLogOnePlusV_eq :
    leaf231InputLogOnePlusV = outerEnclosure 24
      (leaf231Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf231RoundedFacts : LeafRoundedFacts 8
    leaf231Certificate.logOnePlusV leaf231InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf231InputLogOnePlusV_eq }

private noncomputable def leaf231Inputs : Inputs :=
  inputsOfCaches globalInput sk46RoundedInputs
    chi28InputQChi innerPair22Input
    leaf231InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf231LowerChecked :
    lowerCheck 24 leaf231Box leaf231Inputs = true := by
  rfl'

private theorem leaf231CoversExact : CoversExact 8
    leaf231Box leaf231Certificate leaf231InnerLog leaf231Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk46RoundedFacts chi28RoundedFacts
    innerPair22RoundedFacts leaf231RoundedFacts (by rfl)

private theorem leaf231FlatSound : Sound leaf231Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf231CertificateValid
    leaf231InnerLogValid leaf231CoversExact leaf231LowerChecked

private noncomputable def leaf232Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf232Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108943/67108864) }, vSqrt := { lower := (16383/16384), upper := (16777248/16776865) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (87522003/67108864) }, upper := { exponent := 0, mantissa := (1375/1024) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554113/33553730) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf232InnerLog : WideLogData :=
  innerPair17Data

set_option maxRecDepth 1000000 in
private theorem leaf232LocalValidity :
    LeafFacts leaf232Box leaf232Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf232Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777248/16776865) }) = true
      norm_num [leaf232Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf232CertificateValid :
    WideCertificateValid leaf232Box leaf232Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi34ValidityFacts
    leaf232LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf232CoverageChecked :
    coverageCheck (innerAD leaf232Box) leaf232InnerLog = true := by
  rfl'

private theorem leaf232InnerLogValid :
    leaf232InnerLog.Valid 8 (innerAD leaf232Box) :=
  wideLogDataValid_of_cachedCheck endpoint5PositiveFacts
    endpoint7PositiveFacts.valid leaf232CoverageChecked

private noncomputable def leaf232InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf232InputLogOnePlusV_eq :
    leaf232InputLogOnePlusV = outerEnclosure 24
      (leaf232Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf232RoundedFacts : LeafRoundedFacts 8
    leaf232Certificate.logOnePlusV leaf232InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf232InputLogOnePlusV_eq }

private noncomputable def leaf232Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi34InputQChi innerPair17Input
    leaf232InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf232LowerChecked :
    lowerCheck 24 leaf232Box leaf232Inputs = true := by
  rfl'

private theorem leaf232CoversExact : CoversExact 8
    leaf232Box leaf232Certificate leaf232InnerLog leaf232Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi34RoundedFacts
    innerPair17RoundedFacts leaf232RoundedFacts (by rfl)

private theorem leaf232FlatSound : Sound leaf232Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf232CertificateValid
    leaf232InnerLogValid leaf232CoversExact leaf232LowerChecked

private noncomputable def leaf233Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf233Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108945/67108864) }, vSqrt := { lower := (16383/16384), upper := (8388624/8388419) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (89225833/67108864) }, upper := { exponent := 0, mantissa := (701/512) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (16777043/16776838) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf233InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf233LocalValidity :
    LeafFacts leaf233Box leaf233Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf233Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (8388624/8388419) }) = true
      norm_num [leaf233Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf233CertificateValid :
    WideCertificateValid leaf233Box leaf233Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi35ValidityFacts
    leaf233LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf233CoverageChecked :
    coverageCheck (innerAD leaf233Box) leaf233InnerLog = true := by
  rfl'

private theorem leaf233InnerLogValid :
    leaf233InnerLog.Valid 8 (innerAD leaf233Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf233CoverageChecked

private noncomputable def leaf233InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (5814643/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf233InputLogOnePlusV_eq :
    leaf233InputLogOnePlusV = outerEnclosure 24
      (leaf233Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf233RoundedFacts : LeafRoundedFacts 8
    leaf233Certificate.logOnePlusV leaf233InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf233InputLogOnePlusV_eq }

private noncomputable def leaf233Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi35InputQChi innerPair21Input
    leaf233InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf233LowerChecked :
    lowerCheck 24 leaf233Box leaf233Inputs = true := by
  rfl'

private theorem leaf233CoversExact : CoversExact 8
    leaf233Box leaf233Certificate leaf233InnerLog leaf233Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi35RoundedFacts
    innerPair21RoundedFacts leaf233RoundedFacts (by rfl)

private theorem leaf233FlatSound : Sound leaf233Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf233CertificateValid
    leaf233InnerLogValid leaf233CoversExact leaf233LowerChecked

private noncomputable def leaf234Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (3/16), chiHi := (13/64) }

private noncomputable def leaf234Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108945/67108864) }, vSqrt := { lower := (16383/16384), upper := (1398104/1398071) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (88308385/67108864) }, upper := { exponent := 0, mantissa := (347/256) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi34LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (2796175/2796142) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf234InnerLog : WideLogData :=
  innerPair21Data

set_option maxRecDepth 1000000 in
private theorem leaf234LocalValidity :
    LeafFacts leaf234Box leaf234Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf234Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1398104/1398071) }) = true
      norm_num [leaf234Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf234CertificateValid :
    WideCertificateValid leaf234Box leaf234Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi34ValidityFacts
    leaf234LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf234CoverageChecked :
    coverageCheck (innerAD leaf234Box) leaf234InnerLog = true := by
  rfl'

private theorem leaf234InnerLogValid :
    leaf234InnerLog.Valid 8 (innerAD leaf234Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint7PositiveFacts.valid leaf234CoverageChecked

private noncomputable def leaf234InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629279/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf234InputLogOnePlusV_eq :
    leaf234InputLogOnePlusV = outerEnclosure 24
      (leaf234Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf234RoundedFacts : LeafRoundedFacts 8
    leaf234Certificate.logOnePlusV leaf234InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf234InputLogOnePlusV_eq }

private noncomputable def leaf234Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi34InputQChi innerPair21Input
    leaf234InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf234LowerChecked :
    lowerCheck 24 leaf234Box leaf234Inputs = true := by
  rfl'

private theorem leaf234CoversExact : CoversExact 8
    leaf234Box leaf234Certificate leaf234InnerLog leaf234Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi34RoundedFacts
    innerPair21RoundedFacts leaf234RoundedFacts (by rfl)

private theorem leaf234FlatSound : Sound leaf234Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf234CertificateValid
    leaf234InnerLogValid leaf234CoversExact leaf234LowerChecked

private noncomputable def leaf235Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (13/64), chiHi := (7/32) }

private noncomputable def leaf235Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108947/67108864) }, vSqrt := { lower := (16383/16384), upper := (2097156/2097103) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (90077747/67108864) }, upper := { exponent := 0, mantissa := (177/128) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi35LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (4194259/4194206) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf235InnerLog : WideLogData :=
  innerPair33Data

set_option maxRecDepth 1000000 in
private theorem leaf235LocalValidity :
    LeafFacts leaf235Box leaf235Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf235Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (2097156/2097103) }) = true
      norm_num [leaf235Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf235CertificateValid :
    WideCertificateValid leaf235Box leaf235Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi35ValidityFacts
    leaf235LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf235CoverageChecked :
    coverageCheck (innerAD leaf235Box) leaf235InnerLog = true := by
  rfl'

private theorem leaf235InnerLogValid :
    leaf235InnerLog.Valid 8 (innerAD leaf235Box) :=
  wideLogDataValid_of_cachedCheck endpoint9PositiveFacts
    endpoint34PositiveFacts.valid leaf235CoverageChecked

private noncomputable def leaf235InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629293/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf235InputLogOnePlusV_eq :
    leaf235InputLogOnePlusV = outerEnclosure 24
      (leaf235Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf235RoundedFacts : LeafRoundedFacts 8
    leaf235Certificate.logOnePlusV leaf235InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf235InputLogOnePlusV_eq }

private noncomputable def leaf235Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi35InputQChi innerPair33Input
    leaf235InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf235LowerChecked :
    lowerCheck 24 leaf235Box leaf235Inputs = true := by
  rfl'

private theorem leaf235CoversExact : CoversExact 8
    leaf235Box leaf235Certificate leaf235InnerLog leaf235Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi35RoundedFacts
    innerPair33RoundedFacts leaf235RoundedFacts (by rfl)

private theorem leaf235FlatSound : Sound leaf235Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf235CertificateValid
    leaf235InnerLogValid leaf235CoversExact leaf235LowerChecked

private noncomputable def leaf236Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf236Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108947/67108864) }, vSqrt := { lower := (16383/16384), upper := (16777248/16776811) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (90929663/67108864) }, upper := { exponent := 0, mantissa := (1429/1024) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (33554059/33553622) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf236InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf236LocalValidity :
    LeafFacts leaf236Box leaf236Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf236Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (16777248/16776811) }) = true
      norm_num [leaf236Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf236CertificateValid :
    WideCertificateValid leaf236Box leaf236Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi44ValidityFacts
    leaf236LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf236CoverageChecked :
    coverageCheck (innerAD leaf236Box) leaf236InnerLog = true := by
  rfl'

private theorem leaf236InnerLogValid :
    leaf236InnerLog.Valid 8 (innerAD leaf236Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf236CoverageChecked

private noncomputable def leaf236InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629299/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf236InputLogOnePlusV_eq :
    leaf236InputLogOnePlusV = outerEnclosure 24
      (leaf236Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf236RoundedFacts : LeafRoundedFacts 8
    leaf236Certificate.logOnePlusV leaf236InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf236InputLogOnePlusV_eq }

private noncomputable def leaf236Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi44InputQChi innerPair22Input
    leaf236InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf236LowerChecked :
    lowerCheck 24 leaf236Box leaf236Inputs = true := by
  rfl'

private theorem leaf236CoversExact : CoversExact 8
    leaf236Box leaf236Certificate leaf236InnerLog leaf236Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi44RoundedFacts
    innerPair22RoundedFacts leaf236RoundedFacts (by rfl)

private theorem leaf236FlatSound : Sound leaf236Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf236CertificateValid
    leaf236InnerLogValid leaf236CoversExact leaf236LowerChecked

private noncomputable def leaf237Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf237Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108949/67108864) }, vSqrt := { lower := (16383/16384), upper := (1048578/1048549) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (92633493/67108864) }, upper := { exponent := 0, mantissa := (91/64) } }, logOuter := sk33LogOuterCertificate, logK := sk33LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (2097127/2097098) } }, logDArg := sk33LogDArgCertificate }

private noncomputable def leaf237InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf237LocalValidity :
    LeafFacts leaf237Box leaf237Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf237Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (1048578/1048549) }) = true
      norm_num [leaf237Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf237CertificateValid :
    WideCertificateValid leaf237Box leaf237Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk33ValidityFacts chi45ValidityFacts
    leaf237LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf237CoverageChecked :
    coverageCheck (innerAD leaf237Box) leaf237InnerLog = true := by
  rfl'

private theorem leaf237InnerLogValid :
    leaf237InnerLog.Valid 8 (innerAD leaf237Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf237CoverageChecked

private noncomputable def leaf237InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629313/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf237InputLogOnePlusV_eq :
    leaf237InputLogOnePlusV = outerEnclosure 24
      (leaf237Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf237RoundedFacts : LeafRoundedFacts 8
    leaf237Certificate.logOnePlusV leaf237InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf237InputLogOnePlusV_eq }

private noncomputable def leaf237Inputs : Inputs :=
  inputsOfCaches globalInput sk33RoundedInputs
    chi45InputQChi innerPair26Input
    leaf237InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf237LowerChecked :
    lowerCheck 24 leaf237Box leaf237Inputs = true := by
  rfl'

private theorem leaf237CoversExact : CoversExact 8
    leaf237Box leaf237Certificate leaf237InnerLog leaf237Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk33RoundedFacts chi45RoundedFacts
    innerPair26RoundedFacts leaf237RoundedFacts (by rfl)

private theorem leaf237FlatSound : Sound leaf237Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf237CertificateValid
    leaf237InnerLogValid leaf237CoversExact leaf237LowerChecked

private noncomputable def leaf238Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (7/32), chiHi := (15/64) }

private noncomputable def leaf238Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108949/67108864) }, vSqrt := { lower := (16383/16384), upper := (4194312/4194199) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (91847109/67108864) }, upper := { exponent := 0, mantissa := (361/256) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi44LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (8388511/8388398) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf238InnerLog : WideLogData :=
  innerPair22Data

set_option maxRecDepth 1000000 in
private theorem leaf238LocalValidity :
    LeafFacts leaf238Box leaf238Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf238Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (4194312/4194199) }) = true
      norm_num [leaf238Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf238CertificateValid :
    WideCertificateValid leaf238Box leaf238Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi44ValidityFacts
    leaf238LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf238CoverageChecked :
    coverageCheck (innerAD leaf238Box) leaf238InnerLog = true := by
  rfl'

private theorem leaf238InnerLogValid :
    leaf238InnerLog.Valid 8 (innerAD leaf238Box) :=
  wideLogDataValid_of_cachedCheck endpoint6PositiveFacts
    endpoint10PositiveFacts.valid leaf238CoverageChecked

private noncomputable def leaf238InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629307/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf238InputLogOnePlusV_eq :
    leaf238InputLogOnePlusV = outerEnclosure 24
      (leaf238Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf238RoundedFacts : LeafRoundedFacts 8
    leaf238Certificate.logOnePlusV leaf238InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf238InputLogOnePlusV_eq }

private noncomputable def leaf238Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi44InputQChi innerPair22Input
    leaf238InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf238LowerChecked :
    lowerCheck 24 leaf238Box leaf238Inputs = true := by
  rfl'

private theorem leaf238CoversExact : CoversExact 8
    leaf238Box leaf238Certificate leaf238InnerLog leaf238Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi44RoundedFacts
    innerPair22RoundedFacts leaf238RoundedFacts (by rfl)

private theorem leaf238FlatSound : Sound leaf238Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf238CertificateValid
    leaf238InnerLogValid leaf238CoversExact leaf238LowerChecked

private noncomputable def leaf239Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (15/64), chiHi := (1/4) }

private noncomputable def leaf239Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65535/65536), upper := (67108951/67108864) }, vSqrt := { lower := (16383/16384), upper := (174763/174758) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (93616471/67108864) }, upper := { exponent := 0, mantissa := (23/16) } }, logOuter := sk34LogOuterCertificate, logK := sk34LogKCertificate, logChi := chi45LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (32767/16384) }, upper := { exponent := 1, mantissa := (349521/349516) } }, logDArg := sk34LogDArgCertificate }

private noncomputable def leaf239InnerLog : WideLogData :=
  innerPair26Data

set_option maxRecDepth 1000000 in
private theorem leaf239LocalValidity :
    LeafFacts leaf239Box leaf239Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf239Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (16383/16384), upper := (174763/174758) }) = true
      norm_num [leaf239Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf239CertificateValid :
    WideCertificateValid leaf239Box leaf239Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk34ValidityFacts chi45ValidityFacts
    leaf239LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf239CoverageChecked :
    coverageCheck (innerAD leaf239Box) leaf239InnerLog = true := by
  rfl'

private theorem leaf239InnerLogValid :
    leaf239InnerLog.Valid 8 (innerAD leaf239Box) :=
  wideLogDataValid_of_cachedCheck endpoint7PositiveFacts
    endpoint10PositiveFacts.valid leaf239CoverageChecked

private noncomputable def leaf239InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628567/16777216), upper := (11629321/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf239InputLogOnePlusV_eq :
    leaf239InputLogOnePlusV = outerEnclosure 24
      (leaf239Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf239RoundedFacts : LeafRoundedFacts 8
    leaf239Certificate.logOnePlusV leaf239InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf239InputLogOnePlusV_eq }

private noncomputable def leaf239Inputs : Inputs :=
  inputsOfCaches globalInput sk34RoundedInputs
    chi45InputQChi innerPair26Input
    leaf239InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf239LowerChecked :
    lowerCheck 24 leaf239Box leaf239Inputs = true := by
  rfl'

private theorem leaf239CoversExact : CoversExact 8
    leaf239Box leaf239Certificate leaf239InnerLog leaf239Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk34RoundedFacts chi45RoundedFacts
    innerPair26RoundedFacts leaf239RoundedFacts (by rfl)

private theorem leaf239FlatSound : Sound leaf239Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf239CertificateValid
    leaf239InnerLogValid leaf239CoversExact leaf239LowerChecked

private noncomputable def component5Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component5Node0_sound : Sound component5Node0Box :=
  sound_of_literal_split component5Node0Box leaf210Box leaf211Box
    .chi (9/64) (by rfl) (by rfl)
    leaf210FlatSound leaf211FlatSound

private noncomputable def component5Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component5Node1_sound : Sound component5Node1Box :=
  sound_of_literal_split component5Node1Box leaf209Box component5Node0Box
    .k (25/16) (by rfl) (by rfl)
    leaf209FlatSound component5Node0_sound

private noncomputable def component5Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component5Node2_sound : Sound component5Node2Box :=
  sound_of_literal_split component5Node2Box leaf212Box leaf213Box
    .chi (11/64) (by rfl) (by rfl)
    leaf212FlatSound leaf213FlatSound

private noncomputable def component5Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component5Node3_sound : Sound component5Node3Box :=
  sound_of_literal_split component5Node3Box leaf214Box leaf215Box
    .chi (11/64) (by rfl) (by rfl)
    leaf214FlatSound leaf215FlatSound

private noncomputable def component5Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component5Node4_sound : Sound component5Node4Box :=
  sound_of_literal_split component5Node4Box component5Node2Box component5Node3Box
    .k (25/16) (by rfl) (by rfl)
    component5Node2_sound component5Node3_sound

private noncomputable def component5Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component5Node5_sound : Sound component5Node5Box :=
  sound_of_literal_split component5Node5Box component5Node1Box component5Node4Box
    .chi (5/32) (by rfl) (by rfl)
    component5Node1_sound component5Node4_sound

private noncomputable def component5Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component5Node6_sound : Sound component5Node6Box :=
  sound_of_literal_split component5Node6Box leaf216Box leaf217Box
    .chi (9/64) (by rfl) (by rfl)
    leaf216FlatSound leaf217FlatSound

private noncomputable def component5Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component5Node7_sound : Sound component5Node7Box :=
  sound_of_literal_split component5Node7Box leaf218Box leaf219Box
    .chi (9/64) (by rfl) (by rfl)
    leaf218FlatSound leaf219FlatSound

private noncomputable def component5Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (1/8), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component5Node8_sound : Sound component5Node8Box :=
  sound_of_literal_split component5Node8Box component5Node6Box component5Node7Box
    .k (27/16) (by rfl) (by rfl)
    component5Node6_sound component5Node7_sound

private noncomputable def component5Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component5Node9_sound : Sound component5Node9Box :=
  sound_of_literal_split component5Node9Box leaf220Box leaf221Box
    .chi (11/64) (by rfl) (by rfl)
    leaf220FlatSound leaf221FlatSound

private noncomputable def component5Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component5Node10_sound : Sound component5Node10Box :=
  sound_of_literal_split component5Node10Box leaf222Box leaf223Box
    .chi (11/64) (by rfl) (by rfl)
    leaf222FlatSound leaf223FlatSound

private noncomputable def component5Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (5/32), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component5Node11_sound : Sound component5Node11Box :=
  sound_of_literal_split component5Node11Box component5Node9Box component5Node10Box
    .k (27/16) (by rfl) (by rfl)
    component5Node9_sound component5Node10_sound

private noncomputable def component5Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component5Node12_sound : Sound component5Node12Box :=
  sound_of_literal_split component5Node12Box component5Node8Box component5Node11Box
    .chi (5/32) (by rfl) (by rfl)
    component5Node8_sound component5Node11_sound

private noncomputable def component5Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (1/8), chiHi := (3/16) }

set_option maxRecDepth 1000000 in
private theorem component5Node13_sound : Sound component5Node13Box :=
  sound_of_literal_split component5Node13Box component5Node5Box component5Node12Box
    .k (13/8) (by rfl) (by rfl)
    component5Node5_sound component5Node12_sound

private noncomputable def component5Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component5Node14_sound : Sound component5Node14Box :=
  sound_of_literal_split component5Node14Box leaf224Box leaf225Box
    .chi (13/64) (by rfl) (by rfl)
    leaf224FlatSound leaf225FlatSound

private noncomputable def component5Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component5Node15_sound : Sound component5Node15Box :=
  sound_of_literal_split component5Node15Box leaf226Box leaf227Box
    .chi (13/64) (by rfl) (by rfl)
    leaf226FlatSound leaf227FlatSound

private noncomputable def component5Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component5Node16_sound : Sound component5Node16Box :=
  sound_of_literal_split component5Node16Box component5Node14Box component5Node15Box
    .k (25/16) (by rfl) (by rfl)
    component5Node14_sound component5Node15_sound

private noncomputable def component5Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (25/16), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component5Node17_sound : Sound component5Node17Box :=
  sound_of_literal_split component5Node17Box leaf228Box leaf229Box
    .k (49/32) (by rfl) (by rfl)
    leaf228FlatSound leaf229FlatSound

private noncomputable def component5Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/16), kHi := (13/8), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component5Node18_sound : Sound component5Node18Box :=
  sound_of_literal_split component5Node18Box leaf230Box leaf231Box
    .k (51/32) (by rfl) (by rfl)
    leaf230FlatSound leaf231FlatSound

private noncomputable def component5Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component5Node19_sound : Sound component5Node19Box :=
  sound_of_literal_split component5Node19Box component5Node17Box component5Node18Box
    .k (25/16) (by rfl) (by rfl)
    component5Node17_sound component5Node18_sound

private noncomputable def component5Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (13/8), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component5Node20_sound : Sound component5Node20Box :=
  sound_of_literal_split component5Node20Box component5Node16Box component5Node19Box
    .chi (7/32) (by rfl) (by rfl)
    component5Node16_sound component5Node19_sound

private noncomputable def component5Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component5Node21_sound : Sound component5Node21Box :=
  sound_of_literal_split component5Node21Box leaf232Box leaf233Box
    .chi (13/64) (by rfl) (by rfl)
    leaf232FlatSound leaf233FlatSound

private noncomputable def component5Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component5Node22_sound : Sound component5Node22Box :=
  sound_of_literal_split component5Node22Box leaf234Box leaf235Box
    .chi (13/64) (by rfl) (by rfl)
    leaf234FlatSound leaf235FlatSound

private noncomputable def component5Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component5Node23_sound : Sound component5Node23Box :=
  sound_of_literal_split component5Node23Box component5Node21Box component5Node22Box
    .k (27/16) (by rfl) (by rfl)
    component5Node21_sound component5Node22_sound

private noncomputable def component5Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (27/16), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component5Node24_sound : Sound component5Node24Box :=
  sound_of_literal_split component5Node24Box leaf236Box leaf237Box
    .chi (15/64) (by rfl) (by rfl)
    leaf236FlatSound leaf237FlatSound

private noncomputable def component5Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/16), kHi := (7/4), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component5Node25_sound : Sound component5Node25Box :=
  sound_of_literal_split component5Node25Box leaf238Box leaf239Box
    .chi (15/64) (by rfl) (by rfl)
    leaf238FlatSound leaf239FlatSound

private noncomputable def component5Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component5Node26_sound : Sound component5Node26Box :=
  sound_of_literal_split component5Node26Box component5Node24Box component5Node25Box
    .k (27/16) (by rfl) (by rfl)
    component5Node24_sound component5Node25_sound

private noncomputable def component5Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/8), kHi := (7/4), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component5Node27_sound : Sound component5Node27Box :=
  sound_of_literal_split component5Node27Box component5Node23Box component5Node26Box
    .chi (7/32) (by rfl) (by rfl)
    component5Node23_sound component5Node26_sound

private noncomputable def component5Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (3/16), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component5Node28_sound : Sound component5Node28Box :=
  sound_of_literal_split component5Node28Box component5Node20Box component5Node27Box
    .k (13/8) (by rfl) (by rfl)
    component5Node20_sound component5Node27_sound

noncomputable def component5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3/2), kHi := (7/4), chiLo := (1/8), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
theorem component5_sound : Sound component5Box :=
  sound_of_literal_split component5Box component5Node13Box component5Node28Box
    .chi (3/16) (by rfl) (by rfl)
    component5Node13_sound component5Node28_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
