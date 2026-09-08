import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch3

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

private noncomputable def leaf3157Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3157Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432387072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1895741903/1073741824) }, upper := { exponent := 0, mantissa := (29209/16384) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869308927/274864774144) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf3157InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3157LocalValidity :
    LeafFacts leaf3157Box leaf3157Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3157Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432387072) }) = true
      norm_num [leaf3157Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3157CertificateValid :
    WideCertificateValid leaf3157Box leaf3157Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi201ValidityFacts
    leaf3157LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3157CoverageChecked :
    coverageCheck (innerAD leaf3157Box) leaf3157InnerLog = true := by
  rfl'

private theorem leaf3157InnerLogValid :
    leaf3157InnerLog.Valid 8 (innerAD leaf3157Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3157CoverageChecked

private noncomputable def leaf3157InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3157InputLogOnePlusV_eq :
    leaf3157InputLogOnePlusV = outerEnclosure 24
      (leaf3157Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3157RoundedFacts : LeafRoundedFacts 8
    leaf3157Certificate.logOnePlusV leaf3157InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3157InputLogOnePlusV_eq }

private noncomputable def leaf3157Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi201InputQChi innerPair71Input
    leaf3157InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3157LowerChecked :
    lowerCheck 24 leaf3157Box leaf3157Inputs = true := by
  rfl'

private theorem leaf3157CoversExact : CoversExact 8
    leaf3157Box leaf3157Certificate leaf3157InnerLog leaf3157Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi201RoundedFacts
    innerPair71RoundedFacts leaf3157RoundedFacts (by rfl)

private theorem leaf3157FlatSound : Sound leaf3157Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3157CertificateValid
    leaf3157InnerLogValid leaf3157CoversExact leaf3157LowerChecked

private noncomputable def leaf3158Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3158Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432357888) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1899411693/1073741824) }, upper := { exponent := 0, mantissa := (14633/8192) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869279743/274864715776) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf3158InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3158LocalValidity :
    LeafFacts leaf3158Box leaf3158Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3158Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432357888) }) = true
      norm_num [leaf3158Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3158CertificateValid :
    WideCertificateValid leaf3158Box leaf3158Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi201ValidityFacts
    leaf3158LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3158CoverageChecked :
    coverageCheck (innerAD leaf3158Box) leaf3158InnerLog = true := by
  rfl'

private theorem leaf3158InnerLogValid :
    leaf3158InnerLog.Valid 8 (innerAD leaf3158Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3158CoverageChecked

private noncomputable def leaf3158InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3158InputLogOnePlusV_eq :
    leaf3158InputLogOnePlusV = outerEnclosure 24
      (leaf3158Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3158RoundedFacts : LeafRoundedFacts 8
    leaf3158Certificate.logOnePlusV leaf3158InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3158InputLogOnePlusV_eq }

private noncomputable def leaf3158Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi201InputQChi innerPair71Input
    leaf3158InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3158LowerChecked :
    lowerCheck 24 leaf3158Box leaf3158Inputs = true := by
  rfl'

private theorem leaf3158CoversExact : CoversExact 8
    leaf3158Box leaf3158Certificate leaf3158InnerLog leaf3158Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi201RoundedFacts
    innerPair71RoundedFacts leaf3158RoundedFacts (by rfl)

private theorem leaf3158FlatSound : Sound leaf3158Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3158CertificateValid
    leaf3158InnerLogValid leaf3158CoversExact leaf3158LowerChecked

private noncomputable def leaf3159Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3159Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432271872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1910421069/1073741824) }, upper := { exponent := 0, mantissa := (14717/8192) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869193727/274864543744) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf3159InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3159LocalValidity :
    LeafFacts leaf3159Box leaf3159Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3159Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432271872) }) = true
      norm_num [leaf3159Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3159CertificateValid :
    WideCertificateValid leaf3159Box leaf3159Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi202ValidityFacts
    leaf3159LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3159CoverageChecked :
    coverageCheck (innerAD leaf3159Box) leaf3159InnerLog = true := by
  rfl'

private theorem leaf3159InnerLogValid :
    leaf3159InnerLog.Valid 8 (innerAD leaf3159Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3159CoverageChecked

private noncomputable def leaf3159InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3159InputLogOnePlusV_eq :
    leaf3159InputLogOnePlusV = outerEnclosure 24
      (leaf3159Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3159RoundedFacts : LeafRoundedFacts 8
    leaf3159Certificate.logOnePlusV leaf3159InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3159InputLogOnePlusV_eq }

private noncomputable def leaf3159Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi202InputQChi innerPair71Input
    leaf3159InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3159LowerChecked :
    lowerCheck 24 leaf3159Box leaf3159Inputs = true := by
  rfl'

private theorem leaf3159CoversExact : CoversExact 8
    leaf3159Box leaf3159Certificate leaf3159InnerLog leaf3159Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi202RoundedFacts
    innerPair71RoundedFacts leaf3159RoundedFacts (by rfl)

private theorem leaf3159FlatSound : Sound leaf3159Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3159CertificateValid
    leaf3159InnerLogValid leaf3159CoversExact leaf3159LowerChecked

private noncomputable def leaf3160Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3160Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810747392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1914156391/1073741824) }, upper := { exponent := 0, mantissa := (7373/4096) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623054677/91621494784) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf3160InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3160LocalValidity :
    LeafFacts leaf3160Box leaf3160Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3160Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810747392) }) = true
      norm_num [leaf3160Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3160CertificateValid :
    WideCertificateValid leaf3160Box leaf3160Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi202ValidityFacts
    leaf3160LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3160CoverageChecked :
    coverageCheck (innerAD leaf3160Box) leaf3160InnerLog = true := by
  rfl'

private theorem leaf3160InnerLogValid :
    leaf3160InnerLog.Valid 8 (innerAD leaf3160Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3160CoverageChecked

private noncomputable def leaf3160InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3160InputLogOnePlusV_eq :
    leaf3160InputLogOnePlusV = outerEnclosure 24
      (leaf3160Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3160RoundedFacts : LeafRoundedFacts 8
    leaf3160Certificate.logOnePlusV leaf3160InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3160InputLogOnePlusV_eq }

private noncomputable def leaf3160Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi202InputQChi innerPair71Input
    leaf3160InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3160LowerChecked :
    lowerCheck 24 leaf3160Box leaf3160Inputs = true := by
  rfl'

private theorem leaf3160CoversExact : CoversExact 8
    leaf3160Box leaf3160Certificate leaf3160InnerLog leaf3160Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi202RoundedFacts
    innerPair71RoundedFacts leaf3160RoundedFacts (by rfl)

private theorem leaf3160FlatSound : Sound leaf3160Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3160CertificateValid
    leaf3160InnerLogValid leaf3160CoversExact leaf3160LowerChecked

private noncomputable def leaf3161Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3161Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432328704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1903081483/1073741824) }, upper := { exponent := 0, mantissa := (29323/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869250559/274864657408) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf3161InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3161LocalValidity :
    LeafFacts leaf3161Box leaf3161Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3161Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432328704) }) = true
      norm_num [leaf3161Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3161CertificateValid :
    WideCertificateValid leaf3161Box leaf3161Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi201ValidityFacts
    leaf3161LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3161CoverageChecked :
    coverageCheck (innerAD leaf3161Box) leaf3161InnerLog = true := by
  rfl'

private theorem leaf3161InnerLogValid :
    leaf3161InnerLog.Valid 8 (innerAD leaf3161Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3161CoverageChecked

private noncomputable def leaf3161InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3161InputLogOnePlusV_eq :
    leaf3161InputLogOnePlusV = outerEnclosure 24
      (leaf3161Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3161RoundedFacts : LeafRoundedFacts 8
    leaf3161Certificate.logOnePlusV leaf3161InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3161InputLogOnePlusV_eq }

private noncomputable def leaf3161Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi201InputQChi innerPair71Input
    leaf3161InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3161LowerChecked :
    lowerCheck 24 leaf3161Box leaf3161Inputs = true := by
  rfl'

private theorem leaf3161CoversExact : CoversExact 8
    leaf3161Box leaf3161Certificate leaf3161InnerLog leaf3161Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi201RoundedFacts
    innerPair71RoundedFacts leaf3161RoundedFacts (by rfl)

private theorem leaf3161FlatSound : Sound leaf3161Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3161CertificateValid
    leaf3161InnerLogValid leaf3161CoversExact leaf3161LowerChecked

private noncomputable def leaf3162Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3162Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486459904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1906751273/1073741824) }, upper := { exponent := 0, mantissa := (7345/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973844275/54972919808) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf3162InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3162LocalValidity :
    LeafFacts leaf3162Box leaf3162Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3162Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486459904) }) = true
      norm_num [leaf3162Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3162CertificateValid :
    WideCertificateValid leaf3162Box leaf3162Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi201ValidityFacts
    leaf3162LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3162CoverageChecked :
    coverageCheck (innerAD leaf3162Box) leaf3162InnerLog = true := by
  rfl'

private theorem leaf3162InnerLogValid :
    leaf3162InnerLog.Valid 8 (innerAD leaf3162Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3162CoverageChecked

private noncomputable def leaf3162InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3162InputLogOnePlusV_eq :
    leaf3162InputLogOnePlusV = outerEnclosure 24
      (leaf3162Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3162RoundedFacts : LeafRoundedFacts 8
    leaf3162Certificate.logOnePlusV leaf3162InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3162InputLogOnePlusV_eq }

private noncomputable def leaf3162Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi201InputQChi innerPair71Input
    leaf3162InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3162LowerChecked :
    lowerCheck 24 leaf3162Box leaf3162Inputs = true := by
  rfl'

private theorem leaf3162CoversExact : CoversExact 8
    leaf3162Box leaf3162Certificate leaf3162InnerLog leaf3162Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi201RoundedFacts
    innerPair71RoundedFacts leaf3162RoundedFacts (by rfl)

private theorem leaf3162FlatSound : Sound leaf3162Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3162CertificateValid
    leaf3162InnerLogValid leaf3162CoversExact leaf3162LowerChecked

private noncomputable def leaf3163Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3163Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486442496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1917891713/1073741824) }, upper := { exponent := 0, mantissa := (14775/8192) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973826867/54972884992) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf3163InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3163LocalValidity :
    LeafFacts leaf3163Box leaf3163Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3163Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486442496) }) = true
      norm_num [leaf3163Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3163CertificateValid :
    WideCertificateValid leaf3163Box leaf3163Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi202ValidityFacts
    leaf3163LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3163CoverageChecked :
    coverageCheck (innerAD leaf3163Box) leaf3163InnerLog = true := by
  rfl'

private theorem leaf3163InnerLogValid :
    leaf3163InnerLog.Valid 8 (innerAD leaf3163Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3163CoverageChecked

private noncomputable def leaf3163InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3163InputLogOnePlusV_eq :
    leaf3163InputLogOnePlusV = outerEnclosure 24
      (leaf3163Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3163RoundedFacts : LeafRoundedFacts 8
    leaf3163Certificate.logOnePlusV leaf3163InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3163InputLogOnePlusV_eq }

private noncomputable def leaf3163Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi202InputQChi innerPair71Input
    leaf3163InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3163LowerChecked :
    lowerCheck 24 leaf3163Box leaf3163Inputs = true := by
  rfl'

private theorem leaf3163CoversExact : CoversExact 8
    leaf3163Box leaf3163Certificate leaf3163InnerLog leaf3163Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi202RoundedFacts
    innerPair71RoundedFacts leaf3163RoundedFacts (by rfl)

private theorem leaf3163FlatSound : Sound leaf3163Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3163CertificateValid
    leaf3163InnerLogValid leaf3163CoversExact leaf3163LowerChecked

private noncomputable def leaf3164Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3164Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432182784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1921627035/1073741824) }, upper := { exponent := 0, mantissa := (3701/2048) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869104639/274864365568) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf3164InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3164LocalValidity :
    LeafFacts leaf3164Box leaf3164Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3164Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432182784) }) = true
      norm_num [leaf3164Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3164CertificateValid :
    WideCertificateValid leaf3164Box leaf3164Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi202ValidityFacts
    leaf3164LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3164CoverageChecked :
    coverageCheck (innerAD leaf3164Box) leaf3164InnerLog = true := by
  rfl'

private theorem leaf3164InnerLogValid :
    leaf3164InnerLog.Valid 8 (innerAD leaf3164Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3164CoverageChecked

private noncomputable def leaf3164InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3164InputLogOnePlusV_eq :
    leaf3164InputLogOnePlusV = outerEnclosure 24
      (leaf3164Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3164RoundedFacts : LeafRoundedFacts 8
    leaf3164Certificate.logOnePlusV leaf3164InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3164InputLogOnePlusV_eq }

private noncomputable def leaf3164Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi202InputQChi innerPair71Input
    leaf3164InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3164LowerChecked :
    lowerCheck 24 leaf3164Box leaf3164Inputs = true := by
  rfl'

private theorem leaf3164CoversExact : CoversExact 8
    leaf3164Box leaf3164Certificate leaf3164InnerLog leaf3164Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi202RoundedFacts
    innerPair71RoundedFacts leaf3164RoundedFacts (by rfl)

private theorem leaf3164FlatSound : Sound leaf3164Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3164CertificateValid
    leaf3164InnerLogValid leaf3164CoversExact leaf3164LowerChecked

private noncomputable def leaf3165Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3165Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432156672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1925100235/1073741824) }, upper := { exponent := 0, mantissa := (29659/16384) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869078527/274864313344) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf3165InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3165LocalValidity :
    LeafFacts leaf3165Box leaf3165Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3165Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432156672) }) = true
      norm_num [leaf3165Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3165CertificateValid :
    WideCertificateValid leaf3165Box leaf3165Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi199ValidityFacts
    leaf3165LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3165CoverageChecked :
    coverageCheck (innerAD leaf3165Box) leaf3165InnerLog = true := by
  rfl'

private theorem leaf3165InnerLogValid :
    leaf3165InnerLog.Valid 8 (innerAD leaf3165Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3165CoverageChecked

private noncomputable def leaf3165InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3165InputLogOnePlusV_eq :
    leaf3165InputLogOnePlusV = outerEnclosure 24
      (leaf3165Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3165RoundedFacts : LeafRoundedFacts 8
    leaf3165Certificate.logOnePlusV leaf3165InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3165InputLogOnePlusV_eq }

private noncomputable def leaf3165Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi199InputQChi innerPair71Input
    leaf3165InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3165LowerChecked :
    lowerCheck 24 leaf3165Box leaf3165Inputs = true := by
  rfl'

private theorem leaf3165CoversExact : CoversExact 8
    leaf3165Box leaf3165Certificate leaf3165InnerLog leaf3165Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi199RoundedFacts
    innerPair71RoundedFacts leaf3165RoundedFacts (by rfl)

private theorem leaf3165FlatSound : Sound leaf3165Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3165CertificateValid
    leaf3165InnerLogValid leaf3165CoversExact leaf3165LowerChecked

private noncomputable def leaf3166Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3166Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432126464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1928901089/1073741824) }, upper := { exponent := 0, mantissa := (14859/8192) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869048319/274864252928) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf3166InnerLog : WideLogData :=
  innerPair226Data

set_option maxRecDepth 1000000 in
private theorem leaf3166LocalValidity :
    LeafFacts leaf3166Box leaf3166Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3166Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432126464) }) = true
      norm_num [leaf3166Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3166CertificateValid :
    WideCertificateValid leaf3166Box leaf3166Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi199ValidityFacts
    leaf3166LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3166CoverageChecked :
    coverageCheck (innerAD leaf3166Box) leaf3166InnerLog = true := by
  rfl'

private theorem leaf3166InnerLogValid :
    leaf3166InnerLog.Valid 8 (innerAD leaf3166Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint64PositiveFacts.valid leaf3166CoverageChecked

private noncomputable def leaf3166InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3166InputLogOnePlusV_eq :
    leaf3166InputLogOnePlusV = outerEnclosure 24
      (leaf3166Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3166RoundedFacts : LeafRoundedFacts 8
    leaf3166Certificate.logOnePlusV leaf3166InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3166InputLogOnePlusV_eq }

private noncomputable def leaf3166Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi199InputQChi innerPair226Input
    leaf3166InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3166LowerChecked :
    lowerCheck 24 leaf3166Box leaf3166Inputs = true := by
  rfl'

private theorem leaf3166CoversExact : CoversExact 8
    leaf3166Box leaf3166Certificate leaf3166InnerLog leaf3166Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi199RoundedFacts
    innerPair226RoundedFacts leaf3166RoundedFacts (by rfl)

private theorem leaf3166FlatSound : Sound leaf3166Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3166CertificateValid
    leaf3166InnerLogValid leaf3166CoversExact leaf3166LowerChecked

private noncomputable def leaf3167Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3167Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432041472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1939779401/1073741824) }, upper := { exponent := 0, mantissa := (7471/4096) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868963327/274864082944) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf3167InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3167LocalValidity :
    LeafFacts leaf3167Box leaf3167Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3167Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432041472) }) = true
      norm_num [leaf3167Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3167CertificateValid :
    WideCertificateValid leaf3167Box leaf3167Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi200ValidityFacts
    leaf3167LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3167CoverageChecked :
    coverageCheck (innerAD leaf3167Box) leaf3167InnerLog = true := by
  rfl'

private theorem leaf3167InnerLogValid :
    leaf3167InnerLog.Valid 8 (innerAD leaf3167Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3167CoverageChecked

private noncomputable def leaf3167InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3167InputLogOnePlusV_eq :
    leaf3167InputLogOnePlusV = outerEnclosure 24
      (leaf3167Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3167RoundedFacts : LeafRoundedFacts 8
    leaf3167Certificate.logOnePlusV leaf3167InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3167InputLogOnePlusV_eq }

private noncomputable def leaf3167Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi200InputQChi innerPair72Input
    leaf3167InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3167LowerChecked :
    lowerCheck 24 leaf3167Box leaf3167Inputs = true := by
  rfl'

private theorem leaf3167CoversExact : CoversExact 8
    leaf3167Box leaf3167Certificate leaf3167InnerLog leaf3167Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi200RoundedFacts
    innerPair72RoundedFacts leaf3167RoundedFacts (by rfl)

private theorem leaf3167FlatSound : Sound leaf3167Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3167CertificateValid
    leaf3167InnerLogValid leaf3167CoversExact leaf3167LowerChecked

private noncomputable def leaf3168Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3168Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432010752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1943645787/1073741824) }, upper := { exponent := 0, mantissa := (3743/2048) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868932607/274864021504) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf3168InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3168LocalValidity :
    LeafFacts leaf3168Box leaf3168Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3168Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432010752) }) = true
      norm_num [leaf3168Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3168CertificateValid :
    WideCertificateValid leaf3168Box leaf3168Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi200ValidityFacts
    leaf3168LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3168CoverageChecked :
    coverageCheck (innerAD leaf3168Box) leaf3168InnerLog = true := by
  rfl'

private theorem leaf3168InnerLogValid :
    leaf3168InnerLog.Valid 8 (innerAD leaf3168Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3168CoverageChecked

private noncomputable def leaf3168InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3168InputLogOnePlusV_eq :
    leaf3168InputLogOnePlusV = outerEnclosure 24
      (leaf3168Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3168RoundedFacts : LeafRoundedFacts 8
    leaf3168Certificate.logOnePlusV leaf3168InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3168InputLogOnePlusV_eq }

private noncomputable def leaf3168Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi200InputQChi innerPair72Input
    leaf3168InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3168LowerChecked :
    lowerCheck 24 leaf3168Box leaf3168Inputs = true := by
  rfl'

private theorem leaf3168CoversExact : CoversExact 8
    leaf3168Box leaf3168Certificate leaf3168InnerLog leaf3168Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi200RoundedFacts
    innerPair72RoundedFacts leaf3168RoundedFacts (by rfl)

private theorem leaf3168FlatSound : Sound leaf3168Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3168CertificateValid
    leaf3168InnerLogValid leaf3168CoversExact leaf3168LowerChecked

private noncomputable def leaf3169Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3169Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810698752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1932701943/1073741824) }, upper := { exponent := 0, mantissa := (29777/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623006037/91621397504) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf3169InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3169LocalValidity :
    LeafFacts leaf3169Box leaf3169Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3169Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810698752) }) = true
      norm_num [leaf3169Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3169CertificateValid :
    WideCertificateValid leaf3169Box leaf3169Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi199ValidityFacts
    leaf3169LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3169CoverageChecked :
    coverageCheck (innerAD leaf3169Box) leaf3169InnerLog = true := by
  rfl'

private theorem leaf3169InnerLogValid :
    leaf3169InnerLog.Valid 8 (innerAD leaf3169Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3169CoverageChecked

private noncomputable def leaf3169InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3169InputLogOnePlusV_eq :
    leaf3169InputLogOnePlusV = outerEnclosure 24
      (leaf3169Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3169RoundedFacts : LeafRoundedFacts 8
    leaf3169Certificate.logOnePlusV leaf3169InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3169InputLogOnePlusV_eq }

private noncomputable def leaf3169Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi199InputQChi innerPair221Input
    leaf3169InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3169LowerChecked :
    lowerCheck 24 leaf3169Box leaf3169Inputs = true := by
  rfl'

private theorem leaf3169CoversExact : CoversExact 8
    leaf3169Box leaf3169Certificate leaf3169InnerLog leaf3169Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi199RoundedFacts
    innerPair221RoundedFacts leaf3169RoundedFacts (by rfl)

private theorem leaf3169FlatSound : Sound leaf3169Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3169CertificateValid
    leaf3169InnerLogValid leaf3169CoversExact leaf3169LowerChecked

private noncomputable def leaf3170Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3170Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432066048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1936502797/1073741824) }, upper := { exponent := 0, mantissa := (7459/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868987903/274864132096) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf3170InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3170LocalValidity :
    LeafFacts leaf3170Box leaf3170Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3170Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432066048) }) = true
      norm_num [leaf3170Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3170CertificateValid :
    WideCertificateValid leaf3170Box leaf3170Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi199ValidityFacts
    leaf3170LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3170CoverageChecked :
    coverageCheck (innerAD leaf3170Box) leaf3170InnerLog = true := by
  rfl'

private theorem leaf3170InnerLogValid :
    leaf3170InnerLog.Valid 8 (innerAD leaf3170Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3170CoverageChecked

private noncomputable def leaf3170InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3170InputLogOnePlusV_eq :
    leaf3170InputLogOnePlusV = outerEnclosure 24
      (leaf3170Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3170RoundedFacts : LeafRoundedFacts 8
    leaf3170Certificate.logOnePlusV leaf3170InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3170InputLogOnePlusV_eq }

private noncomputable def leaf3170Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi199InputQChi innerPair221Input
    leaf3170InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3170LowerChecked :
    lowerCheck 24 leaf3170Box leaf3170Inputs = true := by
  rfl'

private theorem leaf3170CoversExact : CoversExact 8
    leaf3170Box leaf3170Certificate leaf3170InnerLog leaf3170Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi199RoundedFacts
    innerPair221RoundedFacts leaf3170RoundedFacts (by rfl)

private theorem leaf3170FlatSound : Sound leaf3170Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3170CertificateValid
    leaf3170InnerLogValid leaf3170CoversExact leaf3170LowerChecked

private noncomputable def leaf3171Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3171Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431980032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1947512173/1073741824) }, upper := { exponent := 0, mantissa := (7501/4096) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868901887/274863960064) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf3171InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3171LocalValidity :
    LeafFacts leaf3171Box leaf3171Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3171Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431980032) }) = true
      norm_num [leaf3171Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3171CertificateValid :
    WideCertificateValid leaf3171Box leaf3171Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi200ValidityFacts
    leaf3171LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3171CoverageChecked :
    coverageCheck (innerAD leaf3171Box) leaf3171InnerLog = true := by
  rfl'

private theorem leaf3171InnerLogValid :
    leaf3171InnerLog.Valid 8 (innerAD leaf3171Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3171CoverageChecked

private noncomputable def leaf3171InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814691/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3171InputLogOnePlusV_eq :
    leaf3171InputLogOnePlusV = outerEnclosure 24
      (leaf3171Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3171RoundedFacts : LeafRoundedFacts 8
    leaf3171Certificate.logOnePlusV leaf3171InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3171InputLogOnePlusV_eq }

private noncomputable def leaf3171Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi200InputQChi innerPair91Input
    leaf3171InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3171LowerChecked :
    lowerCheck 24 leaf3171Box leaf3171Inputs = true := by
  rfl'

private theorem leaf3171CoversExact : CoversExact 8
    leaf3171Box leaf3171Certificate leaf3171InnerLog leaf3171Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi200RoundedFacts
    innerPair91RoundedFacts leaf3171RoundedFacts (by rfl)

private theorem leaf3171FlatSound : Sound leaf3171Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3171CertificateValid
    leaf3171InnerLogValid leaf3171CoversExact leaf3171LowerChecked

private noncomputable def leaf3172Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3172Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431949312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1951378559/1073741824) }, upper := { exponent := 0, mantissa := (1879/1024) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868871167/274863898624) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf3172InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3172LocalValidity :
    LeafFacts leaf3172Box leaf3172Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3172Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431949312) }) = true
      norm_num [leaf3172Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3172CertificateValid :
    WideCertificateValid leaf3172Box leaf3172Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi200ValidityFacts
    leaf3172LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3172CoverageChecked :
    coverageCheck (innerAD leaf3172Box) leaf3172InnerLog = true := by
  rfl'

private theorem leaf3172InnerLogValid :
    leaf3172InnerLog.Valid 8 (innerAD leaf3172Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3172CoverageChecked

private noncomputable def leaf3172InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3172InputLogOnePlusV_eq :
    leaf3172InputLogOnePlusV = outerEnclosure 24
      (leaf3172Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3172RoundedFacts : LeafRoundedFacts 8
    leaf3172Certificate.logOnePlusV leaf3172InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3172InputLogOnePlusV_eq }

private noncomputable def leaf3172Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi200InputQChi innerPair91Input
    leaf3172InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3172LowerChecked :
    lowerCheck 24 leaf3172Box leaf3172Inputs = true := by
  rfl'

private theorem leaf3172CoversExact : CoversExact 8
    leaf3172Box leaf3172Certificate leaf3172InnerLog leaf3172Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi200RoundedFacts
    innerPair91RoundedFacts leaf3172RoundedFacts (by rfl)

private theorem leaf3172FlatSound : Sound leaf3172Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3172CertificateValid
    leaf3172InnerLogValid leaf3172CoversExact leaf3172LowerChecked

private noncomputable def leaf3173Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3173Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432270336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1910421063/1073741824) }, upper := { exponent := 0, mantissa := (29437/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869192191/274864540672) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf3173InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3173LocalValidity :
    LeafFacts leaf3173Box leaf3173Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3173Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432270336) }) = true
      norm_num [leaf3173Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3173CertificateValid :
    WideCertificateValid leaf3173Box leaf3173Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi201ValidityFacts
    leaf3173LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3173CoverageChecked :
    coverageCheck (innerAD leaf3173Box) leaf3173InnerLog = true := by
  rfl'

private theorem leaf3173InnerLogValid :
    leaf3173InnerLog.Valid 8 (innerAD leaf3173Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3173CoverageChecked

private noncomputable def leaf3173InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3173InputLogOnePlusV_eq :
    leaf3173InputLogOnePlusV = outerEnclosure 24
      (leaf3173Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3173RoundedFacts : LeafRoundedFacts 8
    leaf3173Certificate.logOnePlusV leaf3173InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3173InputLogOnePlusV_eq }

private noncomputable def leaf3173Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi201InputQChi innerPair71Input
    leaf3173InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3173LowerChecked :
    lowerCheck 24 leaf3173Box leaf3173Inputs = true := by
  rfl'

private theorem leaf3173CoversExact : CoversExact 8
    leaf3173Box leaf3173Certificate leaf3173InnerLog leaf3173Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi201RoundedFacts
    innerPair71RoundedFacts leaf3173RoundedFacts (by rfl)

private theorem leaf3173FlatSound : Sound leaf3173Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3173CertificateValid
    leaf3173InnerLogValid leaf3173CoversExact leaf3173LowerChecked

private noncomputable def leaf3174Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3174Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432241152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1914090853/1073741824) }, upper := { exponent := 0, mantissa := (14747/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869163007/274864482304) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf3174InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3174LocalValidity :
    LeafFacts leaf3174Box leaf3174Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3174Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432241152) }) = true
      norm_num [leaf3174Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3174CertificateValid :
    WideCertificateValid leaf3174Box leaf3174Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi201ValidityFacts
    leaf3174LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3174CoverageChecked :
    coverageCheck (innerAD leaf3174Box) leaf3174InnerLog = true := by
  rfl'

private theorem leaf3174InnerLogValid :
    leaf3174InnerLog.Valid 8 (innerAD leaf3174Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3174CoverageChecked

private noncomputable def leaf3174InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3174InputLogOnePlusV_eq :
    leaf3174InputLogOnePlusV = outerEnclosure 24
      (leaf3174Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3174RoundedFacts : LeafRoundedFacts 8
    leaf3174Certificate.logOnePlusV leaf3174InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3174InputLogOnePlusV_eq }

private noncomputable def leaf3174Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi201InputQChi innerPair71Input
    leaf3174InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3174LowerChecked :
    lowerCheck 24 leaf3174Box leaf3174Inputs = true := by
  rfl'

private theorem leaf3174CoversExact : CoversExact 8
    leaf3174Box leaf3174Certificate leaf3174InnerLog leaf3174Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi201RoundedFacts
    innerPair71RoundedFacts leaf3174RoundedFacts (by rfl)

private theorem leaf3174FlatSound : Sound leaf3174Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3174CertificateValid
    leaf3174InnerLogValid leaf3174CoversExact leaf3174LowerChecked

private noncomputable def leaf3175Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3175Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090079744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1925362357/1073741824) }, upper := { exponent := 0, mantissa := (14833/8192) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180336109/10180159488) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf3175InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3175LocalValidity :
    LeafFacts leaf3175Box leaf3175Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3175Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090079744) }) = true
      norm_num [leaf3175Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3175CertificateValid :
    WideCertificateValid leaf3175Box leaf3175Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi202ValidityFacts
    leaf3175LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3175CoverageChecked :
    coverageCheck (innerAD leaf3175Box) leaf3175InnerLog = true := by
  rfl'

private theorem leaf3175InnerLogValid :
    leaf3175InnerLog.Valid 8 (innerAD leaf3175Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3175CoverageChecked

private noncomputable def leaf3175InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3175InputLogOnePlusV_eq :
    leaf3175InputLogOnePlusV = outerEnclosure 24
      (leaf3175Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3175RoundedFacts : LeafRoundedFacts 8
    leaf3175Certificate.logOnePlusV leaf3175InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3175InputLogOnePlusV_eq }

private noncomputable def leaf3175Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi202InputQChi innerPair71Input
    leaf3175InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3175LowerChecked :
    lowerCheck 24 leaf3175Box leaf3175Inputs = true := by
  rfl'

private theorem leaf3175CoversExact : CoversExact 8
    leaf3175Box leaf3175Certificate leaf3175InnerLog leaf3175Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi202RoundedFacts
    innerPair71RoundedFacts leaf3175RoundedFacts (by rfl)

private theorem leaf3175FlatSound : Sound leaf3175Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3175CertificateValid
    leaf3175InnerLogValid leaf3175CoversExact leaf3175LowerChecked

private noncomputable def leaf3176Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3176Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432123392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1929097679/1073741824) }, upper := { exponent := 0, mantissa := (7431/4096) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869045247/274864246784) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf3176InnerLog : WideLogData :=
  innerPair226Data

set_option maxRecDepth 1000000 in
private theorem leaf3176LocalValidity :
    LeafFacts leaf3176Box leaf3176Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3176Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432123392) }) = true
      norm_num [leaf3176Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3176CertificateValid :
    WideCertificateValid leaf3176Box leaf3176Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi202ValidityFacts
    leaf3176LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3176CoverageChecked :
    coverageCheck (innerAD leaf3176Box) leaf3176InnerLog = true := by
  rfl'

private theorem leaf3176InnerLogValid :
    leaf3176InnerLog.Valid 8 (innerAD leaf3176Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint64PositiveFacts.valid leaf3176CoverageChecked

private noncomputable def leaf3176InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814687/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3176InputLogOnePlusV_eq :
    leaf3176InputLogOnePlusV = outerEnclosure 24
      (leaf3176Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3176RoundedFacts : LeafRoundedFacts 8
    leaf3176Certificate.logOnePlusV leaf3176InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3176InputLogOnePlusV_eq }

private noncomputable def leaf3176Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi202InputQChi innerPair226Input
    leaf3176InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3176LowerChecked :
    lowerCheck 24 leaf3176Box leaf3176Inputs = true := by
  rfl'

private theorem leaf3176CoversExact : CoversExact 8
    leaf3176Box leaf3176Certificate leaf3176InnerLog leaf3176Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi202RoundedFacts
    innerPair226RoundedFacts leaf3176RoundedFacts (by rfl)

private theorem leaf3176FlatSound : Sound leaf3176Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3176CertificateValid
    leaf3176InnerLogValid leaf3176CoversExact leaf3176LowerChecked

private noncomputable def leaf3177Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3177Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432211968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1917760643/1073741824) }, upper := { exponent := 0, mantissa := (29551/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869133823/274864423936) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf3177InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3177LocalValidity :
    LeafFacts leaf3177Box leaf3177Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3177Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432211968) }) = true
      norm_num [leaf3177Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3177CertificateValid :
    WideCertificateValid leaf3177Box leaf3177Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi201ValidityFacts
    leaf3177LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3177CoverageChecked :
    coverageCheck (innerAD leaf3177Box) leaf3177InnerLog = true := by
  rfl'

private theorem leaf3177InnerLogValid :
    leaf3177InnerLog.Valid 8 (innerAD leaf3177Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3177CoverageChecked

private noncomputable def leaf3177InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3177InputLogOnePlusV_eq :
    leaf3177InputLogOnePlusV = outerEnclosure 24
      (leaf3177Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3177RoundedFacts : LeafRoundedFacts 8
    leaf3177Certificate.logOnePlusV leaf3177InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3177InputLogOnePlusV_eq }

private noncomputable def leaf3177Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi201InputQChi innerPair71Input
    leaf3177InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3177LowerChecked :
    lowerCheck 24 leaf3177Box leaf3177Inputs = true := by
  rfl'

private theorem leaf3177CoversExact : CoversExact 8
    leaf3177Box leaf3177Certificate leaf3177InnerLog leaf3177Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi201RoundedFacts
    innerPair71RoundedFacts leaf3177RoundedFacts (by rfl)

private theorem leaf3177FlatSound : Sound leaf3177Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3177CertificateValid
    leaf3177InnerLogValid leaf3177CoversExact leaf3177LowerChecked

private noncomputable def leaf3178Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3178Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432182784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1921430433/1073741824) }, upper := { exponent := 0, mantissa := (3701/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869104639/274864365568) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf3178InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3178LocalValidity :
    LeafFacts leaf3178Box leaf3178Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3178Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432182784) }) = true
      norm_num [leaf3178Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3178CertificateValid :
    WideCertificateValid leaf3178Box leaf3178Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi201ValidityFacts
    leaf3178LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3178CoverageChecked :
    coverageCheck (innerAD leaf3178Box) leaf3178InnerLog = true := by
  rfl'

private theorem leaf3178InnerLogValid :
    leaf3178InnerLog.Valid 8 (innerAD leaf3178Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3178CoverageChecked

private noncomputable def leaf3178InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3178InputLogOnePlusV_eq :
    leaf3178InputLogOnePlusV = outerEnclosure 24
      (leaf3178Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3178RoundedFacts : LeafRoundedFacts 8
    leaf3178Certificate.logOnePlusV leaf3178InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3178InputLogOnePlusV_eq }

private noncomputable def leaf3178Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi201InputQChi innerPair71Input
    leaf3178InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3178LowerChecked :
    lowerCheck 24 leaf3178Box leaf3178Inputs = true := by
  rfl'

private theorem leaf3178CoversExact : CoversExact 8
    leaf3178Box leaf3178Certificate leaf3178InnerLog leaf3178Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi201RoundedFacts
    innerPair71RoundedFacts leaf3178RoundedFacts (by rfl)

private theorem leaf3178FlatSound : Sound leaf3178Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3178CertificateValid
    leaf3178InnerLogValid leaf3178CoversExact leaf3178LowerChecked

private noncomputable def leaf3179Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3179Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432093696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1932833001/1073741824) }, upper := { exponent := 0, mantissa := (14891/8192) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869015551/274864187392) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf3179InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3179LocalValidity :
    LeafFacts leaf3179Box leaf3179Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3179Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432093696) }) = true
      norm_num [leaf3179Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3179CertificateValid :
    WideCertificateValid leaf3179Box leaf3179Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi202ValidityFacts
    leaf3179LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3179CoverageChecked :
    coverageCheck (innerAD leaf3179Box) leaf3179InnerLog = true := by
  rfl'

private theorem leaf3179InnerLogValid :
    leaf3179InnerLog.Valid 8 (innerAD leaf3179Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3179CoverageChecked

private noncomputable def leaf3179InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3179InputLogOnePlusV_eq :
    leaf3179InputLogOnePlusV = outerEnclosure 24
      (leaf3179Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3179RoundedFacts : LeafRoundedFacts 8
    leaf3179Certificate.logOnePlusV leaf3179InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3179InputLogOnePlusV_eq }

private noncomputable def leaf3179Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi202InputQChi innerPair221Input
    leaf3179InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3179LowerChecked :
    lowerCheck 24 leaf3179Box leaf3179Inputs = true := by
  rfl'

private theorem leaf3179CoversExact : CoversExact 8
    leaf3179Box leaf3179Certificate leaf3179InnerLog leaf3179Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi202RoundedFacts
    innerPair221RoundedFacts leaf3179RoundedFacts (by rfl)

private theorem leaf3179FlatSound : Sound leaf3179Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3179CertificateValid
    leaf3179InnerLogValid leaf3179CoversExact leaf3179LowerChecked

private noncomputable def leaf3180Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3180Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162137600) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1936568323/1073741824) }, upper := { exponent := 0, mantissa := (1865/1024) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324599057/18324275200) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf3180InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3180LocalValidity :
    LeafFacts leaf3180Box leaf3180Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3180Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162137600) }) = true
      norm_num [leaf3180Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3180CertificateValid :
    WideCertificateValid leaf3180Box leaf3180Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi202ValidityFacts
    leaf3180LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3180CoverageChecked :
    coverageCheck (innerAD leaf3180Box) leaf3180InnerLog = true := by
  rfl'

private theorem leaf3180InnerLogValid :
    leaf3180InnerLog.Valid 8 (innerAD leaf3180Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3180CoverageChecked

private noncomputable def leaf3180InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3180InputLogOnePlusV_eq :
    leaf3180InputLogOnePlusV = outerEnclosure 24
      (leaf3180Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3180RoundedFacts : LeafRoundedFacts 8
    leaf3180Certificate.logOnePlusV leaf3180InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3180InputLogOnePlusV_eq }

private noncomputable def leaf3180Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi202InputQChi innerPair221Input
    leaf3180InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3180LowerChecked :
    lowerCheck 24 leaf3180Box leaf3180Inputs = true := by
  rfl'

private theorem leaf3180CoversExact : CoversExact 8
    leaf3180Box leaf3180Certificate leaf3180InnerLog leaf3180Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi202RoundedFacts
    innerPair221RoundedFacts leaf3180RoundedFacts (by rfl)

private theorem leaf3180FlatSound : Sound leaf3180Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3180CertificateValid
    leaf3180InnerLogValid leaf3180CoversExact leaf3180LowerChecked

private noncomputable def leaf3181Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3181Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486407168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1940303651/1073741824) }, upper := { exponent := 0, mantissa := (29895/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973791539/54972814336) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf3181InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3181LocalValidity :
    LeafFacts leaf3181Box leaf3181Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3181Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486407168) }) = true
      norm_num [leaf3181Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3181CertificateValid :
    WideCertificateValid leaf3181Box leaf3181Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi199ValidityFacts
    leaf3181LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3181CoverageChecked :
    coverageCheck (innerAD leaf3181Box) leaf3181InnerLog = true := by
  rfl'

private theorem leaf3181InnerLogValid :
    leaf3181InnerLog.Valid 8 (innerAD leaf3181Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3181CoverageChecked

private noncomputable def leaf3181InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3181InputLogOnePlusV_eq :
    leaf3181InputLogOnePlusV = outerEnclosure 24
      (leaf3181Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3181RoundedFacts : LeafRoundedFacts 8
    leaf3181Certificate.logOnePlusV leaf3181InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3181InputLogOnePlusV_eq }

private noncomputable def leaf3181Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi199InputQChi innerPair221Input
    leaf3181InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3181LowerChecked :
    lowerCheck 24 leaf3181Box leaf3181Inputs = true := by
  rfl'

private theorem leaf3181CoversExact : CoversExact 8
    leaf3181Box leaf3181Certificate leaf3181InnerLog leaf3181Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi199RoundedFacts
    innerPair221RoundedFacts leaf3181RoundedFacts (by rfl)

private theorem leaf3181FlatSound : Sound leaf3181Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3181CertificateValid
    leaf3181InnerLogValid leaf3181CoversExact leaf3181LowerChecked

private noncomputable def leaf3182Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3182Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270222848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1944104505/1073741824) }, upper := { exponent := 0, mantissa := (14977/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30540991943/30540445696) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf3182InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3182LocalValidity :
    LeafFacts leaf3182Box leaf3182Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3182Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270222848) }) = true
      norm_num [leaf3182Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3182CertificateValid :
    WideCertificateValid leaf3182Box leaf3182Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi199ValidityFacts
    leaf3182LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3182CoverageChecked :
    coverageCheck (innerAD leaf3182Box) leaf3182InnerLog = true := by
  rfl'

private theorem leaf3182InnerLogValid :
    leaf3182InnerLog.Valid 8 (innerAD leaf3182Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3182CoverageChecked

private noncomputable def leaf3182InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3182InputLogOnePlusV_eq :
    leaf3182InputLogOnePlusV = outerEnclosure 24
      (leaf3182Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3182RoundedFacts : LeafRoundedFacts 8
    leaf3182Certificate.logOnePlusV leaf3182InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3182InputLogOnePlusV_eq }

private noncomputable def leaf3182Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi199InputQChi innerPair72Input
    leaf3182InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3182LowerChecked :
    lowerCheck 24 leaf3182Box leaf3182Inputs = true := by
  rfl'

private theorem leaf3182CoversExact : CoversExact 8
    leaf3182Box leaf3182Certificate leaf3182InnerLog leaf3182Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi199RoundedFacts
    innerPair72RoundedFacts leaf3182RoundedFacts (by rfl)

private theorem leaf3182FlatSound : Sound leaf3182Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3182CertificateValid
    leaf3182InnerLogValid leaf3182CoversExact leaf3182LowerChecked

private noncomputable def leaf3183Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3183Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431918592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1955244945/1073741824) }, upper := { exponent := 0, mantissa := (7531/4096) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868840447/274863837184) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf3183InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3183LocalValidity :
    LeafFacts leaf3183Box leaf3183Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3183Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431918592) }) = true
      norm_num [leaf3183Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3183CertificateValid :
    WideCertificateValid leaf3183Box leaf3183Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi200ValidityFacts
    leaf3183LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3183CoverageChecked :
    coverageCheck (innerAD leaf3183Box) leaf3183InnerLog = true := by
  rfl'

private theorem leaf3183InnerLogValid :
    leaf3183InnerLog.Valid 8 (innerAD leaf3183Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3183CoverageChecked

private noncomputable def leaf3183InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3183InputLogOnePlusV_eq :
    leaf3183InputLogOnePlusV = outerEnclosure 24
      (leaf3183Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3183RoundedFacts : LeafRoundedFacts 8
    leaf3183Certificate.logOnePlusV leaf3183InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3183InputLogOnePlusV_eq }

private noncomputable def leaf3183Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi200InputQChi innerPair91Input
    leaf3183InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3183LowerChecked :
    lowerCheck 24 leaf3183Box leaf3183Inputs = true := by
  rfl'

private theorem leaf3183CoversExact : CoversExact 8
    leaf3183Box leaf3183Certificate leaf3183InnerLog leaf3183Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi200RoundedFacts
    innerPair91RoundedFacts leaf3183RoundedFacts (by rfl)

private theorem leaf3183FlatSound : Sound leaf3183Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3183CertificateValid
    leaf3183InnerLogValid leaf3183CoversExact leaf3183LowerChecked

private noncomputable def leaf3184Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3184Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431887872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1959111331/1073741824) }, upper := { exponent := 0, mantissa := (3773/2048) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868809727/274863775744) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf3184InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3184LocalValidity :
    LeafFacts leaf3184Box leaf3184Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3184Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431887872) }) = true
      norm_num [leaf3184Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3184CertificateValid :
    WideCertificateValid leaf3184Box leaf3184Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi200ValidityFacts
    leaf3184LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3184CoverageChecked :
    coverageCheck (innerAD leaf3184Box) leaf3184InnerLog = true := by
  rfl'

private theorem leaf3184InnerLogValid :
    leaf3184InnerLog.Valid 8 (innerAD leaf3184Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3184CoverageChecked

private noncomputable def leaf3184InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3184InputLogOnePlusV_eq :
    leaf3184InputLogOnePlusV = outerEnclosure 24
      (leaf3184Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3184RoundedFacts : LeafRoundedFacts 8
    leaf3184Certificate.logOnePlusV leaf3184InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3184InputLogOnePlusV_eq }

private noncomputable def leaf3184Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi200InputQChi innerPair91Input
    leaf3184InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3184LowerChecked :
    lowerCheck 24 leaf3184Box leaf3184Inputs = true := by
  rfl'

private theorem leaf3184CoversExact : CoversExact 8
    leaf3184Box leaf3184Certificate leaf3184InnerLog leaf3184Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi200RoundedFacts
    innerPair91RoundedFacts leaf3184RoundedFacts (by rfl)

private theorem leaf3184FlatSound : Sound leaf3184Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3184CertificateValid
    leaf3184InnerLogValid leaf3184CoversExact leaf3184LowerChecked

private noncomputable def leaf3185Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3185Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431975424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1947905359/1073741824) }, upper := { exponent := 0, mantissa := (30013/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868897279/274863950848) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf3185InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3185LocalValidity :
    LeafFacts leaf3185Box leaf3185Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3185Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431975424) }) = true
      norm_num [leaf3185Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3185CertificateValid :
    WideCertificateValid leaf3185Box leaf3185Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi199ValidityFacts
    leaf3185LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3185CoverageChecked :
    coverageCheck (innerAD leaf3185Box) leaf3185InnerLog = true := by
  rfl'

private theorem leaf3185InnerLogValid :
    leaf3185InnerLog.Valid 8 (innerAD leaf3185Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3185CoverageChecked

private noncomputable def leaf3185InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629383/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3185InputLogOnePlusV_eq :
    leaf3185InputLogOnePlusV = outerEnclosure 24
      (leaf3185Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3185RoundedFacts : LeafRoundedFacts 8
    leaf3185Certificate.logOnePlusV leaf3185InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3185InputLogOnePlusV_eq }

private noncomputable def leaf3185Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi199InputQChi innerPair91Input
    leaf3185InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3185LowerChecked :
    lowerCheck 24 leaf3185Box leaf3185Inputs = true := by
  rfl'

private theorem leaf3185CoversExact : CoversExact 8
    leaf3185Box leaf3185Certificate leaf3185InnerLog leaf3185Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi199RoundedFacts
    innerPair91RoundedFacts leaf3185RoundedFacts (by rfl)

private theorem leaf3185FlatSound : Sound leaf3185Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3185CertificateValid
    leaf3185InnerLogValid leaf3185CoversExact leaf3185LowerChecked

private noncomputable def leaf3186Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3186Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431945216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1951706213/1073741824) }, upper := { exponent := 0, mantissa := (3759/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868867071/274863890432) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf3186InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3186LocalValidity :
    LeafFacts leaf3186Box leaf3186Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3186Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431945216) }) = true
      norm_num [leaf3186Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3186CertificateValid :
    WideCertificateValid leaf3186Box leaf3186Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi199ValidityFacts
    leaf3186LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3186CoverageChecked :
    coverageCheck (innerAD leaf3186Box) leaf3186InnerLog = true := by
  rfl'

private theorem leaf3186InnerLogValid :
    leaf3186InnerLog.Valid 8 (innerAD leaf3186Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3186CoverageChecked

private noncomputable def leaf3186InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3186InputLogOnePlusV_eq :
    leaf3186InputLogOnePlusV = outerEnclosure 24
      (leaf3186Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3186RoundedFacts : LeafRoundedFacts 8
    leaf3186Certificate.logOnePlusV leaf3186InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3186InputLogOnePlusV_eq }

private noncomputable def leaf3186Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi199InputQChi innerPair91Input
    leaf3186InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3186LowerChecked :
    lowerCheck 24 leaf3186Box leaf3186Inputs = true := by
  rfl'

private theorem leaf3186CoversExact : CoversExact 8
    leaf3186Box leaf3186Certificate leaf3186InnerLog leaf3186Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi199RoundedFacts
    innerPair91RoundedFacts leaf3186RoundedFacts (by rfl)

private theorem leaf3186FlatSound : Sound leaf3186Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3186CertificateValid
    leaf3186InnerLogValid leaf3186CoversExact leaf3186LowerChecked

private noncomputable def leaf3187Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3187Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431857152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1962977717/1073741824) }, upper := { exponent := 0, mantissa := (7561/4096) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868779007/274863714304) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf3187InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3187LocalValidity :
    LeafFacts leaf3187Box leaf3187Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3187Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431857152) }) = true
      norm_num [leaf3187Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3187CertificateValid :
    WideCertificateValid leaf3187Box leaf3187Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi200ValidityFacts
    leaf3187LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3187CoverageChecked :
    coverageCheck (innerAD leaf3187Box) leaf3187InnerLog = true := by
  rfl'

private theorem leaf3187InnerLogValid :
    leaf3187InnerLog.Valid 8 (innerAD leaf3187Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3187CoverageChecked

private noncomputable def leaf3187InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814695/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3187InputLogOnePlusV_eq :
    leaf3187InputLogOnePlusV = outerEnclosure 24
      (leaf3187Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3187RoundedFacts : LeafRoundedFacts 8
    leaf3187Certificate.logOnePlusV leaf3187InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3187InputLogOnePlusV_eq }

private noncomputable def leaf3187Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi200InputQChi innerPair91Input
    leaf3187InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3187LowerChecked :
    lowerCheck 24 leaf3187Box leaf3187Inputs = true := by
  rfl'

private theorem leaf3187CoversExact : CoversExact 8
    leaf3187Box leaf3187Certificate leaf3187InnerLog leaf3187Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi200RoundedFacts
    innerPair91RoundedFacts leaf3187RoundedFacts (by rfl)

private theorem leaf3187FlatSound : Sound leaf3187Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3187CertificateValid
    leaf3187InnerLogValid leaf3187CoversExact leaf3187LowerChecked

private noncomputable def leaf3188Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3188Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431826432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1966844103/1073741824) }, upper := { exponent := 0, mantissa := (947/512) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868748287/274863652864) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf3188InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3188LocalValidity :
    LeafFacts leaf3188Box leaf3188Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3188Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431826432) }) = true
      norm_num [leaf3188Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3188CertificateValid :
    WideCertificateValid leaf3188Box leaf3188Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi200ValidityFacts
    leaf3188LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3188CoverageChecked :
    coverageCheck (innerAD leaf3188Box) leaf3188InnerLog = true := by
  rfl'

private theorem leaf3188InnerLogValid :
    leaf3188InnerLog.Valid 8 (innerAD leaf3188Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3188CoverageChecked

private noncomputable def leaf3188InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726837/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3188InputLogOnePlusV_eq :
    leaf3188InputLogOnePlusV = outerEnclosure 24
      (leaf3188Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3188RoundedFacts : LeafRoundedFacts 8
    leaf3188Certificate.logOnePlusV leaf3188InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3188InputLogOnePlusV_eq }

private noncomputable def leaf3188Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi200InputQChi innerPair91Input
    leaf3188InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3188LowerChecked :
    lowerCheck 24 leaf3188Box leaf3188Inputs = true := by
  rfl'

private theorem leaf3188CoversExact : CoversExact 8
    leaf3188Box leaf3188Certificate leaf3188InnerLog leaf3188Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi200RoundedFacts
    innerPair91RoundedFacts leaf3188RoundedFacts (by rfl)

private theorem leaf3188FlatSound : Sound leaf3188Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3188CertificateValid
    leaf3188InnerLogValid leaf3188CoversExact leaf3188LowerChecked

private noncomputable def leaf3189Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3189Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431926272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1954458567/1073741824) }, upper := { exponent := 0, mantissa := (30109/16384) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868848127/274863852544) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf3189InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3189LocalValidity :
    LeafFacts leaf3189Box leaf3189Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3189Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431926272) }) = true
      norm_num [leaf3189Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3189CertificateValid :
    WideCertificateValid leaf3189Box leaf3189Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi191ValidityFacts
    leaf3189LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3189CoverageChecked :
    coverageCheck (innerAD leaf3189Box) leaf3189InnerLog = true := by
  rfl'

private theorem leaf3189InnerLogValid :
    leaf3189InnerLog.Valid 8 (innerAD leaf3189Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3189CoverageChecked

private noncomputable def leaf3189InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3189InputLogOnePlusV_eq :
    leaf3189InputLogOnePlusV = outerEnclosure 24
      (leaf3189Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3189RoundedFacts : LeafRoundedFacts 8
    leaf3189Certificate.logOnePlusV leaf3189InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3189InputLogOnePlusV_eq }

private noncomputable def leaf3189Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi191InputQChi innerPair91Input
    leaf3189InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3189LowerChecked :
    lowerCheck 24 leaf3189Box leaf3189Inputs = true := by
  rfl'

private theorem leaf3189CoversExact : CoversExact 8
    leaf3189Box leaf3189Certificate leaf3189InnerLog leaf3189Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi191RoundedFacts
    innerPair91RoundedFacts leaf3189RoundedFacts (by rfl)

private theorem leaf3189FlatSound : Sound leaf3189Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3189CertificateValid
    leaf3189InnerLogValid leaf3189CoversExact leaf3189LowerChecked

private noncomputable def leaf3190Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3190Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (179656107/179649536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1958390485/1073741824) }, upper := { exponent := 0, mantissa := (15085/8192) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (359305643/359299072) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf3190InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3190LocalValidity :
    LeafFacts leaf3190Box leaf3190Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3190Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (179656107/179649536) }) = true
      norm_num [leaf3190Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3190CertificateValid :
    WideCertificateValid leaf3190Box leaf3190Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi191ValidityFacts
    leaf3190LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3190CoverageChecked :
    coverageCheck (innerAD leaf3190Box) leaf3190InnerLog = true := by
  rfl'

private theorem leaf3190InnerLogValid :
    leaf3190InnerLog.Valid 8 (innerAD leaf3190Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3190CoverageChecked

private noncomputable def leaf3190InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3190InputLogOnePlusV_eq :
    leaf3190InputLogOnePlusV = outerEnclosure 24
      (leaf3190Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3190RoundedFacts : LeafRoundedFacts 8
    leaf3190Certificate.logOnePlusV leaf3190InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3190InputLogOnePlusV_eq }

private noncomputable def leaf3190Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi191InputQChi innerPair91Input
    leaf3190InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3190LowerChecked :
    lowerCheck 24 leaf3190Box leaf3190Inputs = true := by
  rfl'

private theorem leaf3190CoversExact : CoversExact 8
    leaf3190Box leaf3190Certificate leaf3190InnerLog leaf3190Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi191RoundedFacts
    innerPair91RoundedFacts leaf3190RoundedFacts (by rfl)

private theorem leaf3190FlatSound : Sound leaf3190Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3190CertificateValid
    leaf3190InnerLogValid leaf3190CoversExact leaf3190LowerChecked

private noncomputable def leaf3191Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3191Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431811072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1969137733/1073741824) }, upper := { exponent := 0, mantissa := (15167/8192) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868732927/274863622144) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf3191InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3191LocalValidity :
    LeafFacts leaf3191Box leaf3191Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3191Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431811072) }) = true
      norm_num [leaf3191Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3191CertificateValid :
    WideCertificateValid leaf3191Box leaf3191Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi192ValidityFacts
    leaf3191LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3191CoverageChecked :
    coverageCheck (innerAD leaf3191Box) leaf3191InnerLog = true := by
  rfl'

private theorem leaf3191InnerLogValid :
    leaf3191InnerLog.Valid 8 (innerAD leaf3191Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3191CoverageChecked

private noncomputable def leaf3191InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3191InputLogOnePlusV_eq :
    leaf3191InputLogOnePlusV = outerEnclosure 24
      (leaf3191Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3191RoundedFacts : LeafRoundedFacts 8
    leaf3191Certificate.logOnePlusV leaf3191InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3191InputLogOnePlusV_eq }

private noncomputable def leaf3191Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi192InputQChi innerPair91Input
    leaf3191InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3191LowerChecked :
    lowerCheck 24 leaf3191Box leaf3191Inputs = true := by
  rfl'

private theorem leaf3191CoversExact : CoversExact 8
    leaf3191Box leaf3191Certificate leaf3191InnerLog leaf3191Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi192RoundedFacts
    innerPair91RoundedFacts leaf3191RoundedFacts (by rfl)

private theorem leaf3191FlatSound : Sound leaf3191Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3191CertificateValid
    leaf3191InnerLogValid leaf3191CoversExact leaf3191LowerChecked

private noncomputable def leaf3192Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3192Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431779328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1973135183/1073741824) }, upper := { exponent := 0, mantissa := (7599/4096) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868701183/274863558656) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf3192InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3192LocalValidity :
    LeafFacts leaf3192Box leaf3192Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3192Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431779328) }) = true
      norm_num [leaf3192Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3192CertificateValid :
    WideCertificateValid leaf3192Box leaf3192Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi192ValidityFacts
    leaf3192LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3192CoverageChecked :
    coverageCheck (innerAD leaf3192Box) leaf3192InnerLog = true := by
  rfl'

private theorem leaf3192InnerLogValid :
    leaf3192InnerLog.Valid 8 (innerAD leaf3192Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3192CoverageChecked

private noncomputable def leaf3192InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629395/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3192InputLogOnePlusV_eq :
    leaf3192InputLogOnePlusV = outerEnclosure 24
      (leaf3192Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3192RoundedFacts : LeafRoundedFacts 8
    leaf3192Certificate.logOnePlusV leaf3192InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3192InputLogOnePlusV_eq }

private noncomputable def leaf3192Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi192InputQChi innerPair91Input
    leaf3192InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3192LowerChecked :
    lowerCheck 24 leaf3192Box leaf3192Inputs = true := by
  rfl'

private theorem leaf3192CoversExact : CoversExact 8
    leaf3192Box leaf3192Certificate leaf3192InnerLog leaf3192Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi192RoundedFacts
    innerPair91RoundedFacts leaf3192RoundedFacts (by rfl)

private theorem leaf3192FlatSound : Sound leaf3192Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3192CertificateValid
    leaf3192InnerLogValid leaf3192CoversExact leaf3192LowerChecked

private noncomputable def leaf3193Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3193Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3196207485/3196089856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1962322403/1073741824) }, upper := { exponent := 0, mantissa := (30231/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6392297341/6392179712) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf3193InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3193LocalValidity :
    LeafFacts leaf3193Box leaf3193Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3193Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3196207485/3196089856) }) = true
      norm_num [leaf3193Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3193CertificateValid :
    WideCertificateValid leaf3193Box leaf3193Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi191ValidityFacts
    leaf3193LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3193CoverageChecked :
    coverageCheck (innerAD leaf3193Box) leaf3193InnerLog = true := by
  rfl'

private theorem leaf3193InnerLogValid :
    leaf3193InnerLog.Valid 8 (innerAD leaf3193Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3193CoverageChecked

private noncomputable def leaf3193InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3193InputLogOnePlusV_eq :
    leaf3193InputLogOnePlusV = outerEnclosure 24
      (leaf3193Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3193RoundedFacts : LeafRoundedFacts 8
    leaf3193Certificate.logOnePlusV leaf3193InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3193InputLogOnePlusV_eq }

private noncomputable def leaf3193Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi191InputQChi innerPair91Input
    leaf3193InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3193LowerChecked :
    lowerCheck 24 leaf3193Box leaf3193Inputs = true := by
  rfl'

private theorem leaf3193CoversExact : CoversExact 8
    leaf3193Box leaf3193Certificate leaf3193InnerLog leaf3193Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi191RoundedFacts
    innerPair91RoundedFacts leaf3193RoundedFacts (by rfl)

private theorem leaf3193FlatSound : Sound leaf3193Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3193CertificateValid
    leaf3193InnerLogValid leaf3193CoversExact leaf3193LowerChecked

private noncomputable def leaf3194Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3194Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431832576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1966254321/1073741824) }, upper := { exponent := 0, mantissa := (7573/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868754431/274863665152) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf3194InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3194LocalValidity :
    LeafFacts leaf3194Box leaf3194Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3194Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431832576) }) = true
      norm_num [leaf3194Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3194CertificateValid :
    WideCertificateValid leaf3194Box leaf3194Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi191ValidityFacts
    leaf3194LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3194CoverageChecked :
    coverageCheck (innerAD leaf3194Box) leaf3194InnerLog = true := by
  rfl'

private theorem leaf3194InnerLogValid :
    leaf3194InnerLog.Valid 8 (innerAD leaf3194Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3194CoverageChecked

private noncomputable def leaf3194InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3194InputLogOnePlusV_eq :
    leaf3194InputLogOnePlusV = outerEnclosure 24
      (leaf3194Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3194RoundedFacts : LeafRoundedFacts 8
    leaf3194Certificate.logOnePlusV leaf3194InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3194InputLogOnePlusV_eq }

private noncomputable def leaf3194Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi191InputQChi innerPair91Input
    leaf3194InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3194LowerChecked :
    lowerCheck 24 leaf3194Box leaf3194Inputs = true := by
  rfl'

private theorem leaf3194CoversExact : CoversExact 8
    leaf3194Box leaf3194Certificate leaf3194InnerLog leaf3194Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi191RoundedFacts
    innerPair91RoundedFacts leaf3194RoundedFacts (by rfl)

private theorem leaf3194FlatSound : Sound leaf3194Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3194CertificateValid
    leaf3194InnerLogValid leaf3194CoversExact leaf3194LowerChecked

private noncomputable def leaf3195Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3195Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270194176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1977132633/1073741824) }, upper := { exponent := 0, mantissa := (15229/8192) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30540963271/30540388352) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf3195InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3195LocalValidity :
    LeafFacts leaf3195Box leaf3195Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3195Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270194176) }) = true
      norm_num [leaf3195Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3195CertificateValid :
    WideCertificateValid leaf3195Box leaf3195Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi192ValidityFacts
    leaf3195LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3195CoverageChecked :
    coverageCheck (innerAD leaf3195Box) leaf3195InnerLog = true := by
  rfl'

private theorem leaf3195InnerLogValid :
    leaf3195InnerLog.Valid 8 (innerAD leaf3195Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3195CoverageChecked

private noncomputable def leaf3195InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3195InputLogOnePlusV_eq :
    leaf3195InputLogOnePlusV = outerEnclosure 24
      (leaf3195Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3195RoundedFacts : LeafRoundedFacts 8
    leaf3195Certificate.logOnePlusV leaf3195InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3195InputLogOnePlusV_eq }

private noncomputable def leaf3195Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi192InputQChi innerPair91Input
    leaf3195InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3195LowerChecked :
    lowerCheck 24 leaf3195Box leaf3195Inputs = true := by
  rfl'

private theorem leaf3195CoversExact : CoversExact 8
    leaf3195Box leaf3195Certificate leaf3195InnerLog leaf3195Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi192RoundedFacts
    innerPair91RoundedFacts leaf3195RoundedFacts (by rfl)

private theorem leaf3195FlatSound : Sound leaf3195Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3195CertificateValid
    leaf3195InnerLogValid leaf3195CoversExact leaf3195LowerChecked

private noncomputable def leaf3196Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3196Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486343168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1981130083/1073741824) }, upper := { exponent := 0, mantissa := (3815/2048) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973727539/54972686336) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf3196InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3196LocalValidity :
    LeafFacts leaf3196Box leaf3196Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3196Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486343168) }) = true
      norm_num [leaf3196Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3196CertificateValid :
    WideCertificateValid leaf3196Box leaf3196Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi192ValidityFacts
    leaf3196LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3196CoverageChecked :
    coverageCheck (innerAD leaf3196Box) leaf3196InnerLog = true := by
  rfl'

private theorem leaf3196InnerLogValid :
    leaf3196InnerLog.Valid 8 (innerAD leaf3196Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3196CoverageChecked

private noncomputable def leaf3196InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3196InputLogOnePlusV_eq :
    leaf3196InputLogOnePlusV = outerEnclosure 24
      (leaf3196Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3196RoundedFacts : LeafRoundedFacts 8
    leaf3196Certificate.logOnePlusV leaf3196InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3196InputLogOnePlusV_eq }

private noncomputable def leaf3196Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi192InputQChi innerPair91Input
    leaf3196InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3196LowerChecked :
    lowerCheck 24 leaf3196Box leaf3196Inputs = true := by
  rfl'

private theorem leaf3196CoversExact : CoversExact 8
    leaf3196Box leaf3196Certificate leaf3196InnerLog leaf3196Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi192RoundedFacts
    innerPair91RoundedFacts leaf3196RoundedFacts (by rfl)

private theorem leaf3196FlatSound : Sound leaf3196Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3196CertificateValid
    leaf3196InnerLogValid leaf3196CoversExact leaf3196LowerChecked

private noncomputable def leaf3197Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3197Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431695872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1983816899/1073741824) }, upper := { exponent := 0, mantissa := (30559/16384) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868617727/274863391744) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf3197InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3197LocalValidity :
    LeafFacts leaf3197Box leaf3197Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3197Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431695872) }) = true
      norm_num [leaf3197Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3197CertificateValid :
    WideCertificateValid leaf3197Box leaf3197Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi189ValidityFacts
    leaf3197LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3197CoverageChecked :
    coverageCheck (innerAD leaf3197Box) leaf3197InnerLog = true := by
  rfl'

private theorem leaf3197InnerLogValid :
    leaf3197InnerLog.Valid 8 (innerAD leaf3197Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3197CoverageChecked

private noncomputable def leaf3197InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3197InputLogOnePlusV_eq :
    leaf3197InputLogOnePlusV = outerEnclosure 24
      (leaf3197Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3197RoundedFacts : LeafRoundedFacts 8
    leaf3197Certificate.logOnePlusV leaf3197InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3197InputLogOnePlusV_eq }

private noncomputable def leaf3197Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi189InputQChi innerPair91Input
    leaf3197InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3197LowerChecked :
    lowerCheck 24 leaf3197Box leaf3197Inputs = true := by
  rfl'

private theorem leaf3197CoversExact : CoversExact 8
    leaf3197Box leaf3197Certificate leaf3197InnerLog leaf3197Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi189RoundedFacts
    innerPair91RoundedFacts leaf3197RoundedFacts (by rfl)

private theorem leaf3197FlatSound : Sound leaf3197Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3197CertificateValid
    leaf3197InnerLogValid leaf3197CoversExact leaf3197LowerChecked

private noncomputable def leaf3198Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3198Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431663616) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1987879881/1073741824) }, upper := { exponent := 0, mantissa := (15311/8192) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868585471/274863327232) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf3198InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3198LocalValidity :
    LeafFacts leaf3198Box leaf3198Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3198Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431663616) }) = true
      norm_num [leaf3198Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3198CertificateValid :
    WideCertificateValid leaf3198Box leaf3198Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi189ValidityFacts
    leaf3198LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3198CoverageChecked :
    coverageCheck (innerAD leaf3198Box) leaf3198InnerLog = true := by
  rfl'

private theorem leaf3198InnerLogValid :
    leaf3198InnerLog.Valid 8 (innerAD leaf3198Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3198CoverageChecked

private noncomputable def leaf3198InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814701/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3198InputLogOnePlusV_eq :
    leaf3198InputLogOnePlusV = outerEnclosure 24
      (leaf3198Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3198RoundedFacts : LeafRoundedFacts 8
    leaf3198Certificate.logOnePlusV leaf3198InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3198InputLogOnePlusV_eq }

private noncomputable def leaf3198Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi189InputQChi innerPair91Input
    leaf3198InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3198LowerChecked :
    lowerCheck 24 leaf3198Box leaf3198Inputs = true := by
  rfl'

private theorem leaf3198CoversExact : CoversExact 8
    leaf3198Box leaf3198Certificate leaf3198InnerLog leaf3198Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi189RoundedFacts
    innerPair91RoundedFacts leaf3198RoundedFacts (by rfl)

private theorem leaf3198FlatSound : Sound leaf3198Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3198CertificateValid
    leaf3198InnerLogValid leaf3198CoversExact leaf3198LowerChecked

private noncomputable def leaf3199Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (225/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3199Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431580672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1998496065/1073741824) }, upper := { exponent := 0, mantissa := (481/256) } }, logOuter := sk213LogOuterCertificate, logK := sk213LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868502527/274863161344) } }, logDArg := sk213LogDArgCertificate }

private noncomputable def leaf3199InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3199LocalValidity :
    LeafFacts leaf3199Box leaf3199Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3199Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431580672) }) = true
      norm_num [leaf3199Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3199CertificateValid :
    WideCertificateValid leaf3199Box leaf3199Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk213ValidityFacts chi190ValidityFacts
    leaf3199LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3199CoverageChecked :
    coverageCheck (innerAD leaf3199Box) leaf3199InnerLog = true := by
  rfl'

private theorem leaf3199InnerLogValid :
    leaf3199InnerLog.Valid 8 (innerAD leaf3199Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3199CoverageChecked

private noncomputable def leaf3199InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3199InputLogOnePlusV_eq :
    leaf3199InputLogOnePlusV = outerEnclosure 24
      (leaf3199Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3199RoundedFacts : LeafRoundedFacts 8
    leaf3199Certificate.logOnePlusV leaf3199InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3199InputLogOnePlusV_eq }

private noncomputable def leaf3199Inputs : Inputs :=
  inputsOfCaches globalInput sk213RoundedInputs
    chi190InputQChi innerPair92Input
    leaf3199InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3199LowerChecked :
    lowerCheck 24 leaf3199Box leaf3199Inputs = true := by
  rfl'

private theorem leaf3199CoversExact : CoversExact 8
    leaf3199Box leaf3199Certificate leaf3199InnerLog leaf3199Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk213RoundedFacts chi190RoundedFacts
    innerPair92RoundedFacts leaf3199RoundedFacts (by rfl)

private theorem leaf3199FlatSound : Sound leaf3199Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3199CertificateValid
    leaf3199InnerLogValid leaf3199CoversExact leaf3199LowerChecked

private noncomputable def leaf3200Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (225/64), kHi := (113/32), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3200Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810515968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2002624579/1073741824) }, upper := { exponent := 0, mantissa := (241/128) } }, logOuter := sk214LogOuterCertificate, logK := sk214LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622823253/91621031936) } }, logDArg := sk214LogDArgCertificate }

private noncomputable def leaf3200InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3200LocalValidity :
    LeafFacts leaf3200Box leaf3200Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3200Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810515968) }) = true
      norm_num [leaf3200Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3200CertificateValid :
    WideCertificateValid leaf3200Box leaf3200Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk214ValidityFacts chi190ValidityFacts
    leaf3200LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3200CoverageChecked :
    coverageCheck (innerAD leaf3200Box) leaf3200InnerLog = true := by
  rfl'

private theorem leaf3200InnerLogValid :
    leaf3200InnerLog.Valid 8 (innerAD leaf3200Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3200CoverageChecked

private noncomputable def leaf3200InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3200InputLogOnePlusV_eq :
    leaf3200InputLogOnePlusV = outerEnclosure 24
      (leaf3200Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3200RoundedFacts : LeafRoundedFacts 8
    leaf3200Certificate.logOnePlusV leaf3200InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3200InputLogOnePlusV_eq }

private noncomputable def leaf3200Inputs : Inputs :=
  inputsOfCaches globalInput sk214RoundedInputs
    chi190InputQChi innerPair92Input
    leaf3200InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3200LowerChecked :
    lowerCheck 24 leaf3200Box leaf3200Inputs = true := by
  rfl'

private theorem leaf3200CoversExact : CoversExact 8
    leaf3200Box leaf3200Certificate leaf3200InnerLog leaf3200Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk214RoundedFacts chi190RoundedFacts
    innerPair92RoundedFacts leaf3200RoundedFacts (by rfl)

private theorem leaf3200FlatSound : Sound leaf3200Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3200CertificateValid
    leaf3200InnerLogValid leaf3200CoversExact leaf3200LowerChecked

private noncomputable def leaf3201Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3201Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486326272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1991942863/1073741824) }, upper := { exponent := 0, mantissa := (30685/16384) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973710643/54972652544) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf3201InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3201LocalValidity :
    LeafFacts leaf3201Box leaf3201Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3201Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486326272) }) = true
      norm_num [leaf3201Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3201CertificateValid :
    WideCertificateValid leaf3201Box leaf3201Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi189ValidityFacts
    leaf3201LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3201CoverageChecked :
    coverageCheck (innerAD leaf3201Box) leaf3201InnerLog = true := by
  rfl'

private theorem leaf3201InnerLogValid :
    leaf3201InnerLog.Valid 8 (innerAD leaf3201Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3201CoverageChecked

private noncomputable def leaf3201InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907351/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3201InputLogOnePlusV_eq :
    leaf3201InputLogOnePlusV = outerEnclosure 24
      (leaf3201Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3201RoundedFacts : LeafRoundedFacts 8
    leaf3201Certificate.logOnePlusV leaf3201InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3201InputLogOnePlusV_eq }

private noncomputable def leaf3201Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi189InputQChi innerPair91Input
    leaf3201InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3201LowerChecked :
    lowerCheck 24 leaf3201Box leaf3201Inputs = true := by
  rfl'

private theorem leaf3201CoversExact : CoversExact 8
    leaf3201Box leaf3201Certificate leaf3201InnerLog leaf3201Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi189RoundedFacts
    innerPair91RoundedFacts leaf3201RoundedFacts (by rfl)

private theorem leaf3201FlatSound : Sound leaf3201Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3201CertificateValid
    leaf3201InnerLogValid leaf3201CoversExact leaf3201LowerChecked

private noncomputable def leaf3202Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3202Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084211712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1996005845/1073741824) }, upper := { exponent := 0, mantissa := (7687/4096) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168736527/16168423424) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf3202InnerLog : WideLogData :=
  innerPair199Data

set_option maxRecDepth 1000000 in
private theorem leaf3202LocalValidity :
    LeafFacts leaf3202Box leaf3202Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3202Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084211712) }) = true
      norm_num [leaf3202Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3202CertificateValid :
    WideCertificateValid leaf3202Box leaf3202Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi189ValidityFacts
    leaf3202LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3202CoverageChecked :
    coverageCheck (innerAD leaf3202Box) leaf3202InnerLog = true := by
  rfl'

private theorem leaf3202InnerLogValid :
    leaf3202InnerLog.Valid 8 (innerAD leaf3202Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint69PositiveFacts.valid leaf3202CoverageChecked

private noncomputable def leaf3202InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3202InputLogOnePlusV_eq :
    leaf3202InputLogOnePlusV = outerEnclosure 24
      (leaf3202Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3202RoundedFacts : LeafRoundedFacts 8
    leaf3202Certificate.logOnePlusV leaf3202InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3202InputLogOnePlusV_eq }

private noncomputable def leaf3202Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi189InputQChi innerPair199Input
    leaf3202InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3202LowerChecked :
    lowerCheck 24 leaf3202Box leaf3202Inputs = true := by
  rfl'

private theorem leaf3202CoversExact : CoversExact 8
    leaf3202Box leaf3202Certificate leaf3202InnerLog leaf3202Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi189RoundedFacts
    innerPair199RoundedFacts leaf3202RoundedFacts (by rfl)

private theorem leaf3202FlatSound : Sound leaf3202Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3202CertificateValid
    leaf3202InnerLogValid leaf3202CoversExact leaf3202LowerChecked

private noncomputable def leaf3203Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (227/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3203Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431515136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2006753093/1073741824) }, upper := { exponent := 0, mantissa := (483/256) } }, logOuter := sk211LogOuterCertificate, logK := sk211LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868436991/274863030272) } }, logDArg := sk211LogDArgCertificate }

private noncomputable def leaf3203InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3203LocalValidity :
    LeafFacts leaf3203Box leaf3203Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3203Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431515136) }) = true
      norm_num [leaf3203Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3203CertificateValid :
    WideCertificateValid leaf3203Box leaf3203Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk211ValidityFacts chi190ValidityFacts
    leaf3203LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3203CoverageChecked :
    coverageCheck (innerAD leaf3203Box) leaf3203InnerLog = true := by
  rfl'

private theorem leaf3203InnerLogValid :
    leaf3203InnerLog.Valid 8 (innerAD leaf3203Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3203CoverageChecked

private noncomputable def leaf3203InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3203InputLogOnePlusV_eq :
    leaf3203InputLogOnePlusV = outerEnclosure 24
      (leaf3203Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3203RoundedFacts : LeafRoundedFacts 8
    leaf3203Certificate.logOnePlusV leaf3203InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3203InputLogOnePlusV_eq }

private noncomputable def leaf3203Inputs : Inputs :=
  inputsOfCaches globalInput sk211RoundedInputs
    chi190InputQChi innerPair92Input
    leaf3203InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3203LowerChecked :
    lowerCheck 24 leaf3203Box leaf3203Inputs = true := by
  rfl'

private theorem leaf3203CoversExact : CoversExact 8
    leaf3203Box leaf3203Certificate leaf3203InnerLog leaf3203Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk211RoundedFacts chi190RoundedFacts
    innerPair92RoundedFacts leaf3203RoundedFacts (by rfl)

private theorem leaf3203FlatSound : Sound leaf3203Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3203CertificateValid
    leaf3203InnerLogValid leaf3203CoversExact leaf3203LowerChecked

private noncomputable def leaf3204Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (227/64), kHi := (57/16), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3204Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431482368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2010881607/1073741824) }, upper := { exponent := 0, mantissa := (121/64) } }, logOuter := sk212LogOuterCertificate, logK := sk212LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868404223/274862964736) } }, logDArg := sk212LogDArgCertificate }

private noncomputable def leaf3204InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3204LocalValidity :
    LeafFacts leaf3204Box leaf3204Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3204Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431482368) }) = true
      norm_num [leaf3204Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3204CertificateValid :
    WideCertificateValid leaf3204Box leaf3204Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk212ValidityFacts chi190ValidityFacts
    leaf3204LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3204CoverageChecked :
    coverageCheck (innerAD leaf3204Box) leaf3204InnerLog = true := by
  rfl'

private theorem leaf3204InnerLogValid :
    leaf3204InnerLog.Valid 8 (innerAD leaf3204Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3204CoverageChecked

private noncomputable def leaf3204InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629413/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3204InputLogOnePlusV_eq :
    leaf3204InputLogOnePlusV = outerEnclosure 24
      (leaf3204Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3204RoundedFacts : LeafRoundedFacts 8
    leaf3204Certificate.logOnePlusV leaf3204InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3204InputLogOnePlusV_eq }

private noncomputable def leaf3204Inputs : Inputs :=
  inputsOfCaches globalInput sk212RoundedInputs
    chi190InputQChi innerPair92Input
    leaf3204InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3204LowerChecked :
    lowerCheck 24 leaf3204Box leaf3204Inputs = true := by
  rfl'

private theorem leaf3204CoversExact : CoversExact 8
    leaf3204Box leaf3204Certificate leaf3204InnerLog leaf3204Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk212RoundedFacts chi190RoundedFacts
    innerPair92RoundedFacts leaf3204RoundedFacts (by rfl)

private theorem leaf3204FlatSound : Sound leaf3204Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3204CertificateValid
    leaf3204InnerLogValid leaf3204CoversExact leaf3204LowerChecked

private noncomputable def leaf3205Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3205Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810600448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1970186239/1073741824) }, upper := { exponent := 0, mantissa := (30353/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622907733/91621200896) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf3205InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3205LocalValidity :
    LeafFacts leaf3205Box leaf3205Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3205Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810600448) }) = true
      norm_num [leaf3205Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3205CertificateValid :
    WideCertificateValid leaf3205Box leaf3205Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi191ValidityFacts
    leaf3205LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3205CoverageChecked :
    coverageCheck (innerAD leaf3205Box) leaf3205InnerLog = true := by
  rfl'

private theorem leaf3205InnerLogValid :
    leaf3205InnerLog.Valid 8 (innerAD leaf3205Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3205CoverageChecked

private noncomputable def leaf3205InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629393/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3205InputLogOnePlusV_eq :
    leaf3205InputLogOnePlusV = outerEnclosure 24
      (leaf3205Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3205RoundedFacts : LeafRoundedFacts 8
    leaf3205Certificate.logOnePlusV leaf3205InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3205InputLogOnePlusV_eq }

private noncomputable def leaf3205Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi191InputQChi innerPair91Input
    leaf3205InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3205LowerChecked :
    lowerCheck 24 leaf3205Box leaf3205Inputs = true := by
  rfl'

private theorem leaf3205CoversExact : CoversExact 8
    leaf3205Box leaf3205Certificate leaf3205InnerLog leaf3205Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi191RoundedFacts
    innerPair91RoundedFacts leaf3205RoundedFacts (by rfl)

private theorem leaf3205FlatSound : Sound leaf3205Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3205CertificateValid
    leaf3205InnerLogValid leaf3205CoversExact leaf3205LowerChecked

private noncomputable def leaf3206Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3206Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431770112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1974118157/1073741824) }, upper := { exponent := 0, mantissa := (15207/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868691967/274863540224) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf3206InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3206LocalValidity :
    LeafFacts leaf3206Box leaf3206Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3206Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431770112) }) = true
      norm_num [leaf3206Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3206CertificateValid :
    WideCertificateValid leaf3206Box leaf3206Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi191ValidityFacts
    leaf3206LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3206CoverageChecked :
    coverageCheck (innerAD leaf3206Box) leaf3206InnerLog = true := by
  rfl'

private theorem leaf3206InnerLogValid :
    leaf3206InnerLog.Valid 8 (innerAD leaf3206Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3206CoverageChecked

private noncomputable def leaf3206InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629395/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3206InputLogOnePlusV_eq :
    leaf3206InputLogOnePlusV = outerEnclosure 24
      (leaf3206Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3206RoundedFacts : LeafRoundedFacts 8
    leaf3206Certificate.logOnePlusV leaf3206InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3206InputLogOnePlusV_eq }

private noncomputable def leaf3206Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi191InputQChi innerPair91Input
    leaf3206InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3206LowerChecked :
    lowerCheck 24 leaf3206Box leaf3206Inputs = true := by
  rfl'

private theorem leaf3206CoversExact : CoversExact 8
    leaf3206Box leaf3206Certificate leaf3206InnerLog leaf3206Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi191RoundedFacts
    innerPair91RoundedFacts leaf3206RoundedFacts (by rfl)

private theorem leaf3206FlatSound : Sound leaf3206Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3206CertificateValid
    leaf3206InnerLogValid leaf3206CoversExact leaf3206LowerChecked

private noncomputable def leaf3207Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3207Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431684096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1985127533/1073741824) }, upper := { exponent := 0, mantissa := (15291/8192) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868605951/274863368192) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf3207InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3207LocalValidity :
    LeafFacts leaf3207Box leaf3207Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3207Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431684096) }) = true
      norm_num [leaf3207Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3207CertificateValid :
    WideCertificateValid leaf3207Box leaf3207Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi192ValidityFacts
    leaf3207LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3207CoverageChecked :
    coverageCheck (innerAD leaf3207Box) leaf3207InnerLog = true := by
  rfl'

private theorem leaf3207InnerLogValid :
    leaf3207InnerLog.Valid 8 (innerAD leaf3207Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3207CoverageChecked

private noncomputable def leaf3207InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3207InputLogOnePlusV_eq :
    leaf3207InputLogOnePlusV = outerEnclosure 24
      (leaf3207Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3207RoundedFacts : LeafRoundedFacts 8
    leaf3207Certificate.logOnePlusV leaf3207InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3207InputLogOnePlusV_eq }

private noncomputable def leaf3207Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi192InputQChi innerPair91Input
    leaf3207InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3207LowerChecked :
    lowerCheck 24 leaf3207Box leaf3207Inputs = true := by
  rfl'

private theorem leaf3207CoversExact : CoversExact 8
    leaf3207Box leaf3207Certificate leaf3207InnerLog leaf3207Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi192RoundedFacts
    innerPair91RoundedFacts leaf3207RoundedFacts (by rfl)

private theorem leaf3207FlatSound : Sound leaf3207Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3207CertificateValid
    leaf3207InnerLogValid leaf3207CoversExact leaf3207LowerChecked

private noncomputable def leaf3208Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3208Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810550784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1989124983/1073741824) }, upper := { exponent := 0, mantissa := (7661/4096) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622858069/91621101568) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf3208InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3208LocalValidity :
    LeafFacts leaf3208Box leaf3208Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3208Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810550784) }) = true
      norm_num [leaf3208Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3208CertificateValid :
    WideCertificateValid leaf3208Box leaf3208Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi192ValidityFacts
    leaf3208LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3208CoverageChecked :
    coverageCheck (innerAD leaf3208Box) leaf3208InnerLog = true := by
  rfl'

private theorem leaf3208InnerLogValid :
    leaf3208InnerLog.Valid 8 (innerAD leaf3208Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3208CoverageChecked

private noncomputable def leaf3208InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814701/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3208InputLogOnePlusV_eq :
    leaf3208InputLogOnePlusV = outerEnclosure 24
      (leaf3208Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3208RoundedFacts : LeafRoundedFacts 8
    leaf3208Certificate.logOnePlusV leaf3208InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3208InputLogOnePlusV_eq }

private noncomputable def leaf3208Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi192InputQChi innerPair91Input
    leaf3208InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3208LowerChecked :
    lowerCheck 24 leaf3208Box leaf3208Inputs = true := by
  rfl'

private theorem leaf3208CoversExact : CoversExact 8
    leaf3208Box leaf3208Certificate leaf3208InnerLog leaf3208Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi192RoundedFacts
    innerPair91RoundedFacts leaf3208RoundedFacts (by rfl)

private theorem leaf3208FlatSound : Sound leaf3208Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3208CertificateValid
    leaf3208InnerLogValid leaf3208CoversExact leaf3208LowerChecked

private noncomputable def leaf3209Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3209Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486347776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1978050075/1073741824) }, upper := { exponent := 0, mantissa := (30475/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973732147/54972695552) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf3209InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3209LocalValidity :
    LeafFacts leaf3209Box leaf3209Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3209Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486347776) }) = true
      norm_num [leaf3209Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3209CertificateValid :
    WideCertificateValid leaf3209Box leaf3209Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi191ValidityFacts
    leaf3209LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3209CoverageChecked :
    coverageCheck (innerAD leaf3209Box) leaf3209InnerLog = true := by
  rfl'

private theorem leaf3209InnerLogValid :
    leaf3209InnerLog.Valid 8 (innerAD leaf3209Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3209CoverageChecked

private noncomputable def leaf3209InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3209InputLogOnePlusV_eq :
    leaf3209InputLogOnePlusV = outerEnclosure 24
      (leaf3209Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3209RoundedFacts : LeafRoundedFacts 8
    leaf3209Certificate.logOnePlusV leaf3209InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3209InputLogOnePlusV_eq }

private noncomputable def leaf3209Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi191InputQChi innerPair91Input
    leaf3209InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3209LowerChecked :
    lowerCheck 24 leaf3209Box leaf3209Inputs = true := by
  rfl'

private theorem leaf3209CoversExact : CoversExact 8
    leaf3209Box leaf3209Certificate leaf3209InnerLog leaf3209Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi191RoundedFacts
    innerPair91RoundedFacts leaf3209RoundedFacts (by rfl)

private theorem leaf3209FlatSound : Sound leaf3209Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3209CertificateValid
    leaf3209InnerLogValid leaf3209CoversExact leaf3209LowerChecked

private noncomputable def leaf3210Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3210Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810569216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1981981993/1073741824) }, upper := { exponent := 0, mantissa := (3817/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622876501/91621138432) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf3210InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3210LocalValidity :
    LeafFacts leaf3210Box leaf3210Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3210Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810569216) }) = true
      norm_num [leaf3210Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3210CertificateValid :
    WideCertificateValid leaf3210Box leaf3210Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi191ValidityFacts
    leaf3210LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3210CoverageChecked :
    coverageCheck (innerAD leaf3210Box) leaf3210InnerLog = true := by
  rfl'

private theorem leaf3210InnerLogValid :
    leaf3210InnerLog.Valid 8 (innerAD leaf3210Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3210CoverageChecked

private noncomputable def leaf3210InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3210InputLogOnePlusV_eq :
    leaf3210InputLogOnePlusV = outerEnclosure 24
      (leaf3210Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3210RoundedFacts : LeafRoundedFacts 8
    leaf3210Certificate.logOnePlusV leaf3210InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3210InputLogOnePlusV_eq }

private noncomputable def leaf3210Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi191InputQChi innerPair91Input
    leaf3210InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3210LowerChecked :
    lowerCheck 24 leaf3210Box leaf3210Inputs = true := by
  rfl'

private theorem leaf3210CoversExact : CoversExact 8
    leaf3210Box leaf3210Certificate leaf3210InnerLog leaf3210Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi191RoundedFacts
    innerPair91RoundedFacts leaf3210RoundedFacts (by rfl)

private theorem leaf3210FlatSound : Sound leaf3210Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3210CertificateValid
    leaf3210InnerLogValid leaf3210CoversExact leaf3210LowerChecked

private noncomputable def leaf3211Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3211Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431620608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1993122433/1073741824) }, upper := { exponent := 0, mantissa := (15353/8192) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868542463/274863241216) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf3211InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3211LocalValidity :
    LeafFacts leaf3211Box leaf3211Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3211Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431620608) }) = true
      norm_num [leaf3211Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3211CertificateValid :
    WideCertificateValid leaf3211Box leaf3211Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi192ValidityFacts
    leaf3211LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3211CoverageChecked :
    coverageCheck (innerAD leaf3211Box) leaf3211InnerLog = true := by
  rfl'

private theorem leaf3211InnerLogValid :
    leaf3211InnerLog.Valid 8 (innerAD leaf3211Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3211CoverageChecked

private noncomputable def leaf3211InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907351/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3211InputLogOnePlusV_eq :
    leaf3211InputLogOnePlusV = outerEnclosure 24
      (leaf3211Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3211RoundedFacts : LeafRoundedFacts 8
    leaf3211Certificate.logOnePlusV leaf3211InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3211InputLogOnePlusV_eq }

private noncomputable def leaf3211Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi192InputQChi innerPair91Input
    leaf3211InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3211LowerChecked :
    lowerCheck 24 leaf3211Box leaf3211Inputs = true := by
  rfl'

private theorem leaf3211CoversExact : CoversExact 8
    leaf3211Box leaf3211Certificate leaf3211InnerLog leaf3211Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi192RoundedFacts
    innerPair91RoundedFacts leaf3211RoundedFacts (by rfl)

private theorem leaf3211FlatSound : Sound leaf3211Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3211CertificateValid
    leaf3211InnerLogValid leaf3211CoversExact leaf3211LowerChecked

private noncomputable def leaf3212Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3212Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431588864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1997119883/1073741824) }, upper := { exponent := 0, mantissa := (1923/1024) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868510719/274863177728) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf3212InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3212LocalValidity :
    LeafFacts leaf3212Box leaf3212Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3212Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431588864) }) = true
      norm_num [leaf3212Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3212CertificateValid :
    WideCertificateValid leaf3212Box leaf3212Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi192ValidityFacts
    leaf3212LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3212CoverageChecked :
    coverageCheck (innerAD leaf3212Box) leaf3212InnerLog = true := by
  rfl'

private theorem leaf3212InnerLogValid :
    leaf3212InnerLog.Valid 8 (innerAD leaf3212Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3212CoverageChecked

private noncomputable def leaf3212InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3212InputLogOnePlusV_eq :
    leaf3212InputLogOnePlusV = outerEnclosure 24
      (leaf3212Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3212RoundedFacts : LeafRoundedFacts 8
    leaf3212Certificate.logOnePlusV leaf3212InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3212InputLogOnePlusV_eq }

private noncomputable def leaf3212Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi192InputQChi innerPair482Input
    leaf3212InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3212LowerChecked :
    lowerCheck 24 leaf3212Box leaf3212Inputs = true := by
  rfl'

private theorem leaf3212CoversExact : CoversExact 8
    leaf3212Box leaf3212Certificate leaf3212InnerLog leaf3212Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi192RoundedFacts
    innerPair482RoundedFacts leaf3212RoundedFacts (by rfl)

private theorem leaf3212FlatSound : Sound leaf3212Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3212CertificateValid
    leaf3212InnerLogValid leaf3212CoversExact leaf3212LowerChecked

private noncomputable def leaf3213Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3213Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431566848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2000068827/1073741824) }, upper := { exponent := 0, mantissa := (30811/16384) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868488703/274863133696) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf3213InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3213LocalValidity :
    LeafFacts leaf3213Box leaf3213Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3213Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431566848) }) = true
      norm_num [leaf3213Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3213CertificateValid :
    WideCertificateValid leaf3213Box leaf3213Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi189ValidityFacts
    leaf3213LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3213CoverageChecked :
    coverageCheck (innerAD leaf3213Box) leaf3213InnerLog = true := by
  rfl'

private theorem leaf3213InnerLogValid :
    leaf3213InnerLog.Valid 8 (innerAD leaf3213Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3213CoverageChecked

private noncomputable def leaf3213InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363419/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf3213InputLogOnePlusV_eq :
    leaf3213InputLogOnePlusV = outerEnclosure 24
      (leaf3213Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3213RoundedFacts : LeafRoundedFacts 8
    leaf3213Certificate.logOnePlusV leaf3213InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3213InputLogOnePlusV_eq }

private noncomputable def leaf3213Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi189InputQChi innerPair482Input
    leaf3213InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3213LowerChecked :
    lowerCheck 24 leaf3213Box leaf3213Inputs = true := by
  rfl'

private theorem leaf3213CoversExact : CoversExact 8
    leaf3213Box leaf3213Certificate leaf3213InnerLog leaf3213Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi189RoundedFacts
    innerPair482RoundedFacts leaf3213RoundedFacts (by rfl)

private theorem leaf3213FlatSound : Sound leaf3213Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3213CertificateValid
    leaf3213InnerLogValid leaf3213CoversExact leaf3213LowerChecked

private noncomputable def leaf3214Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3214Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431534592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2004131809/1073741824) }, upper := { exponent := 0, mantissa := (15437/8192) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868456447/274863069184) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf3214InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3214LocalValidity :
    LeafFacts leaf3214Box leaf3214Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3214Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431534592) }) = true
      norm_num [leaf3214Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3214CertificateValid :
    WideCertificateValid leaf3214Box leaf3214Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi189ValidityFacts
    leaf3214LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3214CoverageChecked :
    coverageCheck (innerAD leaf3214Box) leaf3214InnerLog = true := by
  rfl'

private theorem leaf3214InnerLogValid :
    leaf3214InnerLog.Valid 8 (innerAD leaf3214Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3214CoverageChecked

private noncomputable def leaf3214InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814705/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3214InputLogOnePlusV_eq :
    leaf3214InputLogOnePlusV = outerEnclosure 24
      (leaf3214Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3214RoundedFacts : LeafRoundedFacts 8
    leaf3214Certificate.logOnePlusV leaf3214InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3214InputLogOnePlusV_eq }

private noncomputable def leaf3214Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi189InputQChi innerPair482Input
    leaf3214InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3214LowerChecked :
    lowerCheck 24 leaf3214Box leaf3214Inputs = true := by
  rfl'

private theorem leaf3214CoversExact : CoversExact 8
    leaf3214Box leaf3214Certificate leaf3214InnerLog leaf3214Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi189RoundedFacts
    innerPair482RoundedFacts leaf3214RoundedFacts (by rfl)

private theorem leaf3214FlatSound : Sound leaf3214Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3214CertificateValid
    leaf3214InnerLogValid leaf3214CoversExact leaf3214LowerChecked

private noncomputable def leaf3215Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (229/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3215Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162096640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2015010121/1073741824) }, upper := { exponent := 0, mantissa := (485/256) } }, logOuter := sk215LogOuterCertificate, logK := sk215LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324558097/18324193280) } }, logDArg := sk215LogDArgCertificate }

private noncomputable def leaf3215InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3215LocalValidity :
    LeafFacts leaf3215Box leaf3215Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3215Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162096640) }) = true
      norm_num [leaf3215Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3215CertificateValid :
    WideCertificateValid leaf3215Box leaf3215Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk215ValidityFacts chi190ValidityFacts
    leaf3215LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3215CoverageChecked :
    coverageCheck (innerAD leaf3215Box) leaf3215InnerLog = true := by
  rfl'

private theorem leaf3215InnerLogValid :
    leaf3215InnerLog.Valid 8 (innerAD leaf3215Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3215CoverageChecked

private noncomputable def leaf3215InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629415/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3215InputLogOnePlusV_eq :
    leaf3215InputLogOnePlusV = outerEnclosure 24
      (leaf3215Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3215RoundedFacts : LeafRoundedFacts 8
    leaf3215Certificate.logOnePlusV leaf3215InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3215InputLogOnePlusV_eq }

private noncomputable def leaf3215Inputs : Inputs :=
  inputsOfCaches globalInput sk215RoundedInputs
    chi190InputQChi innerPair100Input
    leaf3215InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3215LowerChecked :
    lowerCheck 24 leaf3215Box leaf3215Inputs = true := by
  rfl'

private theorem leaf3215CoversExact : CoversExact 8
    leaf3215Box leaf3215Certificate leaf3215InnerLog leaf3215Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk215RoundedFacts chi190RoundedFacts
    innerPair100RoundedFacts leaf3215RoundedFacts (by rfl)

private theorem leaf3215FlatSound : Sound leaf3215Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3215CertificateValid
    leaf3215InnerLogValid leaf3215CoversExact leaf3215LowerChecked

private noncomputable def leaf3216Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (229/64), kHi := (115/32), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3216Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431416832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2019138635/1073741824) }, upper := { exponent := 0, mantissa := (243/128) } }, logOuter := sk216LogOuterCertificate, logK := sk216LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868338687/274862833664) } }, logDArg := sk216LogDArgCertificate }

private noncomputable def leaf3216InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3216LocalValidity :
    LeafFacts leaf3216Box leaf3216Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3216Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431416832) }) = true
      norm_num [leaf3216Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3216CertificateValid :
    WideCertificateValid leaf3216Box leaf3216Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk216ValidityFacts chi190ValidityFacts
    leaf3216LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3216CoverageChecked :
    coverageCheck (innerAD leaf3216Box) leaf3216InnerLog = true := by
  rfl'

private theorem leaf3216InnerLogValid :
    leaf3216InnerLog.Valid 8 (innerAD leaf3216Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3216CoverageChecked

private noncomputable def leaf3216InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3216InputLogOnePlusV_eq :
    leaf3216InputLogOnePlusV = outerEnclosure 24
      (leaf3216Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3216RoundedFacts : LeafRoundedFacts 8
    leaf3216Certificate.logOnePlusV leaf3216InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3216InputLogOnePlusV_eq }

private noncomputable def leaf3216Inputs : Inputs :=
  inputsOfCaches globalInput sk216RoundedInputs
    chi190InputQChi innerPair100Input
    leaf3216InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3216LowerChecked :
    lowerCheck 24 leaf3216Box leaf3216Inputs = true := by
  rfl'

private theorem leaf3216CoversExact : CoversExact 8
    leaf3216Box leaf3216Certificate leaf3216InnerLog leaf3216Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk216RoundedFacts chi190RoundedFacts
    innerPair100RoundedFacts leaf3216RoundedFacts (by rfl)

private theorem leaf3216FlatSound : Sound leaf3216Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3216CertificateValid
    leaf3216InnerLogValid leaf3216CoversExact leaf3216LowerChecked

private noncomputable def leaf3217Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3217Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431502336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2008194791/1073741824) }, upper := { exponent := 0, mantissa := (30937/16384) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868424191/274863004672) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf3217InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3217LocalValidity :
    LeafFacts leaf3217Box leaf3217Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3217Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431502336) }) = true
      norm_num [leaf3217Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3217CertificateValid :
    WideCertificateValid leaf3217Box leaf3217Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi189ValidityFacts
    leaf3217LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3217CoverageChecked :
    coverageCheck (innerAD leaf3217Box) leaf3217InnerLog = true := by
  rfl'

private theorem leaf3217InnerLogValid :
    leaf3217InnerLog.Valid 8 (innerAD leaf3217Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3217CoverageChecked

private noncomputable def leaf3217InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3217InputLogOnePlusV_eq :
    leaf3217InputLogOnePlusV = outerEnclosure 24
      (leaf3217Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3217RoundedFacts : LeafRoundedFacts 8
    leaf3217Certificate.logOnePlusV leaf3217InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3217InputLogOnePlusV_eq }

private noncomputable def leaf3217Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi189InputQChi innerPair482Input
    leaf3217InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3217LowerChecked :
    lowerCheck 24 leaf3217Box leaf3217Inputs = true := by
  rfl'

private theorem leaf3217CoversExact : CoversExact 8
    leaf3217Box leaf3217Certificate leaf3217InnerLog leaf3217Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi189RoundedFacts
    innerPair482RoundedFacts leaf3217RoundedFacts (by rfl)

private theorem leaf3217FlatSound : Sound leaf3217Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3217CertificateValid
    leaf3217InnerLogValid leaf3217CoversExact leaf3217LowerChecked

private noncomputable def leaf3218Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3218Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486294016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2012257773/1073741824) }, upper := { exponent := 0, mantissa := (3875/2048) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973678387/54972588032) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf3218InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3218LocalValidity :
    LeafFacts leaf3218Box leaf3218Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3218Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486294016) }) = true
      norm_num [leaf3218Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3218CertificateValid :
    WideCertificateValid leaf3218Box leaf3218Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi189ValidityFacts
    leaf3218LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3218CoverageChecked :
    coverageCheck (innerAD leaf3218Box) leaf3218InnerLog = true := by
  rfl'

private theorem leaf3218InnerLogValid :
    leaf3218InnerLog.Valid 8 (innerAD leaf3218Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3218CoverageChecked

private noncomputable def leaf3218InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3218InputLogOnePlusV_eq :
    leaf3218InputLogOnePlusV = outerEnclosure 24
      (leaf3218Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3218RoundedFacts : LeafRoundedFacts 8
    leaf3218Certificate.logOnePlusV leaf3218InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3218InputLogOnePlusV_eq }

private noncomputable def leaf3218Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi189InputQChi innerPair92Input
    leaf3218InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3218LowerChecked :
    lowerCheck 24 leaf3218Box leaf3218Inputs = true := by
  rfl'

private theorem leaf3218CoversExact : CoversExact 8
    leaf3218Box leaf3218Certificate leaf3218InnerLog leaf3218Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi189RoundedFacts
    innerPair92RoundedFacts leaf3218RoundedFacts (by rfl)

private theorem leaf3218FlatSound : Sound leaf3218Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3218CertificateValid
    leaf3218InnerLogValid leaf3218CoversExact leaf3218LowerChecked

private noncomputable def leaf3219Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (231/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3219Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431384064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2023267149/1073741824) }, upper := { exponent := 0, mantissa := (487/256) } }, logOuter := sk209LogOuterCertificate, logK := sk209LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868305919/274862768128) } }, logDArg := sk209LogDArgCertificate }

private noncomputable def leaf3219InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3219LocalValidity :
    LeafFacts leaf3219Box leaf3219Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3219Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431384064) }) = true
      norm_num [leaf3219Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3219CertificateValid :
    WideCertificateValid leaf3219Box leaf3219Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk209ValidityFacts chi190ValidityFacts
    leaf3219LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3219CoverageChecked :
    coverageCheck (innerAD leaf3219Box) leaf3219InnerLog = true := by
  rfl'

private theorem leaf3219InnerLogValid :
    leaf3219InnerLog.Valid 8 (innerAD leaf3219Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3219CoverageChecked

private noncomputable def leaf3219InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3219InputLogOnePlusV_eq :
    leaf3219InputLogOnePlusV = outerEnclosure 24
      (leaf3219Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3219RoundedFacts : LeafRoundedFacts 8
    leaf3219Certificate.logOnePlusV leaf3219InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3219InputLogOnePlusV_eq }

private noncomputable def leaf3219Inputs : Inputs :=
  inputsOfCaches globalInput sk209RoundedInputs
    chi190InputQChi innerPair100Input
    leaf3219InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3219LowerChecked :
    lowerCheck 24 leaf3219Box leaf3219Inputs = true := by
  rfl'

private theorem leaf3219CoversExact : CoversExact 8
    leaf3219Box leaf3219Certificate leaf3219InnerLog leaf3219Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk209RoundedFacts chi190RoundedFacts
    innerPair100RoundedFacts leaf3219RoundedFacts (by rfl)

private theorem leaf3219FlatSound : Sound leaf3219Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3219CertificateValid
    leaf3219InnerLogValid leaf3219CoversExact leaf3219LowerChecked

private noncomputable def leaf3220Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (231/64), kHi := (29/8), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3220Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090050048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2027395663/1073741824) }, upper := { exponent := 0, mantissa := (61/32) } }, logOuter := sk210LogOuterCertificate, logK := sk210LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180306413/10180100096) } }, logDArg := sk210LogDArgCertificate }

private noncomputable def leaf3220InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3220LocalValidity :
    LeafFacts leaf3220Box leaf3220Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3220Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090050048) }) = true
      norm_num [leaf3220Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3220CertificateValid :
    WideCertificateValid leaf3220Box leaf3220Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk210ValidityFacts chi190ValidityFacts
    leaf3220LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3220CoverageChecked :
    coverageCheck (innerAD leaf3220Box) leaf3220InnerLog = true := by
  rfl'

private theorem leaf3220InnerLogValid :
    leaf3220InnerLog.Valid 8 (innerAD leaf3220Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3220CoverageChecked

private noncomputable def leaf3220InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3220InputLogOnePlusV_eq :
    leaf3220InputLogOnePlusV = outerEnclosure 24
      (leaf3220Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3220RoundedFacts : LeafRoundedFacts 8
    leaf3220Certificate.logOnePlusV leaf3220InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3220InputLogOnePlusV_eq }

private noncomputable def leaf3220Inputs : Inputs :=
  inputsOfCaches globalInput sk210RoundedInputs
    chi190InputQChi innerPair100Input
    leaf3220InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3220LowerChecked :
    lowerCheck 24 leaf3220Box leaf3220Inputs = true := by
  rfl'

private theorem leaf3220CoversExact : CoversExact 8
    leaf3220Box leaf3220Certificate leaf3220InnerLog leaf3220Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk210RoundedFacts chi190RoundedFacts
    innerPair100RoundedFacts leaf3220RoundedFacts (by rfl)

private theorem leaf3220FlatSound : Sound leaf3220Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3220CertificateValid
    leaf3220InnerLogValid leaf3220CoversExact leaf3220LowerChecked

private noncomputable def component66Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component66Node0_sound : Sound component66Node0Box :=
  sound_of_literal_split component66Node0Box leaf3157Box leaf3158Box
    .k (225/64) (by rfl) (by rfl)
    leaf3157FlatSound leaf3158FlatSound

private noncomputable def component66Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node1_sound : Sound component66Node1Box :=
  sound_of_literal_split component66Node1Box leaf3159Box leaf3160Box
    .k (225/64) (by rfl) (by rfl)
    leaf3159FlatSound leaf3160FlatSound

private noncomputable def component66Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node2_sound : Sound component66Node2Box :=
  sound_of_literal_split component66Node2Box component66Node0Box component66Node1Box
    .chi (57/256) (by rfl) (by rfl)
    component66Node0_sound component66Node1_sound

private noncomputable def component66Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component66Node3_sound : Sound component66Node3Box :=
  sound_of_literal_split component66Node3Box leaf3161Box leaf3162Box
    .k (227/64) (by rfl) (by rfl)
    leaf3161FlatSound leaf3162FlatSound

private noncomputable def component66Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node4_sound : Sound component66Node4Box :=
  sound_of_literal_split component66Node4Box leaf3163Box leaf3164Box
    .k (227/64) (by rfl) (by rfl)
    leaf3163FlatSound leaf3164FlatSound

private noncomputable def component66Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node5_sound : Sound component66Node5Box :=
  sound_of_literal_split component66Node5Box component66Node3Box component66Node4Box
    .chi (57/256) (by rfl) (by rfl)
    component66Node3_sound component66Node4_sound

private noncomputable def component66Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node6_sound : Sound component66Node6Box :=
  sound_of_literal_split component66Node6Box component66Node2Box component66Node5Box
    .k (113/32) (by rfl) (by rfl)
    component66Node2_sound component66Node5_sound

private noncomputable def component66Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component66Node7_sound : Sound component66Node7Box :=
  sound_of_literal_split component66Node7Box leaf3165Box leaf3166Box
    .k (225/64) (by rfl) (by rfl)
    leaf3165FlatSound leaf3166FlatSound

private noncomputable def component66Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component66Node8_sound : Sound component66Node8Box :=
  sound_of_literal_split component66Node8Box leaf3167Box leaf3168Box
    .k (225/64) (by rfl) (by rfl)
    leaf3167FlatSound leaf3168FlatSound

private noncomputable def component66Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component66Node9_sound : Sound component66Node9Box :=
  sound_of_literal_split component66Node9Box component66Node7Box component66Node8Box
    .chi (59/256) (by rfl) (by rfl)
    component66Node7_sound component66Node8_sound

private noncomputable def component66Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component66Node10_sound : Sound component66Node10Box :=
  sound_of_literal_split component66Node10Box leaf3169Box leaf3170Box
    .k (227/64) (by rfl) (by rfl)
    leaf3169FlatSound leaf3170FlatSound

private noncomputable def component66Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component66Node11_sound : Sound component66Node11Box :=
  sound_of_literal_split component66Node11Box leaf3171Box leaf3172Box
    .k (227/64) (by rfl) (by rfl)
    leaf3171FlatSound leaf3172FlatSound

private noncomputable def component66Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component66Node12_sound : Sound component66Node12Box :=
  sound_of_literal_split component66Node12Box component66Node10Box component66Node11Box
    .chi (59/256) (by rfl) (by rfl)
    component66Node10_sound component66Node11_sound

private noncomputable def component66Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component66Node13_sound : Sound component66Node13Box :=
  sound_of_literal_split component66Node13Box component66Node9Box component66Node12Box
    .k (113/32) (by rfl) (by rfl)
    component66Node9_sound component66Node12_sound

private noncomputable def component66Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component66Node14_sound : Sound component66Node14Box :=
  sound_of_literal_split component66Node14Box component66Node6Box component66Node13Box
    .chi (29/128) (by rfl) (by rfl)
    component66Node6_sound component66Node13_sound

private noncomputable def component66Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component66Node15_sound : Sound component66Node15Box :=
  sound_of_literal_split component66Node15Box leaf3173Box leaf3174Box
    .k (229/64) (by rfl) (by rfl)
    leaf3173FlatSound leaf3174FlatSound

private noncomputable def component66Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node16_sound : Sound component66Node16Box :=
  sound_of_literal_split component66Node16Box leaf3175Box leaf3176Box
    .k (229/64) (by rfl) (by rfl)
    leaf3175FlatSound leaf3176FlatSound

private noncomputable def component66Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node17_sound : Sound component66Node17Box :=
  sound_of_literal_split component66Node17Box component66Node15Box component66Node16Box
    .chi (57/256) (by rfl) (by rfl)
    component66Node15_sound component66Node16_sound

private noncomputable def component66Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component66Node18_sound : Sound component66Node18Box :=
  sound_of_literal_split component66Node18Box leaf3177Box leaf3178Box
    .k (231/64) (by rfl) (by rfl)
    leaf3177FlatSound leaf3178FlatSound

private noncomputable def component66Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node19_sound : Sound component66Node19Box :=
  sound_of_literal_split component66Node19Box leaf3179Box leaf3180Box
    .k (231/64) (by rfl) (by rfl)
    leaf3179FlatSound leaf3180FlatSound

private noncomputable def component66Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node20_sound : Sound component66Node20Box :=
  sound_of_literal_split component66Node20Box component66Node18Box component66Node19Box
    .chi (57/256) (by rfl) (by rfl)
    component66Node18_sound component66Node19_sound

private noncomputable def component66Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node21_sound : Sound component66Node21Box :=
  sound_of_literal_split component66Node21Box component66Node17Box component66Node20Box
    .k (115/32) (by rfl) (by rfl)
    component66Node17_sound component66Node20_sound

private noncomputable def component66Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component66Node22_sound : Sound component66Node22Box :=
  sound_of_literal_split component66Node22Box leaf3181Box leaf3182Box
    .k (229/64) (by rfl) (by rfl)
    leaf3181FlatSound leaf3182FlatSound

private noncomputable def component66Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component66Node23_sound : Sound component66Node23Box :=
  sound_of_literal_split component66Node23Box leaf3183Box leaf3184Box
    .k (229/64) (by rfl) (by rfl)
    leaf3183FlatSound leaf3184FlatSound

private noncomputable def component66Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component66Node24_sound : Sound component66Node24Box :=
  sound_of_literal_split component66Node24Box component66Node22Box component66Node23Box
    .chi (59/256) (by rfl) (by rfl)
    component66Node22_sound component66Node23_sound

private noncomputable def component66Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component66Node25_sound : Sound component66Node25Box :=
  sound_of_literal_split component66Node25Box leaf3185Box leaf3186Box
    .k (231/64) (by rfl) (by rfl)
    leaf3185FlatSound leaf3186FlatSound

private noncomputable def component66Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component66Node26_sound : Sound component66Node26Box :=
  sound_of_literal_split component66Node26Box leaf3187Box leaf3188Box
    .k (231/64) (by rfl) (by rfl)
    leaf3187FlatSound leaf3188FlatSound

private noncomputable def component66Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component66Node27_sound : Sound component66Node27Box :=
  sound_of_literal_split component66Node27Box component66Node25Box component66Node26Box
    .chi (59/256) (by rfl) (by rfl)
    component66Node25_sound component66Node26_sound

private noncomputable def component66Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component66Node28_sound : Sound component66Node28Box :=
  sound_of_literal_split component66Node28Box component66Node24Box component66Node27Box
    .k (115/32) (by rfl) (by rfl)
    component66Node24_sound component66Node27_sound

private noncomputable def component66Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component66Node29_sound : Sound component66Node29Box :=
  sound_of_literal_split component66Node29Box component66Node21Box component66Node28Box
    .chi (29/128) (by rfl) (by rfl)
    component66Node21_sound component66Node28_sound

private noncomputable def component66Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component66Node30_sound : Sound component66Node30Box :=
  sound_of_literal_split component66Node30Box component66Node14Box component66Node29Box
    .k (57/16) (by rfl) (by rfl)
    component66Node14_sound component66Node29_sound

private noncomputable def component66Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component66Node31_sound : Sound component66Node31Box :=
  sound_of_literal_split component66Node31Box leaf3189Box leaf3190Box
    .k (225/64) (by rfl) (by rfl)
    leaf3189FlatSound leaf3190FlatSound

private noncomputable def component66Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node32_sound : Sound component66Node32Box :=
  sound_of_literal_split component66Node32Box leaf3191Box leaf3192Box
    .k (225/64) (by rfl) (by rfl)
    leaf3191FlatSound leaf3192FlatSound

private noncomputable def component66Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node33_sound : Sound component66Node33Box :=
  sound_of_literal_split component66Node33Box component66Node31Box component66Node32Box
    .chi (61/256) (by rfl) (by rfl)
    component66Node31_sound component66Node32_sound

private noncomputable def component66Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component66Node34_sound : Sound component66Node34Box :=
  sound_of_literal_split component66Node34Box leaf3193Box leaf3194Box
    .k (227/64) (by rfl) (by rfl)
    leaf3193FlatSound leaf3194FlatSound

private noncomputable def component66Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node35_sound : Sound component66Node35Box :=
  sound_of_literal_split component66Node35Box leaf3195Box leaf3196Box
    .k (227/64) (by rfl) (by rfl)
    leaf3195FlatSound leaf3196FlatSound

private noncomputable def component66Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node36_sound : Sound component66Node36Box :=
  sound_of_literal_split component66Node36Box component66Node34Box component66Node35Box
    .chi (61/256) (by rfl) (by rfl)
    component66Node34_sound component66Node35_sound

private noncomputable def component66Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node37_sound : Sound component66Node37Box :=
  sound_of_literal_split component66Node37Box component66Node33Box component66Node36Box
    .k (113/32) (by rfl) (by rfl)
    component66Node33_sound component66Node36_sound

private noncomputable def component66Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component66Node38_sound : Sound component66Node38Box :=
  sound_of_literal_split component66Node38Box leaf3197Box leaf3198Box
    .k (225/64) (by rfl) (by rfl)
    leaf3197FlatSound leaf3198FlatSound

private noncomputable def component66Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component66Node39_sound : Sound component66Node39Box :=
  sound_of_literal_split component66Node39Box leaf3199Box leaf3200Box
    .k (225/64) (by rfl) (by rfl)
    leaf3199FlatSound leaf3200FlatSound

private noncomputable def component66Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (113/32), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component66Node40_sound : Sound component66Node40Box :=
  sound_of_literal_split component66Node40Box component66Node38Box component66Node39Box
    .chi (63/256) (by rfl) (by rfl)
    component66Node38_sound component66Node39_sound

private noncomputable def component66Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component66Node41_sound : Sound component66Node41Box :=
  sound_of_literal_split component66Node41Box leaf3201Box leaf3202Box
    .k (227/64) (by rfl) (by rfl)
    leaf3201FlatSound leaf3202FlatSound

private noncomputable def component66Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component66Node42_sound : Sound component66Node42Box :=
  sound_of_literal_split component66Node42Box leaf3203Box leaf3204Box
    .k (227/64) (by rfl) (by rfl)
    leaf3203FlatSound leaf3204FlatSound

private noncomputable def component66Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (113/32), kHi := (57/16), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component66Node43_sound : Sound component66Node43Box :=
  sound_of_literal_split component66Node43Box component66Node41Box component66Node42Box
    .chi (63/256) (by rfl) (by rfl)
    component66Node41_sound component66Node42_sound

private noncomputable def component66Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component66Node44_sound : Sound component66Node44Box :=
  sound_of_literal_split component66Node44Box component66Node40Box component66Node43Box
    .k (113/32) (by rfl) (by rfl)
    component66Node40_sound component66Node43_sound

private noncomputable def component66Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (57/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component66Node45_sound : Sound component66Node45Box :=
  sound_of_literal_split component66Node45Box component66Node37Box component66Node44Box
    .chi (31/128) (by rfl) (by rfl)
    component66Node37_sound component66Node44_sound

private noncomputable def component66Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component66Node46_sound : Sound component66Node46Box :=
  sound_of_literal_split component66Node46Box leaf3205Box leaf3206Box
    .k (229/64) (by rfl) (by rfl)
    leaf3205FlatSound leaf3206FlatSound

private noncomputable def component66Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node47_sound : Sound component66Node47Box :=
  sound_of_literal_split component66Node47Box leaf3207Box leaf3208Box
    .k (229/64) (by rfl) (by rfl)
    leaf3207FlatSound leaf3208FlatSound

private noncomputable def component66Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node48_sound : Sound component66Node48Box :=
  sound_of_literal_split component66Node48Box component66Node46Box component66Node47Box
    .chi (61/256) (by rfl) (by rfl)
    component66Node46_sound component66Node47_sound

private noncomputable def component66Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component66Node49_sound : Sound component66Node49Box :=
  sound_of_literal_split component66Node49Box leaf3209Box leaf3210Box
    .k (231/64) (by rfl) (by rfl)
    leaf3209FlatSound leaf3210FlatSound

private noncomputable def component66Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node50_sound : Sound component66Node50Box :=
  sound_of_literal_split component66Node50Box leaf3211Box leaf3212Box
    .k (231/64) (by rfl) (by rfl)
    leaf3211FlatSound leaf3212FlatSound

private noncomputable def component66Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node51_sound : Sound component66Node51Box :=
  sound_of_literal_split component66Node51Box component66Node49Box component66Node50Box
    .chi (61/256) (by rfl) (by rfl)
    component66Node49_sound component66Node50_sound

private noncomputable def component66Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component66Node52_sound : Sound component66Node52Box :=
  sound_of_literal_split component66Node52Box component66Node48Box component66Node51Box
    .k (115/32) (by rfl) (by rfl)
    component66Node48_sound component66Node51_sound

private noncomputable def component66Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component66Node53_sound : Sound component66Node53Box :=
  sound_of_literal_split component66Node53Box leaf3213Box leaf3214Box
    .k (229/64) (by rfl) (by rfl)
    leaf3213FlatSound leaf3214FlatSound

private noncomputable def component66Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component66Node54_sound : Sound component66Node54Box :=
  sound_of_literal_split component66Node54Box leaf3215Box leaf3216Box
    .k (229/64) (by rfl) (by rfl)
    leaf3215FlatSound leaf3216FlatSound

private noncomputable def component66Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (115/32), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component66Node55_sound : Sound component66Node55Box :=
  sound_of_literal_split component66Node55Box component66Node53Box component66Node54Box
    .chi (63/256) (by rfl) (by rfl)
    component66Node53_sound component66Node54_sound

private noncomputable def component66Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component66Node56_sound : Sound component66Node56Box :=
  sound_of_literal_split component66Node56Box leaf3217Box leaf3218Box
    .k (231/64) (by rfl) (by rfl)
    leaf3217FlatSound leaf3218FlatSound

private noncomputable def component66Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component66Node57_sound : Sound component66Node57Box :=
  sound_of_literal_split component66Node57Box leaf3219Box leaf3220Box
    .k (231/64) (by rfl) (by rfl)
    leaf3219FlatSound leaf3220FlatSound

private noncomputable def component66Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (115/32), kHi := (29/8), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component66Node58_sound : Sound component66Node58Box :=
  sound_of_literal_split component66Node58Box component66Node56Box component66Node57Box
    .chi (63/256) (by rfl) (by rfl)
    component66Node56_sound component66Node57_sound

private noncomputable def component66Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component66Node59_sound : Sound component66Node59Box :=
  sound_of_literal_split component66Node59Box component66Node55Box component66Node58Box
    .k (115/32) (by rfl) (by rfl)
    component66Node55_sound component66Node58_sound

private noncomputable def component66Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (57/16), kHi := (29/8), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component66Node60_sound : Sound component66Node60Box :=
  sound_of_literal_split component66Node60Box component66Node52Box component66Node59Box
    .chi (31/128) (by rfl) (by rfl)
    component66Node52_sound component66Node59_sound

private noncomputable def component66Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component66Node61_sound : Sound component66Node61Box :=
  sound_of_literal_split component66Node61Box component66Node45Box component66Node60Box
    .k (57/16) (by rfl) (by rfl)
    component66Node45_sound component66Node60_sound

noncomputable def component66Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (7/2), kHi := (29/8), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
theorem component66_sound : Sound component66Box :=
  sound_of_literal_split component66Box component66Node30Box component66Node61Box
    .chi (15/64) (by rfl) (by rfl)
    component66Node30_sound component66Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
