import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch9
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

private noncomputable def leaf4444Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4444Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742387/1073741824) }, vSqrt := { lower := (65529/65536), upper := (3196207485/3196086784) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1979622863/1073741824) }, upper := { exponent := 0, mantissa := (30489/16384) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (6392294269/6392173568) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf4444InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4444LocalValidity :
    LeafFacts leaf4444Box leaf4444Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4444Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (3196207485/3196086784) }) = true
      norm_num [leaf4444Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4444CertificateValid :
    WideCertificateValid leaf4444Box leaf4444Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi277ValidityFacts
    leaf4444LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4444CoverageChecked :
    coverageCheck (innerAD leaf4444Box) leaf4444InnerLog = true := by
  rfl'

private theorem leaf4444InnerLogValid :
    leaf4444InnerLog.Valid 8 (innerAD leaf4444Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4444CoverageChecked

private noncomputable def leaf4444InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814699/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4444InputLogOnePlusV_eq :
    leaf4444InputLogOnePlusV = outerEnclosure 24
      (leaf4444Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4444RoundedFacts : LeafRoundedFacts 8
    leaf4444Certificate.logOnePlusV leaf4444InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4444InputLogOnePlusV_eq }

private noncomputable def leaf4444Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi277InputQChi innerPair91Input
    leaf4444InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4444LowerChecked :
    lowerCheck 24 leaf4444Box leaf4444Inputs = true := by
  rfl'

private theorem leaf4444CoversExact : CoversExact 8
    leaf4444Box leaf4444Certificate leaf4444InnerLog leaf4444Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi277RoundedFacts
    innerPair91RoundedFacts leaf4444RoundedFacts (by rfl)

private theorem leaf4444FlatSound : Sound leaf4444Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4444CertificateValid
    leaf4444InnerLogValid leaf4444CoversExact leaf4444LowerChecked

private noncomputable def leaf4445Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4445Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810566144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1983816909/1073741824) }, upper := { exponent := 0, mantissa := (15277/8192) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91622873429/91621132288) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf4445InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4445LocalValidity :
    LeafFacts leaf4445Box leaf4445Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4445Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810566144) }) = true
      norm_num [leaf4445Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4445CertificateValid :
    WideCertificateValid leaf4445Box leaf4445Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi277ValidityFacts
    leaf4445LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4445CoverageChecked :
    coverageCheck (innerAD leaf4445Box) leaf4445InnerLog = true := by
  rfl'

private theorem leaf4445InnerLogValid :
    leaf4445InnerLog.Valid 8 (innerAD leaf4445Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4445CoverageChecked

private noncomputable def leaf4445InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf4445InputLogOnePlusV_eq :
    leaf4445InputLogOnePlusV = outerEnclosure 24
      (leaf4445Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4445RoundedFacts : LeafRoundedFacts 8
    leaf4445Certificate.logOnePlusV leaf4445InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4445InputLogOnePlusV_eq }

private noncomputable def leaf4445Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi277InputQChi innerPair91Input
    leaf4445InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4445LowerChecked :
    lowerCheck 24 leaf4445Box leaf4445Inputs = true := by
  rfl'

private theorem leaf4445CoversExact : CoversExact 8
    leaf4445Box leaf4445Certificate leaf4445InnerLog leaf4445Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi277RoundedFacts
    innerPair91RoundedFacts leaf4445RoundedFacts (by rfl)

private theorem leaf4445FlatSound : Sound leaf4445Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4445CertificateValid
    leaf4445InnerLogValid leaf4445CoversExact leaf4445LowerChecked

private noncomputable def leaf4446Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (217/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4446Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742389/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431620608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1993777773/1073741824) }, upper := { exponent := 0, mantissa := (15353/8192) } }, logOuter := sk183LogOuterCertificate, logK := sk183LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868542463/274863241216) } }, logDArg := sk183LogDArgCertificate }

private noncomputable def leaf4446InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4446LocalValidity :
    LeafFacts leaf4446Box leaf4446Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4446Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431620608) }) = true
      norm_num [leaf4446Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4446CertificateValid :
    WideCertificateValid leaf4446Box leaf4446Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk183ValidityFacts chi278ValidityFacts
    leaf4446LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4446CoverageChecked :
    coverageCheck (innerAD leaf4446Box) leaf4446InnerLog = true := by
  rfl'

private theorem leaf4446InnerLogValid :
    leaf4446InnerLog.Valid 8 (innerAD leaf4446Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4446CoverageChecked

private noncomputable def leaf4446InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907351/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4446InputLogOnePlusV_eq :
    leaf4446InputLogOnePlusV = outerEnclosure 24
      (leaf4446Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4446RoundedFacts : LeafRoundedFacts 8
    leaf4446Certificate.logOnePlusV leaf4446InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4446InputLogOnePlusV_eq }

private noncomputable def leaf4446Inputs : Inputs :=
  inputsOfCaches globalInput sk183RoundedInputs
    chi278InputQChi innerPair91Input
    leaf4446InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4446LowerChecked :
    lowerCheck 24 leaf4446Box leaf4446Inputs = true := by
  rfl'

private theorem leaf4446CoversExact : CoversExact 8
    leaf4446Box leaf4446Certificate leaf4446InnerLog leaf4446Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk183RoundedFacts chi278RoundedFacts
    innerPair91RoundedFacts leaf4446RoundedFacts (by rfl)

private theorem leaf4446FlatSound : Sound leaf4446Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4446CertificateValid
    leaf4446InnerLogValid leaf4446CoversExact leaf4446LowerChecked

private noncomputable def leaf4447Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (217/64), kHi := (109/32), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4447Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431586816) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1998037351/1073741824) }, upper := { exponent := 0, mantissa := (7693/4096) } }, logOuter := sk184LogOuterCertificate, logK := sk184LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868508671/274863173632) } }, logDArg := sk184LogDArgCertificate }

private noncomputable def leaf4447InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf4447LocalValidity :
    LeafFacts leaf4447Box leaf4447Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4447Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431586816) }) = true
      norm_num [leaf4447Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4447CertificateValid :
    WideCertificateValid leaf4447Box leaf4447Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk184ValidityFacts chi278ValidityFacts
    leaf4447LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4447CoverageChecked :
    coverageCheck (innerAD leaf4447Box) leaf4447InnerLog = true := by
  rfl'

private theorem leaf4447InnerLogValid :
    leaf4447InnerLog.Valid 8 (innerAD leaf4447Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf4447CoverageChecked

private noncomputable def leaf4447InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4447InputLogOnePlusV_eq :
    leaf4447InputLogOnePlusV = outerEnclosure 24
      (leaf4447Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4447RoundedFacts : LeafRoundedFacts 8
    leaf4447Certificate.logOnePlusV leaf4447InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4447InputLogOnePlusV_eq }

private noncomputable def leaf4447Inputs : Inputs :=
  inputsOfCaches globalInput sk184RoundedInputs
    chi278InputQChi innerPair92Input
    leaf4447InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4447LowerChecked :
    lowerCheck 24 leaf4447Box leaf4447Inputs = true := by
  rfl'

private theorem leaf4447CoversExact : CoversExact 8
    leaf4447Box leaf4447Certificate leaf4447InnerLog leaf4447Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk184RoundedFacts chi278RoundedFacts
    innerPair92RoundedFacts leaf4447RoundedFacts (by rfl)

private theorem leaf4447FlatSound : Sound leaf4447Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4447CertificateValid
    leaf4447InnerLogValid leaf4447CoversExact leaf4447LowerChecked

private noncomputable def leaf4448Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4448Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742391/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431665152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1988010955/1073741824) }, upper := { exponent := 0, mantissa := (30619/16384) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868587007/274863330304) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf4448InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4448LocalValidity :
    LeafFacts leaf4448Box leaf4448Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4448Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431665152) }) = true
      norm_num [leaf4448Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4448CertificateValid :
    WideCertificateValid leaf4448Box leaf4448Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi277ValidityFacts
    leaf4448LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4448CoverageChecked :
    coverageCheck (innerAD leaf4448Box) leaf4448InnerLog = true := by
  rfl'

private theorem leaf4448InnerLogValid :
    leaf4448InnerLog.Valid 8 (innerAD leaf4448Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4448CoverageChecked

private noncomputable def leaf4448InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814701/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4448InputLogOnePlusV_eq :
    leaf4448InputLogOnePlusV = outerEnclosure 24
      (leaf4448Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4448RoundedFacts : LeafRoundedFacts 8
    leaf4448Certificate.logOnePlusV leaf4448InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4448InputLogOnePlusV_eq }

private noncomputable def leaf4448Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi277InputQChi innerPair91Input
    leaf4448InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4448LowerChecked :
    lowerCheck 24 leaf4448Box leaf4448Inputs = true := by
  rfl'

private theorem leaf4448CoversExact : CoversExact 8
    leaf4448Box leaf4448Certificate leaf4448InnerLog leaf4448Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi277RoundedFacts
    innerPair91RoundedFacts leaf4448RoundedFacts (by rfl)

private theorem leaf4448FlatSound : Sound leaf4448Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4448CertificateValid
    leaf4448InnerLogValid leaf4448CoversExact leaf4448LowerChecked

private noncomputable def leaf4449Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4449Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431631872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1992205001/1073741824) }, upper := { exponent := 0, mantissa := (7671/4096) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868553727/274863263744) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf4449InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf4449LocalValidity :
    LeafFacts leaf4449Box leaf4449Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4449Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431631872) }) = true
      norm_num [leaf4449Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4449CertificateValid :
    WideCertificateValid leaf4449Box leaf4449Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi277ValidityFacts
    leaf4449LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4449CoverageChecked :
    coverageCheck (innerAD leaf4449Box) leaf4449InnerLog = true := by
  rfl'

private theorem leaf4449InnerLogValid :
    leaf4449InnerLog.Valid 8 (innerAD leaf4449Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf4449CoverageChecked

private noncomputable def leaf4449InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907351/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4449InputLogOnePlusV_eq :
    leaf4449InputLogOnePlusV = outerEnclosure 24
      (leaf4449Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4449RoundedFacts : LeafRoundedFacts 8
    leaf4449Certificate.logOnePlusV leaf4449InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4449InputLogOnePlusV_eq }

private noncomputable def leaf4449Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi277InputQChi innerPair91Input
    leaf4449InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4449LowerChecked :
    lowerCheck 24 leaf4449Box leaf4449Inputs = true := by
  rfl'

private theorem leaf4449CoversExact : CoversExact 8
    leaf4449Box leaf4449Certificate leaf4449InnerLog leaf4449Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi277RoundedFacts
    innerPair91RoundedFacts leaf4449RoundedFacts (by rfl)

private theorem leaf4449FlatSound : Sound leaf4449Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4449CertificateValid
    leaf4449InnerLogValid leaf4449CoversExact leaf4449LowerChecked

private noncomputable def leaf4450Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4450Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742393/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431553024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2002296929/1073741824) }, upper := { exponent := 0, mantissa := (15419/8192) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868474879/274863106048) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf4450InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf4450LocalValidity :
    LeafFacts leaf4450Box leaf4450Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4450Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431553024) }) = true
      norm_num [leaf4450Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4450CertificateValid :
    WideCertificateValid leaf4450Box leaf4450Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi278ValidityFacts
    leaf4450LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4450CoverageChecked :
    coverageCheck (innerAD leaf4450Box) leaf4450InnerLog = true := by
  rfl'

private theorem leaf4450InnerLogValid :
    leaf4450InnerLog.Valid 8 (innerAD leaf4450Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf4450CoverageChecked

private noncomputable def leaf4450InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363419/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf4450InputLogOnePlusV_eq :
    leaf4450InputLogOnePlusV = outerEnclosure 24
      (leaf4450Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4450RoundedFacts : LeafRoundedFacts 8
    leaf4450Certificate.logOnePlusV leaf4450InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4450InputLogOnePlusV_eq }

private noncomputable def leaf4450Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi278InputQChi innerPair92Input
    leaf4450InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4450LowerChecked :
    lowerCheck 24 leaf4450Box leaf4450Inputs = true := by
  rfl'

private theorem leaf4450CoversExact : CoversExact 8
    leaf4450Box leaf4450Certificate leaf4450InnerLog leaf4450Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi278RoundedFacts
    innerPair92RoundedFacts leaf4450RoundedFacts (by rfl)

private theorem leaf4450FlatSound : Sound leaf4450Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4450CertificateValid
    leaf4450InnerLogValid leaf4450CoversExact leaf4450LowerChecked

private noncomputable def leaf4451Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4451Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431519232) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2006556507/1073741824) }, upper := { exponent := 0, mantissa := (3863/2048) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868441087/274863038464) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf4451InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf4451LocalValidity :
    LeafFacts leaf4451Box leaf4451Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4451Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431519232) }) = true
      norm_num [leaf4451Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4451CertificateValid :
    WideCertificateValid leaf4451Box leaf4451Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi278ValidityFacts
    leaf4451LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4451CoverageChecked :
    coverageCheck (innerAD leaf4451Box) leaf4451InnerLog = true := by
  rfl'

private theorem leaf4451InnerLogValid :
    leaf4451InnerLog.Valid 8 (innerAD leaf4451Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf4451CoverageChecked

private noncomputable def leaf4451InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4451InputLogOnePlusV_eq :
    leaf4451InputLogOnePlusV = outerEnclosure 24
      (leaf4451Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4451RoundedFacts : LeafRoundedFacts 8
    leaf4451Certificate.logOnePlusV leaf4451InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4451InputLogOnePlusV_eq }

private noncomputable def leaf4451Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi278InputQChi innerPair92Input
    leaf4451InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4451LowerChecked :
    lowerCheck 24 leaf4451Box leaf4451Inputs = true := by
  rfl'

private theorem leaf4451CoversExact : CoversExact 8
    leaf4451Box leaf4451Certificate leaf4451InnerLog leaf4451Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi278RoundedFacts
    innerPair92RoundedFacts leaf4451RoundedFacts (by rfl)

private theorem leaf4451FlatSound : Sound leaf4451Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4451CertificateValid
    leaf4451InnerLogValid leaf4451CoversExact leaf4451LowerChecked

private noncomputable def leaf4452Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4452Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871263/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743147520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1003949891/536870912) }, upper := { exponent := 0, mantissa := (15495/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486846259/27486295040) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4452InnerLog : WideLogData :=
  innerPair598Data

set_option maxRecDepth 1000000 in
private theorem leaf4452LocalValidity :
    LeafFacts leaf4452Box leaf4452Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4452Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743147520) }) = true
      norm_num [leaf4452Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4452CertificateValid :
    WideCertificateValid leaf4452Box leaf4452Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi275ValidityFacts
    leaf4452LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4452CoverageChecked :
    coverageCheck (innerAD leaf4452Box) leaf4452InnerLog = true := by
  rfl'

private theorem leaf4452InnerLogValid :
    leaf4452InnerLog.Valid 8 (innerAD leaf4452Box) :=
  wideLogDataValid_of_cachedCheck endpoint314PositiveFacts
    endpoint259PositiveFacts.valid leaf4452CoverageChecked

private noncomputable def leaf4452InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4452InputLogOnePlusV_eq :
    leaf4452InputLogOnePlusV = outerEnclosure 24
      (leaf4452Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4452RoundedFacts : LeafRoundedFacts 8
    leaf4452Certificate.logOnePlusV leaf4452InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4452InputLogOnePlusV_eq }

private noncomputable def leaf4452Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi275InputQChi innerPair598Input
    leaf4452InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4452LowerChecked :
    lowerCheck 24 leaf4452Box leaf4452Inputs = true := by
  rfl'

private theorem leaf4452CoversExact : CoversExact 8
    leaf4452Box leaf4452Certificate leaf4452InnerLog leaf4452Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi275RoundedFacts
    innerPair598RoundedFacts leaf4452RoundedFacts (by rfl)

private theorem leaf4452FlatSound : Sound leaf4452Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4452CertificateValid
    leaf4452InnerLogValid leaf4452CoversExact leaf4452LowerChecked

private noncomputable def leaf4453Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4453Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871265/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905227264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1011027345/536870912) }, upper := { exponent := 0, mantissa := (3901/2048) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811391829/45810454528) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4453InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf4453LocalValidity :
    LeafFacts leaf4453Box leaf4453Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4453Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905227264) }) = true
      norm_num [leaf4453Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4453CertificateValid :
    WideCertificateValid leaf4453Box leaf4453Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi276ValidityFacts
    leaf4453LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4453CoverageChecked :
    coverageCheck (innerAD leaf4453Box) leaf4453InnerLog = true := by
  rfl'

private theorem leaf4453InnerLogValid :
    leaf4453InnerLog.Valid 8 (innerAD leaf4453Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf4453CoverageChecked

private noncomputable def leaf4453InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726839/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4453InputLogOnePlusV_eq :
    leaf4453InputLogOnePlusV = outerEnclosure 24
      (leaf4453Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4453RoundedFacts : LeafRoundedFacts 8
    leaf4453Certificate.logOnePlusV leaf4453InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4453InputLogOnePlusV_eq }

private noncomputable def leaf4453Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi276InputQChi innerPair103Input
    leaf4453InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4453LowerChecked :
    lowerCheck 24 leaf4453Box leaf4453Inputs = true := by
  rfl'

private theorem leaf4453CoversExact : CoversExact 8
    leaf4453Box leaf4453Certificate leaf4453InnerLog leaf4453Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi276RoundedFacts
    innerPair103RoundedFacts leaf4453RoundedFacts (by rfl)

private theorem leaf4453FlatSound : Sound leaf4453Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4453CertificateValid
    leaf4453InnerLogValid leaf4453CoversExact leaf4453LowerChecked

private noncomputable def leaf4454Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4454Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431440896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2016582903/1073741824) }, upper := { exponent := 0, mantissa := (31057/16384) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868362751/274862881792) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf4454InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4454LocalValidity :
    LeafFacts leaf4454Box leaf4454Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4454Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431440896) }) = true
      norm_num [leaf4454Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4454CertificateValid :
    WideCertificateValid leaf4454Box leaf4454Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi275ValidityFacts
    leaf4454LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4454CoverageChecked :
    coverageCheck (innerAD leaf4454Box) leaf4454InnerLog = true := by
  rfl'

private theorem leaf4454InnerLogValid :
    leaf4454InnerLog.Valid 8 (innerAD leaf4454Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4454CoverageChecked

private noncomputable def leaf4454InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629415/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4454InputLogOnePlusV_eq :
    leaf4454InputLogOnePlusV = outerEnclosure 24
      (leaf4454Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4454RoundedFacts : LeafRoundedFacts 8
    leaf4454Certificate.logOnePlusV leaf4454InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4454InputLogOnePlusV_eq }

private noncomputable def leaf4454Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi275InputQChi innerPair100Input
    leaf4454InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4454LowerChecked :
    lowerCheck 24 leaf4454Box leaf4454Inputs = true := by
  rfl'

private theorem leaf4454CoversExact : CoversExact 8
    leaf4454Box leaf4454Certificate leaf4454InnerLog leaf4454Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi275RoundedFacts
    innerPair100RoundedFacts leaf4454RoundedFacts (by rfl)

private theorem leaf4454FlatSound : Sound leaf4454Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4454CertificateValid
    leaf4454InnerLogValid leaf4454CoversExact leaf4454LowerChecked

private noncomputable def leaf4455Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4455Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (65529/65536), upper := (5090256365/5090052096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2020908013/1073741824) }, upper := { exponent := 0, mantissa := (7781/4096) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (10180308461/10180104192) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf4455InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4455LocalValidity :
    LeafFacts leaf4455Box leaf4455Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4455Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (5090256365/5090052096) }) = true
      norm_num [leaf4455Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4455CertificateValid :
    WideCertificateValid leaf4455Box leaf4455Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi275ValidityFacts
    leaf4455LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4455CoverageChecked :
    coverageCheck (innerAD leaf4455Box) leaf4455InnerLog = true := by
  rfl'

private theorem leaf4455InnerLogValid :
    leaf4455InnerLog.Valid 8 (innerAD leaf4455Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4455CoverageChecked

private noncomputable def leaf4455InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4455InputLogOnePlusV_eq :
    leaf4455InputLogOnePlusV = outerEnclosure 24
      (leaf4455Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4455RoundedFacts : LeafRoundedFacts 8
    leaf4455Certificate.logOnePlusV leaf4455InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4455InputLogOnePlusV_eq }

private noncomputable def leaf4455Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi275InputQChi innerPair100Input
    leaf4455InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4455LowerChecked :
    lowerCheck 24 leaf4455Box leaf4455Inputs = true := by
  rfl'

private theorem leaf4455CoversExact : CoversExact 8
    leaf4455Box leaf4455Certificate leaf4455InnerLog leaf4455Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi275RoundedFacts
    innerPair100RoundedFacts leaf4455RoundedFacts (by rfl)

private theorem leaf4455FlatSound : Sound leaf4455Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4455CertificateValid
    leaf4455InnerLogValid leaf4455CoversExact leaf4455LowerChecked

private noncomputable def leaf4456Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (219/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4456Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431328768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2030868877/1073741824) }, upper := { exponent := 0, mantissa := (7819/4096) } }, logOuter := sk177LogOuterCertificate, logK := sk177LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868250623/274862657536) } }, logDArg := sk177LogDArgCertificate }

private noncomputable def leaf4456InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4456LocalValidity :
    LeafFacts leaf4456Box leaf4456Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4456Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431328768) }) = true
      norm_num [leaf4456Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4456CertificateValid :
    WideCertificateValid leaf4456Box leaf4456Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk177ValidityFacts chi276ValidityFacts
    leaf4456LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4456CoverageChecked :
    coverageCheck (innerAD leaf4456Box) leaf4456InnerLog = true := by
  rfl'

private theorem leaf4456InnerLogValid :
    leaf4456InnerLog.Valid 8 (innerAD leaf4456Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4456CoverageChecked

private noncomputable def leaf4456InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4456InputLogOnePlusV_eq :
    leaf4456InputLogOnePlusV = outerEnclosure 24
      (leaf4456Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4456RoundedFacts : LeafRoundedFacts 8
    leaf4456Certificate.logOnePlusV leaf4456InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4456InputLogOnePlusV_eq }

private noncomputable def leaf4456Inputs : Inputs :=
  inputsOfCaches globalInput sk177RoundedInputs
    chi276InputQChi innerPair100Input
    leaf4456InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4456LowerChecked :
    lowerCheck 24 leaf4456Box leaf4456Inputs = true := by
  rfl'

private theorem leaf4456CoversExact : CoversExact 8
    leaf4456Box leaf4456Certificate leaf4456InnerLog leaf4456Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk177RoundedFacts chi276RoundedFacts
    innerPair100RoundedFacts leaf4456RoundedFacts (by rfl)

private theorem leaf4456FlatSound : Sound leaf4456Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4456CertificateValid
    leaf4456InnerLogValid leaf4456CoversExact leaf4456LowerChecked

private noncomputable def leaf4457Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (219/64), kHi := (55/16), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4457Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431293952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2035259519/1073741824) }, upper := { exponent := 0, mantissa := (1959/1024) } }, logOuter := sk178LogOuterCertificate, logK := sk178LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868215807/274862587904) } }, logDArg := sk178LogDArgCertificate }

private noncomputable def leaf4457InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4457LocalValidity :
    LeafFacts leaf4457Box leaf4457Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4457Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431293952) }) = true
      norm_num [leaf4457Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4457CertificateValid :
    WideCertificateValid leaf4457Box leaf4457Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk178ValidityFacts chi276ValidityFacts
    leaf4457LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4457CoverageChecked :
    coverageCheck (innerAD leaf4457Box) leaf4457InnerLog = true := by
  rfl'

private theorem leaf4457InnerLogValid :
    leaf4457InnerLog.Valid 8 (innerAD leaf4457Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4457CoverageChecked

private noncomputable def leaf4457InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726839/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4457InputLogOnePlusV_eq :
    leaf4457InputLogOnePlusV = outerEnclosure 24
      (leaf4457Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4457RoundedFacts : LeafRoundedFacts 8
    leaf4457Certificate.logOnePlusV leaf4457InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4457InputLogOnePlusV_eq }

private noncomputable def leaf4457Inputs : Inputs :=
  inputsOfCaches globalInput sk178RoundedInputs
    chi276InputQChi innerPair100Input
    leaf4457InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4457LowerChecked :
    lowerCheck 24 leaf4457Box leaf4457Inputs = true := by
  rfl'

private theorem leaf4457CoversExact : CoversExact 8
    leaf4457Box leaf4457Certificate leaf4457InnerLog leaf4457Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk178RoundedFacts chi276RoundedFacts
    innerPair100RoundedFacts leaf4457RoundedFacts (by rfl)

private theorem leaf4457FlatSound : Sound leaf4457Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4457CertificateValid
    leaf4457InnerLogValid leaf4457CoversExact leaf4457LowerChecked

private noncomputable def leaf4458Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4458Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (65529/65536), upper := (45812307285/45810532864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1996399047/1073741824) }, upper := { exponent := 0, mantissa := (30749/16384) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (91622840149/91621065728) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf4458InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf4458LocalValidity :
    LeafFacts leaf4458Box leaf4458Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4458Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (45812307285/45810532864) }) = true
      norm_num [leaf4458Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4458CertificateValid :
    WideCertificateValid leaf4458Box leaf4458Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi277ValidityFacts
    leaf4458LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4458CoverageChecked :
    coverageCheck (innerAD leaf4458Box) leaf4458InnerLog = true := by
  rfl'

private theorem leaf4458InnerLogValid :
    leaf4458InnerLog.Valid 8 (innerAD leaf4458Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf4458CoverageChecked

private noncomputable def leaf4458InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4458InputLogOnePlusV_eq :
    leaf4458InputLogOnePlusV = outerEnclosure 24
      (leaf4458Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4458RoundedFacts : LeafRoundedFacts 8
    leaf4458Certificate.logOnePlusV leaf4458InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4458InputLogOnePlusV_eq }

private noncomputable def leaf4458Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi277InputQChi innerPair92Input
    leaf4458InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4458LowerChecked :
    lowerCheck 24 leaf4458Box leaf4458Inputs = true := by
  rfl'

private theorem leaf4458CoversExact : CoversExact 8
    leaf4458Box leaf4458Certificate leaf4458InnerLog leaf4458Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi277RoundedFacts
    innerPair92RoundedFacts leaf4458RoundedFacts (by rfl)

private theorem leaf4458FlatSound : Sound leaf4458Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4458CertificateValid
    leaf4458InnerLogValid leaf4458CoversExact leaf4458LowerChecked

private noncomputable def leaf4459Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4459Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431565312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2000593093/1073741824) }, upper := { exponent := 0, mantissa := (15407/8192) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868487167/274863130624) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf4459InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf4459LocalValidity :
    LeafFacts leaf4459Box leaf4459Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4459Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431565312) }) = true
      norm_num [leaf4459Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4459CertificateValid :
    WideCertificateValid leaf4459Box leaf4459Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi277ValidityFacts
    leaf4459LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4459CoverageChecked :
    coverageCheck (innerAD leaf4459Box) leaf4459InnerLog = true := by
  rfl'

private theorem leaf4459InnerLogValid :
    leaf4459InnerLog.Valid 8 (innerAD leaf4459Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf4459CoverageChecked

private noncomputable def leaf4459InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (363419/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf4459InputLogOnePlusV_eq :
    leaf4459InputLogOnePlusV = outerEnclosure 24
      (leaf4459Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4459RoundedFacts : LeafRoundedFacts 8
    leaf4459Certificate.logOnePlusV leaf4459InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4459InputLogOnePlusV_eq }

private noncomputable def leaf4459Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi277InputQChi innerPair92Input
    leaf4459InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4459LowerChecked :
    lowerCheck 24 leaf4459Box leaf4459Inputs = true := by
  rfl'

private theorem leaf4459CoversExact : CoversExact 8
    leaf4459Box leaf4459Certificate leaf4459InnerLog leaf4459Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi277RoundedFacts
    innerPair92RoundedFacts leaf4459RoundedFacts (by rfl)

private theorem leaf4459FlatSound : Sound leaf4459Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4459CertificateValid
    leaf4459InnerLogValid leaf4459CoversExact leaf4459LowerChecked

private noncomputable def leaf4460Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4460Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486297088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2010816085/1073741824) }, upper := { exponent := 0, mantissa := (15485/8192) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973681459/54972594176) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf4460InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf4460LocalValidity :
    LeafFacts leaf4460Box leaf4460Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4460Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486297088) }) = true
      norm_num [leaf4460Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4460CertificateValid :
    WideCertificateValid leaf4460Box leaf4460Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi278ValidityFacts
    leaf4460LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4460CoverageChecked :
    coverageCheck (innerAD leaf4460Box) leaf4460InnerLog = true := by
  rfl'

private theorem leaf4460InnerLogValid :
    leaf4460InnerLog.Valid 8 (innerAD leaf4460Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf4460CoverageChecked

private noncomputable def leaf4460InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629413/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4460InputLogOnePlusV_eq :
    leaf4460InputLogOnePlusV = outerEnclosure 24
      (leaf4460Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4460RoundedFacts : LeafRoundedFacts 8
    leaf4460Certificate.logOnePlusV leaf4460InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4460InputLogOnePlusV_eq }

private noncomputable def leaf4460Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi278InputQChi innerPair92Input
    leaf4460InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4460LowerChecked :
    lowerCheck 24 leaf4460Box leaf4460Inputs = true := by
  rfl'

private theorem leaf4460CoversExact : CoversExact 8
    leaf4460Box leaf4460Certificate leaf4460InnerLog leaf4460Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi278RoundedFacts
    innerPair92RoundedFacts leaf4460RoundedFacts (by rfl)

private theorem leaf4460FlatSound : Sound leaf4460Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4460CertificateValid
    leaf4460InnerLogValid leaf4460CoversExact leaf4460LowerChecked

private noncomputable def leaf4461Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4461Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431451648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2015075663/1073741824) }, upper := { exponent := 0, mantissa := (7759/4096) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868373503/274862903296) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf4461InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4461LocalValidity :
    LeafFacts leaf4461Box leaf4461Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4461Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431451648) }) = true
      norm_num [leaf4461Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4461CertificateValid :
    WideCertificateValid leaf4461Box leaf4461Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi278ValidityFacts
    leaf4461LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4461CoverageChecked :
    coverageCheck (innerAD leaf4461Box) leaf4461InnerLog = true := by
  rfl'

private theorem leaf4461InnerLogValid :
    leaf4461InnerLog.Valid 8 (innerAD leaf4461Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4461CoverageChecked

private noncomputable def leaf4461InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629415/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4461InputLogOnePlusV_eq :
    leaf4461InputLogOnePlusV = outerEnclosure 24
      (leaf4461Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4461RoundedFacts : LeafRoundedFacts 8
    leaf4461Certificate.logOnePlusV leaf4461InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4461InputLogOnePlusV_eq }

private noncomputable def leaf4461Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi278InputQChi innerPair100Input
    leaf4461InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4461LowerChecked :
    lowerCheck 24 leaf4461Box leaf4461Inputs = true := by
  rfl'

private theorem leaf4461CoversExact : CoversExact 8
    leaf4461Box leaf4461Certificate leaf4461InnerLog leaf4461Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi278RoundedFacts
    innerPair100RoundedFacts leaf4461RoundedFacts (by rfl)

private theorem leaf4461FlatSound : Sound leaf4461Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4461CertificateValid
    leaf4461InnerLogValid leaf4461CoversExact leaf4461LowerChecked

private noncomputable def leaf4462Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4462Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431532032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2004787139/1073741824) }, upper := { exponent := 0, mantissa := (30879/16384) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868453887/274863064064) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf4462InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf4462LocalValidity :
    LeafFacts leaf4462Box leaf4462Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4462Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431532032) }) = true
      norm_num [leaf4462Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4462CertificateValid :
    WideCertificateValid leaf4462Box leaf4462Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi277ValidityFacts
    leaf4462LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4462CoverageChecked :
    coverageCheck (innerAD leaf4462Box) leaf4462InnerLog = true := by
  rfl'

private theorem leaf4462InnerLogValid :
    leaf4462InnerLog.Valid 8 (innerAD leaf4462Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf4462CoverageChecked

private noncomputable def leaf4462InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814705/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4462InputLogOnePlusV_eq :
    leaf4462InputLogOnePlusV = outerEnclosure 24
      (leaf4462Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4462RoundedFacts : LeafRoundedFacts 8
    leaf4462Certificate.logOnePlusV leaf4462InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4462InputLogOnePlusV_eq }

private noncomputable def leaf4462Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi277InputQChi innerPair92Input
    leaf4462InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4462LowerChecked :
    lowerCheck 24 leaf4462Box leaf4462Inputs = true := by
  rfl'

private theorem leaf4462CoversExact : CoversExact 8
    leaf4462Box leaf4462Certificate leaf4462InnerLog leaf4462Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi277RoundedFacts
    innerPair92RoundedFacts leaf4462RoundedFacts (by rfl)

private theorem leaf4462FlatSound : Sound leaf4462Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4462CertificateValid
    leaf4462InnerLogValid leaf4462CoversExact leaf4462LowerChecked

private noncomputable def leaf4463Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (1/4), chiHi := (65/256) }

private noncomputable def leaf4463Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270166528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2008981185/1073741824) }, upper := { exponent := 0, mantissa := (967/512) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi277LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30540935623/30540333056) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf4463InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf4463LocalValidity :
    LeafFacts leaf4463Box leaf4463Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4463Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270166528) }) = true
      norm_num [leaf4463Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4463CertificateValid :
    WideCertificateValid leaf4463Box leaf4463Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi277ValidityFacts
    leaf4463LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4463CoverageChecked :
    coverageCheck (innerAD leaf4463Box) leaf4463InnerLog = true := by
  rfl'

private theorem leaf4463InnerLogValid :
    leaf4463InnerLog.Valid 8 (innerAD leaf4463Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf4463CoverageChecked

private noncomputable def leaf4463InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4463InputLogOnePlusV_eq :
    leaf4463InputLogOnePlusV = outerEnclosure 24
      (leaf4463Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4463RoundedFacts : LeafRoundedFacts 8
    leaf4463Certificate.logOnePlusV leaf4463InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4463InputLogOnePlusV_eq }

private noncomputable def leaf4463Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi277InputQChi innerPair92Input
    leaf4463InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4463LowerChecked :
    lowerCheck 24 leaf4463Box leaf4463Inputs = true := by
  rfl'

private theorem leaf4463CoversExact : CoversExact 8
    leaf4463Box leaf4463Certificate leaf4463InnerLog leaf4463Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi277RoundedFacts
    innerPair92RoundedFacts leaf4463RoundedFacts (by rfl)

private theorem leaf4463FlatSound : Sound leaf4463Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4463CertificateValid
    leaf4463InnerLogValid leaf4463CoversExact leaf4463LowerChecked

private noncomputable def leaf4464Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4464Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431417856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2019335241/1073741824) }, upper := { exponent := 0, mantissa := (15551/8192) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868339711/274862835712) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf4464InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4464LocalValidity :
    LeafFacts leaf4464Box leaf4464Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4464Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431417856) }) = true
      norm_num [leaf4464Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4464CertificateValid :
    WideCertificateValid leaf4464Box leaf4464Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi278ValidityFacts
    leaf4464LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4464CoverageChecked :
    coverageCheck (innerAD leaf4464Box) leaf4464InnerLog = true := by
  rfl'

private theorem leaf4464InnerLogValid :
    leaf4464InnerLog.Valid 8 (innerAD leaf4464Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4464CoverageChecked

private noncomputable def leaf4464InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4464InputLogOnePlusV_eq :
    leaf4464InputLogOnePlusV = outerEnclosure 24
      (leaf4464Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4464RoundedFacts : LeafRoundedFacts 8
    leaf4464Certificate.logOnePlusV leaf4464InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4464InputLogOnePlusV_eq }

private noncomputable def leaf4464Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi278InputQChi innerPair100Input
    leaf4464InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4464LowerChecked :
    lowerCheck 24 leaf4464Box leaf4464Inputs = true := by
  rfl'

private theorem leaf4464CoversExact : CoversExact 8
    leaf4464Box leaf4464Certificate leaf4464InnerLog leaf4464Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi278RoundedFacts
    innerPair100RoundedFacts leaf4464RoundedFacts (by rfl)

private theorem leaf4464FlatSound : Sound leaf4464Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4464CertificateValid
    leaf4464InnerLogValid leaf4464CoversExact leaf4464LowerChecked

private noncomputable def leaf4465Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (65/256), chiHi := (33/128) }

private noncomputable def leaf4465Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431384064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2023594819/1073741824) }, upper := { exponent := 0, mantissa := (487/256) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi278LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868305919/274862768128) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf4465InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4465LocalValidity :
    LeafFacts leaf4465Box leaf4465Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4465Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431384064) }) = true
      norm_num [leaf4465Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4465CertificateValid :
    WideCertificateValid leaf4465Box leaf4465Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi278ValidityFacts
    leaf4465LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4465CoverageChecked :
    coverageCheck (innerAD leaf4465Box) leaf4465InnerLog = true := by
  rfl'

private theorem leaf4465InnerLogValid :
    leaf4465InnerLog.Valid 8 (innerAD leaf4465Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4465CoverageChecked

private noncomputable def leaf4465InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4465InputLogOnePlusV_eq :
    leaf4465InputLogOnePlusV = outerEnclosure 24
      (leaf4465Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4465RoundedFacts : LeafRoundedFacts 8
    leaf4465Certificate.logOnePlusV leaf4465InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4465InputLogOnePlusV_eq }

private noncomputable def leaf4465Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi278InputQChi innerPair100Input
    leaf4465InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4465LowerChecked :
    lowerCheck 24 leaf4465Box leaf4465Inputs = true := by
  rfl'

private theorem leaf4465CoversExact : CoversExact 8
    leaf4465Box leaf4465Certificate leaf4465InnerLog leaf4465Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi278RoundedFacts
    innerPair100RoundedFacts leaf4465RoundedFacts (by rfl)

private theorem leaf4465FlatSound : Sound leaf4465Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4465CertificateValid
    leaf4465InnerLogValid leaf4465CoversExact leaf4465LowerChecked

private noncomputable def leaf4466Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4466Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431372288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2025233123/1073741824) }, upper := { exponent := 0, mantissa := (31191/16384) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868294143/274862744576) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf4466InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4466LocalValidity :
    LeafFacts leaf4466Box leaf4466Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4466Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431372288) }) = true
      norm_num [leaf4466Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4466CertificateValid :
    WideCertificateValid leaf4466Box leaf4466Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi275ValidityFacts
    leaf4466LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4466CoverageChecked :
    coverageCheck (innerAD leaf4466Box) leaf4466InnerLog = true := by
  rfl'

private theorem leaf4466InnerLogValid :
    leaf4466InnerLog.Valid 8 (innerAD leaf4466Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4466CoverageChecked

private noncomputable def leaf4466InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4466InputLogOnePlusV_eq :
    leaf4466InputLogOnePlusV = outerEnclosure 24
      (leaf4466Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4466RoundedFacts : LeafRoundedFacts 8
    leaf4466Certificate.logOnePlusV leaf4466InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4466InputLogOnePlusV_eq }

private noncomputable def leaf4466Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi275InputQChi innerPair100Input
    leaf4466InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4466LowerChecked :
    lowerCheck 24 leaf4466Box leaf4466Inputs = true := by
  rfl'

private theorem leaf4466CoversExact : CoversExact 8
    leaf4466Box leaf4466Certificate leaf4466InnerLog leaf4466Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi275RoundedFacts
    innerPair100RoundedFacts leaf4466RoundedFacts (by rfl)

private theorem leaf4466FlatSound : Sound leaf4466Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4466CertificateValid
    leaf4466InnerLogValid leaf4466CoversExact leaf4466LowerChecked

private noncomputable def leaf4467Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4467Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (65529/65536), upper := (8084524815/8084196352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2029558233/1073741824) }, upper := { exponent := 0, mantissa := (15629/8192) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (16168721167/16168392704) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf4467InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4467LocalValidity :
    LeafFacts leaf4467Box leaf4467Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4467Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8084524815/8084196352) }) = true
      norm_num [leaf4467Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4467CertificateValid :
    WideCertificateValid leaf4467Box leaf4467Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi275ValidityFacts
    leaf4467LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4467CoverageChecked :
    coverageCheck (innerAD leaf4467Box) leaf4467InnerLog = true := by
  rfl'

private theorem leaf4467InnerLogValid :
    leaf4467InnerLog.Valid 8 (innerAD leaf4467Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4467CoverageChecked

private noncomputable def leaf4467InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4467InputLogOnePlusV_eq :
    leaf4467InputLogOnePlusV = outerEnclosure 24
      (leaf4467Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4467RoundedFacts : LeafRoundedFacts 8
    leaf4467Certificate.logOnePlusV leaf4467InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4467InputLogOnePlusV_eq }

private noncomputable def leaf4467Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi275InputQChi innerPair100Input
    leaf4467InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4467LowerChecked :
    lowerCheck 24 leaf4467Box leaf4467Inputs = true := by
  rfl'

private theorem leaf4467CoversExact : CoversExact 8
    leaf4467Box leaf4467Certificate leaf4467InnerLog leaf4467Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi275RoundedFacts
    innerPair100RoundedFacts leaf4467RoundedFacts (by rfl)

private theorem leaf4467FlatSound : Sound leaf4467Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4467CertificateValid
    leaf4467InnerLogValid leaf4467CoversExact leaf4467LowerChecked

private noncomputable def leaf4468Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4468Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (65529/65536), upper := (15270769095/15270139904) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2039650161/1073741824) }, upper := { exponent := 0, mantissa := (7853/4096) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (30540908999/30540279808) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf4468InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4468LocalValidity :
    LeafFacts leaf4468Box leaf4468Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4468Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (15270769095/15270139904) }) = true
      norm_num [leaf4468Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4468CertificateValid :
    WideCertificateValid leaf4468Box leaf4468Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi276ValidityFacts
    leaf4468LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4468CoverageChecked :
    coverageCheck (innerAD leaf4468Box) leaf4468InnerLog = true := by
  rfl'

private theorem leaf4468InnerLogValid :
    leaf4468InnerLog.Valid 8 (innerAD leaf4468Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4468CoverageChecked

private noncomputable def leaf4468InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4468InputLogOnePlusV_eq :
    leaf4468InputLogOnePlusV = outerEnclosure 24
      (leaf4468Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4468RoundedFacts : LeafRoundedFacts 8
    leaf4468Certificate.logOnePlusV leaf4468InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4468InputLogOnePlusV_eq }

private noncomputable def leaf4468Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi276InputQChi innerPair100Input
    leaf4468InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4468LowerChecked :
    lowerCheck 24 leaf4468Box leaf4468Inputs = true := by
  rfl'

private theorem leaf4468CoversExact : CoversExact 8
    leaf4468Box leaf4468Certificate leaf4468InnerLog leaf4468Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi276RoundedFacts
    innerPair100RoundedFacts leaf4468RoundedFacts (by rfl)

private theorem leaf4468FlatSound : Sound leaf4468Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4468CertificateValid
    leaf4468InnerLogValid leaf4468CoversExact leaf4468LowerChecked

private noncomputable def leaf4469Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4469Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486244864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2044040803/1073741824) }, upper := { exponent := 0, mantissa := (3935/2048) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973629235/54972489728) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf4469InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4469LocalValidity :
    LeafFacts leaf4469Box leaf4469Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4469Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486244864) }) = true
      norm_num [leaf4469Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4469CertificateValid :
    WideCertificateValid leaf4469Box leaf4469Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi276ValidityFacts
    leaf4469LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4469CoverageChecked :
    coverageCheck (innerAD leaf4469Box) leaf4469InnerLog = true := by
  rfl'

private theorem leaf4469InnerLogValid :
    leaf4469InnerLog.Valid 8 (innerAD leaf4469Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4469CoverageChecked

private noncomputable def leaf4469InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4469InputLogOnePlusV_eq :
    leaf4469InputLogOnePlusV = outerEnclosure 24
      (leaf4469Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4469RoundedFacts : LeafRoundedFacts 8
    leaf4469Certificate.logOnePlusV leaf4469InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4469InputLogOnePlusV_eq }

private noncomputable def leaf4469Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi276InputQChi innerPair100Input
    leaf4469InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4469LowerChecked :
    lowerCheck 24 leaf4469Box leaf4469Inputs = true := by
  rfl'

private theorem leaf4469CoversExact : CoversExact 8
    leaf4469Box leaf4469Certificate leaf4469InnerLog leaf4469Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi276RoundedFacts
    innerPair100RoundedFacts leaf4469RoundedFacts (by rfl)

private theorem leaf4469FlatSound : Sound leaf4469Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4469CertificateValid
    leaf4469InnerLogValid leaf4469CoversExact leaf4469LowerChecked

private noncomputable def leaf4470Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4470Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (65529/65536), upper := (9162461457/9162086912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2033883343/1073741824) }, upper := { exponent := 0, mantissa := (31325/16384) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (18324548369/18324173824) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf4470InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4470LocalValidity :
    LeafFacts leaf4470Box leaf4470Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4470Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (9162461457/9162086912) }) = true
      norm_num [leaf4470Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4470CertificateValid :
    WideCertificateValid leaf4470Box leaf4470Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi275ValidityFacts
    leaf4470LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4470CoverageChecked :
    coverageCheck (innerAD leaf4470Box) leaf4470InnerLog = true := by
  rfl'

private theorem leaf4470InnerLogValid :
    leaf4470InnerLog.Valid 8 (innerAD leaf4470Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4470CoverageChecked

private noncomputable def leaf4470InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726839/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4470InputLogOnePlusV_eq :
    leaf4470InputLogOnePlusV = outerEnclosure 24
      (leaf4470Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4470RoundedFacts : LeafRoundedFacts 8
    leaf4470Certificate.logOnePlusV leaf4470InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4470InputLogOnePlusV_eq }

private noncomputable def leaf4470Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi275InputQChi innerPair100Input
    leaf4470InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4470LowerChecked :
    lowerCheck 24 leaf4470Box leaf4470Inputs = true := by
  rfl'

private theorem leaf4470CoversExact : CoversExact 8
    leaf4470Box leaf4470Certificate leaf4470InnerLog leaf4470Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi275RoundedFacts
    innerPair100RoundedFacts leaf4470RoundedFacts (by rfl)

private theorem leaf4470FlatSound : Sound leaf4470Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4470CertificateValid
    leaf4470InnerLogValid leaf4470CoversExact leaf4470LowerChecked

private noncomputable def leaf4471Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (33/128), chiHi := (67/256) }

private noncomputable def leaf4471Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3196207485/3196076032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2038208453/1073741824) }, upper := { exponent := 0, mantissa := (981/512) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi275LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6392283517/6392152064) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf4471InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4471LocalValidity :
    LeafFacts leaf4471Box leaf4471Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4471Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3196207485/3196076032) }) = true
      norm_num [leaf4471Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4471CertificateValid :
    WideCertificateValid leaf4471Box leaf4471Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi275ValidityFacts
    leaf4471LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4471CoverageChecked :
    coverageCheck (innerAD leaf4471Box) leaf4471InnerLog = true := by
  rfl'

private theorem leaf4471InnerLogValid :
    leaf4471InnerLog.Valid 8 (innerAD leaf4471Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4471CoverageChecked

private noncomputable def leaf4471InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4471InputLogOnePlusV_eq :
    leaf4471InputLogOnePlusV = outerEnclosure 24
      (leaf4471Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4471RoundedFacts : LeafRoundedFacts 8
    leaf4471Certificate.logOnePlusV leaf4471InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4471InputLogOnePlusV_eq }

private noncomputable def leaf4471Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi275InputQChi innerPair100Input
    leaf4471InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4471LowerChecked :
    lowerCheck 24 leaf4471Box leaf4471Inputs = true := by
  rfl'

private theorem leaf4471CoversExact : CoversExact 8
    leaf4471Box leaf4471Certificate leaf4471InnerLog leaf4471Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi275RoundedFacts
    innerPair100RoundedFacts leaf4471RoundedFacts (by rfl)

private theorem leaf4471FlatSound : Sound leaf4471Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4471CertificateValid
    leaf4471InnerLogValid leaf4471CoversExact leaf4471LowerChecked

private noncomputable def leaf4472Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4472Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431189504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2048431445/1073741824) }, upper := { exponent := 0, mantissa := (7887/4096) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868111359/274862379008) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf4472InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4472LocalValidity :
    LeafFacts leaf4472Box leaf4472Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4472Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431189504) }) = true
      norm_num [leaf4472Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4472CertificateValid :
    WideCertificateValid leaf4472Box leaf4472Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi276ValidityFacts
    leaf4472LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4472CoverageChecked :
    coverageCheck (innerAD leaf4472Box) leaf4472InnerLog = true := by
  rfl'

private theorem leaf4472InnerLogValid :
    leaf4472InnerLog.Valid 8 (innerAD leaf4472Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4472CoverageChecked

private noncomputable def leaf4472InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4472InputLogOnePlusV_eq :
    leaf4472InputLogOnePlusV = outerEnclosure 24
      (leaf4472Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4472RoundedFacts : LeafRoundedFacts 8
    leaf4472Certificate.logOnePlusV leaf4472InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4472InputLogOnePlusV_eq }

private noncomputable def leaf4472Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi276InputQChi innerPair100Input
    leaf4472InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4472LowerChecked :
    lowerCheck 24 leaf4472Box leaf4472Inputs = true := by
  rfl'

private theorem leaf4472CoversExact : CoversExact 8
    leaf4472Box leaf4472Certificate leaf4472InnerLog leaf4472Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi276RoundedFacts
    innerPair100RoundedFacts leaf4472RoundedFacts (by rfl)

private theorem leaf4472FlatSound : Sound leaf4472Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4472CertificateValid
    leaf4472InnerLogValid leaf4472CoversExact leaf4472LowerChecked

private noncomputable def leaf4473Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (67/256), chiHi := (17/64) }

private noncomputable def leaf4473Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810384896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2052822087/1073741824) }, upper := { exponent := 0, mantissa := (247/128) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi276LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622692181/91620769792) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf4473InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4473LocalValidity :
    LeafFacts leaf4473Box leaf4473Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4473Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810384896) }) = true
      norm_num [leaf4473Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4473CertificateValid :
    WideCertificateValid leaf4473Box leaf4473Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi276ValidityFacts
    leaf4473LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4473CoverageChecked :
    coverageCheck (innerAD leaf4473Box) leaf4473InnerLog = true := by
  rfl'

private theorem leaf4473InnerLogValid :
    leaf4473InnerLog.Valid 8 (innerAD leaf4473Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4473CoverageChecked

private noncomputable def leaf4473InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4473InputLogOnePlusV_eq :
    leaf4473InputLogOnePlusV = outerEnclosure 24
      (leaf4473Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4473RoundedFacts : LeafRoundedFacts 8
    leaf4473Certificate.logOnePlusV leaf4473InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4473InputLogOnePlusV_eq }

private noncomputable def leaf4473Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi276InputQChi innerPair100Input
    leaf4473InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4473LowerChecked :
    lowerCheck 24 leaf4473Box leaf4473Inputs = true := by
  rfl'

private theorem leaf4473CoversExact : CoversExact 8
    leaf4473Box leaf4473Certificate leaf4473InnerLog leaf4473Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi276RoundedFacts
    innerPair100RoundedFacts leaf4473RoundedFacts (by rfl)

private theorem leaf4473FlatSound : Sound leaf4473Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4473CertificateValid
    leaf4473InnerLogValid leaf4473CoversExact leaf4473LowerChecked

private noncomputable def leaf4474Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4474Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871267/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715625984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1018104799/536870912) }, upper := { exponent := 0, mantissa := (15713/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434119679/137431251968) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4474InnerLog : WideLogData :=
  innerPair229Data

set_option maxRecDepth 1000000 in
private theorem leaf4474LocalValidity :
    LeafFacts leaf4474Box leaf4474Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4474Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715625984) }) = true
      norm_num [leaf4474Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4474CertificateValid :
    WideCertificateValid leaf4474Box leaf4474Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi257ValidityFacts
    leaf4474LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4474CoverageChecked :
    coverageCheck (innerAD leaf4474Box) leaf4474InnerLog = true := by
  rfl'

private theorem leaf4474InnerLogValid :
    leaf4474InnerLog.Valid 8 (innerAD leaf4474Box) :=
  wideLogDataValid_of_cachedCheck endpoint69PositiveFacts
    endpoint81PositiveFacts.valid leaf4474CoverageChecked

private noncomputable def leaf4474InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4474InputLogOnePlusV_eq :
    leaf4474InputLogOnePlusV = outerEnclosure 24
      (leaf4474Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4474RoundedFacts : LeafRoundedFacts 8
    leaf4474Certificate.logOnePlusV leaf4474InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4474InputLogOnePlusV_eq }

private noncomputable def leaf4474Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi257InputQChi innerPair229Input
    leaf4474InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4474LowerChecked :
    lowerCheck 24 leaf4474Box leaf4474Inputs = true := by
  rfl'

private theorem leaf4474CoversExact : CoversExact 8
    leaf4474Box leaf4474Certificate leaf4474InnerLog leaf4474Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi257RoundedFacts
    innerPair229RoundedFacts leaf4474RoundedFacts (by rfl)

private theorem leaf4474FlatSound : Sound leaf4474Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4474CertificateValid
    leaf4474InnerLogValid leaf4474CoversExact leaf4474LowerChecked

private noncomputable def leaf4475Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4475Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871269/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715570176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1025182253/536870912) }, upper := { exponent := 0, mantissa := (7911/4096) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137434063871/137431140352) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4475InnerLog : WideLogData :=
  innerPair235Data

set_option maxRecDepth 1000000 in
private theorem leaf4475LocalValidity :
    LeafFacts leaf4475Box leaf4475Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4475Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715570176) }) = true
      norm_num [leaf4475Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4475CertificateValid :
    WideCertificateValid leaf4475Box leaf4475Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi258ValidityFacts
    leaf4475LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4475CoverageChecked :
    coverageCheck (innerAD leaf4475Box) leaf4475InnerLog = true := by
  rfl'

private theorem leaf4475InnerLogValid :
    leaf4475InnerLog.Valid 8 (innerAD leaf4475Box) :=
  wideLogDataValid_of_cachedCheck endpoint70PositiveFacts
    endpoint265PositiveFacts.valid leaf4475CoverageChecked

private noncomputable def leaf4475InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814719/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4475InputLogOnePlusV_eq :
    leaf4475InputLogOnePlusV = outerEnclosure 24
      (leaf4475Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4475RoundedFacts : LeafRoundedFacts 8
    leaf4475Certificate.logOnePlusV leaf4475InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4475InputLogOnePlusV_eq }

private noncomputable def leaf4475Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi258InputQChi innerPair235Input
    leaf4475InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4475LowerChecked :
    lowerCheck 24 leaf4475Box leaf4475Inputs = true := by
  rfl'

private theorem leaf4475CoversExact : CoversExact 8
    leaf4475Box leaf4475Certificate leaf4475InnerLog leaf4475Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi258RoundedFacts
    innerPair235RoundedFacts leaf4475RoundedFacts (by rfl)

private theorem leaf4475FlatSound : Sound leaf4475Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4475CertificateValid
    leaf4475InnerLogValid leaf4475CoversExact leaf4475LowerChecked

private noncomputable def leaf4476Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4476Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871269/536870912) }, vSqrt := { lower := (65529/65536), upper := (4042264335/4042093568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1022560973/536870912) }, upper := { exponent := 0, mantissa := (7891/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (8084357903/8084187136) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4476InnerLog : WideLogData :=
  innerPair599Data

set_option maxRecDepth 1000000 in
private theorem leaf4476LocalValidity :
    LeafFacts leaf4476Box leaf4476Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4476Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (4042264335/4042093568) }) = true
      norm_num [leaf4476Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4476CertificateValid :
    WideCertificateValid leaf4476Box leaf4476Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi257ValidityFacts
    leaf4476LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4476CoverageChecked :
    coverageCheck (innerAD leaf4476Box) leaf4476InnerLog = true := by
  rfl'

private theorem leaf4476InnerLogValid :
    leaf4476InnerLog.Valid 8 (innerAD leaf4476Box) :=
  wideLogDataValid_of_cachedCheck endpoint315PositiveFacts
    endpoint316PositiveFacts.valid leaf4476CoverageChecked

private noncomputable def leaf4476InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4476InputLogOnePlusV_eq :
    leaf4476InputLogOnePlusV = outerEnclosure 24
      (leaf4476Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4476RoundedFacts : LeafRoundedFacts 8
    leaf4476Certificate.logOnePlusV leaf4476InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4476InputLogOnePlusV_eq }

private noncomputable def leaf4476Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi257InputQChi innerPair599Input
    leaf4476InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4476LowerChecked :
    lowerCheck 24 leaf4476Box leaf4476Inputs = true := by
  rfl'

private theorem leaf4476CoversExact : CoversExact 8
    leaf4476Box leaf4476Certificate leaf4476InnerLog leaf4476Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi257RoundedFacts
    innerPair599RoundedFacts leaf4476RoundedFacts (by rfl)

private theorem leaf4476FlatSound : Sound leaf4476Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4476CertificateValid
    leaf4476InnerLogValid leaf4476CoversExact leaf4476LowerChecked

private noncomputable def leaf4477Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4477Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871271/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905178112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1029703959/536870912) }, upper := { exponent := 0, mantissa := (3973/2048) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811342677/45810356224) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4477InnerLog : WideLogData :=
  innerPair519Data

set_option maxRecDepth 1000000 in
private theorem leaf4477LocalValidity :
    LeafFacts leaf4477Box leaf4477Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4477Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905178112) }) = true
      norm_num [leaf4477Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4477CertificateValid :
    WideCertificateValid leaf4477Box leaf4477Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi258ValidityFacts
    leaf4477LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4477CoverageChecked :
    coverageCheck (innerAD leaf4477Box) leaf4477InnerLog = true := by
  rfl'

private theorem leaf4477InnerLogValid :
    leaf4477InnerLog.Valid 8 (innerAD leaf4477Box) :=
  wideLogDataValid_of_cachedCheck endpoint249PositiveFacts
    endpoint250PositiveFacts.valid leaf4477CoverageChecked

private noncomputable def leaf4477InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814721/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4477InputLogOnePlusV_eq :
    leaf4477InputLogOnePlusV = outerEnclosure 24
      (leaf4477Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4477RoundedFacts : LeafRoundedFacts 8
    leaf4477Certificate.logOnePlusV leaf4477InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4477InputLogOnePlusV_eq }

private noncomputable def leaf4477Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi258InputQChi innerPair519Input
    leaf4477InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4477LowerChecked :
    lowerCheck 24 leaf4477Box leaf4477Inputs = true := by
  rfl'

private theorem leaf4477CoversExact : CoversExact 8
    leaf4477Box leaf4477Certificate leaf4477InnerLog leaf4477Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi258RoundedFacts
    innerPair519RoundedFacts leaf4477RoundedFacts (by rfl)

private theorem leaf4477FlatSound : Sound leaf4477Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4477CertificateValid
    leaf4477InnerLogValid leaf4477CoversExact leaf4477LowerChecked

private noncomputable def leaf4478Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4478Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871271/536870912) }, vSqrt := { lower := (65529/65536), upper := (22906164565/22905171456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1032259707/536870912) }, upper := { exponent := 0, mantissa := (15931/8192) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (45811336021/45810342912) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4478InnerLog : WideLogData :=
  innerPair310Data

set_option maxRecDepth 1000000 in
private theorem leaf4478LocalValidity :
    LeafFacts leaf4478Box leaf4478Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4478Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (22906164565/22905171456) }) = true
      norm_num [leaf4478Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4478CertificateValid :
    WideCertificateValid leaf4478Box leaf4478Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi279ValidityFacts
    leaf4478LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4478CoverageChecked :
    coverageCheck (innerAD leaf4478Box) leaf4478InnerLog = true := by
  rfl'

private theorem leaf4478InnerLogValid :
    leaf4478InnerLog.Valid 8 (innerAD leaf4478Box) :=
  wideLogDataValid_of_cachedCheck endpoint81PositiveFacts
    endpoint273PositiveFacts.valid leaf4478CoverageChecked

private noncomputable def leaf4478InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907361/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4478InputLogOnePlusV_eq :
    leaf4478InputLogOnePlusV = outerEnclosure 24
      (leaf4478Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4478RoundedFacts : LeafRoundedFacts 8
    leaf4478Certificate.logOnePlusV leaf4478InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4478InputLogOnePlusV_eq }

private noncomputable def leaf4478Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi279InputQChi innerPair310Input
    leaf4478InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4478LowerChecked :
    lowerCheck 24 leaf4478Box leaf4478Inputs = true := by
  rfl'

private theorem leaf4478CoversExact : CoversExact 8
    leaf4478Box leaf4478Certificate leaf4478InnerLog leaf4478Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi279RoundedFacts
    innerPair310RoundedFacts leaf4478RoundedFacts (by rfl)

private theorem leaf4478FlatSound : Sound leaf4478Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4478CertificateValid
    leaf4478InnerLogValid leaf4478CoversExact leaf4478LowerChecked

private noncomputable def leaf4479Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4479Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871273/536870912) }, vSqrt := { lower := (65529/65536), upper := (13743698739/13743091712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1039337161/536870912) }, upper := { exponent := 0, mantissa := (2005/1024) } }, logOuter := sk145LogOuterCertificate, logK := sk145LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (27486790451/27486183424) } }, logDArg := sk145LogDArgCertificate }

private noncomputable def leaf4479InnerLog : WideLogData :=
  innerPair528Data

set_option maxRecDepth 1000000 in
private theorem leaf4479LocalValidity :
    LeafFacts leaf4479Box leaf4479Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4479Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (13743698739/13743091712) }) = true
      norm_num [leaf4479Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4479CertificateValid :
    WideCertificateValid leaf4479Box leaf4479Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk145ValidityFacts chi280ValidityFacts
    leaf4479LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4479CoverageChecked :
    coverageCheck (innerAD leaf4479Box) leaf4479InnerLog = true := by
  rfl'

private theorem leaf4479InnerLogValid :
    leaf4479InnerLog.Valid 8 (innerAD leaf4479Box) :=
  wideLogDataValid_of_cachedCheck endpoint265PositiveFacts
    endpoint83PositiveFacts.valid leaf4479CoverageChecked

private noncomputable def leaf4479InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629451/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4479InputLogOnePlusV_eq :
    leaf4479InputLogOnePlusV = outerEnclosure 24
      (leaf4479Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4479RoundedFacts : LeafRoundedFacts 8
    leaf4479Certificate.logOnePlusV leaf4479InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4479InputLogOnePlusV_eq }

private noncomputable def leaf4479Inputs : Inputs :=
  inputsOfCaches globalInput sk145RoundedInputs
    chi280InputQChi innerPair528Input
    leaf4479InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4479LowerChecked :
    lowerCheck 24 leaf4479Box leaf4479Inputs = true := by
  rfl'

private theorem leaf4479CoversExact : CoversExact 8
    leaf4479Box leaf4479Certificate leaf4479InnerLog leaf4479Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk145RoundedFacts chi280RoundedFacts
    innerPair528RoundedFacts leaf4479RoundedFacts (by rfl)

private theorem leaf4479FlatSound : Sound leaf4479Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4479CertificateValid
    leaf4479InnerLogValid leaf4479CoversExact leaf4479LowerChecked

private noncomputable def leaf4480Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4480Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871273/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715478016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1036846945/536870912) }, upper := { exponent := 0, mantissa := (8001/4096) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433971711/137430956032) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4480InnerLog : WideLogData :=
  innerPair600Data

set_option maxRecDepth 1000000 in
private theorem leaf4480LocalValidity :
    LeafFacts leaf4480Box leaf4480Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4480Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715478016) }) = true
      norm_num [leaf4480Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4480CertificateValid :
    WideCertificateValid leaf4480Box leaf4480Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi279ValidityFacts
    leaf4480LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4480CoverageChecked :
    coverageCheck (innerAD leaf4480Box) leaf4480InnerLog = true := by
  rfl'

private theorem leaf4480InnerLogValid :
    leaf4480InnerLog.Valid 8 (innerAD leaf4480Box) :=
  wideLogDataValid_of_cachedCheck endpoint317PositiveFacts
    endpoint318PositiveFacts.valid leaf4480CoverageChecked

private noncomputable def leaf4480InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4480InputLogOnePlusV_eq :
    leaf4480InputLogOnePlusV = outerEnclosure 24
      (leaf4480Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4480RoundedFacts : LeafRoundedFacts 8
    leaf4480Certificate.logOnePlusV leaf4480InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4480InputLogOnePlusV_eq }

private noncomputable def leaf4480Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi279InputQChi innerPair600Input
    leaf4480InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4480LowerChecked :
    lowerCheck 24 leaf4480Box leaf4480Inputs = true := by
  rfl'

private theorem leaf4480CoversExact : CoversExact 8
    leaf4480Box leaf4480Certificate leaf4480InnerLog leaf4480Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi279RoundedFacts
    innerPair600RoundedFacts leaf4480RoundedFacts (by rfl)

private theorem leaf4480FlatSound : Sound leaf4480Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4480CertificateValid
    leaf4480InnerLogValid leaf4480CoversExact leaf4480LowerChecked

private noncomputable def leaf4481Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4481Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871275/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715421696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1043989931/536870912) }, upper := { exponent := 0, mantissa := (1007/512) } }, logOuter := sk146LogOuterCertificate, logK := sk146LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433915391/137430843392) } }, logDArg := sk146LogDArgCertificate }

private noncomputable def leaf4481InnerLog : WideLogData :=
  innerPair113Data

set_option maxRecDepth 1000000 in
private theorem leaf4481LocalValidity :
    LeafFacts leaf4481Box leaf4481Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4481Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715421696) }) = true
      norm_num [leaf4481Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4481CertificateValid :
    WideCertificateValid leaf4481Box leaf4481Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk146ValidityFacts chi280ValidityFacts
    leaf4481LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4481CoverageChecked :
    coverageCheck (innerAD leaf4481Box) leaf4481InnerLog = true := by
  rfl'

private theorem leaf4481InnerLogValid :
    leaf4481InnerLog.Valid 8 (innerAD leaf4481Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint85PositiveFacts.valid leaf4481CoverageChecked

private noncomputable def leaf4481InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726841/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf4481InputLogOnePlusV_eq :
    leaf4481InputLogOnePlusV = outerEnclosure 24
      (leaf4481Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4481RoundedFacts : LeafRoundedFacts 8
    leaf4481Certificate.logOnePlusV leaf4481InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4481InputLogOnePlusV_eq }

private noncomputable def leaf4481Inputs : Inputs :=
  inputsOfCaches globalInput sk146RoundedInputs
    chi280InputQChi innerPair113Input
    leaf4481InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4481LowerChecked :
    lowerCheck 24 leaf4481Box leaf4481Inputs = true := by
  rfl'

private theorem leaf4481CoversExact : CoversExact 8
    leaf4481Box leaf4481Certificate leaf4481InnerLog leaf4481Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk146RoundedFacts chi280RoundedFacts
    innerPair113RoundedFacts leaf4481RoundedFacts (by rfl)

private theorem leaf4481FlatSound : Sound leaf4481Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4481CertificateValid
    leaf4481InnerLogValid leaf4481CoversExact leaf4481LowerChecked

private noncomputable def leaf4482Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4482Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431145984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2054067199/1073741824) }, upper := { exponent := 0, mantissa := (31633/16384) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868067839/274862291968) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf4482InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4482LocalValidity :
    LeafFacts leaf4482Box leaf4482Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4482Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431145984) }) = true
      norm_num [leaf4482Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4482CertificateValid :
    WideCertificateValid leaf4482Box leaf4482Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi257ValidityFacts
    leaf4482LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4482CoverageChecked :
    coverageCheck (innerAD leaf4482Box) leaf4482InnerLog = true := by
  rfl'

private theorem leaf4482InnerLogValid :
    leaf4482InnerLog.Valid 8 (innerAD leaf4482Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4482CoverageChecked

private noncomputable def leaf4482InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4482InputLogOnePlusV_eq :
    leaf4482InputLogOnePlusV = outerEnclosure 24
      (leaf4482Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4482RoundedFacts : LeafRoundedFacts 8
    leaf4482Certificate.logOnePlusV leaf4482InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4482InputLogOnePlusV_eq }

private noncomputable def leaf4482Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi257InputQChi innerPair100Input
    leaf4482InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4482LowerChecked :
    lowerCheck 24 leaf4482Box leaf4482Inputs = true := by
  rfl'

private theorem leaf4482CoversExact : CoversExact 8
    leaf4482Box leaf4482Certificate leaf4482InnerLog leaf4482Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi257RoundedFacts
    innerPair100RoundedFacts leaf4482RoundedFacts (by rfl)

private theorem leaf4482FlatSound : Sound leaf4482Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4482CertificateValid
    leaf4482InnerLogValid leaf4482CoversExact leaf4482LowerChecked

private noncomputable def leaf4483Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4483Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431110656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2058523373/1073741824) }, upper := { exponent := 0, mantissa := (15851/8192) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274868032511/274862221312) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf4483InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf4483LocalValidity :
    LeafFacts leaf4483Box leaf4483Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4483Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431110656) }) = true
      norm_num [leaf4483Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4483CertificateValid :
    WideCertificateValid leaf4483Box leaf4483Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi257ValidityFacts
    leaf4483LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4483CoverageChecked :
    coverageCheck (innerAD leaf4483Box) leaf4483InnerLog = true := by
  rfl'

private theorem leaf4483InnerLogValid :
    leaf4483InnerLog.Valid 8 (innerAD leaf4483Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf4483CoverageChecked

private noncomputable def leaf4483InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4483InputLogOnePlusV_eq :
    leaf4483InputLogOnePlusV = outerEnclosure 24
      (leaf4483Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4483RoundedFacts : LeafRoundedFacts 8
    leaf4483Certificate.logOnePlusV leaf4483InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4483InputLogOnePlusV_eq }

private noncomputable def leaf4483Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi257InputQChi innerPair100Input
    leaf4483InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4483LowerChecked :
    lowerCheck 24 leaf4483Box leaf4483Inputs = true := by
  rfl'

private theorem leaf4483CoversExact : CoversExact 8
    leaf4483Box leaf4483Certificate leaf4483InnerLog leaf4483Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi257RoundedFacts
    innerPair100RoundedFacts leaf4483RoundedFacts (by rfl)

private theorem leaf4483FlatSound : Sound leaf4483Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4483CertificateValid
    leaf4483InnerLogValid leaf4483CoversExact leaf4483LowerChecked

private noncomputable def leaf4484Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4484Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431032832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2068484237/1073741824) }, upper := { exponent := 0, mantissa := (15927/8192) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274867954687/274862065664) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf4484InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4484LocalValidity :
    LeafFacts leaf4484Box leaf4484Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4484Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431032832) }) = true
      norm_num [leaf4484Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4484CertificateValid :
    WideCertificateValid leaf4484Box leaf4484Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi258ValidityFacts
    leaf4484LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4484CoverageChecked :
    coverageCheck (innerAD leaf4484Box) leaf4484InnerLog = true := by
  rfl'

private theorem leaf4484InnerLogValid :
    leaf4484InnerLog.Valid 8 (innerAD leaf4484Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4484CoverageChecked

private noncomputable def leaf4484InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (90855/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf4484InputLogOnePlusV_eq :
    leaf4484InputLogOnePlusV = outerEnclosure 24
      (leaf4484Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4484RoundedFacts : LeafRoundedFacts 8
    leaf4484Certificate.logOnePlusV leaf4484InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4484InputLogOnePlusV_eq }

private noncomputable def leaf4484Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi258InputQChi innerPair101Input
    leaf4484InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4484LowerChecked :
    lowerCheck 24 leaf4484Box leaf4484Inputs = true := by
  rfl'

private theorem leaf4484CoversExact : CoversExact 8
    leaf4484Box leaf4484Certificate leaf4484InnerLog leaf4484Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi258RoundedFacts
    innerPair101RoundedFacts leaf4484RoundedFacts (by rfl)

private theorem leaf4484FlatSound : Sound leaf4484Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4484CertificateValid
    leaf4484InnerLogValid leaf4484CoversExact leaf4484LowerChecked

private noncomputable def leaf4485Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4485Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137430996992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2073005943/1073741824) }, upper := { exponent := 0, mantissa := (7981/4096) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274867918847/274861993984) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf4485InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4485LocalValidity :
    LeafFacts leaf4485Box leaf4485Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4485Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137430996992) }) = true
      norm_num [leaf4485Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4485CertificateValid :
    WideCertificateValid leaf4485Box leaf4485Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi258ValidityFacts
    leaf4485LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4485CoverageChecked :
    coverageCheck (innerAD leaf4485Box) leaf4485InnerLog = true := by
  rfl'

private theorem leaf4485InnerLogValid :
    leaf4485InnerLog.Valid 8 (innerAD leaf4485Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4485CoverageChecked

private noncomputable def leaf4485InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814721/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4485InputLogOnePlusV_eq :
    leaf4485InputLogOnePlusV = outerEnclosure 24
      (leaf4485Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4485RoundedFacts : LeafRoundedFacts 8
    leaf4485Certificate.logOnePlusV leaf4485InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4485InputLogOnePlusV_eq }

private noncomputable def leaf4485Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi258InputQChi innerPair101Input
    leaf4485InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4485LowerChecked :
    lowerCheck 24 leaf4485Box leaf4485Inputs = true := by
  rfl'

private theorem leaf4485CoversExact : CoversExact 8
    leaf4485Box leaf4485Certificate leaf4485InnerLog leaf4485Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi258RoundedFacts
    innerPair101RoundedFacts leaf4485RoundedFacts (by rfl)

private theorem leaf4485FlatSound : Sound leaf4485Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4485CertificateValid
    leaf4485InnerLogValid leaf4485CoversExact leaf4485LowerChecked

private noncomputable def leaf4486Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4486Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137431075328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2062979547/1073741824) }, upper := { exponent := 0, mantissa := (31771/16384) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274867997183/274862150656) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf4486InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4486LocalValidity :
    LeafFacts leaf4486Box leaf4486Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4486Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137431075328) }) = true
      norm_num [leaf4486Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4486CertificateValid :
    WideCertificateValid leaf4486Box leaf4486Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi257ValidityFacts
    leaf4486LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4486CoverageChecked :
    coverageCheck (innerAD leaf4486Box) leaf4486InnerLog = true := by
  rfl'

private theorem leaf4486InnerLogValid :
    leaf4486InnerLog.Valid 8 (innerAD leaf4486Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4486CoverageChecked

private noncomputable def leaf4486InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814719/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4486InputLogOnePlusV_eq :
    leaf4486InputLogOnePlusV = outerEnclosure 24
      (leaf4486Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4486RoundedFacts : LeafRoundedFacts 8
    leaf4486Certificate.logOnePlusV leaf4486InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4486InputLogOnePlusV_eq }

private noncomputable def leaf4486Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi257InputQChi innerPair101Input
    leaf4486InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4486LowerChecked :
    lowerCheck 24 leaf4486Box leaf4486Inputs = true := by
  rfl'

private theorem leaf4486CoversExact : CoversExact 8
    leaf4486Box leaf4486Certificate leaf4486InnerLog leaf4486Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi257RoundedFacts
    innerPair101RoundedFacts leaf4486RoundedFacts (by rfl)

private theorem leaf4486FlatSound : Sound leaf4486Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4486CertificateValid
    leaf4486InnerLogValid leaf4486CoversExact leaf4486LowerChecked

private noncomputable def leaf4487Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (17/64), chiHi := (69/256) }

private noncomputable def leaf4487Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486208000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2067435721/1073741824) }, upper := { exponent := 0, mantissa := (995/512) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi257LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973592371/54972416000) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf4487InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4487LocalValidity :
    LeafFacts leaf4487Box leaf4487Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4487Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486208000) }) = true
      norm_num [leaf4487Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4487CertificateValid :
    WideCertificateValid leaf4487Box leaf4487Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi257ValidityFacts
    leaf4487LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4487CoverageChecked :
    coverageCheck (innerAD leaf4487Box) leaf4487InnerLog = true := by
  rfl'

private theorem leaf4487InnerLogValid :
    leaf4487InnerLog.Valid 8 (innerAD leaf4487Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4487CoverageChecked

private noncomputable def leaf4487InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (90855/131072) }

set_option maxRecDepth 1000000 in
private theorem leaf4487InputLogOnePlusV_eq :
    leaf4487InputLogOnePlusV = outerEnclosure 24
      (leaf4487Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4487RoundedFacts : LeafRoundedFacts 8
    leaf4487Certificate.logOnePlusV leaf4487InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4487InputLogOnePlusV_eq }

private noncomputable def leaf4487Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi257InputQChi innerPair101Input
    leaf4487InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4487LowerChecked :
    lowerCheck 24 leaf4487Box leaf4487Inputs = true := by
  rfl'

private theorem leaf4487CoversExact : CoversExact 8
    leaf4487Box leaf4487Certificate leaf4487InnerLog leaf4487Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi257RoundedFacts
    innerPair101RoundedFacts leaf4487RoundedFacts (by rfl)

private theorem leaf4487FlatSound : Sound leaf4487Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4487CertificateValid
    leaf4487InnerLogValid leaf4487CoversExact leaf4487LowerChecked

private noncomputable def leaf4488Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4488Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (65529/65536), upper := (1065402495/1065356288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2077527649/1073741824) }, upper := { exponent := 0, mantissa := (15997/8192) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (2130758783/2130712576) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf4488InnerLog : WideLogData :=
  innerPair101Data

set_option maxRecDepth 1000000 in
private theorem leaf4488LocalValidity :
    LeafFacts leaf4488Box leaf4488Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4488Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (1065402495/1065356288) }) = true
      norm_num [leaf4488Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4488CertificateValid :
    WideCertificateValid leaf4488Box leaf4488Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi258ValidityFacts
    leaf4488LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4488CoverageChecked :
    coverageCheck (innerAD leaf4488Box) leaf4488InnerLog = true := by
  rfl'

private theorem leaf4488InnerLogValid :
    leaf4488InnerLog.Valid 8 (innerAD leaf4488Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint24PositiveFacts.valid leaf4488CoverageChecked

private noncomputable def leaf4488InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629445/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4488InputLogOnePlusV_eq :
    leaf4488InputLogOnePlusV = outerEnclosure 24
      (leaf4488Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4488RoundedFacts : LeafRoundedFacts 8
    leaf4488Certificate.logOnePlusV leaf4488InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4488InputLogOnePlusV_eq }

private noncomputable def leaf4488Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi258InputQChi innerPair101Input
    leaf4488InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4488LowerChecked :
    lowerCheck 24 leaf4488Box leaf4488Inputs = true := by
  rfl'

private theorem leaf4488CoversExact : CoversExact 8
    leaf4488Box leaf4488Certificate leaf4488InnerLog leaf4488Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi258RoundedFacts
    innerPair101RoundedFacts leaf4488RoundedFacts (by rfl)

private theorem leaf4488FlatSound : Sound leaf4488Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4488CertificateValid
    leaf4488InnerLogValid leaf4488CoversExact leaf4488LowerChecked

private noncomputable def leaf4489Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (69/256), chiHi := (35/128) }

private noncomputable def leaf4489Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430925312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2082049355/1073741824) }, upper := { exponent := 0, mantissa := (501/256) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi258LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867847167/274861850624) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf4489InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4489LocalValidity :
    LeafFacts leaf4489Box leaf4489Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4489Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430925312) }) = true
      norm_num [leaf4489Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4489CertificateValid :
    WideCertificateValid leaf4489Box leaf4489Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi258ValidityFacts
    leaf4489LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4489CoverageChecked :
    coverageCheck (innerAD leaf4489Box) leaf4489InnerLog = true := by
  rfl'

private theorem leaf4489InnerLogValid :
    leaf4489InnerLog.Valid 8 (innerAD leaf4489Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4489CoverageChecked

private noncomputable def leaf4489InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629447/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4489InputLogOnePlusV_eq :
    leaf4489InputLogOnePlusV = outerEnclosure 24
      (leaf4489Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4489RoundedFacts : LeafRoundedFacts 8
    leaf4489Certificate.logOnePlusV leaf4489InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4489InputLogOnePlusV_eq }

private noncomputable def leaf4489Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi258InputQChi innerPair108Input
    leaf4489InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4489LowerChecked :
    lowerCheck 24 leaf4489Box leaf4489Inputs = true := by
  rfl'

private theorem leaf4489CoversExact : CoversExact 8
    leaf4489Box leaf4489Certificate leaf4489InnerLog leaf4489Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi258RoundedFacts
    innerPair108RoundedFacts leaf4489RoundedFacts (by rfl)

private theorem leaf4489FlatSound : Sound leaf4489Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4489CertificateValid
    leaf4489InnerLogValid leaf4489CoversExact leaf4489LowerChecked

private noncomputable def leaf4490Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (221/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4490Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (65529/65536), upper := (9162461457/9162061312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2082901275/1073741824) }, upper := { exponent := 0, mantissa := (32075/16384) } }, logOuter := sk179LogOuterCertificate, logK := sk179LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (18324522769/18324122624) } }, logDArg := sk179LogDArgCertificate }

private noncomputable def leaf4490InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4490LocalValidity :
    LeafFacts leaf4490Box leaf4490Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4490Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (9162461457/9162061312) }) = true
      norm_num [leaf4490Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4490CertificateValid :
    WideCertificateValid leaf4490Box leaf4490Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk179ValidityFacts chi279ValidityFacts
    leaf4490LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4490CoverageChecked :
    coverageCheck (innerAD leaf4490Box) leaf4490InnerLog = true := by
  rfl'

private theorem leaf4490InnerLogValid :
    leaf4490InnerLog.Valid 8 (innerAD leaf4490Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4490CoverageChecked

private noncomputable def leaf4490InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629447/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4490InputLogOnePlusV_eq :
    leaf4490InputLogOnePlusV = outerEnclosure 24
      (leaf4490Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4490RoundedFacts : LeafRoundedFacts 8
    leaf4490Certificate.logOnePlusV leaf4490InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4490InputLogOnePlusV_eq }

private noncomputable def leaf4490Inputs : Inputs :=
  inputsOfCaches globalInput sk179RoundedInputs
    chi279InputQChi innerPair108Input
    leaf4490InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4490LowerChecked :
    lowerCheck 24 leaf4490Box leaf4490Inputs = true := by
  rfl'

private theorem leaf4490CoversExact : CoversExact 8
    leaf4490Box leaf4490Certificate leaf4490InnerLog leaf4490Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk179RoundedFacts chi279RoundedFacts
    innerPair108RoundedFacts leaf4490RoundedFacts (by rfl)

private theorem leaf4490FlatSound : Sound leaf4490Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4490CertificateValid
    leaf4490InnerLogValid leaf4490CoversExact leaf4490LowerChecked

private noncomputable def leaf4491Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (221/64), kHi := (111/32), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4491Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137430883328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2087488513/1073741824) }, upper := { exponent := 0, mantissa := (16073/8192) } }, logOuter := sk180LogOuterCertificate, logK := sk180LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274867805183/274861766656) } }, logDArg := sk180LogDArgCertificate }

private noncomputable def leaf4491InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4491LocalValidity :
    LeafFacts leaf4491Box leaf4491Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4491Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137430883328) }) = true
      norm_num [leaf4491Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4491CertificateValid :
    WideCertificateValid leaf4491Box leaf4491Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk180ValidityFacts chi279ValidityFacts
    leaf4491LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4491CoverageChecked :
    coverageCheck (innerAD leaf4491Box) leaf4491InnerLog = true := by
  rfl'

private theorem leaf4491InnerLogValid :
    leaf4491InnerLog.Valid 8 (innerAD leaf4491Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4491CoverageChecked

private noncomputable def leaf4491InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629449/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4491InputLogOnePlusV_eq :
    leaf4491InputLogOnePlusV = outerEnclosure 24
      (leaf4491Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4491RoundedFacts : LeafRoundedFacts 8
    leaf4491Certificate.logOnePlusV leaf4491InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4491InputLogOnePlusV_eq }

private noncomputable def leaf4491Inputs : Inputs :=
  inputsOfCaches globalInput sk180RoundedInputs
    chi279InputQChi innerPair108Input
    leaf4491InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4491LowerChecked :
    lowerCheck 24 leaf4491Box leaf4491Inputs = true := by
  rfl'

private theorem leaf4491CoversExact : CoversExact 8
    leaf4491Box leaf4491Certificate leaf4491InnerLog leaf4491Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk180RoundedFacts chi279RoundedFacts
    innerPair108RoundedFacts leaf4491RoundedFacts (by rfl)

private theorem leaf4491FlatSound : Sound leaf4491Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4491CertificateValid
    leaf4491InnerLogValid leaf4491CoversExact leaf4491LowerChecked

private noncomputable def leaf4492Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4492Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (536871277/536870912) }, vSqrt := { lower := (65529/65536), upper := (68718493695/68715384832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1048642701/536870912) }, upper := { exponent := 0, mantissa := (2023/1024) } }, logOuter := sk147LogOuterCertificate, logK := sk147LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (137433878527/137430769664) } }, logDArg := sk147LogDArgCertificate }

private noncomputable def leaf4492InnerLog : WideLogData :=
  innerPair239Data

set_option maxRecDepth 1000000 in
private theorem leaf4492LocalValidity :
    LeafFacts leaf4492Box leaf4492Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4492Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (68718493695/68715384832) }) = true
      norm_num [leaf4492Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4492CertificateValid :
    WideCertificateValid leaf4492Box leaf4492Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk147ValidityFacts chi280ValidityFacts
    leaf4492LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4492CoverageChecked :
    coverageCheck (innerAD leaf4492Box) leaf4492InnerLog = true := by
  rfl'

private theorem leaf4492InnerLogValid :
    leaf4492InnerLog.Valid 8 (innerAD leaf4492Box) :=
  wideLogDataValid_of_cachedCheck endpoint71PositiveFacts
    endpoint275PositiveFacts.valid leaf4492CoverageChecked

private noncomputable def leaf4492InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907365/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4492InputLogOnePlusV_eq :
    leaf4492InputLogOnePlusV = outerEnclosure 24
      (leaf4492Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4492RoundedFacts : LeafRoundedFacts 8
    leaf4492Certificate.logOnePlusV leaf4492InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4492InputLogOnePlusV_eq }

private noncomputable def leaf4492Inputs : Inputs :=
  inputsOfCaches globalInput sk147RoundedInputs
    chi280InputQChi innerPair239Input
    leaf4492InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4492LowerChecked :
    lowerCheck 24 leaf4492Box leaf4492Inputs = true := by
  rfl'

private theorem leaf4492CoversExact : CoversExact 8
    leaf4492Box leaf4492Certificate leaf4492InnerLog leaf4492Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk147RoundedFacts chi280RoundedFacts
    innerPair239RoundedFacts leaf4492RoundedFacts (by rfl)

private theorem leaf4492FlatSound : Sound leaf4492Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4492CertificateValid
    leaf4492InnerLogValid leaf4492CoversExact leaf4492LowerChecked

private noncomputable def leaf4493Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4493Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (65529/65536), upper := (137436921855/137430846976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2092075751/1073741824) }, upper := { exponent := 0, mantissa := (32217/16384) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (274867768831/274861693952) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf4493InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4493LocalValidity :
    LeafFacts leaf4493Box leaf4493Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4493Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (137436921855/137430846976) }) = true
      norm_num [leaf4493Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4493CertificateValid :
    WideCertificateValid leaf4493Box leaf4493Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi279ValidityFacts
    leaf4493LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4493CoverageChecked :
    coverageCheck (innerAD leaf4493Box) leaf4493InnerLog = true := by
  rfl'

private theorem leaf4493InnerLogValid :
    leaf4493InnerLog.Valid 8 (innerAD leaf4493Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4493CoverageChecked

private noncomputable def leaf4493InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907363/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf4493InputLogOnePlusV_eq :
    leaf4493InputLogOnePlusV = outerEnclosure 24
      (leaf4493Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4493RoundedFacts : LeafRoundedFacts 8
    leaf4493Certificate.logOnePlusV leaf4493InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4493InputLogOnePlusV_eq }

private noncomputable def leaf4493Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi279InputQChi innerPair108Input
    leaf4493InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4493LowerChecked :
    lowerCheck 24 leaf4493Box leaf4493Inputs = true := by
  rfl'

private theorem leaf4493CoversExact : CoversExact 8
    leaf4493Box leaf4493Certificate leaf4493InnerLog leaf4493Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi279RoundedFacts
    innerPair108RoundedFacts leaf4493RoundedFacts (by rfl)

private theorem leaf4493FlatSound : Sound leaf4493Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4493CertificateValid
    leaf4493InnerLogValid leaf4493CoversExact leaf4493LowerChecked

private noncomputable def leaf4494Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (35/128), chiHi := (71/256) }

private noncomputable def leaf4494Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810270208) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2096662989/1073741824) }, upper := { exponent := 0, mantissa := (1009/512) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi279LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622577493/91620540416) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf4494InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4494LocalValidity :
    LeafFacts leaf4494Box leaf4494Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4494Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810270208) }) = true
      norm_num [leaf4494Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4494CertificateValid :
    WideCertificateValid leaf4494Box leaf4494Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi279ValidityFacts
    leaf4494LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4494CoverageChecked :
    coverageCheck (innerAD leaf4494Box) leaf4494InnerLog = true := by
  rfl'

private theorem leaf4494InnerLogValid :
    leaf4494InnerLog.Valid 8 (innerAD leaf4494Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4494CoverageChecked

private noncomputable def leaf4494InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814727/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf4494InputLogOnePlusV_eq :
    leaf4494InputLogOnePlusV = outerEnclosure 24
      (leaf4494Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4494RoundedFacts : LeafRoundedFacts 8
    leaf4494Certificate.logOnePlusV leaf4494InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4494InputLogOnePlusV_eq }

private noncomputable def leaf4494Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi279InputQChi innerPair108Input
    leaf4494InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4494LowerChecked :
    lowerCheck 24 leaf4494Box leaf4494Inputs = true := by
  rfl'

private theorem leaf4494CoversExact : CoversExact 8
    leaf4494Box leaf4494Certificate leaf4494InnerLog leaf4494Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi279RoundedFacts
    innerPair108RoundedFacts leaf4494RoundedFacts (by rfl)

private theorem leaf4494FlatSound : Sound leaf4494Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4494CertificateValid
    leaf4494InnerLogValid leaf4494CoversExact leaf4494LowerChecked

private noncomputable def leaf4495Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (223/64), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4495Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (65529/65536), upper := (27487384371/27486146560) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2106623853/1073741824) }, upper := { exponent := 0, mantissa := (4055/2048) } }, logOuter := sk181LogOuterCertificate, logK := sk181LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (54973530931/54972293120) } }, logDArg := sk181LogDArgCertificate }

private noncomputable def leaf4495InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4495LocalValidity :
    LeafFacts leaf4495Box leaf4495Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4495Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (27487384371/27486146560) }) = true
      norm_num [leaf4495Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4495CertificateValid :
    WideCertificateValid leaf4495Box leaf4495Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk181ValidityFacts chi280ValidityFacts
    leaf4495LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4495CoverageChecked :
    coverageCheck (innerAD leaf4495Box) leaf4495InnerLog = true := by
  rfl'

private theorem leaf4495InnerLogValid :
    leaf4495InnerLog.Valid 8 (innerAD leaf4495Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4495CoverageChecked

private noncomputable def leaf4495InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629459/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4495InputLogOnePlusV_eq :
    leaf4495InputLogOnePlusV = outerEnclosure 24
      (leaf4495Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4495RoundedFacts : LeafRoundedFacts 8
    leaf4495Certificate.logOnePlusV leaf4495InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4495InputLogOnePlusV_eq }

private noncomputable def leaf4495Inputs : Inputs :=
  inputsOfCaches globalInput sk181RoundedInputs
    chi280InputQChi innerPair108Input
    leaf4495InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4495LowerChecked :
    lowerCheck 24 leaf4495Box leaf4495Inputs = true := by
  rfl'

private theorem leaf4495CoversExact : CoversExact 8
    leaf4495Box leaf4495Certificate leaf4495InnerLog leaf4495Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk181RoundedFacts chi280RoundedFacts
    innerPair108RoundedFacts leaf4495RoundedFacts (by rfl)

private theorem leaf4495FlatSound : Sound leaf4495Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4495CertificateValid
    leaf4495InnerLogValid leaf4495CoversExact leaf4495LowerChecked

private noncomputable def leaf4496Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (223/64), kHi := (7/2), chiLo := (71/256), chiHi := (9/32) }

private noncomputable def leaf4496Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137430695936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2111276623/1073741824) }, upper := { exponent := 0, mantissa := (127/64) } }, logOuter := sk182LogOuterCertificate, logK := sk182LogKCertificate, logChi := chi280LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274867617791/274861391872) } }, logDArg := sk182LogDArgCertificate }

private noncomputable def leaf4496InnerLog : WideLogData :=
  innerPair108Data

set_option maxRecDepth 1000000 in
private theorem leaf4496LocalValidity :
    LeafFacts leaf4496Box leaf4496Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf4496Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137430695936) }) = true
      norm_num [leaf4496Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf4496CertificateValid :
    WideCertificateValid leaf4496Box leaf4496Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk182ValidityFacts chi280ValidityFacts
    leaf4496LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf4496CoverageChecked :
    coverageCheck (innerAD leaf4496Box) leaf4496InnerLog = true := by
  rfl'

private theorem leaf4496InnerLogValid :
    leaf4496InnerLog.Valid 8 (innerAD leaf4496Box) :=
  wideLogDataValid_of_cachedCheck endpoint23PositiveFacts
    endpoint24PositiveFacts.valid leaf4496CoverageChecked

private noncomputable def leaf4496InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629461/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf4496InputLogOnePlusV_eq :
    leaf4496InputLogOnePlusV = outerEnclosure 24
      (leaf4496Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf4496RoundedFacts : LeafRoundedFacts 8
    leaf4496Certificate.logOnePlusV leaf4496InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf4496InputLogOnePlusV_eq }

private noncomputable def leaf4496Inputs : Inputs :=
  inputsOfCaches globalInput sk182RoundedInputs
    chi280InputQChi innerPair108Input
    leaf4496InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf4496LowerChecked :
    lowerCheck 24 leaf4496Box leaf4496Inputs = true := by
  rfl'

private theorem leaf4496CoversExact : CoversExact 8
    leaf4496Box leaf4496Certificate leaf4496InnerLog leaf4496Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk182RoundedFacts chi280RoundedFacts
    innerPair108RoundedFacts leaf4496RoundedFacts (by rfl)

private theorem leaf4496FlatSound : Sound leaf4496Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf4496CertificateValid
    leaf4496InnerLogValid leaf4496CoversExact leaf4496LowerChecked

private noncomputable def component91Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component91Node0_sound : Sound component91Node0Box :=
  sound_of_literal_split component91Node0Box leaf4444Box leaf4445Box
    .k (217/64) (by rfl) (by rfl)
    leaf4444FlatSound leaf4445FlatSound

private noncomputable def component91Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node1_sound : Sound component91Node1Box :=
  sound_of_literal_split component91Node1Box leaf4446Box leaf4447Box
    .k (217/64) (by rfl) (by rfl)
    leaf4446FlatSound leaf4447FlatSound

private noncomputable def component91Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node2_sound : Sound component91Node2Box :=
  sound_of_literal_split component91Node2Box component91Node0Box component91Node1Box
    .chi (65/256) (by rfl) (by rfl)
    component91Node0_sound component91Node1_sound

private noncomputable def component91Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component91Node3_sound : Sound component91Node3Box :=
  sound_of_literal_split component91Node3Box leaf4448Box leaf4449Box
    .k (219/64) (by rfl) (by rfl)
    leaf4448FlatSound leaf4449FlatSound

private noncomputable def component91Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node4_sound : Sound component91Node4Box :=
  sound_of_literal_split component91Node4Box leaf4450Box leaf4451Box
    .k (219/64) (by rfl) (by rfl)
    leaf4450FlatSound leaf4451FlatSound

private noncomputable def component91Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node5_sound : Sound component91Node5Box :=
  sound_of_literal_split component91Node5Box component91Node3Box component91Node4Box
    .chi (65/256) (by rfl) (by rfl)
    component91Node3_sound component91Node4_sound

private noncomputable def component91Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node6_sound : Sound component91Node6Box :=
  sound_of_literal_split component91Node6Box component91Node2Box component91Node5Box
    .k (109/32) (by rfl) (by rfl)
    component91Node2_sound component91Node5_sound

private noncomputable def component91Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component91Node7_sound : Sound component91Node7Box :=
  sound_of_literal_split component91Node7Box leaf4452Box leaf4453Box
    .chi (67/256) (by rfl) (by rfl)
    leaf4452FlatSound leaf4453FlatSound

private noncomputable def component91Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component91Node8_sound : Sound component91Node8Box :=
  sound_of_literal_split component91Node8Box leaf4454Box leaf4455Box
    .k (219/64) (by rfl) (by rfl)
    leaf4454FlatSound leaf4455FlatSound

private noncomputable def component91Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component91Node9_sound : Sound component91Node9Box :=
  sound_of_literal_split component91Node9Box leaf4456Box leaf4457Box
    .k (219/64) (by rfl) (by rfl)
    leaf4456FlatSound leaf4457FlatSound

private noncomputable def component91Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component91Node10_sound : Sound component91Node10Box :=
  sound_of_literal_split component91Node10Box component91Node8Box component91Node9Box
    .chi (67/256) (by rfl) (by rfl)
    component91Node8_sound component91Node9_sound

private noncomputable def component91Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component91Node11_sound : Sound component91Node11Box :=
  sound_of_literal_split component91Node11Box component91Node7Box component91Node10Box
    .k (109/32) (by rfl) (by rfl)
    component91Node7_sound component91Node10_sound

private noncomputable def component91Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component91Node12_sound : Sound component91Node12Box :=
  sound_of_literal_split component91Node12Box component91Node6Box component91Node11Box
    .chi (33/128) (by rfl) (by rfl)
    component91Node6_sound component91Node11_sound

private noncomputable def component91Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component91Node13_sound : Sound component91Node13Box :=
  sound_of_literal_split component91Node13Box leaf4458Box leaf4459Box
    .k (221/64) (by rfl) (by rfl)
    leaf4458FlatSound leaf4459FlatSound

private noncomputable def component91Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node14_sound : Sound component91Node14Box :=
  sound_of_literal_split component91Node14Box leaf4460Box leaf4461Box
    .k (221/64) (by rfl) (by rfl)
    leaf4460FlatSound leaf4461FlatSound

private noncomputable def component91Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node15_sound : Sound component91Node15Box :=
  sound_of_literal_split component91Node15Box component91Node13Box component91Node14Box
    .chi (65/256) (by rfl) (by rfl)
    component91Node13_sound component91Node14_sound

private noncomputable def component91Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (1/4), chiHi := (65/256) }

set_option maxRecDepth 1000000 in
private theorem component91Node16_sound : Sound component91Node16Box :=
  sound_of_literal_split component91Node16Box leaf4462Box leaf4463Box
    .k (223/64) (by rfl) (by rfl)
    leaf4462FlatSound leaf4463FlatSound

private noncomputable def component91Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (65/256), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node17_sound : Sound component91Node17Box :=
  sound_of_literal_split component91Node17Box leaf4464Box leaf4465Box
    .k (223/64) (by rfl) (by rfl)
    leaf4464FlatSound leaf4465FlatSound

private noncomputable def component91Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node18_sound : Sound component91Node18Box :=
  sound_of_literal_split component91Node18Box component91Node16Box component91Node17Box
    .chi (65/256) (by rfl) (by rfl)
    component91Node16_sound component91Node17_sound

private noncomputable def component91Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (1/4), chiHi := (33/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node19_sound : Sound component91Node19Box :=
  sound_of_literal_split component91Node19Box component91Node15Box component91Node18Box
    .k (111/32) (by rfl) (by rfl)
    component91Node15_sound component91Node18_sound

private noncomputable def component91Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component91Node20_sound : Sound component91Node20Box :=
  sound_of_literal_split component91Node20Box leaf4466Box leaf4467Box
    .k (221/64) (by rfl) (by rfl)
    leaf4466FlatSound leaf4467FlatSound

private noncomputable def component91Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component91Node21_sound : Sound component91Node21Box :=
  sound_of_literal_split component91Node21Box leaf4468Box leaf4469Box
    .k (221/64) (by rfl) (by rfl)
    leaf4468FlatSound leaf4469FlatSound

private noncomputable def component91Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component91Node22_sound : Sound component91Node22Box :=
  sound_of_literal_split component91Node22Box component91Node20Box component91Node21Box
    .chi (67/256) (by rfl) (by rfl)
    component91Node20_sound component91Node21_sound

private noncomputable def component91Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (33/128), chiHi := (67/256) }

set_option maxRecDepth 1000000 in
private theorem component91Node23_sound : Sound component91Node23Box :=
  sound_of_literal_split component91Node23Box leaf4470Box leaf4471Box
    .k (223/64) (by rfl) (by rfl)
    leaf4470FlatSound leaf4471FlatSound

private noncomputable def component91Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (67/256), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component91Node24_sound : Sound component91Node24Box :=
  sound_of_literal_split component91Node24Box leaf4472Box leaf4473Box
    .k (223/64) (by rfl) (by rfl)
    leaf4472FlatSound leaf4473FlatSound

private noncomputable def component91Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component91Node25_sound : Sound component91Node25Box :=
  sound_of_literal_split component91Node25Box component91Node23Box component91Node24Box
    .chi (67/256) (by rfl) (by rfl)
    component91Node23_sound component91Node24_sound

private noncomputable def component91Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (33/128), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component91Node26_sound : Sound component91Node26Box :=
  sound_of_literal_split component91Node26Box component91Node22Box component91Node25Box
    .k (111/32) (by rfl) (by rfl)
    component91Node22_sound component91Node25_sound

private noncomputable def component91Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component91Node27_sound : Sound component91Node27Box :=
  sound_of_literal_split component91Node27Box component91Node19Box component91Node26Box
    .chi (33/128) (by rfl) (by rfl)
    component91Node19_sound component91Node26_sound

private noncomputable def component91Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (1/4), chiHi := (17/64) }

set_option maxRecDepth 1000000 in
private theorem component91Node28_sound : Sound component91Node28Box :=
  sound_of_literal_split component91Node28Box component91Node12Box component91Node27Box
    .k (55/16) (by rfl) (by rfl)
    component91Node12_sound component91Node27_sound

private noncomputable def component91Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node29_sound : Sound component91Node29Box :=
  sound_of_literal_split component91Node29Box leaf4474Box leaf4475Box
    .chi (69/256) (by rfl) (by rfl)
    leaf4474FlatSound leaf4475FlatSound

private noncomputable def component91Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node30_sound : Sound component91Node30Box :=
  sound_of_literal_split component91Node30Box leaf4476Box leaf4477Box
    .chi (69/256) (by rfl) (by rfl)
    leaf4476FlatSound leaf4477FlatSound

private noncomputable def component91Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node31_sound : Sound component91Node31Box :=
  sound_of_literal_split component91Node31Box component91Node29Box component91Node30Box
    .k (109/32) (by rfl) (by rfl)
    component91Node29_sound component91Node30_sound

private noncomputable def component91Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (109/32), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component91Node32_sound : Sound component91Node32Box :=
  sound_of_literal_split component91Node32Box leaf4478Box leaf4479Box
    .chi (71/256) (by rfl) (by rfl)
    leaf4478FlatSound leaf4479FlatSound

private noncomputable def component91Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (109/32), kHi := (55/16), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component91Node33_sound : Sound component91Node33Box :=
  sound_of_literal_split component91Node33Box leaf4480Box leaf4481Box
    .chi (71/256) (by rfl) (by rfl)
    leaf4480FlatSound leaf4481FlatSound

private noncomputable def component91Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component91Node34_sound : Sound component91Node34Box :=
  sound_of_literal_split component91Node34Box component91Node32Box component91Node33Box
    .k (109/32) (by rfl) (by rfl)
    component91Node32_sound component91Node33_sound

private noncomputable def component91Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component91Node35_sound : Sound component91Node35Box :=
  sound_of_literal_split component91Node35Box component91Node31Box component91Node34Box
    .chi (35/128) (by rfl) (by rfl)
    component91Node31_sound component91Node34_sound

private noncomputable def component91Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component91Node36_sound : Sound component91Node36Box :=
  sound_of_literal_split component91Node36Box leaf4482Box leaf4483Box
    .k (221/64) (by rfl) (by rfl)
    leaf4482FlatSound leaf4483FlatSound

private noncomputable def component91Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node37_sound : Sound component91Node37Box :=
  sound_of_literal_split component91Node37Box leaf4484Box leaf4485Box
    .k (221/64) (by rfl) (by rfl)
    leaf4484FlatSound leaf4485FlatSound

private noncomputable def component91Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node38_sound : Sound component91Node38Box :=
  sound_of_literal_split component91Node38Box component91Node36Box component91Node37Box
    .chi (69/256) (by rfl) (by rfl)
    component91Node36_sound component91Node37_sound

private noncomputable def component91Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (17/64), chiHi := (69/256) }

set_option maxRecDepth 1000000 in
private theorem component91Node39_sound : Sound component91Node39Box :=
  sound_of_literal_split component91Node39Box leaf4486Box leaf4487Box
    .k (223/64) (by rfl) (by rfl)
    leaf4486FlatSound leaf4487FlatSound

private noncomputable def component91Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (69/256), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node40_sound : Sound component91Node40Box :=
  sound_of_literal_split component91Node40Box leaf4488Box leaf4489Box
    .k (223/64) (by rfl) (by rfl)
    leaf4488FlatSound leaf4489FlatSound

private noncomputable def component91Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node41_sound : Sound component91Node41Box :=
  sound_of_literal_split component91Node41Box component91Node39Box component91Node40Box
    .chi (69/256) (by rfl) (by rfl)
    component91Node39_sound component91Node40_sound

private noncomputable def component91Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (17/64), chiHi := (35/128) }

set_option maxRecDepth 1000000 in
private theorem component91Node42_sound : Sound component91Node42Box :=
  sound_of_literal_split component91Node42Box component91Node38Box component91Node41Box
    .k (111/32) (by rfl) (by rfl)
    component91Node38_sound component91Node41_sound

private noncomputable def component91Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component91Node43_sound : Sound component91Node43Box :=
  sound_of_literal_split component91Node43Box leaf4490Box leaf4491Box
    .k (221/64) (by rfl) (by rfl)
    leaf4490FlatSound leaf4491FlatSound

private noncomputable def component91Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (111/32), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component91Node44_sound : Sound component91Node44Box :=
  sound_of_literal_split component91Node44Box component91Node43Box leaf4492Box
    .chi (71/256) (by rfl) (by rfl)
    component91Node43_sound leaf4492FlatSound

private noncomputable def component91Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (35/128), chiHi := (71/256) }

set_option maxRecDepth 1000000 in
private theorem component91Node45_sound : Sound component91Node45Box :=
  sound_of_literal_split component91Node45Box leaf4493Box leaf4494Box
    .k (223/64) (by rfl) (by rfl)
    leaf4493FlatSound leaf4494FlatSound

private noncomputable def component91Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (71/256), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component91Node46_sound : Sound component91Node46Box :=
  sound_of_literal_split component91Node46Box leaf4495Box leaf4496Box
    .k (223/64) (by rfl) (by rfl)
    leaf4495FlatSound leaf4496FlatSound

private noncomputable def component91Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (111/32), kHi := (7/2), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component91Node47_sound : Sound component91Node47Box :=
  sound_of_literal_split component91Node47Box component91Node45Box component91Node46Box
    .chi (71/256) (by rfl) (by rfl)
    component91Node45_sound component91Node46_sound

private noncomputable def component91Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (35/128), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component91Node48_sound : Sound component91Node48Box :=
  sound_of_literal_split component91Node48Box component91Node44Box component91Node47Box
    .k (111/32) (by rfl) (by rfl)
    component91Node44_sound component91Node47_sound

private noncomputable def component91Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component91Node49_sound : Sound component91Node49Box :=
  sound_of_literal_split component91Node49Box component91Node42Box component91Node48Box
    .chi (35/128) (by rfl) (by rfl)
    component91Node42_sound component91Node48_sound

private noncomputable def component91Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (17/64), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
private theorem component91Node50_sound : Sound component91Node50Box :=
  sound_of_literal_split component91Node50Box component91Node35Box component91Node49Box
    .k (55/16) (by rfl) (by rfl)
    component91Node35_sound component91Node49_sound

noncomputable def component91Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (1/4), chiHi := (9/32) }

set_option maxRecDepth 1000000 in
theorem component91_sound : Sound component91Box :=
  sound_of_literal_split component91Box component91Node28Box component91Node50Box
    .chi (17/64) (by rfl) (by rfl)
    component91Node28_sound component91Node50_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
