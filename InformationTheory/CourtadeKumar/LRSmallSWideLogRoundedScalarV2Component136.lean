import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch12
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch13
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheSKBatch1

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

private noncomputable def leaf6702Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (5/8), chiHi := (41/64) }

private noncomputable def leaf6702Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (16383/16384), upper := (67109043/67108864) }, vSqrt := { lower := (65529/65536), upper := (34358231037/34355623936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (192897359/134217728) }, upper := { exponent := 1, mantissa := (3033/2048) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi323LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68713854973/68711247872) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6702InnerLog : WideLogData :=
  innerPair781Data

set_option maxRecDepth 1000000 in
private theorem leaf6702LocalValidity :
    LeafFacts leaf6702Box leaf6702Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6702Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34358231037/34355623936) }) = true
      norm_num [leaf6702Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6702CertificateValid :
    WideCertificateValid leaf6702Box leaf6702Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi323ValidityFacts
    leaf6702LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6702CoverageChecked :
    coverageCheck (innerAD leaf6702Box) leaf6702InnerLog = true := by
  rfl'

private theorem leaf6702InnerLogValid :
    leaf6702InnerLog.Valid 8 (innerAD leaf6702Box) :=
  wideLogDataValid_of_cachedCheck endpoint490PositiveFacts
    endpoint481PositiveFacts.valid leaf6702CoverageChecked

private noncomputable def leaf6702InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629717/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6702InputLogOnePlusV_eq :
    leaf6702InputLogOnePlusV = outerEnclosure 24
      (leaf6702Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6702RoundedFacts : LeafRoundedFacts 8
    leaf6702Certificate.logOnePlusV leaf6702InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6702InputLogOnePlusV_eq }

private noncomputable def leaf6702Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi323InputQChi innerPair781Input
    leaf6702InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6702LowerChecked :
    lowerCheck 24 leaf6702Box leaf6702Inputs = true := by
  rfl'

private theorem leaf6702CoversExact : CoversExact 8
    leaf6702Box leaf6702Certificate leaf6702InnerLog leaf6702Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi323RoundedFacts
    innerPair781RoundedFacts leaf6702RoundedFacts (by rfl)

private theorem leaf6702FlatSound : Sound leaf6702Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6702CertificateValid
    leaf6702InnerLogValid leaf6702CoversExact leaf6702LowerChecked

private noncomputable def leaf6703Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6703Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109045/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588880896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (196042893/134217728) }, upper := { exponent := 1, mantissa := (1541/1024) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178307583/17177761792) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6703InnerLog : WideLogData :=
  innerPair736Data

set_option maxRecDepth 1000000 in
private theorem leaf6703LocalValidity :
    LeafFacts leaf6703Box leaf6703Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6703Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588880896) }) = true
      norm_num [leaf6703Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6703CertificateValid :
    WideCertificateValid leaf6703Box leaf6703Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi324ValidityFacts
    leaf6703LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6703CoverageChecked :
    coverageCheck (innerAD leaf6703Box) leaf6703InnerLog = true := by
  rfl'

private theorem leaf6703InnerLogValid :
    leaf6703InnerLog.Valid 8 (innerAD leaf6703Box) :=
  wideLogDataValid_of_cachedCheck endpoint471PositiveFacts
    endpoint491PositiveFacts.valid leaf6703CoverageChecked

private noncomputable def leaf6703InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814807/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6703InputLogOnePlusV_eq :
    leaf6703InputLogOnePlusV = outerEnclosure 24
      (leaf6703Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6703RoundedFacts : LeafRoundedFacts 8
    leaf6703Certificate.logOnePlusV leaf6703InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6703InputLogOnePlusV_eq }

private noncomputable def leaf6703Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi324InputQChi innerPair736Input
    leaf6703InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6703LowerChecked :
    lowerCheck 24 leaf6703Box leaf6703Inputs = true := by
  rfl'

private theorem leaf6703CoversExact : CoversExact 8
    leaf6703Box leaf6703Certificate leaf6703InnerLog leaf6703Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi324RoundedFacts
    innerPair736RoundedFacts leaf6703RoundedFacts (by rfl)

private theorem leaf6703FlatSound : Sound leaf6703Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6703CertificateValid
    leaf6703InnerLogValid leaf6703CoversExact leaf6703LowerChecked

private noncomputable def leaf6704Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (5/8), chiHi := (41/64) }

private noncomputable def leaf6704Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109045/67108864) }, vSqrt := { lower := (65529/65536), upper := (2863142229/2862961664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (195518637/134217728) }, upper := { exponent := 1, mantissa := (1537/1024) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi323LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5726103893/5725923328) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6704InnerLog : WideLogData :=
  innerPair828Data

set_option maxRecDepth 1000000 in
private theorem leaf6704LocalValidity :
    LeafFacts leaf6704Box leaf6704Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6704Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2863142229/2862961664) }) = true
      norm_num [leaf6704Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6704CertificateValid :
    WideCertificateValid leaf6704Box leaf6704Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi323ValidityFacts
    leaf6704LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6704CoverageChecked :
    coverageCheck (innerAD leaf6704Box) leaf6704InnerLog = true := by
  rfl'

private theorem leaf6704InnerLogValid :
    leaf6704InnerLog.Valid 8 (innerAD leaf6704Box) :=
  wideLogDataValid_of_cachedCheck endpoint523PositiveFacts
    endpoint529PositiveFacts.valid leaf6704CoverageChecked

private noncomputable def leaf6704InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814805/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6704InputLogOnePlusV_eq :
    leaf6704InputLogOnePlusV = outerEnclosure 24
      (leaf6704Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6704RoundedFacts : LeafRoundedFacts 8
    leaf6704Certificate.logOnePlusV leaf6704InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6704InputLogOnePlusV_eq }

private noncomputable def leaf6704Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi323InputQChi innerPair828Input
    leaf6704InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6704LowerChecked :
    lowerCheck 24 leaf6704Box leaf6704Inputs = true := by
  rfl'

private theorem leaf6704CoversExact : CoversExact 8
    leaf6704Box leaf6704Certificate leaf6704InnerLog leaf6704Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi323RoundedFacts
    innerPair828RoundedFacts leaf6704RoundedFacts (by rfl)

private theorem leaf6704FlatSound : Sound leaf6704Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6704CertificateValid
    leaf6704InnerLogValid leaf6704CoversExact leaf6704LowerChecked

private noncomputable def leaf6705Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6705Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109047/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588859392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (198729703/134217728) }, upper := { exponent := 1, mantissa := (781/512) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178286079/17177718784) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6705InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6705LocalValidity :
    LeafFacts leaf6705Box leaf6705Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6705Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588859392) }) = true
      norm_num [leaf6705Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6705CertificateValid :
    WideCertificateValid leaf6705Box leaf6705Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi324ValidityFacts
    leaf6705LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6705CoverageChecked :
    coverageCheck (innerAD leaf6705Box) leaf6705InnerLog = true := by
  rfl'

private theorem leaf6705InnerLogValid :
    leaf6705InnerLog.Valid 8 (innerAD leaf6705Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6705CoverageChecked

private noncomputable def leaf6705InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629635/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6705InputLogOnePlusV_eq :
    leaf6705InputLogOnePlusV = outerEnclosure 24
      (leaf6705Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6705RoundedFacts : LeafRoundedFacts 8
    leaf6705Certificate.logOnePlusV leaf6705InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6705InputLogOnePlusV_eq }

private noncomputable def leaf6705Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi324InputQChi innerPair376Input
    leaf6705InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6705LowerChecked :
    lowerCheck 24 leaf6705Box leaf6705Inputs = true := by
  rfl'

private theorem leaf6705CoversExact : CoversExact 8
    leaf6705Box leaf6705Certificate leaf6705InnerLog leaf6705Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi324RoundedFacts
    innerPair376RoundedFacts leaf6705RoundedFacts (by rfl)

private theorem leaf6705FlatSound : Sound leaf6705Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6705CertificateValid
    leaf6705InnerLogValid leaf6705CoversExact leaf6705LowerChecked

private noncomputable def leaf6706Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6706Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109047/67108864) }, vSqrt := { lower := (65529/65536), upper := (954380743/954317312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (199188427/134217728) }, upper := { exponent := 1, mantissa := (3131/2048) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1908698055/1908634624) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6706InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6706LocalValidity :
    LeafFacts leaf6706Box leaf6706Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6706Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (954380743/954317312) }) = true
      norm_num [leaf6706Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6706CertificateValid :
    WideCertificateValid leaf6706Box leaf6706Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi325ValidityFacts
    leaf6706LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6706CoverageChecked :
    coverageCheck (innerAD leaf6706Box) leaf6706InnerLog = true := by
  rfl'

private theorem leaf6706InnerLogValid :
    leaf6706InnerLog.Valid 8 (innerAD leaf6706Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6706CoverageChecked

private noncomputable def leaf6706InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814819/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6706InputLogOnePlusV_eq :
    leaf6706InputLogOnePlusV = outerEnclosure 24
      (leaf6706Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6706RoundedFacts : LeafRoundedFacts 8
    leaf6706Certificate.logOnePlusV leaf6706InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6706InputLogOnePlusV_eq }

private noncomputable def leaf6706Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi325InputQChi innerPair376Input
    leaf6706InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6706LowerChecked :
    lowerCheck 24 leaf6706Box leaf6706Inputs = true := by
  rfl'

private theorem leaf6706CoversExact : CoversExact 8
    leaf6706Box leaf6706Certificate leaf6706InnerLog leaf6706Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi325RoundedFacts
    innerPair376RoundedFacts leaf6706RoundedFacts (by rfl)

private theorem leaf6706FlatSound : Sound leaf6706Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6706CertificateValid
    leaf6706InnerLogValid leaf6706CoversExact leaf6706LowerChecked

private noncomputable def leaf6707Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6707Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109049/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588830720) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (202333961/134217728) }, upper := { exponent := 1, mantissa := (795/512) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178257407/17177661440) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6707InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6707LocalValidity :
    LeafFacts leaf6707Box leaf6707Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6707Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588830720) }) = true
      norm_num [leaf6707Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6707CertificateValid :
    WideCertificateValid leaf6707Box leaf6707Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi326ValidityFacts
    leaf6707LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6707CoverageChecked :
    coverageCheck (innerAD leaf6707Box) leaf6707InnerLog = true := by
  rfl'

private theorem leaf6707InnerLogValid :
    leaf6707InnerLog.Valid 8 (innerAD leaf6707Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6707CoverageChecked

private noncomputable def leaf6707InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629663/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6707InputLogOnePlusV_eq :
    leaf6707InputLogOnePlusV = outerEnclosure 24
      (leaf6707Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6707RoundedFacts : LeafRoundedFacts 8
    leaf6707Certificate.logOnePlusV leaf6707InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6707InputLogOnePlusV_eq }

private noncomputable def leaf6707Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi326InputQChi innerPair382Input
    leaf6707InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6707LowerChecked :
    lowerCheck 24 leaf6707Box leaf6707Inputs = true := by
  rfl'

private theorem leaf6707CoversExact : CoversExact 8
    leaf6707Box leaf6707Certificate leaf6707InnerLog leaf6707Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi326RoundedFacts
    innerPair382RoundedFacts leaf6707RoundedFacts (by rfl)

private theorem leaf6707FlatSound : Sound leaf6707Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6707CertificateValid
    leaf6707InnerLogValid leaf6707CoversExact leaf6707LowerChecked

private noncomputable def leaf6708Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6708Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109049/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588833792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (201940769/134217728) }, upper := { exponent := 1, mantissa := (1587/1024) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178260479/17177667584) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6708InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6708LocalValidity :
    LeafFacts leaf6708Box leaf6708Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6708Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588833792) }) = true
      norm_num [leaf6708Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6708CertificateValid :
    WideCertificateValid leaf6708Box leaf6708Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi325ValidityFacts
    leaf6708LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6708CoverageChecked :
    coverageCheck (innerAD leaf6708Box) leaf6708InnerLog = true := by
  rfl'

private theorem leaf6708InnerLogValid :
    leaf6708InnerLog.Valid 8 (innerAD leaf6708Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6708CoverageChecked

private noncomputable def leaf6708InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907415/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6708InputLogOnePlusV_eq :
    leaf6708InputLogOnePlusV = outerEnclosure 24
      (leaf6708Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6708RoundedFacts : LeafRoundedFacts 8
    leaf6708Certificate.logOnePlusV leaf6708InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6708InputLogOnePlusV_eq }

private noncomputable def leaf6708Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi325InputQChi innerPair382Input
    leaf6708InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6708LowerChecked :
    lowerCheck 24 leaf6708Box leaf6708Inputs = true := by
  rfl'

private theorem leaf6708CoversExact : CoversExact 8
    leaf6708Box leaf6708Certificate leaf6708InnerLog leaf6708Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi325RoundedFacts
    innerPair382RoundedFacts leaf6708RoundedFacts (by rfl)

private theorem leaf6708FlatSound : Sound leaf6708Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6708CertificateValid
    leaf6708InnerLogValid leaf6708CoversExact leaf6708LowerChecked

private noncomputable def leaf6709Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6709Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109051/67108864) }, vSqrt := { lower := (65529/65536), upper := (2863142229/2862936064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (205151835/134217728) }, upper := { exponent := 1, mantissa := (403/256) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5726078293/5725872128) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6709InnerLog : WideLogData :=
  innerPair383Data

set_option maxRecDepth 1000000 in
private theorem leaf6709LocalValidity :
    LeafFacts leaf6709Box leaf6709Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6709Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2863142229/2862936064) }) = true
      norm_num [leaf6709Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6709CertificateValid :
    WideCertificateValid leaf6709Box leaf6709Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi326ValidityFacts
    leaf6709LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6709CoverageChecked :
    coverageCheck (innerAD leaf6709Box) leaf6709InnerLog = true := by
  rfl'

private theorem leaf6709InnerLogValid :
    leaf6709InnerLog.Valid 8 (innerAD leaf6709Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint484PositiveFacts.valid leaf6709CoverageChecked

private noncomputable def leaf6709InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629685/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6709InputLogOnePlusV_eq :
    leaf6709InputLogOnePlusV = outerEnclosure 24
      (leaf6709Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6709RoundedFacts : LeafRoundedFacts 8
    leaf6709Certificate.logOnePlusV leaf6709InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6709InputLogOnePlusV_eq }

private noncomputable def leaf6709Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi326InputQChi innerPair383Input
    leaf6709InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6709LowerChecked :
    lowerCheck 24 leaf6709Box leaf6709Inputs = true := by
  rfl'

private theorem leaf6709CoversExact : CoversExact 8
    leaf6709Box leaf6709Certificate leaf6709InnerLog leaf6709Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi326RoundedFacts
    innerPair383RoundedFacts leaf6709RoundedFacts (by rfl)

private theorem leaf6709FlatSound : Sound leaf6709Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6709CertificateValid
    leaf6709InnerLogValid leaf6709CoversExact leaf6709LowerChecked

private noncomputable def leaf6710Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (5/8), chiHi := (41/64) }

private noncomputable def leaf6710Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109047/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588864000) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (198139915/134217728) }, upper := { exponent := 1, mantissa := (3115/2048) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi323LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178290687/17177728000) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6710InnerLog : WideLogData :=
  innerPair379Data

set_option maxRecDepth 1000000 in
private theorem leaf6710LocalValidity :
    LeafFacts leaf6710Box leaf6710Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6710Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588864000) }) = true
      norm_num [leaf6710Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6710CertificateValid :
    WideCertificateValid leaf6710Box leaf6710Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi323ValidityFacts
    leaf6710LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6710CoverageChecked :
    coverageCheck (innerAD leaf6710Box) leaf6710InnerLog = true := by
  rfl'

private theorem leaf6710InnerLogValid :
    leaf6710InnerLog.Valid 8 (innerAD leaf6710Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint493PositiveFacts.valid leaf6710CoverageChecked

private noncomputable def leaf6710InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814815/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6710InputLogOnePlusV_eq :
    leaf6710InputLogOnePlusV = outerEnclosure 24
      (leaf6710Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6710RoundedFacts : LeafRoundedFacts 8
    leaf6710Certificate.logOnePlusV leaf6710InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6710InputLogOnePlusV_eq }

private noncomputable def leaf6710Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi323InputQChi innerPair379Input
    leaf6710InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6710LowerChecked :
    lowerCheck 24 leaf6710Box leaf6710Inputs = true := by
  rfl'

private theorem leaf6710CoversExact : CoversExact 8
    leaf6710Box leaf6710Certificate leaf6710InnerLog leaf6710Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi323RoundedFacts
    innerPair379RoundedFacts leaf6710RoundedFacts (by rfl)

private theorem leaf6710FlatSound : Sound leaf6710Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6710CertificateValid
    leaf6710InnerLogValid leaf6710CoversExact leaf6710LowerChecked

private noncomputable def leaf6711Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6711Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109049/67108864) }, vSqrt := { lower := (65529/65536), upper := (199754109/199740416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (201416513/134217728) }, upper := { exponent := 1, mantissa := (1583/1024) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (399494525/399480832) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6711InnerLog : WideLogData :=
  innerPair386Data

set_option maxRecDepth 1000000 in
private theorem leaf6711LocalValidity :
    LeafFacts leaf6711Box leaf6711Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6711Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (199754109/199740416) }) = true
      norm_num [leaf6711Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6711CertificateValid :
    WideCertificateValid leaf6711Box leaf6711Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi324ValidityFacts
    leaf6711LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6711CoverageChecked :
    coverageCheck (innerAD leaf6711Box) leaf6711InnerLog = true := by
  rfl'

private theorem leaf6711InnerLogValid :
    leaf6711InnerLog.Valid 8 (innerAD leaf6711Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint530PositiveFacts.valid leaf6711CoverageChecked

private noncomputable def leaf6711InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453707/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6711InputLogOnePlusV_eq :
    leaf6711InputLogOnePlusV = outerEnclosure 24
      (leaf6711Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6711RoundedFacts : LeafRoundedFacts 8
    leaf6711Certificate.logOnePlusV leaf6711InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6711InputLogOnePlusV_eq }

private noncomputable def leaf6711Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi324InputQChi innerPair386Input
    leaf6711InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6711LowerChecked :
    lowerCheck 24 leaf6711Box leaf6711Inputs = true := by
  rfl'

private theorem leaf6711CoversExact : CoversExact 8
    leaf6711Box leaf6711Certificate leaf6711InnerLog leaf6711Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi324RoundedFacts
    innerPair386RoundedFacts leaf6711RoundedFacts (by rfl)

private theorem leaf6711FlatSound : Sound leaf6711Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6711CertificateValid
    leaf6711InnerLogValid leaf6711CoversExact leaf6711LowerChecked

private noncomputable def leaf6712Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (5/8), chiHi := (81/128) }

private noncomputable def leaf6712Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217993/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588856320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (401555257/268435456) }, upper := { exponent := 1, mantissa := (1565/1024) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi349LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178283007/17177712640) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6712InnerLog : WideLogData :=
  innerPair376Data

set_option maxRecDepth 1000000 in
private theorem leaf6712LocalValidity :
    LeafFacts leaf6712Box leaf6712Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6712Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588856320) }) = true
      norm_num [leaf6712Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6712CertificateValid :
    WideCertificateValid leaf6712Box leaf6712Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi349ValidityFacts
    leaf6712LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6712CoverageChecked :
    coverageCheck (innerAD leaf6712Box) leaf6712InnerLog = true := by
  rfl'

private theorem leaf6712InnerLogValid :
    leaf6712InnerLog.Valid 8 (innerAD leaf6712Box) :=
  wideLogDataValid_of_cachedCheck endpoint98PositiveFacts
    endpoint482PositiveFacts.valid leaf6712CoverageChecked

private noncomputable def leaf6712InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814819/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6712InputLogOnePlusV_eq :
    leaf6712InputLogOnePlusV = outerEnclosure 24
      (leaf6712Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6712RoundedFacts : LeafRoundedFacts 8
    leaf6712Certificate.logOnePlusV leaf6712InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6712InputLogOnePlusV_eq }

private noncomputable def leaf6712Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi349InputQChi innerPair376Input
    leaf6712InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6712LowerChecked :
    lowerCheck 24 leaf6712Box leaf6712Inputs = true := by
  rfl'

private theorem leaf6712CoversExact : CoversExact 8
    leaf6712Box leaf6712Certificate leaf6712InnerLog leaf6712Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi349RoundedFacts
    innerPair376RoundedFacts leaf6712RoundedFacts (by rfl)

private theorem leaf6712FlatSound : Sound leaf6712Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6712CertificateValid
    leaf6712InnerLogValid leaf6712CoversExact leaf6712LowerChecked

private noncomputable def leaf6713Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (81/128), chiHi := (41/64) }

private noncomputable def leaf6713Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (134217995/134217728) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588843008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (404897387/268435456) }, upper := { exponent := 1, mantissa := (789/512) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi350LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178269695/17177686016) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6713InnerLog : WideLogData :=
  innerPair382Data

set_option maxRecDepth 1000000 in
private theorem leaf6713LocalValidity :
    LeafFacts leaf6713Box leaf6713Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6713Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588843008) }) = true
      norm_num [leaf6713Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6713CertificateValid :
    WideCertificateValid leaf6713Box leaf6713Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi350ValidityFacts
    leaf6713LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6713CoverageChecked :
    coverageCheck (innerAD leaf6713Box) leaf6713InnerLog = true := by
  rfl'

private theorem leaf6713InnerLogValid :
    leaf6713InnerLog.Valid 8 (innerAD leaf6713Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint483PositiveFacts.valid leaf6713CoverageChecked

private noncomputable def leaf6713InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629651/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6713InputLogOnePlusV_eq :
    leaf6713InputLogOnePlusV = outerEnclosure 24
      (leaf6713Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6713RoundedFacts : LeafRoundedFacts 8
    leaf6713Certificate.logOnePlusV leaf6713InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6713InputLogOnePlusV_eq }

private noncomputable def leaf6713Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi350InputQChi innerPair382Input
    leaf6713InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6713LowerChecked :
    lowerCheck 24 leaf6713Box leaf6713Inputs = true := by
  rfl'

private theorem leaf6713CoversExact : CoversExact 8
    leaf6713Box leaf6713Certificate leaf6713InnerLog leaf6713Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi350RoundedFacts
    innerPair382RoundedFacts leaf6713RoundedFacts (by rfl)

private theorem leaf6713FlatSound : Sound leaf6713Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6713CertificateValid
    leaf6713InnerLogValid leaf6713CoversExact leaf6713LowerChecked

private noncomputable def leaf6714Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (41/64), chiHi := (21/32) }

private noncomputable def leaf6714Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109051/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588816384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (204103323/134217728) }, upper := { exponent := 1, mantissa := (401/256) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi324LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178243071/17177632768) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6714InnerLog : WideLogData :=
  innerPair830Data

set_option maxRecDepth 1000000 in
private theorem leaf6714LocalValidity :
    LeafFacts leaf6714Box leaf6714Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6714Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588816384) }) = true
      norm_num [leaf6714Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6714CertificateValid :
    WideCertificateValid leaf6714Box leaf6714Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi324ValidityFacts
    leaf6714LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6714CoverageChecked :
    coverageCheck (innerAD leaf6714Box) leaf6714InnerLog = true := by
  rfl'

private theorem leaf6714InnerLogValid :
    leaf6714InnerLog.Valid 8 (innerAD leaf6714Box) :=
  wideLogDataValid_of_cachedCheck endpoint526PositiveFacts
    endpoint528PositiveFacts.valid leaf6714CoverageChecked

private noncomputable def leaf6714InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629677/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6714InputLogOnePlusV_eq :
    leaf6714InputLogOnePlusV = outerEnclosure 24
      (leaf6714Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6714RoundedFacts : LeafRoundedFacts 8
    leaf6714Certificate.logOnePlusV leaf6714InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6714InputLogOnePlusV_eq }

private noncomputable def leaf6714Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi324InputQChi innerPair830Input
    leaf6714InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6714LowerChecked :
    lowerCheck 24 leaf6714Box leaf6714Inputs = true := by
  rfl'

private theorem leaf6714CoversExact : CoversExact 8
    leaf6714Box leaf6714Certificate leaf6714InnerLog leaf6714Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi324RoundedFacts
    innerPair830RoundedFacts leaf6714RoundedFacts (by rfl)

private theorem leaf6714FlatSound : Sound leaf6714Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6714CertificateValid
    leaf6714InnerLogValid leaf6714CoversExact leaf6714LowerChecked

private noncomputable def leaf6715Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6715Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109051/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588811776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (204693111/134217728) }, upper := { exponent := 1, mantissa := (3217/2048) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178238463/17177623552) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6715InnerLog : WideLogData :=
  innerPair785Data

set_option maxRecDepth 1000000 in
private theorem leaf6715LocalValidity :
    LeafFacts leaf6715Box leaf6715Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6715Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588811776) }) = true
      norm_num [leaf6715Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6715CertificateValid :
    WideCertificateValid leaf6715Box leaf6715Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi325ValidityFacts
    leaf6715LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6715CoverageChecked :
    coverageCheck (innerAD leaf6715Box) leaf6715InnerLog = true := by
  rfl'

private theorem leaf6715InnerLogValid :
    leaf6715InnerLog.Valid 8 (innerAD leaf6715Box) :=
  wideLogDataValid_of_cachedCheck endpoint493PositiveFacts
    endpoint492PositiveFacts.valid leaf6715CoverageChecked

private noncomputable def leaf6715InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629681/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6715InputLogOnePlusV_eq :
    leaf6715InputLogOnePlusV = outerEnclosure 24
      (leaf6715Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6715RoundedFacts : LeafRoundedFacts 8
    leaf6715Certificate.logOnePlusV leaf6715InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6715InputLogOnePlusV_eq }

private noncomputable def leaf6715Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi325InputQChi innerPair785Input
    leaf6715InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6715LowerChecked :
    lowerCheck 24 leaf6715Box leaf6715Inputs = true := by
  rfl'

private theorem leaf6715CoversExact : CoversExact 8
    leaf6715Box leaf6715Certificate leaf6715InnerLog leaf6715Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi325RoundedFacts
    innerPair785RoundedFacts leaf6715RoundedFacts (by rfl)

private theorem leaf6715FlatSound : Sound leaf6715Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6715CertificateValid
    leaf6715InnerLogValid leaf6715CoversExact leaf6715LowerChecked

private noncomputable def leaf6716Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6716Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109053/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588785664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (207969709/134217728) }, upper := { exponent := 1, mantissa := (817/512) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178212351/17177571328) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6716InnerLog : WideLogData :=
  innerPair835Data

set_option maxRecDepth 1000000 in
private theorem leaf6716LocalValidity :
    LeafFacts leaf6716Box leaf6716Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6716Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588785664) }) = true
      norm_num [leaf6716Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6716CertificateValid :
    WideCertificateValid leaf6716Box leaf6716Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi326ValidityFacts
    leaf6716LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6716CoverageChecked :
    coverageCheck (innerAD leaf6716Box) leaf6716InnerLog = true := by
  rfl'

private theorem leaf6716InnerLogValid :
    leaf6716InnerLog.Valid 8 (innerAD leaf6716Box) :=
  wideLogDataValid_of_cachedCheck endpoint530PositiveFacts
    endpoint494PositiveFacts.valid leaf6716CoverageChecked

private noncomputable def leaf6716InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629707/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6716InputLogOnePlusV_eq :
    leaf6716InputLogOnePlusV = outerEnclosure 24
      (leaf6716Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6716RoundedFacts : LeafRoundedFacts 8
    leaf6716Certificate.logOnePlusV leaf6716InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6716InputLogOnePlusV_eq }

private noncomputable def leaf6716Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi326InputQChi innerPair835Input
    leaf6716InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6716LowerChecked :
    lowerCheck 24 leaf6716Box leaf6716Inputs = true := by
  rfl'

private theorem leaf6716CoversExact : CoversExact 8
    leaf6716Box leaf6716Certificate leaf6716InnerLog leaf6716Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi326RoundedFacts
    innerPair835RoundedFacts leaf6716RoundedFacts (by rfl)

private theorem leaf6716FlatSound : Sound leaf6716Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6716CertificateValid
    leaf6716InnerLogValid leaf6716CoversExact leaf6716LowerChecked

private noncomputable def leaf6717Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (21/32), chiHi := (43/64) }

private noncomputable def leaf6717Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109053/67108864) }, vSqrt := { lower := (65529/65536), upper := (2863142229/2862929920) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (207445453/134217728) }, upper := { exponent := 1, mantissa := (815/512) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi325LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5726072149/5725859840) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6717InnerLog : WideLogData :=
  innerPair744Data

set_option maxRecDepth 1000000 in
private theorem leaf6717LocalValidity :
    LeafFacts leaf6717Box leaf6717Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6717Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2863142229/2862929920) }) = true
      norm_num [leaf6717Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6717CertificateValid :
    WideCertificateValid leaf6717Box leaf6717Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi325ValidityFacts
    leaf6717LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6717CoverageChecked :
    coverageCheck (innerAD leaf6717Box) leaf6717InnerLog = true := by
  rfl'

private theorem leaf6717InnerLogValid :
    leaf6717InnerLog.Valid 8 (innerAD leaf6717Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint484PositiveFacts.valid leaf6717CoverageChecked

private noncomputable def leaf6717InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629703/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6717InputLogOnePlusV_eq :
    leaf6717InputLogOnePlusV = outerEnclosure 24
      (leaf6717Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6717RoundedFacts : LeafRoundedFacts 8
    leaf6717Certificate.logOnePlusV leaf6717InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6717InputLogOnePlusV_eq }

private noncomputable def leaf6717Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi325InputQChi innerPair744Input
    leaf6717InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6717LowerChecked :
    lowerCheck 24 leaf6717Box leaf6717Inputs = true := by
  rfl'

private theorem leaf6717CoversExact : CoversExact 8
    leaf6717Box leaf6717Certificate leaf6717InnerLog leaf6717Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi325RoundedFacts
    innerPair744RoundedFacts leaf6717RoundedFacts (by rfl)

private theorem leaf6717FlatSound : Sound leaf6717Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6717CertificateValid
    leaf6717InnerLogValid leaf6717CoversExact leaf6717LowerChecked

private noncomputable def leaf6718Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (43/64), chiHi := (11/16) }

private noncomputable def leaf6718Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109055/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588763136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (210787583/134217728) }, upper := { exponent := 1, mantissa := (207/128) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi326LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178189823/17177526272) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6718InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6718LocalValidity :
    LeafFacts leaf6718Box leaf6718Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6718Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588763136) }) = true
      norm_num [leaf6718Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6718CertificateValid :
    WideCertificateValid leaf6718Box leaf6718Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi326ValidityFacts
    leaf6718LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6718CoverageChecked :
    coverageCheck (innerAD leaf6718Box) leaf6718InnerLog = true := by
  rfl'

private theorem leaf6718InnerLogValid :
    leaf6718InnerLog.Valid 8 (innerAD leaf6718Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6718CoverageChecked

private noncomputable def leaf6718InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629729/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6718InputLogOnePlusV_eq :
    leaf6718InputLogOnePlusV = outerEnclosure 24
      (leaf6718Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6718RoundedFacts : LeafRoundedFacts 8
    leaf6718Certificate.logOnePlusV leaf6718InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6718InputLogOnePlusV_eq }

private noncomputable def leaf6718Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi326InputQChi innerPair749Input
    leaf6718InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6718LowerChecked :
    lowerCheck 24 leaf6718Box leaf6718Inputs = true := by
  rfl'

private theorem leaf6718CoversExact : CoversExact 8
    leaf6718Box leaf6718Certificate leaf6718InnerLog leaf6718Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi326RoundedFacts
    innerPair749RoundedFacts leaf6718RoundedFacts (by rfl)

private theorem leaf6718FlatSound : Sound leaf6718Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6718CertificateValid
    leaf6718InnerLogValid leaf6718CoversExact leaf6718LowerChecked

private noncomputable def leaf6719Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf6719Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109051/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588805632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (205479495/134217728) }, upper := { exponent := 1, mantissa := (3229/2048) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178232319/17177611264) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6719InnerLog : WideLogData :=
  innerPair383Data

set_option maxRecDepth 1000000 in
private theorem leaf6719LocalValidity :
    LeafFacts leaf6719Box leaf6719Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6719Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588805632) }) = true
      norm_num [leaf6719Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6719CertificateValid :
    WideCertificateValid leaf6719Box leaf6719Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi341ValidityFacts
    leaf6719LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6719CoverageChecked :
    coverageCheck (innerAD leaf6719Box) leaf6719InnerLog = true := by
  rfl'

private theorem leaf6719InnerLogValid :
    leaf6719InnerLog.Valid 8 (innerAD leaf6719Box) :=
  wideLogDataValid_of_cachedCheck endpoint99PositiveFacts
    endpoint484PositiveFacts.valid leaf6719CoverageChecked

private noncomputable def leaf6719InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629687/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6719InputLogOnePlusV_eq :
    leaf6719InputLogOnePlusV = outerEnclosure 24
      (leaf6719Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6719RoundedFacts : LeafRoundedFacts 8
    leaf6719Certificate.logOnePlusV leaf6719InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6719InputLogOnePlusV_eq }

private noncomputable def leaf6719Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi341InputQChi innerPair383Input
    leaf6719InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6719LowerChecked :
    lowerCheck 24 leaf6719Box leaf6719Inputs = true := by
  rfl'

private theorem leaf6719CoversExact : CoversExact 8
    leaf6719Box leaf6719Certificate leaf6719InnerLog leaf6719Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi341RoundedFacts
    innerPair383RoundedFacts leaf6719RoundedFacts (by rfl)

private theorem leaf6719FlatSound : Sound leaf6719Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6719CertificateValid
    leaf6719InnerLogValid leaf6719CoversExact leaf6719LowerChecked

private noncomputable def leaf6720Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf6720Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109053/67108864) }, vSqrt := { lower := (65529/65536), upper := (2863142229/2862926848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (208625029/134217728) }, upper := { exponent := 1, mantissa := (1639/1024) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5726069077/5725853696) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6720InnerLog : WideLogData :=
  innerPair745Data

set_option maxRecDepth 1000000 in
private theorem leaf6720LocalValidity :
    LeafFacts leaf6720Box leaf6720Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6720Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2863142229/2862926848) }) = true
      norm_num [leaf6720Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6720CertificateValid :
    WideCertificateValid leaf6720Box leaf6720Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi342ValidityFacts
    leaf6720LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6720CoverageChecked :
    coverageCheck (innerAD leaf6720Box) leaf6720InnerLog = true := by
  rfl'

private theorem leaf6720InnerLogValid :
    leaf6720InnerLog.Valid 8 (innerAD leaf6720Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint485PositiveFacts.valid leaf6720CoverageChecked

private noncomputable def leaf6720InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726857/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf6720InputLogOnePlusV_eq :
    leaf6720InputLogOnePlusV = outerEnclosure 24
      (leaf6720Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6720RoundedFacts : LeafRoundedFacts 8
    leaf6720Certificate.logOnePlusV leaf6720InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6720InputLogOnePlusV_eq }

private noncomputable def leaf6720Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi342InputQChi innerPair745Input
    leaf6720InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6720LowerChecked :
    lowerCheck 24 leaf6720Box leaf6720Inputs = true := by
  rfl'

private theorem leaf6720CoversExact : CoversExact 8
    leaf6720Box leaf6720Certificate leaf6720InnerLog leaf6720Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi342RoundedFacts
    innerPair745RoundedFacts leaf6720RoundedFacts (by rfl)

private theorem leaf6720FlatSound : Sound leaf6720Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6720CertificateValid
    leaf6720InnerLogValid leaf6720CoversExact leaf6720LowerChecked

private noncomputable def leaf6721Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf6721Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109053/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588782592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (208362901/134217728) }, upper := { exponent := 1, mantissa := (1637/1024) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178209279/17177565184) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6721InnerLog : WideLogData :=
  innerPair745Data

set_option maxRecDepth 1000000 in
private theorem leaf6721LocalValidity :
    LeafFacts leaf6721Box leaf6721Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6721Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588782592) }) = true
      norm_num [leaf6721Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6721CertificateValid :
    WideCertificateValid leaf6721Box leaf6721Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi341ValidityFacts
    leaf6721LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6721CoverageChecked :
    coverageCheck (innerAD leaf6721Box) leaf6721InnerLog = true := by
  rfl'

private theorem leaf6721InnerLogValid :
    leaf6721InnerLog.Valid 8 (innerAD leaf6721Box) :=
  wideLogDataValid_of_cachedCheck endpoint482PositiveFacts
    endpoint485PositiveFacts.valid leaf6721CoverageChecked

private noncomputable def leaf6721InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814855/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6721InputLogOnePlusV_eq :
    leaf6721InputLogOnePlusV = outerEnclosure 24
      (leaf6721Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6721RoundedFacts : LeafRoundedFacts 8
    leaf6721Certificate.logOnePlusV leaf6721InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6721InputLogOnePlusV_eq }

private noncomputable def leaf6721Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi341InputQChi innerPair745Input
    leaf6721InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6721LowerChecked :
    lowerCheck 24 leaf6721Box leaf6721Inputs = true := by
  rfl'

private theorem leaf6721CoversExact : CoversExact 8
    leaf6721Box leaf6721Certificate leaf6721InnerLog leaf6721Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi341RoundedFacts
    innerPair745RoundedFacts leaf6721RoundedFacts (by rfl)

private theorem leaf6721FlatSound : Sound leaf6721Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6721CertificateValid
    leaf6721InnerLogValid leaf6721CoversExact leaf6721LowerChecked

private noncomputable def leaf6722Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf6722Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109055/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588756992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (211573967/134217728) }, upper := { exponent := 1, mantissa := (831/512) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178183679/17177513984) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6722InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6722LocalValidity :
    LeafFacts leaf6722Box leaf6722Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6722Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588756992) }) = true
      norm_num [leaf6722Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6722CertificateValid :
    WideCertificateValid leaf6722Box leaf6722Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi342ValidityFacts
    leaf6722LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6722CoverageChecked :
    coverageCheck (innerAD leaf6722Box) leaf6722InnerLog = true := by
  rfl'

private theorem leaf6722InnerLogValid :
    leaf6722InnerLog.Valid 8 (innerAD leaf6722Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6722CoverageChecked

private noncomputable def leaf6722InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629735/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6722InputLogOnePlusV_eq :
    leaf6722InputLogOnePlusV = outerEnclosure 24
      (leaf6722Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6722RoundedFacts : LeafRoundedFacts 8
    leaf6722Certificate.logOnePlusV leaf6722InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6722InputLogOnePlusV_eq }

private noncomputable def leaf6722Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi342InputQChi innerPair749Input
    leaf6722InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6722LowerChecked :
    lowerCheck 24 leaf6722Box leaf6722Inputs = true := by
  rfl'

private theorem leaf6722CoversExact : CoversExact 8
    leaf6722Box leaf6722Certificate leaf6722InnerLog leaf6722Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi342RoundedFacts
    innerPair749RoundedFacts leaf6722RoundedFacts (by rfl)

private theorem leaf6722FlatSound : Sound leaf6722Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6722CertificateValid
    leaf6722InnerLogValid leaf6722CoversExact leaf6722LowerChecked

private noncomputable def leaf6723Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf6723Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109055/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588755456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (211770563/134217728) }, upper := { exponent := 1, mantissa := (3327/2048) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178182143/17177510912) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6723InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6723LocalValidity :
    LeafFacts leaf6723Box leaf6723Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6723Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588755456) }) = true
      norm_num [leaf6723Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6723CertificateValid :
    WideCertificateValid leaf6723Box leaf6723Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi343ValidityFacts
    leaf6723LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6723CoverageChecked :
    coverageCheck (innerAD leaf6723Box) leaf6723InnerLog = true := by
  rfl'

private theorem leaf6723InnerLogValid :
    leaf6723InnerLog.Valid 8 (innerAD leaf6723Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6723CoverageChecked

private noncomputable def leaf6723InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453717/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf6723InputLogOnePlusV_eq :
    leaf6723InputLogOnePlusV = outerEnclosure 24
      (leaf6723Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6723RoundedFacts : LeafRoundedFacts 8
    leaf6723Certificate.logOnePlusV leaf6723InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6723InputLogOnePlusV_eq }

private noncomputable def leaf6723Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi343InputQChi innerPair749Input
    leaf6723InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6723LowerChecked :
    lowerCheck 24 leaf6723Box leaf6723Inputs = true := by
  rfl'

private theorem leaf6723CoversExact : CoversExact 8
    leaf6723Box leaf6723Certificate leaf6723InnerLog leaf6723Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi343RoundedFacts
    innerPair749RoundedFacts leaf6723RoundedFacts (by rfl)

private theorem leaf6723FlatSound : Sound leaf6723Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6723CertificateValid
    leaf6723InnerLogValid leaf6723CoversExact leaf6723LowerChecked

private noncomputable def leaf6724Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf6724Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109057/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588730368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (214916097/134217728) }, upper := { exponent := 1, mantissa := (211/128) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178157055/17177460736) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf6724InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6724LocalValidity :
    LeafFacts leaf6724Box leaf6724Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6724Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588730368) }) = true
      norm_num [leaf6724Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6724CertificateValid :
    WideCertificateValid leaf6724Box leaf6724Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi344ValidityFacts
    leaf6724LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6724CoverageChecked :
    coverageCheck (innerAD leaf6724Box) leaf6724InnerLog = true := by
  rfl'

private theorem leaf6724InnerLogValid :
    leaf6724InnerLog.Valid 8 (innerAD leaf6724Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6724CoverageChecked

private noncomputable def leaf6724InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629761/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6724InputLogOnePlusV_eq :
    leaf6724InputLogOnePlusV = outerEnclosure 24
      (leaf6724Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6724RoundedFacts : LeafRoundedFacts 8
    leaf6724Certificate.logOnePlusV leaf6724InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6724InputLogOnePlusV_eq }

private noncomputable def leaf6724Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi344InputQChi innerPair755Input
    leaf6724InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6724LowerChecked :
    lowerCheck 24 leaf6724Box leaf6724Inputs = true := by
  rfl'

private theorem leaf6724CoversExact : CoversExact 8
    leaf6724Box leaf6724Certificate leaf6724InnerLog leaf6724Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi344RoundedFacts
    innerPair755RoundedFacts leaf6724RoundedFacts (by rfl)

private theorem leaf6724FlatSound : Sound leaf6724Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6724CertificateValid
    leaf6724InnerLogValid leaf6724CoversExact leaf6724LowerChecked

private noncomputable def leaf6725Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf6725Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109057/67108864) }, vSqrt := { lower := (65529/65536), upper := (954380743/954303488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (214785033/134217728) }, upper := { exponent := 1, mantissa := (1687/1024) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1908684231/1908606976) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6725InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6725LocalValidity :
    LeafFacts leaf6725Box leaf6725Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6725Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (954380743/954303488) }) = true
      norm_num [leaf6725Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6725CertificateValid :
    WideCertificateValid leaf6725Box leaf6725Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi343ValidityFacts
    leaf6725LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6725CoverageChecked :
    coverageCheck (innerAD leaf6725Box) leaf6725InnerLog = true := by
  rfl'

private theorem leaf6725InnerLogValid :
    leaf6725InnerLog.Valid 8 (innerAD leaf6725Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6725CoverageChecked

private noncomputable def leaf6725InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (181715/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf6725InputLogOnePlusV_eq :
    leaf6725InputLogOnePlusV = outerEnclosure 24
      (leaf6725Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6725RoundedFacts : LeafRoundedFacts 8
    leaf6725Certificate.logOnePlusV leaf6725InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6725InputLogOnePlusV_eq }

private noncomputable def leaf6725Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi343InputQChi innerPair755Input
    leaf6725InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6725LowerChecked :
    lowerCheck 24 leaf6725Box leaf6725Inputs = true := by
  rfl'

private theorem leaf6725CoversExact : CoversExact 8
    leaf6725Box leaf6725Certificate leaf6725InnerLog leaf6725Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi343RoundedFacts
    innerPair755RoundedFacts leaf6725RoundedFacts (by rfl)

private theorem leaf6725FlatSound : Sound leaf6725Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6725CertificateValid
    leaf6725InnerLogValid leaf6725CoversExact leaf6725LowerChecked

private noncomputable def leaf6726Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf6726Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109059/67108864) }, vSqrt := { lower := (65529/65536), upper := (199754109/199737344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (217996099/134217728) }, upper := { exponent := 1, mantissa := (107/64) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (399491453/399474688) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf6726InnerLog : WideLogData :=
  innerPair756Data

set_option maxRecDepth 1000000 in
private theorem leaf6726LocalValidity :
    LeafFacts leaf6726Box leaf6726Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6726Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (199754109/199737344) }) = true
      norm_num [leaf6726Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6726CertificateValid :
    WideCertificateValid leaf6726Box leaf6726Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi344ValidityFacts
    leaf6726LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6726CoverageChecked :
    coverageCheck (innerAD leaf6726Box) leaf6726InnerLog = true := by
  rfl'

private theorem leaf6726InnerLogValid :
    leaf6726InnerLog.Valid 8 (innerAD leaf6726Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint487PositiveFacts.valid leaf6726CoverageChecked

private noncomputable def leaf6726InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629785/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6726InputLogOnePlusV_eq :
    leaf6726InputLogOnePlusV = outerEnclosure 24
      (leaf6726Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6726RoundedFacts : LeafRoundedFacts 8
    leaf6726Certificate.logOnePlusV leaf6726InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6726InputLogOnePlusV_eq }

private noncomputable def leaf6726Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi344InputQChi innerPair756Input
    leaf6726InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6726LowerChecked :
    lowerCheck 24 leaf6726Box leaf6726Inputs = true := by
  rfl'

private theorem leaf6726CoversExact : CoversExact 8
    leaf6726Box leaf6726Certificate leaf6726InnerLog leaf6726Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi344RoundedFacts
    innerPair756RoundedFacts leaf6726RoundedFacts (by rfl)

private theorem leaf6726FlatSound : Sound leaf6726Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6726CertificateValid
    leaf6726InnerLogValid leaf6726CoversExact leaf6726LowerChecked

private noncomputable def leaf6727Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf6727Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109055/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588759552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (211246307/134217728) }, upper := { exponent := 1, mantissa := (3319/2048) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178186239/17177519104) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6727InnerLog : WideLogData :=
  innerPair749Data

set_option maxRecDepth 1000000 in
private theorem leaf6727LocalValidity :
    LeafFacts leaf6727Box leaf6727Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6727Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588759552) }) = true
      norm_num [leaf6727Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6727CertificateValid :
    WideCertificateValid leaf6727Box leaf6727Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi341ValidityFacts
    leaf6727LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6727CoverageChecked :
    coverageCheck (innerAD leaf6727Box) leaf6727InnerLog = true := by
  rfl'

private theorem leaf6727InnerLogValid :
    leaf6727InnerLog.Valid 8 (innerAD leaf6727Box) :=
  wideLogDataValid_of_cachedCheck endpoint483PositiveFacts
    endpoint485PositiveFacts.valid leaf6727CoverageChecked

private noncomputable def leaf6727InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907433/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf6727InputLogOnePlusV_eq :
    leaf6727InputLogOnePlusV = outerEnclosure 24
      (leaf6727Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6727RoundedFacts : LeafRoundedFacts 8
    leaf6727Certificate.logOnePlusV leaf6727InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6727InputLogOnePlusV_eq }

private noncomputable def leaf6727Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi341InputQChi innerPair749Input
    leaf6727InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6727LowerChecked :
    lowerCheck 24 leaf6727Box leaf6727Inputs = true := by
  rfl'

private theorem leaf6727CoversExact : CoversExact 8
    leaf6727Box leaf6727Certificate leaf6727InnerLog leaf6727Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi341RoundedFacts
    innerPair749RoundedFacts leaf6727RoundedFacts (by rfl)

private theorem leaf6727FlatSound : Sound leaf6727Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6727CertificateValid
    leaf6727InnerLogValid leaf6727CoversExact leaf6727LowerChecked

private noncomputable def leaf6728Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf6728Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109057/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588733440) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (214522905/134217728) }, upper := { exponent := 1, mantissa := (1685/1024) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178160127/17177466880) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6728InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6728LocalValidity :
    LeafFacts leaf6728Box leaf6728Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6728Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588733440) }) = true
      norm_num [leaf6728Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6728CertificateValid :
    WideCertificateValid leaf6728Box leaf6728Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi342ValidityFacts
    leaf6728LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6728CoverageChecked :
    coverageCheck (innerAD leaf6728Box) leaf6728InnerLog = true := by
  rfl'

private theorem leaf6728InnerLogValid :
    leaf6728InnerLog.Valid 8 (innerAD leaf6728Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6728CoverageChecked

private noncomputable def leaf6728InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814879/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf6728InputLogOnePlusV_eq :
    leaf6728InputLogOnePlusV = outerEnclosure 24
      (leaf6728Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6728RoundedFacts : LeafRoundedFacts 8
    leaf6728Certificate.logOnePlusV leaf6728InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6728InputLogOnePlusV_eq }

private noncomputable def leaf6728Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi342InputQChi innerPair755Input
    leaf6728InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6728LowerChecked :
    lowerCheck 24 leaf6728Box leaf6728Inputs = true := by
  rfl'

private theorem leaf6728CoversExact : CoversExact 8
    leaf6728Box leaf6728Certificate leaf6728InnerLog leaf6728Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi342RoundedFacts
    innerPair755RoundedFacts leaf6728RoundedFacts (by rfl)

private theorem leaf6728FlatSound : Sound leaf6728Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6728CertificateValid
    leaf6728InnerLogValid leaf6728CoversExact leaf6728LowerChecked

private noncomputable def leaf6729Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (11/16), chiHi := (45/64) }

private noncomputable def leaf6729Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109057/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588736512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (214129713/134217728) }, upper := { exponent := 1, mantissa := (841/512) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi341LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178163199/17177473024) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6729InnerLog : WideLogData :=
  innerPair755Data

set_option maxRecDepth 1000000 in
private theorem leaf6729LocalValidity :
    LeafFacts leaf6729Box leaf6729Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6729Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588736512) }) = true
      norm_num [leaf6729Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6729CertificateValid :
    WideCertificateValid leaf6729Box leaf6729Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi341ValidityFacts
    leaf6729LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6729CoverageChecked :
    coverageCheck (innerAD leaf6729Box) leaf6729InnerLog = true := by
  rfl'

private theorem leaf6729InnerLogValid :
    leaf6729InnerLog.Valid 8 (innerAD leaf6729Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint486PositiveFacts.valid leaf6729CoverageChecked

private noncomputable def leaf6729InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629755/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6729InputLogOnePlusV_eq :
    leaf6729InputLogOnePlusV = outerEnclosure 24
      (leaf6729Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6729RoundedFacts : LeafRoundedFacts 8
    leaf6729Certificate.logOnePlusV leaf6729InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6729InputLogOnePlusV_eq }

private noncomputable def leaf6729Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi341InputQChi innerPair755Input
    leaf6729InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6729LowerChecked :
    lowerCheck 24 leaf6729Box leaf6729Inputs = true := by
  rfl'

private theorem leaf6729CoversExact : CoversExact 8
    leaf6729Box leaf6729Certificate leaf6729InnerLog leaf6729Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi341RoundedFacts
    innerPair755RoundedFacts leaf6729RoundedFacts (by rfl)

private theorem leaf6729FlatSound : Sound leaf6729Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6729CertificateValid
    leaf6729InnerLogValid leaf6729CoversExact leaf6729LowerChecked

private noncomputable def leaf6730Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (45/64), chiHi := (23/32) }

private noncomputable def leaf6730Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109059/67108864) }, vSqrt := { lower := (65529/65536), upper := (2863142229/2862903296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (217471843/134217728) }, upper := { exponent := 1, mantissa := (427/256) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi342LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5726045525/5725806592) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6730InnerLog : WideLogData :=
  innerPair756Data

set_option maxRecDepth 1000000 in
private theorem leaf6730LocalValidity :
    LeafFacts leaf6730Box leaf6730Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6730Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2863142229/2862903296) }) = true
      norm_num [leaf6730Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6730CertificateValid :
    WideCertificateValid leaf6730Box leaf6730Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi342ValidityFacts
    leaf6730LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6730CoverageChecked :
    coverageCheck (innerAD leaf6730Box) leaf6730InnerLog = true := by
  rfl'

private theorem leaf6730InnerLogValid :
    leaf6730InnerLog.Valid 8 (innerAD leaf6730Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint487PositiveFacts.valid leaf6730CoverageChecked

private noncomputable def leaf6730InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629781/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6730InputLogOnePlusV_eq :
    leaf6730InputLogOnePlusV = outerEnclosure 24
      (leaf6730Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6730RoundedFacts : LeafRoundedFacts 8
    leaf6730Certificate.logOnePlusV leaf6730InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6730InputLogOnePlusV_eq }

private noncomputable def leaf6730Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi342InputQChi innerPair756Input
    leaf6730InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6730LowerChecked :
    lowerCheck 24 leaf6730Box leaf6730Inputs = true := by
  rfl'

private theorem leaf6730CoversExact : CoversExact 8
    leaf6730Box leaf6730Certificate leaf6730InnerLog leaf6730Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi342RoundedFacts
    innerPair756RoundedFacts leaf6730RoundedFacts (by rfl)

private theorem leaf6730FlatSound : Sound leaf6730Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6730CertificateValid
    leaf6730InnerLogValid leaf6730CoversExact leaf6730LowerChecked

private noncomputable def leaf6731Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf6731Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109059/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588707328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (217799503/134217728) }, upper := { exponent := 1, mantissa := (3421/2048) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178134015/17177414656) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6731InnerLog : WideLogData :=
  innerPair756Data

set_option maxRecDepth 1000000 in
private theorem leaf6731LocalValidity :
    LeafFacts leaf6731Box leaf6731Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6731Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588707328) }) = true
      norm_num [leaf6731Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6731CertificateValid :
    WideCertificateValid leaf6731Box leaf6731Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi343ValidityFacts
    leaf6731LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6731CoverageChecked :
    coverageCheck (innerAD leaf6731Box) leaf6731InnerLog = true := by
  rfl'

private theorem leaf6731InnerLogValid :
    leaf6731InnerLog.Valid 8 (innerAD leaf6731Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint487PositiveFacts.valid leaf6731CoverageChecked

private noncomputable def leaf6731InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629783/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6731InputLogOnePlusV_eq :
    leaf6731InputLogOnePlusV = outerEnclosure 24
      (leaf6731Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6731RoundedFacts : LeafRoundedFacts 8
    leaf6731Certificate.logOnePlusV leaf6731InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6731InputLogOnePlusV_eq }

private noncomputable def leaf6731Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi343InputQChi innerPair756Input
    leaf6731InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6731LowerChecked :
    lowerCheck 24 leaf6731Box leaf6731Inputs = true := by
  rfl'

private theorem leaf6731CoversExact : CoversExact 8
    leaf6731Box leaf6731Certificate leaf6731InnerLog leaf6731Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi343RoundedFacts
    innerPair756RoundedFacts leaf6731RoundedFacts (by rfl)

private theorem leaf6731FlatSound : Sound leaf6731Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6731CertificateValid
    leaf6731InnerLogValid leaf6731CoversExact leaf6731LowerChecked

private noncomputable def leaf6732Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf6732Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109061/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588681216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (221076101/134217728) }, upper := { exponent := 1, mantissa := (217/128) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178107903/17177362432) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf6732InnerLog : WideLogData :=
  innerPair762Data

set_option maxRecDepth 1000000 in
private theorem leaf6732LocalValidity :
    LeafFacts leaf6732Box leaf6732Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6732Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588681216) }) = true
      norm_num [leaf6732Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6732CertificateValid :
    WideCertificateValid leaf6732Box leaf6732Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi344ValidityFacts
    leaf6732LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6732CoverageChecked :
    coverageCheck (innerAD leaf6732Box) leaf6732InnerLog = true := by
  rfl'

private theorem leaf6732InnerLogValid :
    leaf6732InnerLog.Valid 8 (innerAD leaf6732Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint488PositiveFacts.valid leaf6732CoverageChecked

private noncomputable def leaf6732InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629809/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6732InputLogOnePlusV_eq :
    leaf6732InputLogOnePlusV = outerEnclosure 24
      (leaf6732Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6732RoundedFacts : LeafRoundedFacts 8
    leaf6732Certificate.logOnePlusV leaf6732InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6732InputLogOnePlusV_eq }

private noncomputable def leaf6732Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi344InputQChi innerPair762Input
    leaf6732InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6732LowerChecked :
    lowerCheck 24 leaf6732Box leaf6732Inputs = true := by
  rfl'

private theorem leaf6732CoversExact : CoversExact 8
    leaf6732Box leaf6732Certificate leaf6732InnerLog leaf6732Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi344RoundedFacts
    innerPair762RoundedFacts leaf6732RoundedFacts (by rfl)

private theorem leaf6732FlatSound : Sound leaf6732Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6732CertificateValid
    leaf6732InnerLogValid leaf6732CoversExact leaf6732LowerChecked

private noncomputable def leaf6733Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (23/32), chiHi := (47/64) }

private noncomputable def leaf6733Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109061/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588683264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (220813973/134217728) }, upper := { exponent := 1, mantissa := (867/512) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi343LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178109951/17177366528) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6733InnerLog : WideLogData :=
  innerPair762Data

set_option maxRecDepth 1000000 in
private theorem leaf6733LocalValidity :
    LeafFacts leaf6733Box leaf6733Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6733Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588683264) }) = true
      norm_num [leaf6733Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6733CertificateValid :
    WideCertificateValid leaf6733Box leaf6733Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi343ValidityFacts
    leaf6733LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6733CoverageChecked :
    coverageCheck (innerAD leaf6733Box) leaf6733InnerLog = true := by
  rfl'

private theorem leaf6733InnerLogValid :
    leaf6733InnerLog.Valid 8 (innerAD leaf6733Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint488PositiveFacts.valid leaf6733CoverageChecked

private noncomputable def leaf6733InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629807/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6733InputLogOnePlusV_eq :
    leaf6733InputLogOnePlusV = outerEnclosure 24
      (leaf6733Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6733RoundedFacts : LeafRoundedFacts 8
    leaf6733Certificate.logOnePlusV leaf6733InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6733InputLogOnePlusV_eq }

private noncomputable def leaf6733Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi343InputQChi innerPair762Input
    leaf6733InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6733LowerChecked :
    lowerCheck 24 leaf6733Box leaf6733Inputs = true := by
  rfl'

private theorem leaf6733CoversExact : CoversExact 8
    leaf6733Box leaf6733Certificate leaf6733InnerLog leaf6733Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi343RoundedFacts
    innerPair762RoundedFacts leaf6733RoundedFacts (by rfl)

private theorem leaf6733FlatSound : Sound leaf6733Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6733CertificateValid
    leaf6733InnerLogValid leaf6733CoversExact leaf6733LowerChecked

private noncomputable def leaf6734Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (47/64), chiHi := (3/4) }

private noncomputable def leaf6734Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109063/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588656640) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (224156103/134217728) }, upper := { exponent := 1, mantissa := (55/32) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi344LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178083327/17177313280) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf6734InnerLog : WideLogData :=
  innerPair765Data

set_option maxRecDepth 1000000 in
private theorem leaf6734LocalValidity :
    LeafFacts leaf6734Box leaf6734Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf6734Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588656640) }) = true
      norm_num [leaf6734Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf6734CertificateValid :
    WideCertificateValid leaf6734Box leaf6734Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi344ValidityFacts
    leaf6734LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf6734CoverageChecked :
    coverageCheck (innerAD leaf6734Box) leaf6734InnerLog = true := by
  rfl'

private theorem leaf6734InnerLogValid :
    leaf6734InnerLog.Valid 8 (innerAD leaf6734Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint488PositiveFacts.valid leaf6734CoverageChecked

private noncomputable def leaf6734InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629833/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf6734InputLogOnePlusV_eq :
    leaf6734InputLogOnePlusV = outerEnclosure 24
      (leaf6734Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf6734RoundedFacts : LeafRoundedFacts 8
    leaf6734Certificate.logOnePlusV leaf6734InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf6734InputLogOnePlusV_eq }

private noncomputable def leaf6734Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi344InputQChi innerPair765Input
    leaf6734InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf6734LowerChecked :
    lowerCheck 24 leaf6734Box leaf6734Inputs = true := by
  rfl'

private theorem leaf6734CoversExact : CoversExact 8
    leaf6734Box leaf6734Certificate leaf6734InnerLog leaf6734Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi344RoundedFacts
    innerPair765RoundedFacts leaf6734RoundedFacts (by rfl)

private theorem leaf6734FlatSound : Sound leaf6734Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf6734CertificateValid
    leaf6734InnerLogValid leaf6734CoversExact leaf6734LowerChecked

private noncomputable def component136Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component136Node0_sound : Sound component136Node0Box :=
  sound_of_literal_split component136Node0Box leaf6702Box leaf6703Box
    .chi (41/64) (by rfl) (by rfl)
    leaf6702FlatSound leaf6703FlatSound

private noncomputable def component136Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component136Node1_sound : Sound component136Node1Box :=
  sound_of_literal_split component136Node1Box leaf6704Box leaf6705Box
    .chi (41/64) (by rfl) (by rfl)
    leaf6704FlatSound leaf6705FlatSound

private noncomputable def component136Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component136Node2_sound : Sound component136Node2Box :=
  sound_of_literal_split component136Node2Box component136Node0Box component136Node1Box
    .k (49/16) (by rfl) (by rfl)
    component136Node0_sound component136Node1_sound

private noncomputable def component136Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component136Node3_sound : Sound component136Node3Box :=
  sound_of_literal_split component136Node3Box leaf6706Box leaf6707Box
    .chi (43/64) (by rfl) (by rfl)
    leaf6706FlatSound leaf6707FlatSound

private noncomputable def component136Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component136Node4_sound : Sound component136Node4Box :=
  sound_of_literal_split component136Node4Box leaf6708Box leaf6709Box
    .chi (43/64) (by rfl) (by rfl)
    leaf6708FlatSound leaf6709FlatSound

private noncomputable def component136Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component136Node5_sound : Sound component136Node5Box :=
  sound_of_literal_split component136Node5Box component136Node3Box component136Node4Box
    .k (49/16) (by rfl) (by rfl)
    component136Node3_sound component136Node4_sound

private noncomputable def component136Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component136Node6_sound : Sound component136Node6Box :=
  sound_of_literal_split component136Node6Box component136Node2Box component136Node5Box
    .chi (21/32) (by rfl) (by rfl)
    component136Node2_sound component136Node5_sound

private noncomputable def component136Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component136Node7_sound : Sound component136Node7Box :=
  sound_of_literal_split component136Node7Box leaf6710Box leaf6711Box
    .chi (41/64) (by rfl) (by rfl)
    leaf6710FlatSound leaf6711FlatSound

private noncomputable def component136Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (5/8), chiHi := (41/64) }

set_option maxRecDepth 1000000 in
private theorem component136Node8_sound : Sound component136Node8Box :=
  sound_of_literal_split component136Node8Box leaf6712Box leaf6713Box
    .chi (81/128) (by rfl) (by rfl)
    leaf6712FlatSound leaf6713FlatSound

private noncomputable def component136Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component136Node9_sound : Sound component136Node9Box :=
  sound_of_literal_split component136Node9Box component136Node8Box leaf6714Box
    .chi (41/64) (by rfl) (by rfl)
    component136Node8_sound leaf6714FlatSound

private noncomputable def component136Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (5/8), chiHi := (21/32) }

set_option maxRecDepth 1000000 in
private theorem component136Node10_sound : Sound component136Node10Box :=
  sound_of_literal_split component136Node10Box component136Node7Box component136Node9Box
    .k (51/16) (by rfl) (by rfl)
    component136Node7_sound component136Node9_sound

private noncomputable def component136Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component136Node11_sound : Sound component136Node11Box :=
  sound_of_literal_split component136Node11Box leaf6715Box leaf6716Box
    .chi (43/64) (by rfl) (by rfl)
    leaf6715FlatSound leaf6716FlatSound

private noncomputable def component136Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component136Node12_sound : Sound component136Node12Box :=
  sound_of_literal_split component136Node12Box leaf6717Box leaf6718Box
    .chi (43/64) (by rfl) (by rfl)
    leaf6717FlatSound leaf6718FlatSound

private noncomputable def component136Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (21/32), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component136Node13_sound : Sound component136Node13Box :=
  sound_of_literal_split component136Node13Box component136Node11Box component136Node12Box
    .k (51/16) (by rfl) (by rfl)
    component136Node11_sound component136Node12_sound

private noncomputable def component136Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component136Node14_sound : Sound component136Node14Box :=
  sound_of_literal_split component136Node14Box component136Node10Box component136Node13Box
    .chi (21/32) (by rfl) (by rfl)
    component136Node10_sound component136Node13_sound

private noncomputable def component136Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (5/8), chiHi := (11/16) }

set_option maxRecDepth 1000000 in
private theorem component136Node15_sound : Sound component136Node15Box :=
  sound_of_literal_split component136Node15Box component136Node6Box component136Node14Box
    .k (25/8) (by rfl) (by rfl)
    component136Node6_sound component136Node14_sound

private noncomputable def component136Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component136Node16_sound : Sound component136Node16Box :=
  sound_of_literal_split component136Node16Box leaf6719Box leaf6720Box
    .chi (45/64) (by rfl) (by rfl)
    leaf6719FlatSound leaf6720FlatSound

private noncomputable def component136Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component136Node17_sound : Sound component136Node17Box :=
  sound_of_literal_split component136Node17Box leaf6721Box leaf6722Box
    .chi (45/64) (by rfl) (by rfl)
    leaf6721FlatSound leaf6722FlatSound

private noncomputable def component136Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component136Node18_sound : Sound component136Node18Box :=
  sound_of_literal_split component136Node18Box component136Node16Box component136Node17Box
    .k (49/16) (by rfl) (by rfl)
    component136Node16_sound component136Node17_sound

private noncomputable def component136Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component136Node19_sound : Sound component136Node19Box :=
  sound_of_literal_split component136Node19Box leaf6723Box leaf6724Box
    .chi (47/64) (by rfl) (by rfl)
    leaf6723FlatSound leaf6724FlatSound

private noncomputable def component136Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component136Node20_sound : Sound component136Node20Box :=
  sound_of_literal_split component136Node20Box leaf6725Box leaf6726Box
    .chi (47/64) (by rfl) (by rfl)
    leaf6725FlatSound leaf6726FlatSound

private noncomputable def component136Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component136Node21_sound : Sound component136Node21Box :=
  sound_of_literal_split component136Node21Box component136Node19Box component136Node20Box
    .k (49/16) (by rfl) (by rfl)
    component136Node19_sound component136Node20_sound

private noncomputable def component136Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component136Node22_sound : Sound component136Node22Box :=
  sound_of_literal_split component136Node22Box component136Node18Box component136Node21Box
    .chi (23/32) (by rfl) (by rfl)
    component136Node18_sound component136Node21_sound

private noncomputable def component136Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component136Node23_sound : Sound component136Node23Box :=
  sound_of_literal_split component136Node23Box leaf6727Box leaf6728Box
    .chi (45/64) (by rfl) (by rfl)
    leaf6727FlatSound leaf6728FlatSound

private noncomputable def component136Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component136Node24_sound : Sound component136Node24Box :=
  sound_of_literal_split component136Node24Box leaf6729Box leaf6730Box
    .chi (45/64) (by rfl) (by rfl)
    leaf6729FlatSound leaf6730FlatSound

private noncomputable def component136Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (11/16), chiHi := (23/32) }

set_option maxRecDepth 1000000 in
private theorem component136Node25_sound : Sound component136Node25Box :=
  sound_of_literal_split component136Node25Box component136Node23Box component136Node24Box
    .k (51/16) (by rfl) (by rfl)
    component136Node23_sound component136Node24_sound

private noncomputable def component136Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component136Node26_sound : Sound component136Node26Box :=
  sound_of_literal_split component136Node26Box leaf6731Box leaf6732Box
    .chi (47/64) (by rfl) (by rfl)
    leaf6731FlatSound leaf6732FlatSound

private noncomputable def component136Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component136Node27_sound : Sound component136Node27Box :=
  sound_of_literal_split component136Node27Box leaf6733Box leaf6734Box
    .chi (47/64) (by rfl) (by rfl)
    leaf6733FlatSound leaf6734FlatSound

private noncomputable def component136Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (23/32), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component136Node28_sound : Sound component136Node28Box :=
  sound_of_literal_split component136Node28Box component136Node26Box component136Node27Box
    .k (51/16) (by rfl) (by rfl)
    component136Node26_sound component136Node27_sound

private noncomputable def component136Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component136Node29_sound : Sound component136Node29Box :=
  sound_of_literal_split component136Node29Box component136Node25Box component136Node28Box
    .chi (23/32) (by rfl) (by rfl)
    component136Node25_sound component136Node28_sound

private noncomputable def component136Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (11/16), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
private theorem component136Node30_sound : Sound component136Node30Box :=
  sound_of_literal_split component136Node30Box component136Node22Box component136Node29Box
    .k (25/8) (by rfl) (by rfl)
    component136Node22_sound component136Node29_sound

noncomputable def component136Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (5/8), chiHi := (3/4) }

set_option maxRecDepth 1000000 in
theorem component136_sound : Sound component136Box :=
  sound_of_literal_split component136Box component136Node15Box component136Node30Box
    .chi (11/16) (by rfl) (by rfl)
    component136Node15_sound component136Node30_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
