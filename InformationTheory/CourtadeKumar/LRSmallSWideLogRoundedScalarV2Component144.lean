import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch9
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch11
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch12
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch13
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

private noncomputable def leaf7076Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf7076Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109059/67108864) }, vSqrt := { lower := (65529/65536), upper := (2863142229/2862901760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (218061631/134217728) }, upper := { exponent := 1, mantissa := (3425/2048) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5726043989/5725803520) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf7076InnerLog : WideLogData :=
  innerPair756Data

set_option maxRecDepth 1000000 in
private theorem leaf7076LocalValidity :
    LeafFacts leaf7076Box leaf7076Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7076Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2863142229/2862901760) }) = true
      norm_num [leaf7076Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7076CertificateValid :
    WideCertificateValid leaf7076Box leaf7076Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi345ValidityFacts
    leaf7076LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7076CoverageChecked :
    coverageCheck (innerAD leaf7076Box) leaf7076InnerLog = true := by
  rfl'

private theorem leaf7076InnerLogValid :
    leaf7076InnerLog.Valid 8 (innerAD leaf7076Box) :=
  wideLogDataValid_of_cachedCheck endpoint484PositiveFacts
    endpoint487PositiveFacts.valid leaf7076CoverageChecked

private noncomputable def leaf7076InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629785/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7076InputLogOnePlusV_eq :
    leaf7076InputLogOnePlusV = outerEnclosure 24
      (leaf7076Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7076RoundedFacts : LeafRoundedFacts 8
    leaf7076Certificate.logOnePlusV leaf7076InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7076InputLogOnePlusV_eq }

private noncomputable def leaf7076Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi345InputQChi innerPair756Input
    leaf7076InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7076LowerChecked :
    lowerCheck 24 leaf7076Box leaf7076Inputs = true := by
  rfl'

private theorem leaf7076CoversExact : CoversExact 8
    leaf7076Box leaf7076Certificate leaf7076InnerLog leaf7076Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi345RoundedFacts
    innerPair756RoundedFacts leaf7076RoundedFacts (by rfl)

private theorem leaf7076FlatSound : Sound leaf7076Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7076CertificateValid
    leaf7076InnerLogValid leaf7076CoversExact leaf7076LowerChecked

private noncomputable def leaf7077Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf7077Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109061/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588680192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (221207165/134217728) }, upper := { exponent := 1, mantissa := (1737/1024) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178106879/17177360384) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf7077InnerLog : WideLogData :=
  innerPair762Data

set_option maxRecDepth 1000000 in
private theorem leaf7077LocalValidity :
    LeafFacts leaf7077Box leaf7077Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7077Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588680192) }) = true
      norm_num [leaf7077Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7077CertificateValid :
    WideCertificateValid leaf7077Box leaf7077Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi346ValidityFacts
    leaf7077LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7077CoverageChecked :
    coverageCheck (innerAD leaf7077Box) leaf7077InnerLog = true := by
  rfl'

private theorem leaf7077InnerLogValid :
    leaf7077InnerLog.Valid 8 (innerAD leaf7077Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint488PositiveFacts.valid leaf7077CoverageChecked

private noncomputable def leaf7077InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814905/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7077InputLogOnePlusV_eq :
    leaf7077InputLogOnePlusV = outerEnclosure 24
      (leaf7077Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7077RoundedFacts : LeafRoundedFacts 8
    leaf7077Certificate.logOnePlusV leaf7077InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7077InputLogOnePlusV_eq }

private noncomputable def leaf7077Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi346InputQChi innerPair762Input
    leaf7077InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7077LowerChecked :
    lowerCheck 24 leaf7077Box leaf7077Inputs = true := by
  rfl'

private theorem leaf7077CoversExact : CoversExact 8
    leaf7077Box leaf7077Certificate leaf7077InnerLog leaf7077Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi346RoundedFacts
    innerPair762RoundedFacts leaf7077RoundedFacts (by rfl)

private theorem leaf7077FlatSound : Sound leaf7077Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7077CertificateValid
    leaf7077InnerLogValid leaf7077CoversExact leaf7077LowerChecked

private noncomputable def leaf7078Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf7078Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109061/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588680192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (221207165/134217728) }, upper := { exponent := 1, mantissa := (1737/1024) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178106879/17177360384) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf7078InnerLog : WideLogData :=
  innerPair762Data

set_option maxRecDepth 1000000 in
private theorem leaf7078LocalValidity :
    LeafFacts leaf7078Box leaf7078Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7078Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588680192) }) = true
      norm_num [leaf7078Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7078CertificateValid :
    WideCertificateValid leaf7078Box leaf7078Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi345ValidityFacts
    leaf7078LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7078CoverageChecked :
    coverageCheck (innerAD leaf7078Box) leaf7078InnerLog = true := by
  rfl'

private theorem leaf7078InnerLogValid :
    leaf7078InnerLog.Valid 8 (innerAD leaf7078Box) :=
  wideLogDataValid_of_cachedCheck endpoint485PositiveFacts
    endpoint488PositiveFacts.valid leaf7078CoverageChecked

private noncomputable def leaf7078InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814905/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7078InputLogOnePlusV_eq :
    leaf7078InputLogOnePlusV = outerEnclosure 24
      (leaf7078Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7078RoundedFacts : LeafRoundedFacts 8
    leaf7078Certificate.logOnePlusV leaf7078InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7078InputLogOnePlusV_eq }

private noncomputable def leaf7078Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi345InputQChi innerPair762Input
    leaf7078InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7078LowerChecked :
    lowerCheck 24 leaf7078Box leaf7078Inputs = true := by
  rfl'

private theorem leaf7078CoversExact : CoversExact 8
    leaf7078Box leaf7078Certificate leaf7078InnerLog leaf7078Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi345RoundedFacts
    innerPair762RoundedFacts leaf7078RoundedFacts (by rfl)

private theorem leaf7078FlatSound : Sound leaf7078Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7078CertificateValid
    leaf7078InnerLogValid leaf7078CoversExact leaf7078LowerChecked

private noncomputable def leaf7079Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf7079Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109063/67108864) }, vSqrt := { lower := (65529/65536), upper := (2863142229/2862884864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (224418231/134217728) }, upper := { exponent := 1, mantissa := (881/512) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (5726027093/5725769728) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf7079InnerLog : WideLogData :=
  innerPair766Data

set_option maxRecDepth 1000000 in
private theorem leaf7079LocalValidity :
    LeafFacts leaf7079Box leaf7079Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7079Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (2863142229/2862884864) }) = true
      norm_num [leaf7079Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7079CertificateValid :
    WideCertificateValid leaf7079Box leaf7079Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi346ValidityFacts
    leaf7079LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7079CoverageChecked :
    coverageCheck (innerAD leaf7079Box) leaf7079InnerLog = true := by
  rfl'

private theorem leaf7079InnerLogValid :
    leaf7079InnerLog.Valid 8 (innerAD leaf7079Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint489PositiveFacts.valid leaf7079CoverageChecked

private noncomputable def leaf7079InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629835/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7079InputLogOnePlusV_eq :
    leaf7079InputLogOnePlusV = outerEnclosure 24
      (leaf7079Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7079RoundedFacts : LeafRoundedFacts 8
    leaf7079Certificate.logOnePlusV leaf7079InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7079InputLogOnePlusV_eq }

private noncomputable def leaf7079Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi346InputQChi innerPair766Input
    leaf7079InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7079LowerChecked :
    lowerCheck 24 leaf7079Box leaf7079Inputs = true := by
  rfl'

private theorem leaf7079CoversExact : CoversExact 8
    leaf7079Box leaf7079Certificate leaf7079InnerLog leaf7079Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi346RoundedFacts
    innerPair766RoundedFacts leaf7079RoundedFacts (by rfl)

private theorem leaf7079FlatSound : Sound leaf7079Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7079CertificateValid
    leaf7079InnerLogValid leaf7079CoversExact leaf7079LowerChecked

private noncomputable def leaf7080Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (25/32), chiHi := (51/64) }

private noncomputable def leaf7080Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109063/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588655104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (224352699/134217728) }, upper := { exponent := 1, mantissa := (3523/2048) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi361LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178081791/17177310208) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf7080InnerLog : WideLogData :=
  innerPair766Data

set_option maxRecDepth 1000000 in
private theorem leaf7080LocalValidity :
    LeafFacts leaf7080Box leaf7080Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7080Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588655104) }) = true
      norm_num [leaf7080Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7080CertificateValid :
    WideCertificateValid leaf7080Box leaf7080Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi361ValidityFacts
    leaf7080LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7080CoverageChecked :
    coverageCheck (innerAD leaf7080Box) leaf7080InnerLog = true := by
  rfl'

private theorem leaf7080InnerLogValid :
    leaf7080InnerLog.Valid 8 (innerAD leaf7080Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint489PositiveFacts.valid leaf7080CoverageChecked

private noncomputable def leaf7080InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814917/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7080InputLogOnePlusV_eq :
    leaf7080InputLogOnePlusV = outerEnclosure 24
      (leaf7080Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7080RoundedFacts : LeafRoundedFacts 8
    leaf7080Certificate.logOnePlusV leaf7080InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7080InputLogOnePlusV_eq }

private noncomputable def leaf7080Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi361InputQChi innerPair766Input
    leaf7080InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7080LowerChecked :
    lowerCheck 24 leaf7080Box leaf7080Inputs = true := by
  rfl'

private theorem leaf7080CoversExact : CoversExact 8
    leaf7080Box leaf7080Certificate leaf7080InnerLog leaf7080Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi361RoundedFacts
    innerPair766RoundedFacts leaf7080RoundedFacts (by rfl)

private theorem leaf7080FlatSound : Sound leaf7080Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7080CertificateValid
    leaf7080InnerLogValid leaf7080CoversExact leaf7080LowerChecked

private noncomputable def leaf7081Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (51/64), chiHi := (13/16) }

private noncomputable def leaf7081Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109065/67108864) }, vSqrt := { lower := (65529/65536), upper := (11452394153/11451506688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (227498233/134217728) }, upper := { exponent := 1, mantissa := (893/512) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi362LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22903900841/22903013376) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf7081InnerLog : WideLogData :=
  innerPair770Data

set_option maxRecDepth 1000000 in
private theorem leaf7081LocalValidity :
    LeafFacts leaf7081Box leaf7081Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7081Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452394153/11451506688) }) = true
      norm_num [leaf7081Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7081CertificateValid :
    WideCertificateValid leaf7081Box leaf7081Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi362ValidityFacts
    leaf7081LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7081CoverageChecked :
    coverageCheck (innerAD leaf7081Box) leaf7081InnerLog = true := by
  rfl'

private theorem leaf7081InnerLogValid :
    leaf7081InnerLog.Valid 8 (innerAD leaf7081Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint489PositiveFacts.valid leaf7081CoverageChecked

private noncomputable def leaf7081InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629731/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7081InputLogOnePlusV_eq :
    leaf7081InputLogOnePlusV = outerEnclosure 24
      (leaf7081Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7081RoundedFacts : LeafRoundedFacts 8
    leaf7081Certificate.logOnePlusV leaf7081InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7081InputLogOnePlusV_eq }

private noncomputable def leaf7081Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi362InputQChi innerPair770Input
    leaf7081InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7081LowerChecked :
    lowerCheck 24 leaf7081Box leaf7081Inputs = true := by
  rfl'

private theorem leaf7081CoversExact : CoversExact 8
    leaf7081Box leaf7081Certificate leaf7081InnerLog leaf7081Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi362RoundedFacts
    innerPair770RoundedFacts leaf7081RoundedFacts (by rfl)

private theorem leaf7081FlatSound : Sound leaf7081Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7081CertificateValid
    leaf7081InnerLogValid leaf7081CoversExact leaf7081LowerChecked

private noncomputable def leaf7082Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (25/32), chiHi := (51/64) }

private noncomputable def leaf7082Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109065/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354515968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (227629297/134217728) }, upper := { exponent := 1, mantissa := (1787/1024) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi361LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711698427/68709031936) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf7082InnerLog : WideLogData :=
  innerPair770Data

set_option maxRecDepth 1000000 in
private theorem leaf7082LocalValidity :
    LeafFacts leaf7082Box leaf7082Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7082Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354515968) }) = true
      norm_num [leaf7082Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7082CertificateValid :
    WideCertificateValid leaf7082Box leaf7082Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi361ValidityFacts
    leaf7082LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7082CoverageChecked :
    coverageCheck (innerAD leaf7082Box) leaf7082InnerLog = true := by
  rfl'

private theorem leaf7082InnerLogValid :
    leaf7082InnerLog.Valid 8 (innerAD leaf7082Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint489PositiveFacts.valid leaf7082CoverageChecked

private noncomputable def leaf7082InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907433/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7082InputLogOnePlusV_eq :
    leaf7082InputLogOnePlusV = outerEnclosure 24
      (leaf7082Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7082RoundedFacts : LeafRoundedFacts 8
    leaf7082Certificate.logOnePlusV leaf7082InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7082InputLogOnePlusV_eq }

private noncomputable def leaf7082Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi361InputQChi innerPair770Input
    leaf7082InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7082LowerChecked :
    lowerCheck 24 leaf7082Box leaf7082Inputs = true := by
  rfl'

private theorem leaf7082CoversExact : CoversExact 8
    leaf7082Box leaf7082Certificate leaf7082InnerLog leaf7082Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi361RoundedFacts
    innerPair770RoundedFacts leaf7082RoundedFacts (by rfl)

private theorem leaf7082FlatSound : Sound leaf7082Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7082CertificateValid
    leaf7082InnerLogValid leaf7082CoversExact leaf7082LowerChecked

private noncomputable def leaf7083Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (51/64), chiHi := (13/16) }

private noncomputable def leaf7083Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109067/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354413568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (230840363/134217728) }, upper := { exponent := 1, mantissa := (453/256) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi362LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711596027/68708827136) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf7083InnerLog : WideLogData :=
  innerPair775Data

set_option maxRecDepth 1000000 in
private theorem leaf7083LocalValidity :
    LeafFacts leaf7083Box leaf7083Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7083Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354413568) }) = true
      norm_num [leaf7083Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7083CertificateValid :
    WideCertificateValid leaf7083Box leaf7083Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi362ValidityFacts
    leaf7083LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7083CoverageChecked :
    coverageCheck (innerAD leaf7083Box) leaf7083InnerLog = true := by
  rfl'

private theorem leaf7083InnerLogValid :
    leaf7083InnerLog.Valid 8 (innerAD leaf7083Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint498PositiveFacts.valid leaf7083CoverageChecked

private noncomputable def leaf7083InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629757/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7083InputLogOnePlusV_eq :
    leaf7083InputLogOnePlusV = outerEnclosure 24
      (leaf7083Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7083RoundedFacts : LeafRoundedFacts 8
    leaf7083Certificate.logOnePlusV leaf7083InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7083InputLogOnePlusV_eq }

private noncomputable def leaf7083Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi362InputQChi innerPair775Input
    leaf7083InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7083LowerChecked :
    lowerCheck 24 leaf7083Box leaf7083Inputs = true := by
  rfl'

private theorem leaf7083CoversExact : CoversExact 8
    leaf7083Box leaf7083Certificate leaf7083InnerLog leaf7083Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi362RoundedFacts
    innerPair775RoundedFacts leaf7083RoundedFacts (by rfl)

private theorem leaf7083FlatSound : Sound leaf7083Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7083CertificateValid
    leaf7083InnerLogValid leaf7083CoversExact leaf7083LowerChecked

private noncomputable def leaf7084Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf7084Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109063/67108864) }, vSqrt := { lower := (65529/65536), upper := (8589426687/8588655104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (224352699/134217728) }, upper := { exponent := 1, mantissa := (3523/2048) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (17178081791/17177310208) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf7084InnerLog : WideLogData :=
  innerPair766Data

set_option maxRecDepth 1000000 in
private theorem leaf7084LocalValidity :
    LeafFacts leaf7084Box leaf7084Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7084Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (8589426687/8588655104) }) = true
      norm_num [leaf7084Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7084CertificateValid :
    WideCertificateValid leaf7084Box leaf7084Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi345ValidityFacts
    leaf7084LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7084CoverageChecked :
    coverageCheck (innerAD leaf7084Box) leaf7084InnerLog = true := by
  rfl'

private theorem leaf7084InnerLogValid :
    leaf7084InnerLog.Valid 8 (innerAD leaf7084Box) :=
  wideLogDataValid_of_cachedCheck endpoint486PositiveFacts
    endpoint489PositiveFacts.valid leaf7084CoverageChecked

private noncomputable def leaf7084InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814917/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7084InputLogOnePlusV_eq :
    leaf7084InputLogOnePlusV = outerEnclosure 24
      (leaf7084Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7084RoundedFacts : LeafRoundedFacts 8
    leaf7084Certificate.logOnePlusV leaf7084InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7084InputLogOnePlusV_eq }

private noncomputable def leaf7084Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi345InputQChi innerPair766Input
    leaf7084InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7084LowerChecked :
    lowerCheck 24 leaf7084Box leaf7084Inputs = true := by
  rfl'

private theorem leaf7084CoversExact : CoversExact 8
    leaf7084Box leaf7084Certificate leaf7084InnerLog leaf7084Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi345RoundedFacts
    innerPair766RoundedFacts leaf7084RoundedFacts (by rfl)

private theorem leaf7084FlatSound : Sound leaf7084Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7084CertificateValid
    leaf7084InnerLogValid leaf7084CoversExact leaf7084LowerChecked

private noncomputable def leaf7085Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf7085Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109065/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354515968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (227629297/134217728) }, upper := { exponent := 1, mantissa := (1787/1024) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711698427/68709031936) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf7085InnerLog : WideLogData :=
  innerPair770Data

set_option maxRecDepth 1000000 in
private theorem leaf7085LocalValidity :
    LeafFacts leaf7085Box leaf7085Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7085Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354515968) }) = true
      norm_num [leaf7085Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7085CertificateValid :
    WideCertificateValid leaf7085Box leaf7085Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi346ValidityFacts
    leaf7085LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7085CoverageChecked :
    coverageCheck (innerAD leaf7085Box) leaf7085InnerLog = true := by
  rfl'

private theorem leaf7085InnerLogValid :
    leaf7085InnerLog.Valid 8 (innerAD leaf7085Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint489PositiveFacts.valid leaf7085CoverageChecked

private noncomputable def leaf7085InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907433/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7085InputLogOnePlusV_eq :
    leaf7085InputLogOnePlusV = outerEnclosure 24
      (leaf7085Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7085RoundedFacts : LeafRoundedFacts 8
    leaf7085Certificate.logOnePlusV leaf7085InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7085InputLogOnePlusV_eq }

private noncomputable def leaf7085Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi346InputQChi innerPair770Input
    leaf7085InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7085LowerChecked :
    lowerCheck 24 leaf7085Box leaf7085Inputs = true := by
  rfl'

private theorem leaf7085CoversExact : CoversExact 8
    leaf7085Box leaf7085Certificate leaf7085InnerLog leaf7085Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi346RoundedFacts
    innerPair770RoundedFacts leaf7085RoundedFacts (by rfl)

private theorem leaf7085FlatSound : Sound leaf7085Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7085CertificateValid
    leaf7085InnerLogValid leaf7085CoversExact leaf7085LowerChecked

private noncomputable def leaf7086Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf7086Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65531/65536), upper := (67109065/67108864) }, vSqrt := { lower := (65529/65536), upper := (11452394153/11451506688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (227498233/134217728) }, upper := { exponent := 1, mantissa := (893/512) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22903900841/22903013376) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf7086InnerLog : WideLogData :=
  innerPair770Data

set_option maxRecDepth 1000000 in
private theorem leaf7086LocalValidity :
    LeafFacts leaf7086Box leaf7086Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7086Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452394153/11451506688) }) = true
      norm_num [leaf7086Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7086CertificateValid :
    WideCertificateValid leaf7086Box leaf7086Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi345ValidityFacts
    leaf7086LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7086CoverageChecked :
    coverageCheck (innerAD leaf7086Box) leaf7086InnerLog = true := by
  rfl'

private theorem leaf7086InnerLogValid :
    leaf7086InnerLog.Valid 8 (innerAD leaf7086Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint489PositiveFacts.valid leaf7086CoverageChecked

private noncomputable def leaf7086InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629731/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7086InputLogOnePlusV_eq :
    leaf7086InputLogOnePlusV = outerEnclosure 24
      (leaf7086Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7086RoundedFacts : LeafRoundedFacts 8
    leaf7086Certificate.logOnePlusV leaf7086InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7086InputLogOnePlusV_eq }

private noncomputable def leaf7086Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi345InputQChi innerPair770Input
    leaf7086InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7086LowerChecked :
    lowerCheck 24 leaf7086Box leaf7086Inputs = true := by
  rfl'

private theorem leaf7086CoversExact : CoversExact 8
    leaf7086Box leaf7086Certificate leaf7086InnerLog leaf7086Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi345RoundedFacts
    innerPair770RoundedFacts leaf7086RoundedFacts (by rfl)

private theorem leaf7086FlatSound : Sound leaf7086Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7086CertificateValid
    leaf7086InnerLogValid leaf7086CoversExact leaf7086LowerChecked

private noncomputable def leaf7087Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf7087Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109067/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354413568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (230840363/134217728) }, upper := { exponent := 1, mantissa := (453/256) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711596027/68708827136) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf7087InnerLog : WideLogData :=
  innerPair775Data

set_option maxRecDepth 1000000 in
private theorem leaf7087LocalValidity :
    LeafFacts leaf7087Box leaf7087Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7087Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354413568) }) = true
      norm_num [leaf7087Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7087CertificateValid :
    WideCertificateValid leaf7087Box leaf7087Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi346ValidityFacts
    leaf7087LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7087CoverageChecked :
    coverageCheck (innerAD leaf7087Box) leaf7087InnerLog = true := by
  rfl'

private theorem leaf7087InnerLogValid :
    leaf7087InnerLog.Valid 8 (innerAD leaf7087Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint498PositiveFacts.valid leaf7087CoverageChecked

private noncomputable def leaf7087InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629757/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7087InputLogOnePlusV_eq :
    leaf7087InputLogOnePlusV = outerEnclosure 24
      (leaf7087Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7087RoundedFacts : LeafRoundedFacts 8
    leaf7087Certificate.logOnePlusV leaf7087InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7087InputLogOnePlusV_eq }

private noncomputable def leaf7087Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi346InputQChi innerPair775Input
    leaf7087InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7087LowerChecked :
    lowerCheck 24 leaf7087Box leaf7087Inputs = true := by
  rfl'

private theorem leaf7087CoversExact : CoversExact 8
    leaf7087Box leaf7087Certificate leaf7087InnerLog leaf7087Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi346RoundedFacts
    innerPair775RoundedFacts leaf7087RoundedFacts (by rfl)

private theorem leaf7087FlatSound : Sound leaf7087Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7087CertificateValid
    leaf7087InnerLogValid leaf7087CoversExact leaf7087LowerChecked

private noncomputable def leaf7088Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (25/32), chiHi := (51/64) }

private noncomputable def leaf7088Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109067/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354411520) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (230905895/134217728) }, upper := { exponent := 1, mantissa := (3625/2048) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi361LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711593979/68708823040) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf7088InnerLog : WideLogData :=
  innerPair775Data

set_option maxRecDepth 1000000 in
private theorem leaf7088LocalValidity :
    LeafFacts leaf7088Box leaf7088Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7088Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354411520) }) = true
      norm_num [leaf7088Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7088CertificateValid :
    WideCertificateValid leaf7088Box leaf7088Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi361ValidityFacts
    leaf7088LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7088CoverageChecked :
    coverageCheck (innerAD leaf7088Box) leaf7088InnerLog = true := by
  rfl'

private theorem leaf7088InnerLogValid :
    leaf7088InnerLog.Valid 8 (innerAD leaf7088Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint498PositiveFacts.valid leaf7088CoverageChecked

private noncomputable def leaf7088InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629757/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7088InputLogOnePlusV_eq :
    leaf7088InputLogOnePlusV = outerEnclosure 24
      (leaf7088Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7088RoundedFacts : LeafRoundedFacts 8
    leaf7088Certificate.logOnePlusV leaf7088InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7088InputLogOnePlusV_eq }

private noncomputable def leaf7088Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi361InputQChi innerPair775Input
    leaf7088InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7088LowerChecked :
    lowerCheck 24 leaf7088Box leaf7088Inputs = true := by
  rfl'

private theorem leaf7088CoversExact : CoversExact 8
    leaf7088Box leaf7088Certificate leaf7088InnerLog leaf7088Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi361RoundedFacts
    innerPair775RoundedFacts leaf7088RoundedFacts (by rfl)

private theorem leaf7088FlatSound : Sound leaf7088Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7088CertificateValid
    leaf7088InnerLogValid leaf7088CoversExact leaf7088LowerChecked

private noncomputable def leaf7089Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (51/64), chiHi := (13/16) }

private noncomputable def leaf7089Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109069/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354307072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (234182493/134217728) }, upper := { exponent := 1, mantissa := (919/512) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi362LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711489531/68708614144) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf7089InnerLog : WideLogData :=
  innerPair776Data

set_option maxRecDepth 1000000 in
private theorem leaf7089LocalValidity :
    LeafFacts leaf7089Box leaf7089Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7089Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354307072) }) = true
      norm_num [leaf7089Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7089CertificateValid :
    WideCertificateValid leaf7089Box leaf7089Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi362ValidityFacts
    leaf7089LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7089CoverageChecked :
    coverageCheck (innerAD leaf7089Box) leaf7089InnerLog = true := by
  rfl'

private theorem leaf7089InnerLogValid :
    leaf7089InnerLog.Valid 8 (innerAD leaf7089Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint500PositiveFacts.valid leaf7089CoverageChecked

private noncomputable def leaf7089InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629783/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7089InputLogOnePlusV_eq :
    leaf7089InputLogOnePlusV = outerEnclosure 24
      (leaf7089Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7089RoundedFacts : LeafRoundedFacts 8
    leaf7089Certificate.logOnePlusV leaf7089InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7089InputLogOnePlusV_eq }

private noncomputable def leaf7089Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi362InputQChi innerPair776Input
    leaf7089InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7089LowerChecked :
    lowerCheck 24 leaf7089Box leaf7089Inputs = true := by
  rfl'

private theorem leaf7089CoversExact : CoversExact 8
    leaf7089Box leaf7089Certificate leaf7089InnerLog leaf7089Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi362RoundedFacts
    innerPair776RoundedFacts leaf7089RoundedFacts (by rfl)

private theorem leaf7089FlatSound : Sound leaf7089Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7089CertificateValid
    leaf7089InnerLogValid leaf7089CoversExact leaf7089LowerChecked

private noncomputable def leaf7090Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (25/32), chiHi := (51/64) }

private noncomputable def leaf7090Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109069/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354307072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (234182493/134217728) }, upper := { exponent := 1, mantissa := (919/512) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi361LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711489531/68708614144) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf7090InnerLog : WideLogData :=
  innerPair776Data

set_option maxRecDepth 1000000 in
private theorem leaf7090LocalValidity :
    LeafFacts leaf7090Box leaf7090Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7090Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354307072) }) = true
      norm_num [leaf7090Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7090CertificateValid :
    WideCertificateValid leaf7090Box leaf7090Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi361ValidityFacts
    leaf7090LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7090CoverageChecked :
    coverageCheck (innerAD leaf7090Box) leaf7090InnerLog = true := by
  rfl'

private theorem leaf7090InnerLogValid :
    leaf7090InnerLog.Valid 8 (innerAD leaf7090Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint500PositiveFacts.valid leaf7090CoverageChecked

private noncomputable def leaf7090InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629783/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7090InputLogOnePlusV_eq :
    leaf7090InputLogOnePlusV = outerEnclosure 24
      (leaf7090Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7090RoundedFacts : LeafRoundedFacts 8
    leaf7090Certificate.logOnePlusV leaf7090InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7090InputLogOnePlusV_eq }

private noncomputable def leaf7090Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi361InputQChi innerPair776Input
    leaf7090InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7090LowerChecked :
    lowerCheck 24 leaf7090Box leaf7090Inputs = true := by
  rfl'

private theorem leaf7090CoversExact : CoversExact 8
    leaf7090Box leaf7090Certificate leaf7090InnerLog leaf7090Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi361RoundedFacts
    innerPair776RoundedFacts leaf7090RoundedFacts (by rfl)

private theorem leaf7090FlatSound : Sound leaf7090Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7090CertificateValid
    leaf7090InnerLogValid leaf7090CoversExact leaf7090LowerChecked

private noncomputable def leaf7091Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (51/64), chiHi := (13/16) }

private noncomputable def leaf7091Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109071/67108864) }, vSqrt := { lower := (65529/65536), upper := (11452394153/11451400192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (237524623/134217728) }, upper := { exponent := 1, mantissa := (233/128) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi362LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22903794345/22902800384) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf7091InnerLog : WideLogData :=
  innerPair779Data

set_option maxRecDepth 1000000 in
private theorem leaf7091LocalValidity :
    LeafFacts leaf7091Box leaf7091Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7091Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452394153/11451400192) }) = true
      norm_num [leaf7091Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7091CertificateValid :
    WideCertificateValid leaf7091Box leaf7091Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi362ValidityFacts
    leaf7091LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7091CoverageChecked :
    coverageCheck (innerAD leaf7091Box) leaf7091InnerLog = true := by
  rfl'

private theorem leaf7091InnerLogValid :
    leaf7091InnerLog.Valid 8 (innerAD leaf7091Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint501PositiveFacts.valid leaf7091CoverageChecked

private noncomputable def leaf7091InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629809/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7091InputLogOnePlusV_eq :
    leaf7091InputLogOnePlusV = outerEnclosure 24
      (leaf7091Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7091RoundedFacts : LeafRoundedFacts 8
    leaf7091Certificate.logOnePlusV leaf7091InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7091InputLogOnePlusV_eq }

private noncomputable def leaf7091Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi362InputQChi innerPair779Input
    leaf7091InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7091LowerChecked :
    lowerCheck 24 leaf7091Box leaf7091Inputs = true := by
  rfl'

private theorem leaf7091CoversExact : CoversExact 8
    leaf7091Box leaf7091Certificate leaf7091InnerLog leaf7091Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi362RoundedFacts
    innerPair779RoundedFacts leaf7091RoundedFacts (by rfl)

private theorem leaf7091FlatSound : Sound leaf7091Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7091CertificateValid
    leaf7091InnerLogValid leaf7091CoversExact leaf7091LowerChecked

private noncomputable def leaf7092Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf7092Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554583/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354319360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (115305451/67108864) }, upper := { exponent := 1, mantissa := (1835/1024) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711501819/68708638720) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf7092InnerLog : WideLogData :=
  innerPair866Data

set_option maxRecDepth 1000000 in
private theorem leaf7092LocalValidity :
    LeafFacts leaf7092Box leaf7092Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7092Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354319360) }) = true
      norm_num [leaf7092Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7092CertificateValid :
    WideCertificateValid leaf7092Box leaf7092Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi90ValidityFacts
    leaf7092LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7092CoverageChecked :
    coverageCheck (innerAD leaf7092Box) leaf7092InnerLog = true := by
  rfl'

private theorem leaf7092InnerLogValid :
    leaf7092InnerLog.Valid 8 (innerAD leaf7092Box) :=
  wideLogDataValid_of_cachedCheck endpoint578PositiveFacts
    endpoint562PositiveFacts.valid leaf7092CoverageChecked

private noncomputable def leaf7092InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907445/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7092InputLogOnePlusV_eq :
    leaf7092InputLogOnePlusV = outerEnclosure 24
      (leaf7092Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7092RoundedFacts : LeafRoundedFacts 8
    leaf7092Certificate.logOnePlusV leaf7092InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7092InputLogOnePlusV_eq }

private noncomputable def leaf7092Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi90InputQChi innerPair866Input
    leaf7092InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7092LowerChecked :
    lowerCheck 24 leaf7092Box leaf7092Inputs = true := by
  rfl'

private theorem leaf7092CoversExact : CoversExact 8
    leaf7092Box leaf7092Certificate leaf7092InnerLog leaf7092Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi90RoundedFacts
    innerPair866RoundedFacts leaf7092RoundedFacts (by rfl)

private theorem leaf7092FlatSound : Sound leaf7092Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7092CertificateValid
    leaf7092InnerLogValid leaf7092CoversExact leaf7092LowerChecked

private noncomputable def leaf7093Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf7093Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554585/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354208768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (117009281/67108864) }, upper := { exponent := 1, mantissa := (931/512) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711391227/68708417536) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf7093InnerLog : WideLogData :=
  innerPair856Data

set_option maxRecDepth 1000000 in
private theorem leaf7093LocalValidity :
    LeafFacts leaf7093Box leaf7093Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7093Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354208768) }) = true
      norm_num [leaf7093Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7093CertificateValid :
    WideCertificateValid leaf7093Box leaf7093Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi90ValidityFacts
    leaf7093LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7093CoverageChecked :
    coverageCheck (innerAD leaf7093Box) leaf7093InnerLog = true := by
  rfl'

private theorem leaf7093InnerLogValid :
    leaf7093InnerLog.Valid 8 (innerAD leaf7093Box) :=
  wideLogDataValid_of_cachedCheck endpoint561PositiveFacts
    endpoint568PositiveFacts.valid leaf7093CoverageChecked

private noncomputable def leaf7093InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629807/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7093InputLogOnePlusV_eq :
    leaf7093InputLogOnePlusV = outerEnclosure 24
      (leaf7093Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7093RoundedFacts : LeafRoundedFacts 8
    leaf7093Certificate.logOnePlusV leaf7093InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7093InputLogOnePlusV_eq }

private noncomputable def leaf7093Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi90InputQChi innerPair856Input
    leaf7093InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7093LowerChecked :
    lowerCheck 24 leaf7093Box leaf7093Inputs = true := by
  rfl'

private theorem leaf7093CoversExact : CoversExact 8
    leaf7093Box leaf7093Certificate leaf7093InnerLog leaf7093Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi90RoundedFacts
    innerPair856RoundedFacts leaf7093RoundedFacts (by rfl)

private theorem leaf7093FlatSound : Sound leaf7093Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7093CertificateValid
    leaf7093InnerLogValid leaf7093CoversExact leaf7093LowerChecked

private noncomputable def leaf7094Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf7094Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554585/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354118656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (118450985/67108864) }, upper := { exponent := 1, mantissa := (471/256) } }, logOuter := sk123LogOuterCertificate, logK := sk123LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711301115/68708237312) } }, logDArg := sk123LogDArgCertificate }

private noncomputable def leaf7094InnerLog : WideLogData :=
  innerPair779Data

set_option maxRecDepth 1000000 in
private theorem leaf7094LocalValidity :
    LeafFacts leaf7094Box leaf7094Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7094Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354118656) }) = true
      norm_num [leaf7094Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7094CertificateValid :
    WideCertificateValid leaf7094Box leaf7094Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk123ValidityFacts chi91ValidityFacts
    leaf7094LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7094CoverageChecked :
    coverageCheck (innerAD leaf7094Box) leaf7094InnerLog = true := by
  rfl'

private theorem leaf7094InnerLogValid :
    leaf7094InnerLog.Valid 8 (innerAD leaf7094Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint501PositiveFacts.valid leaf7094CoverageChecked

private noncomputable def leaf7094InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629829/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7094InputLogOnePlusV_eq :
    leaf7094InputLogOnePlusV = outerEnclosure 24
      (leaf7094Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7094RoundedFacts : LeafRoundedFacts 8
    leaf7094Certificate.logOnePlusV leaf7094InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7094InputLogOnePlusV_eq }

private noncomputable def leaf7094Inputs : Inputs :=
  inputsOfCaches globalInput sk123RoundedInputs
    chi91InputQChi innerPair779Input
    leaf7094InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7094LowerChecked :
    lowerCheck 24 leaf7094Box leaf7094Inputs = true := by
  rfl'

private theorem leaf7094CoversExact : CoversExact 8
    leaf7094Box leaf7094Certificate leaf7094InnerLog leaf7094Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk123RoundedFacts chi91RoundedFacts
    innerPair779RoundedFacts leaf7094RoundedFacts (by rfl)

private theorem leaf7094FlatSound : Sound leaf7094Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7094CertificateValid
    leaf7094InnerLogValid leaf7094CoversExact leaf7094LowerChecked

private noncomputable def leaf7095Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf7095Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554587/33554432) }, vSqrt := { lower := (65529/65536), upper := (602757587/602701824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (120220347/67108864) }, upper := { exponent := 1, mantissa := (239/128) } }, logOuter := sk124LogOuterCertificate, logK := sk124LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (1205459411/1205403648) } }, logDArg := sk124LogDArgCertificate }

private noncomputable def leaf7095InnerLog : WideLogData :=
  innerPair795Data

set_option maxRecDepth 1000000 in
private theorem leaf7095LocalValidity :
    LeafFacts leaf7095Box leaf7095Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7095Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (602757587/602701824) }) = true
      norm_num [leaf7095Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7095CertificateValid :
    WideCertificateValid leaf7095Box leaf7095Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk124ValidityFacts chi91ValidityFacts
    leaf7095LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7095CoverageChecked :
    coverageCheck (innerAD leaf7095Box) leaf7095InnerLog = true := by
  rfl'

private theorem leaf7095InnerLogValid :
    leaf7095InnerLog.Valid 8 (innerAD leaf7095Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint502PositiveFacts.valid leaf7095CoverageChecked

private noncomputable def leaf7095InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629857/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7095InputLogOnePlusV_eq :
    leaf7095InputLogOnePlusV = outerEnclosure 24
      (leaf7095Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7095RoundedFacts : LeafRoundedFacts 8
    leaf7095Certificate.logOnePlusV leaf7095InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7095InputLogOnePlusV_eq }

private noncomputable def leaf7095Inputs : Inputs :=
  inputsOfCaches globalInput sk124RoundedInputs
    chi91InputQChi innerPair795Input
    leaf7095InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7095LowerChecked :
    lowerCheck 24 leaf7095Box leaf7095Inputs = true := by
  rfl'

private theorem leaf7095CoversExact : CoversExact 8
    leaf7095Box leaf7095Certificate leaf7095InnerLog leaf7095Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk124RoundedFacts chi91RoundedFacts
    innerPair795RoundedFacts leaf7095RoundedFacts (by rfl)

private theorem leaf7095FlatSound : Sound leaf7095Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7095CertificateValid
    leaf7095InnerLogValid leaf7095CoversExact leaf7095LowerChecked

private noncomputable def leaf7096Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (13/16), chiHi := (27/32) }

private noncomputable def leaf7096Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554587/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354098176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (118713111/67108864) }, upper := { exponent := 1, mantissa := (1889/1024) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi90LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711280635/68708196352) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf7096InnerLog : WideLogData :=
  innerPair867Data

set_option maxRecDepth 1000000 in
private theorem leaf7096LocalValidity :
    LeafFacts leaf7096Box leaf7096Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7096Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354098176) }) = true
      norm_num [leaf7096Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7096CertificateValid :
    WideCertificateValid leaf7096Box leaf7096Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi90ValidityFacts
    leaf7096LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7096CoverageChecked :
    coverageCheck (innerAD leaf7096Box) leaf7096InnerLog = true := by
  rfl'

private theorem leaf7096InnerLogValid :
    leaf7096InnerLog.Valid 8 (innerAD leaf7096Box) :=
  wideLogDataValid_of_cachedCheck endpoint579PositiveFacts
    endpoint580PositiveFacts.valid leaf7096CoverageChecked

private noncomputable def leaf7096InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814917/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7096InputLogOnePlusV_eq :
    leaf7096InputLogOnePlusV = outerEnclosure 24
      (leaf7096Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7096RoundedFacts : LeafRoundedFacts 8
    leaf7096Certificate.logOnePlusV leaf7096InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7096InputLogOnePlusV_eq }

private noncomputable def leaf7096Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi90InputQChi innerPair867Input
    leaf7096InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7096LowerChecked :
    lowerCheck 24 leaf7096Box leaf7096Inputs = true := by
  rfl'

private theorem leaf7096CoversExact : CoversExact 8
    leaf7096Box leaf7096Certificate leaf7096InnerLog leaf7096Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi90RoundedFacts
    innerPair867RoundedFacts leaf7096RoundedFacts (by rfl)

private theorem leaf7096FlatSound : Sound leaf7096Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7096CertificateValid
    leaf7096InnerLogValid leaf7096CoversExact leaf7096LowerChecked

private noncomputable def leaf7097Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (13/16), chiHi := (53/64) }

private noncomputable def leaf7097Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109073/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354094080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (240866753/134217728) }, upper := { exponent := 1, mantissa := (945/512) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi363LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711276539/68708188160) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf7097InnerLog : WideLogData :=
  innerPair795Data

set_option maxRecDepth 1000000 in
private theorem leaf7097LocalValidity :
    LeafFacts leaf7097Box leaf7097Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7097Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354094080) }) = true
      norm_num [leaf7097Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7097CertificateValid :
    WideCertificateValid leaf7097Box leaf7097Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi363ValidityFacts
    leaf7097LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7097CoverageChecked :
    coverageCheck (innerAD leaf7097Box) leaf7097InnerLog = true := by
  rfl'

private theorem leaf7097InnerLogValid :
    leaf7097InnerLog.Valid 8 (innerAD leaf7097Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint502PositiveFacts.valid leaf7097CoverageChecked

private noncomputable def leaf7097InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629835/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7097InputLogOnePlusV_eq :
    leaf7097InputLogOnePlusV = outerEnclosure 24
      (leaf7097Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7097RoundedFacts : LeafRoundedFacts 8
    leaf7097Certificate.logOnePlusV leaf7097InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7097InputLogOnePlusV_eq }

private noncomputable def leaf7097Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi363InputQChi innerPair795Input
    leaf7097InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7097LowerChecked :
    lowerCheck 24 leaf7097Box leaf7097Inputs = true := by
  rfl'

private theorem leaf7097CoversExact : CoversExact 8
    leaf7097Box leaf7097Certificate leaf7097InnerLog leaf7097Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi363RoundedFacts
    innerPair795RoundedFacts leaf7097RoundedFacts (by rfl)

private theorem leaf7097FlatSound : Sound leaf7097Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7097CertificateValid
    leaf7097InnerLogValid leaf7097CoversExact leaf7097LowerChecked

private noncomputable def leaf7098Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (53/64), chiHi := (27/32) }

private noncomputable def leaf7098Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109075/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353987584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (244208883/134217728) }, upper := { exponent := 1, mantissa := (479/256) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi364LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711170043/68707975168) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf7098InnerLog : WideLogData :=
  innerPair798Data

set_option maxRecDepth 1000000 in
private theorem leaf7098LocalValidity :
    LeafFacts leaf7098Box leaf7098Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7098Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353987584) }) = true
      norm_num [leaf7098Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7098CertificateValid :
    WideCertificateValid leaf7098Box leaf7098Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi364ValidityFacts
    leaf7098LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7098CoverageChecked :
    coverageCheck (innerAD leaf7098Box) leaf7098InnerLog = true := by
  rfl'

private theorem leaf7098InnerLogValid :
    leaf7098InnerLog.Valid 8 (innerAD leaf7098Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint502PositiveFacts.valid leaf7098CoverageChecked

private noncomputable def leaf7098InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629861/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7098InputLogOnePlusV_eq :
    leaf7098InputLogOnePlusV = outerEnclosure 24
      (leaf7098Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7098RoundedFacts : LeafRoundedFacts 8
    leaf7098Certificate.logOnePlusV leaf7098InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7098InputLogOnePlusV_eq }

private noncomputable def leaf7098Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi364InputQChi innerPair798Input
    leaf7098InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7098LowerChecked :
    lowerCheck 24 leaf7098Box leaf7098Inputs = true := by
  rfl'

private theorem leaf7098CoversExact : CoversExact 8
    leaf7098Box leaf7098Certificate leaf7098InnerLog leaf7098Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi364RoundedFacts
    innerPair798RoundedFacts leaf7098RoundedFacts (by rfl)

private theorem leaf7098FlatSound : Sound leaf7098Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7098CertificateValid
    leaf7098InnerLogValid leaf7098CoversExact leaf7098LowerChecked

private noncomputable def leaf7099Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf7099Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554589/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353889280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (121989709/67108864) }, upper := { exponent := 1, mantissa := (485/256) } }, logOuter := sk125LogOuterCertificate, logK := sk125LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711071739/68707778560) } }, logDArg := sk125LogDArgCertificate }

private noncomputable def leaf7099InnerLog : WideLogData :=
  innerPair799Data

set_option maxRecDepth 1000000 in
private theorem leaf7099LocalValidity :
    LeafFacts leaf7099Box leaf7099Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7099Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353889280) }) = true
      norm_num [leaf7099Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7099CertificateValid :
    WideCertificateValid leaf7099Box leaf7099Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk125ValidityFacts chi91ValidityFacts
    leaf7099LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7099CoverageChecked :
    coverageCheck (innerAD leaf7099Box) leaf7099InnerLog = true := by
  rfl'

private theorem leaf7099InnerLogValid :
    leaf7099InnerLog.Valid 8 (innerAD leaf7099Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint503PositiveFacts.valid leaf7099CoverageChecked

private noncomputable def leaf7099InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629885/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7099InputLogOnePlusV_eq :
    leaf7099InputLogOnePlusV = outerEnclosure 24
      (leaf7099Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7099RoundedFacts : LeafRoundedFacts 8
    leaf7099Certificate.logOnePlusV leaf7099InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7099InputLogOnePlusV_eq }

private noncomputable def leaf7099Inputs : Inputs :=
  inputsOfCaches globalInput sk125RoundedInputs
    chi91InputQChi innerPair799Input
    leaf7099InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7099LowerChecked :
    lowerCheck 24 leaf7099Box leaf7099Inputs = true := by
  rfl'

private theorem leaf7099CoversExact : CoversExact 8
    leaf7099Box leaf7099Certificate leaf7099InnerLog leaf7099Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk125RoundedFacts chi91RoundedFacts
    innerPair799RoundedFacts leaf7099RoundedFacts (by rfl)

private theorem leaf7099FlatSound : Sound leaf7099Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7099CertificateValid
    leaf7099InnerLogValid leaf7099CoversExact leaf7099LowerChecked

private noncomputable def leaf7100Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf7100Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554591/33554432) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353774592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (123759071/67108864) }, upper := { exponent := 1, mantissa := (123/64) } }, logOuter := sk126LogOuterCertificate, logK := sk126LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68710957051/68707549184) } }, logDArg := sk126LogDArgCertificate }

private noncomputable def leaf7100InnerLog : WideLogData :=
  innerPair804Data

set_option maxRecDepth 1000000 in
private theorem leaf7100LocalValidity :
    LeafFacts leaf7100Box leaf7100Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7100Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353774592) }) = true
      norm_num [leaf7100Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7100CertificateValid :
    WideCertificateValid leaf7100Box leaf7100Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk126ValidityFacts chi91ValidityFacts
    leaf7100LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7100CoverageChecked :
    coverageCheck (innerAD leaf7100Box) leaf7100InnerLog = true := by
  rfl'

private theorem leaf7100InnerLogValid :
    leaf7100InnerLog.Valid 8 (innerAD leaf7100Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint576PositiveFacts.valid leaf7100CoverageChecked

private noncomputable def leaf7100InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629913/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7100InputLogOnePlusV_eq :
    leaf7100InputLogOnePlusV = outerEnclosure 24
      (leaf7100Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7100RoundedFacts : LeafRoundedFacts 8
    leaf7100Certificate.logOnePlusV leaf7100InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7100InputLogOnePlusV_eq }

private noncomputable def leaf7100Inputs : Inputs :=
  inputsOfCaches globalInput sk126RoundedInputs
    chi91InputQChi innerPair804Input
    leaf7100InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7100LowerChecked :
    lowerCheck 24 leaf7100Box leaf7100Inputs = true := by
  rfl'

private theorem leaf7100CoversExact : CoversExact 8
    leaf7100Box leaf7100Certificate leaf7100InnerLog leaf7100Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk126RoundedFacts chi91RoundedFacts
    innerPair804RoundedFacts leaf7100RoundedFacts (by rfl)

private theorem leaf7100FlatSound : Sound leaf7100Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7100CertificateValid
    leaf7100InnerLogValid leaf7100CoversExact leaf7100LowerChecked

private noncomputable def leaf7101Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf7101Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109067/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354419712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (230643767/134217728) }, upper := { exponent := 1, mantissa := (3621/2048) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711602171/68708839424) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf7101InnerLog : WideLogData :=
  innerPair771Data

set_option maxRecDepth 1000000 in
private theorem leaf7101LocalValidity :
    LeafFacts leaf7101Box leaf7101Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7101Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354419712) }) = true
      norm_num [leaf7101Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7101CertificateValid :
    WideCertificateValid leaf7101Box leaf7101Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi345ValidityFacts
    leaf7101LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7101CoverageChecked :
    coverageCheck (innerAD leaf7101Box) leaf7101InnerLog = true := by
  rfl'

private theorem leaf7101InnerLogValid :
    leaf7101InnerLog.Valid 8 (innerAD leaf7101Box) :=
  wideLogDataValid_of_cachedCheck endpoint487PositiveFacts
    endpoint498PositiveFacts.valid leaf7101CoverageChecked

private noncomputable def leaf7101InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629755/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7101InputLogOnePlusV_eq :
    leaf7101InputLogOnePlusV = outerEnclosure 24
      (leaf7101Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7101RoundedFacts : LeafRoundedFacts 8
    leaf7101Certificate.logOnePlusV leaf7101InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7101InputLogOnePlusV_eq }

private noncomputable def leaf7101Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi345InputQChi innerPair771Input
    leaf7101InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7101LowerChecked :
    lowerCheck 24 leaf7101Box leaf7101Inputs = true := by
  rfl'

private theorem leaf7101CoversExact : CoversExact 8
    leaf7101Box leaf7101Certificate leaf7101InnerLog leaf7101Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi345RoundedFacts
    innerPair771RoundedFacts leaf7101RoundedFacts (by rfl)

private theorem leaf7101FlatSound : Sound leaf7101Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7101CertificateValid
    leaf7101InnerLogValid leaf7101CoversExact leaf7101LowerChecked

private noncomputable def leaf7102Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf7102Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109069/67108864) }, vSqrt := { lower := (65529/65536), upper := (11452394153/11451437056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (234051429/134217728) }, upper := { exponent := 1, mantissa := (1837/1024) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22903831209/22902874112) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf7102InnerLog : WideLogData :=
  innerPair776Data

set_option maxRecDepth 1000000 in
private theorem leaf7102LocalValidity :
    LeafFacts leaf7102Box leaf7102Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7102Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452394153/11451437056) }) = true
      norm_num [leaf7102Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7102CertificateValid :
    WideCertificateValid leaf7102Box leaf7102Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi346ValidityFacts
    leaf7102LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7102CoverageChecked :
    coverageCheck (innerAD leaf7102Box) leaf7102InnerLog = true := by
  rfl'

private theorem leaf7102InnerLogValid :
    leaf7102InnerLog.Valid 8 (innerAD leaf7102Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint500PositiveFacts.valid leaf7102CoverageChecked

private noncomputable def leaf7102InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814891/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7102InputLogOnePlusV_eq :
    leaf7102InputLogOnePlusV = outerEnclosure 24
      (leaf7102Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7102RoundedFacts : LeafRoundedFacts 8
    leaf7102Certificate.logOnePlusV leaf7102InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7102InputLogOnePlusV_eq }

private noncomputable def leaf7102Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi346InputQChi innerPair776Input
    leaf7102InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7102LowerChecked :
    lowerCheck 24 leaf7102Box leaf7102Inputs = true := by
  rfl'

private theorem leaf7102CoversExact : CoversExact 8
    leaf7102Box leaf7102Certificate leaf7102InnerLog leaf7102Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi346RoundedFacts
    innerPair776RoundedFacts leaf7102RoundedFacts (by rfl)

private theorem leaf7102FlatSound : Sound leaf7102Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7102CertificateValid
    leaf7102InnerLogValid leaf7102CoversExact leaf7102LowerChecked

private noncomputable def leaf7103Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf7103Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109069/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354319360) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (233789301/134217728) }, upper := { exponent := 1, mantissa := (1835/1024) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711501819/68708638720) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf7103InnerLog : WideLogData :=
  innerPair776Data

set_option maxRecDepth 1000000 in
private theorem leaf7103LocalValidity :
    LeafFacts leaf7103Box leaf7103Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7103Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354319360) }) = true
      norm_num [leaf7103Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7103CertificateValid :
    WideCertificateValid leaf7103Box leaf7103Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi345ValidityFacts
    leaf7103LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7103CoverageChecked :
    coverageCheck (innerAD leaf7103Box) leaf7103InnerLog = true := by
  rfl'

private theorem leaf7103InnerLogValid :
    leaf7103InnerLog.Valid 8 (innerAD leaf7103Box) :=
  wideLogDataValid_of_cachedCheck endpoint488PositiveFacts
    endpoint500PositiveFacts.valid leaf7103CoverageChecked

private noncomputable def leaf7103InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907445/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7103InputLogOnePlusV_eq :
    leaf7103InputLogOnePlusV = outerEnclosure 24
      (leaf7103Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7103RoundedFacts : LeafRoundedFacts 8
    leaf7103Certificate.logOnePlusV leaf7103InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7103InputLogOnePlusV_eq }

private noncomputable def leaf7103Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi345InputQChi innerPair776Input
    leaf7103InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7103LowerChecked :
    lowerCheck 24 leaf7103Box leaf7103Inputs = true := by
  rfl'

private theorem leaf7103CoversExact : CoversExact 8
    leaf7103Box leaf7103Certificate leaf7103InnerLog leaf7103Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi345RoundedFacts
    innerPair776RoundedFacts leaf7103RoundedFacts (by rfl)

private theorem leaf7103FlatSound : Sound leaf7103Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7103CertificateValid
    leaf7103InnerLogValid leaf7103CoversExact leaf7103LowerChecked

private noncomputable def leaf7104Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf7104Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109071/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354208768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (237262495/134217728) }, upper := { exponent := 1, mantissa := (931/512) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711391227/68708417536) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf7104InnerLog : WideLogData :=
  innerPair779Data

set_option maxRecDepth 1000000 in
private theorem leaf7104LocalValidity :
    LeafFacts leaf7104Box leaf7104Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7104Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354208768) }) = true
      norm_num [leaf7104Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7104CertificateValid :
    WideCertificateValid leaf7104Box leaf7104Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi346ValidityFacts
    leaf7104LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7104CoverageChecked :
    coverageCheck (innerAD leaf7104Box) leaf7104InnerLog = true := by
  rfl'

private theorem leaf7104InnerLogValid :
    leaf7104InnerLog.Valid 8 (innerAD leaf7104Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint501PositiveFacts.valid leaf7104CoverageChecked

private noncomputable def leaf7104InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629807/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7104InputLogOnePlusV_eq :
    leaf7104InputLogOnePlusV = outerEnclosure 24
      (leaf7104Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7104RoundedFacts : LeafRoundedFacts 8
    leaf7104Certificate.logOnePlusV leaf7104InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7104InputLogOnePlusV_eq }

private noncomputable def leaf7104Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi346InputQChi innerPair779Input
    leaf7104InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7104LowerChecked :
    lowerCheck 24 leaf7104Box leaf7104Inputs = true := by
  rfl'

private theorem leaf7104CoversExact : CoversExact 8
    leaf7104Box leaf7104Certificate leaf7104InnerLog leaf7104Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi346RoundedFacts
    innerPair779RoundedFacts leaf7104RoundedFacts (by rfl)

private theorem leaf7104FlatSound : Sound leaf7104Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7104CertificateValid
    leaf7104InnerLogValid leaf7104CoversExact leaf7104LowerChecked

private noncomputable def leaf7105Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (25/32), chiHi := (51/64) }

private noncomputable def leaf7105Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109071/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354202624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (237459091/134217728) }, upper := { exponent := 1, mantissa := (3727/2048) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi361LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711385083/68708405248) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf7105InnerLog : WideLogData :=
  innerPair779Data

set_option maxRecDepth 1000000 in
private theorem leaf7105LocalValidity :
    LeafFacts leaf7105Box leaf7105Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7105Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354202624) }) = true
      norm_num [leaf7105Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7105CertificateValid :
    WideCertificateValid leaf7105Box leaf7105Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi361ValidityFacts
    leaf7105LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7105CoverageChecked :
    coverageCheck (innerAD leaf7105Box) leaf7105InnerLog = true := by
  rfl'

private theorem leaf7105InnerLogValid :
    leaf7105InnerLog.Valid 8 (innerAD leaf7105Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint501PositiveFacts.valid leaf7105CoverageChecked

private noncomputable def leaf7105InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (726863/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf7105InputLogOnePlusV_eq :
    leaf7105InputLogOnePlusV = outerEnclosure 24
      (leaf7105Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7105RoundedFacts : LeafRoundedFacts 8
    leaf7105Certificate.logOnePlusV leaf7105InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7105InputLogOnePlusV_eq }

private noncomputable def leaf7105Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi361InputQChi innerPair779Input
    leaf7105InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7105LowerChecked :
    lowerCheck 24 leaf7105Box leaf7105Inputs = true := by
  rfl'

private theorem leaf7105CoversExact : CoversExact 8
    leaf7105Box leaf7105Certificate leaf7105InnerLog leaf7105Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi361RoundedFacts
    innerPair779RoundedFacts leaf7105RoundedFacts (by rfl)

private theorem leaf7105FlatSound : Sound leaf7105Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7105CertificateValid
    leaf7105InnerLogValid leaf7105CoversExact leaf7105LowerChecked

private noncomputable def leaf7106Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (51/64), chiHi := (13/16) }

private noncomputable def leaf7106Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109073/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354094080) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (240866753/134217728) }, upper := { exponent := 1, mantissa := (945/512) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi362LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711276539/68708188160) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf7106InnerLog : WideLogData :=
  innerPair795Data

set_option maxRecDepth 1000000 in
private theorem leaf7106LocalValidity :
    LeafFacts leaf7106Box leaf7106Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7106Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354094080) }) = true
      norm_num [leaf7106Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7106CertificateValid :
    WideCertificateValid leaf7106Box leaf7106Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi362ValidityFacts
    leaf7106LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7106CoverageChecked :
    coverageCheck (innerAD leaf7106Box) leaf7106InnerLog = true := by
  rfl'

private theorem leaf7106InnerLogValid :
    leaf7106InnerLog.Valid 8 (innerAD leaf7106Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint502PositiveFacts.valid leaf7106CoverageChecked

private noncomputable def leaf7106InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629835/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7106InputLogOnePlusV_eq :
    leaf7106InputLogOnePlusV = outerEnclosure 24
      (leaf7106Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7106RoundedFacts : LeafRoundedFacts 8
    leaf7106Certificate.logOnePlusV leaf7106InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7106InputLogOnePlusV_eq }

private noncomputable def leaf7106Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi362InputQChi innerPair795Input
    leaf7106InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7106LowerChecked :
    lowerCheck 24 leaf7106Box leaf7106Inputs = true := by
  rfl'

private theorem leaf7106CoversExact : CoversExact 8
    leaf7106Box leaf7106Certificate leaf7106InnerLog leaf7106Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi362RoundedFacts
    innerPair795RoundedFacts leaf7106RoundedFacts (by rfl)

private theorem leaf7106FlatSound : Sound leaf7106Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7106CertificateValid
    leaf7106InnerLogValid leaf7106CoversExact leaf7106LowerChecked

private noncomputable def leaf7107Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (25/32), chiHi := (51/64) }

private noncomputable def leaf7107Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109073/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354098176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (240735689/134217728) }, upper := { exponent := 1, mantissa := (1889/1024) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi361LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711280635/68708196352) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf7107InnerLog : WideLogData :=
  innerPair795Data

set_option maxRecDepth 1000000 in
private theorem leaf7107LocalValidity :
    LeafFacts leaf7107Box leaf7107Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7107Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354098176) }) = true
      norm_num [leaf7107Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7107CertificateValid :
    WideCertificateValid leaf7107Box leaf7107Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi361ValidityFacts
    leaf7107LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7107CoverageChecked :
    coverageCheck (innerAD leaf7107Box) leaf7107InnerLog = true := by
  rfl'

private theorem leaf7107InnerLogValid :
    leaf7107InnerLog.Valid 8 (innerAD leaf7107Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint502PositiveFacts.valid leaf7107CoverageChecked

private noncomputable def leaf7107InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814917/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7107InputLogOnePlusV_eq :
    leaf7107InputLogOnePlusV = outerEnclosure 24
      (leaf7107Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7107RoundedFacts : LeafRoundedFacts 8
    leaf7107Certificate.logOnePlusV leaf7107InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7107InputLogOnePlusV_eq }

private noncomputable def leaf7107Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi361InputQChi innerPair795Input
    leaf7107InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7107LowerChecked :
    lowerCheck 24 leaf7107Box leaf7107Inputs = true := by
  rfl'

private theorem leaf7107CoversExact : CoversExact 8
    leaf7107Box leaf7107Certificate leaf7107InnerLog leaf7107Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi361RoundedFacts
    innerPair795RoundedFacts leaf7107RoundedFacts (by rfl)

private theorem leaf7107FlatSound : Sound leaf7107Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7107CertificateValid
    leaf7107InnerLogValid leaf7107CoversExact leaf7107LowerChecked

private noncomputable def leaf7108Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (51/64), chiHi := (13/16) }

private noncomputable def leaf7108Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109075/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353987584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (244208883/134217728) }, upper := { exponent := 1, mantissa := (479/256) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi362LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711170043/68707975168) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf7108InnerLog : WideLogData :=
  innerPair798Data

set_option maxRecDepth 1000000 in
private theorem leaf7108LocalValidity :
    LeafFacts leaf7108Box leaf7108Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7108Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353987584) }) = true
      norm_num [leaf7108Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7108CertificateValid :
    WideCertificateValid leaf7108Box leaf7108Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi362ValidityFacts
    leaf7108LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7108CoverageChecked :
    coverageCheck (innerAD leaf7108Box) leaf7108InnerLog = true := by
  rfl'

private theorem leaf7108InnerLogValid :
    leaf7108InnerLog.Valid 8 (innerAD leaf7108Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint502PositiveFacts.valid leaf7108CoverageChecked

private noncomputable def leaf7108InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629861/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7108InputLogOnePlusV_eq :
    leaf7108InputLogOnePlusV = outerEnclosure 24
      (leaf7108Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7108RoundedFacts : LeafRoundedFacts 8
    leaf7108Certificate.logOnePlusV leaf7108InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7108InputLogOnePlusV_eq }

private noncomputable def leaf7108Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi362InputQChi innerPair798Input
    leaf7108InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7108LowerChecked :
    lowerCheck 24 leaf7108Box leaf7108Inputs = true := by
  rfl'

private theorem leaf7108CoversExact : CoversExact 8
    leaf7108Box leaf7108Certificate leaf7108InnerLog leaf7108Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi362RoundedFacts
    innerPair798RoundedFacts leaf7108RoundedFacts (by rfl)

private theorem leaf7108FlatSound : Sound leaf7108Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7108CertificateValid
    leaf7108InnerLogValid leaf7108CoversExact leaf7108LowerChecked

private noncomputable def leaf7109Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf7109Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109071/67108864) }, vSqrt := { lower := (65529/65536), upper := (11452394153/11451406336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (236934835/134217728) }, upper := { exponent := 1, mantissa := (3719/2048) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22903800489/22902812672) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf7109InnerLog : WideLogData :=
  innerPair779Data

set_option maxRecDepth 1000000 in
private theorem leaf7109LocalValidity :
    LeafFacts leaf7109Box leaf7109Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7109Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452394153/11451406336) }) = true
      norm_num [leaf7109Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7109CertificateValid :
    WideCertificateValid leaf7109Box leaf7109Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi345ValidityFacts
    leaf7109LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7109CoverageChecked :
    coverageCheck (innerAD leaf7109Box) leaf7109InnerLog = true := by
  rfl'

private theorem leaf7109InnerLogValid :
    leaf7109InnerLog.Valid 8 (innerAD leaf7109Box) :=
  wideLogDataValid_of_cachedCheck endpoint489PositiveFacts
    endpoint501PositiveFacts.valid leaf7109CoverageChecked

private noncomputable def leaf7109InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (2907451/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf7109InputLogOnePlusV_eq :
    leaf7109InputLogOnePlusV = outerEnclosure 24
      (leaf7109Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7109RoundedFacts : LeafRoundedFacts 8
    leaf7109Certificate.logOnePlusV leaf7109InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7109InputLogOnePlusV_eq }

private noncomputable def leaf7109Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi345InputQChi innerPair779Input
    leaf7109InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7109LowerChecked :
    lowerCheck 24 leaf7109Box leaf7109Inputs = true := by
  rfl'

private theorem leaf7109CoversExact : CoversExact 8
    leaf7109Box leaf7109Certificate leaf7109InnerLog leaf7109Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi345RoundedFacts
    innerPair779RoundedFacts leaf7109RoundedFacts (by rfl)

private theorem leaf7109FlatSound : Sound leaf7109Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7109CertificateValid
    leaf7109InnerLogValid leaf7109CoversExact leaf7109LowerChecked

private noncomputable def leaf7110Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (3/4), chiHi := (49/64) }

private noncomputable def leaf7110Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109073/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34354118656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (240080369/134217728) }, upper := { exponent := 1, mantissa := (471/256) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi345LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711301115/68708237312) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf7110InnerLog : WideLogData :=
  innerPair794Data

set_option maxRecDepth 1000000 in
private theorem leaf7110LocalValidity :
    LeafFacts leaf7110Box leaf7110Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7110Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34354118656) }) = true
      norm_num [leaf7110Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7110CertificateValid :
    WideCertificateValid leaf7110Box leaf7110Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi345ValidityFacts
    leaf7110LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7110CoverageChecked :
    coverageCheck (innerAD leaf7110Box) leaf7110InnerLog = true := by
  rfl'

private theorem leaf7110InnerLogValid :
    leaf7110InnerLog.Valid 8 (innerAD leaf7110Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint501PositiveFacts.valid leaf7110CoverageChecked

private noncomputable def leaf7110InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629829/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7110InputLogOnePlusV_eq :
    leaf7110InputLogOnePlusV = outerEnclosure 24
      (leaf7110Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7110RoundedFacts : LeafRoundedFacts 8
    leaf7110Certificate.logOnePlusV leaf7110InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7110InputLogOnePlusV_eq }

private noncomputable def leaf7110Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi345InputQChi innerPair794Input
    leaf7110InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7110LowerChecked :
    lowerCheck 24 leaf7110Box leaf7110Inputs = true := by
  rfl'

private theorem leaf7110CoversExact : CoversExact 8
    leaf7110Box leaf7110Certificate leaf7110InnerLog leaf7110Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi345RoundedFacts
    innerPair794RoundedFacts leaf7110RoundedFacts (by rfl)

private theorem leaf7110FlatSound : Sound leaf7110Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7110CertificateValid
    leaf7110InnerLogValid leaf7110CoversExact leaf7110LowerChecked

private noncomputable def leaf7111Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf7111Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109073/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34354106368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (240473561/134217728) }, upper := { exponent := 1, mantissa := (1887/1024) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711288827/68708212736) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf7111InnerLog : WideLogData :=
  innerPair794Data

set_option maxRecDepth 1000000 in
private theorem leaf7111LocalValidity :
    LeafFacts leaf7111Box leaf7111Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7111Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34354106368) }) = true
      norm_num [leaf7111Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7111CertificateValid :
    WideCertificateValid leaf7111Box leaf7111Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi346ValidityFacts
    leaf7111LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7111CoverageChecked :
    coverageCheck (innerAD leaf7111Box) leaf7111InnerLog = true := by
  rfl'

private theorem leaf7111InnerLogValid :
    leaf7111InnerLog.Valid 8 (innerAD leaf7111Box) :=
  wideLogDataValid_of_cachedCheck endpoint498PositiveFacts
    endpoint501PositiveFacts.valid leaf7111CoverageChecked

private noncomputable def leaf7111InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (1453729/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf7111InputLogOnePlusV_eq :
    leaf7111InputLogOnePlusV = outerEnclosure 24
      (leaf7111Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7111RoundedFacts : LeafRoundedFacts 8
    leaf7111Certificate.logOnePlusV leaf7111InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7111InputLogOnePlusV_eq }

private noncomputable def leaf7111Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi346InputQChi innerPair794Input
    leaf7111InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7111LowerChecked :
    lowerCheck 24 leaf7111Box leaf7111Inputs = true := by
  rfl'

private theorem leaf7111CoversExact : CoversExact 8
    leaf7111Box leaf7111Certificate leaf7111InnerLog leaf7111Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi346RoundedFacts
    innerPair794RoundedFacts leaf7111RoundedFacts (by rfl)

private theorem leaf7111FlatSound : Sound leaf7111Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7111CertificateValid
    leaf7111InnerLogValid leaf7111CoversExact leaf7111LowerChecked

private noncomputable def leaf7112Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (49/64), chiHi := (25/32) }

private noncomputable def leaf7112Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109075/67108864) }, vSqrt := { lower := (8191/8192), upper := (602757587/602701824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (243684627/134217728) }, upper := { exponent := 1, mantissa := (239/128) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi346LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1205459411/1205403648) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf7112InnerLog : WideLogData :=
  innerPair798Data

set_option maxRecDepth 1000000 in
private theorem leaf7112LocalValidity :
    LeafFacts leaf7112Box leaf7112Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7112Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (602757587/602701824) }) = true
      norm_num [leaf7112Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7112CertificateValid :
    WideCertificateValid leaf7112Box leaf7112Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi346ValidityFacts
    leaf7112LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7112CoverageChecked :
    coverageCheck (innerAD leaf7112Box) leaf7112InnerLog = true := by
  rfl'

private theorem leaf7112InnerLogValid :
    leaf7112InnerLog.Valid 8 (innerAD leaf7112Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint502PositiveFacts.valid leaf7112CoverageChecked

private noncomputable def leaf7112InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629857/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7112InputLogOnePlusV_eq :
    leaf7112InputLogOnePlusV = outerEnclosure 24
      (leaf7112Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7112RoundedFacts : LeafRoundedFacts 8
    leaf7112Certificate.logOnePlusV leaf7112InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7112InputLogOnePlusV_eq }

private noncomputable def leaf7112Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi346InputQChi innerPair798Input
    leaf7112InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7112LowerChecked :
    lowerCheck 24 leaf7112Box leaf7112Inputs = true := by
  rfl'

private theorem leaf7112CoversExact : CoversExact 8
    leaf7112Box leaf7112Certificate leaf7112InnerLog leaf7112Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi346RoundedFacts
    innerPair798RoundedFacts leaf7112RoundedFacts (by rfl)

private theorem leaf7112FlatSound : Sound leaf7112Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7112CertificateValid
    leaf7112InnerLogValid leaf7112CoversExact leaf7112LowerChecked

private noncomputable def leaf7113Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (25/32), chiHi := (51/64) }

private noncomputable def leaf7113Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109075/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353993728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (244012287/134217728) }, upper := { exponent := 1, mantissa := (3829/2048) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi361LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711176187/68707987456) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf7113InnerLog : WideLogData :=
  innerPair798Data

set_option maxRecDepth 1000000 in
private theorem leaf7113LocalValidity :
    LeafFacts leaf7113Box leaf7113Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7113Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353993728) }) = true
      norm_num [leaf7113Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7113CertificateValid :
    WideCertificateValid leaf7113Box leaf7113Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi361ValidityFacts
    leaf7113LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7113CoverageChecked :
    coverageCheck (innerAD leaf7113Box) leaf7113InnerLog = true := by
  rfl'

private theorem leaf7113InnerLogValid :
    leaf7113InnerLog.Valid 8 (innerAD leaf7113Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint502PositiveFacts.valid leaf7113CoverageChecked

private noncomputable def leaf7113InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629859/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7113InputLogOnePlusV_eq :
    leaf7113InputLogOnePlusV = outerEnclosure 24
      (leaf7113Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7113RoundedFacts : LeafRoundedFacts 8
    leaf7113Certificate.logOnePlusV leaf7113InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7113InputLogOnePlusV_eq }

private noncomputable def leaf7113Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi361InputQChi innerPair798Input
    leaf7113InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7113LowerChecked :
    lowerCheck 24 leaf7113Box leaf7113Inputs = true := by
  rfl'

private theorem leaf7113CoversExact : CoversExact 8
    leaf7113Box leaf7113Certificate leaf7113InnerLog leaf7113Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi361RoundedFacts
    innerPair798RoundedFacts leaf7113RoundedFacts (by rfl)

private theorem leaf7113FlatSound : Sound leaf7113Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7113CertificateValid
    leaf7113InnerLogValid leaf7113CoversExact leaf7113LowerChecked

private noncomputable def leaf7114Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (25/32), chiHi := (51/64) }

private noncomputable def leaf7114Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109077/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353889280) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (247288885/134217728) }, upper := { exponent := 1, mantissa := (485/256) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi361LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68711071739/68707778560) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf7114InnerLog : WideLogData :=
  innerPair799Data

set_option maxRecDepth 1000000 in
private theorem leaf7114LocalValidity :
    LeafFacts leaf7114Box leaf7114Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7114Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353889280) }) = true
      norm_num [leaf7114Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7114CertificateValid :
    WideCertificateValid leaf7114Box leaf7114Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi361ValidityFacts
    leaf7114LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7114CoverageChecked :
    coverageCheck (innerAD leaf7114Box) leaf7114InnerLog = true := by
  rfl'

private theorem leaf7114InnerLogValid :
    leaf7114InnerLog.Valid 8 (innerAD leaf7114Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint503PositiveFacts.valid leaf7114CoverageChecked

private noncomputable def leaf7114InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629885/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7114InputLogOnePlusV_eq :
    leaf7114InputLogOnePlusV = outerEnclosure 24
      (leaf7114Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7114RoundedFacts : LeafRoundedFacts 8
    leaf7114Certificate.logOnePlusV leaf7114InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7114InputLogOnePlusV_eq }

private noncomputable def leaf7114Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi361InputQChi innerPair799Input
    leaf7114InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7114LowerChecked :
    lowerCheck 24 leaf7114Box leaf7114Inputs = true := by
  rfl'

private theorem leaf7114CoversExact : CoversExact 8
    leaf7114Box leaf7114Certificate leaf7114InnerLog leaf7114Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi361RoundedFacts
    innerPair799RoundedFacts leaf7114RoundedFacts (by rfl)

private theorem leaf7114FlatSound : Sound leaf7114Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7114CertificateValid
    leaf7114InnerLogValid leaf7114CoversExact leaf7114LowerChecked

private noncomputable def leaf7115Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (51/64), chiHi := (13/16) }

private noncomputable def leaf7115Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109077/67108864) }, vSqrt := { lower := (65529/65536), upper := (11452394153/11451293696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (247551013/134217728) }, upper := { exponent := 1, mantissa := (971/512) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi362LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22903687849/22902587392) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf7115InnerLog : WideLogData :=
  innerPair801Data

set_option maxRecDepth 1000000 in
private theorem leaf7115LocalValidity :
    LeafFacts leaf7115Box leaf7115Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7115Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452394153/11451293696) }) = true
      norm_num [leaf7115Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7115CertificateValid :
    WideCertificateValid leaf7115Box leaf7115Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi362ValidityFacts
    leaf7115LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7115CoverageChecked :
    coverageCheck (innerAD leaf7115Box) leaf7115InnerLog = true := by
  rfl'

private theorem leaf7115InnerLogValid :
    leaf7115InnerLog.Valid 8 (innerAD leaf7115Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint503PositiveFacts.valid leaf7115CoverageChecked

private noncomputable def leaf7115InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629887/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7115InputLogOnePlusV_eq :
    leaf7115InputLogOnePlusV = outerEnclosure 24
      (leaf7115Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7115RoundedFacts : LeafRoundedFacts 8
    leaf7115Certificate.logOnePlusV leaf7115InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7115InputLogOnePlusV_eq }

private noncomputable def leaf7115Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi362InputQChi innerPair801Input
    leaf7115InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7115LowerChecked :
    lowerCheck 24 leaf7115Box leaf7115Inputs = true := by
  rfl'

private theorem leaf7115CoversExact : CoversExact 8
    leaf7115Box leaf7115Certificate leaf7115InnerLog leaf7115Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi362RoundedFacts
    innerPair801RoundedFacts leaf7115RoundedFacts (by rfl)

private theorem leaf7115FlatSound : Sound leaf7115Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7115CertificateValid
    leaf7115InnerLogValid leaf7115CoversExact leaf7115LowerChecked

private noncomputable def leaf7116Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (51/64), chiHi := (13/16) }

private noncomputable def leaf7116Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109079/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353774592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (250893143/134217728) }, upper := { exponent := 1, mantissa := (123/64) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi362LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68710957051/68707549184) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf7116InnerLog : WideLogData :=
  innerPair802Data

set_option maxRecDepth 1000000 in
private theorem leaf7116LocalValidity :
    LeafFacts leaf7116Box leaf7116Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7116Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353774592) }) = true
      norm_num [leaf7116Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7116CertificateValid :
    WideCertificateValid leaf7116Box leaf7116Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi362ValidityFacts
    leaf7116LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7116CoverageChecked :
    coverageCheck (innerAD leaf7116Box) leaf7116InnerLog = true := by
  rfl'

private theorem leaf7116InnerLogValid :
    leaf7116InnerLog.Valid 8 (innerAD leaf7116Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint504PositiveFacts.valid leaf7116CoverageChecked

private noncomputable def leaf7116InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629913/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7116InputLogOnePlusV_eq :
    leaf7116InputLogOnePlusV = outerEnclosure 24
      (leaf7116Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7116RoundedFacts : LeafRoundedFacts 8
    leaf7116Certificate.logOnePlusV leaf7116InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7116InputLogOnePlusV_eq }

private noncomputable def leaf7116Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi362InputQChi innerPair802Input
    leaf7116InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7116LowerChecked :
    lowerCheck 24 leaf7116Box leaf7116Inputs = true := by
  rfl'

private theorem leaf7116CoversExact : CoversExact 8
    leaf7116Box leaf7116Certificate leaf7116InnerLog leaf7116Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi362RoundedFacts
    innerPair802RoundedFacts leaf7116RoundedFacts (by rfl)

private theorem leaf7116FlatSound : Sound leaf7116Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7116CertificateValid
    leaf7116InnerLogValid leaf7116CoversExact leaf7116LowerChecked

private noncomputable def leaf7117Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (13/16), chiHi := (53/64) }

private noncomputable def leaf7117Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109075/67108864) }, vSqrt := { lower := (65529/65536), upper := (11452394153/11451328512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (244274415/134217728) }, upper := { exponent := 1, mantissa := (3833/2048) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi363LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22903722665/22902657024) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf7117InnerLog : WideLogData :=
  innerPair798Data

set_option maxRecDepth 1000000 in
private theorem leaf7117LocalValidity :
    LeafFacts leaf7117Box leaf7117Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7117Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452394153/11451328512) }) = true
      norm_num [leaf7117Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7117CertificateValid :
    WideCertificateValid leaf7117Box leaf7117Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi363ValidityFacts
    leaf7117LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7117CoverageChecked :
    coverageCheck (innerAD leaf7117Box) leaf7117InnerLog = true := by
  rfl'

private theorem leaf7117InnerLogValid :
    leaf7117InnerLog.Valid 8 (innerAD leaf7117Box) :=
  wideLogDataValid_of_cachedCheck endpoint500PositiveFacts
    endpoint502PositiveFacts.valid leaf7117CoverageChecked

private noncomputable def leaf7117InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629861/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7117InputLogOnePlusV_eq :
    leaf7117InputLogOnePlusV = outerEnclosure 24
      (leaf7117Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7117RoundedFacts : LeafRoundedFacts 8
    leaf7117Certificate.logOnePlusV leaf7117InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7117InputLogOnePlusV_eq }

private noncomputable def leaf7117Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi363InputQChi innerPair798Input
    leaf7117InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7117LowerChecked :
    lowerCheck 24 leaf7117Box leaf7117Inputs = true := by
  rfl'

private theorem leaf7117CoversExact : CoversExact 8
    leaf7117Box leaf7117Certificate leaf7117InnerLog leaf7117Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi363RoundedFacts
    innerPair798RoundedFacts leaf7117RoundedFacts (by rfl)

private theorem leaf7117FlatSound : Sound leaf7117Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7117CertificateValid
    leaf7117InnerLogValid leaf7117CoversExact leaf7117LowerChecked

private noncomputable def leaf7118Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (53/64), chiHi := (27/32) }

private noncomputable def leaf7118Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109077/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353876992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (247682077/134217728) }, upper := { exponent := 1, mantissa := (1943/1024) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi364LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711059451/68707753984) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf7118InnerLog : WideLogData :=
  innerPair801Data

set_option maxRecDepth 1000000 in
private theorem leaf7118LocalValidity :
    LeafFacts leaf7118Box leaf7118Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7118Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353876992) }) = true
      norm_num [leaf7118Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7118CertificateValid :
    WideCertificateValid leaf7118Box leaf7118Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi364ValidityFacts
    leaf7118LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7118CoverageChecked :
    coverageCheck (innerAD leaf7118Box) leaf7118InnerLog = true := by
  rfl'

private theorem leaf7118InnerLogValid :
    leaf7118InnerLog.Valid 8 (innerAD leaf7118Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint503PositiveFacts.valid leaf7118CoverageChecked

private noncomputable def leaf7118InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (181717/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf7118InputLogOnePlusV_eq :
    leaf7118InputLogOnePlusV = outerEnclosure 24
      (leaf7118Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7118RoundedFacts : LeafRoundedFacts 8
    leaf7118Certificate.logOnePlusV leaf7118InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7118InputLogOnePlusV_eq }

private noncomputable def leaf7118Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi364InputQChi innerPair801Input
    leaf7118InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7118LowerChecked :
    lowerCheck 24 leaf7118Box leaf7118Inputs = true := by
  rfl'

private theorem leaf7118CoversExact : CoversExact 8
    leaf7118Box leaf7118Certificate leaf7118InnerLog leaf7118Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi364RoundedFacts
    innerPair801RoundedFacts leaf7118RoundedFacts (by rfl)

private theorem leaf7118FlatSound : Sound leaf7118Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7118CertificateValid
    leaf7118InnerLogValid leaf7118CoversExact leaf7118LowerChecked

private noncomputable def leaf7119Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (13/16), chiHi := (53/64) }

private noncomputable def leaf7119Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109077/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353876992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (247682077/134217728) }, upper := { exponent := 1, mantissa := (1943/1024) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi363LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68711059451/68707753984) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf7119InnerLog : WideLogData :=
  innerPair801Data

set_option maxRecDepth 1000000 in
private theorem leaf7119LocalValidity :
    LeafFacts leaf7119Box leaf7119Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7119Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353876992) }) = true
      norm_num [leaf7119Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7119CertificateValid :
    WideCertificateValid leaf7119Box leaf7119Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi363ValidityFacts
    leaf7119LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7119CoverageChecked :
    coverageCheck (innerAD leaf7119Box) leaf7119InnerLog = true := by
  rfl'

private theorem leaf7119InnerLogValid :
    leaf7119InnerLog.Valid 8 (innerAD leaf7119Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint503PositiveFacts.valid leaf7119CoverageChecked

private noncomputable def leaf7119InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (181717/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf7119InputLogOnePlusV_eq :
    leaf7119InputLogOnePlusV = outerEnclosure 24
      (leaf7119Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7119RoundedFacts : LeafRoundedFacts 8
    leaf7119Certificate.logOnePlusV leaf7119InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7119InputLogOnePlusV_eq }

private noncomputable def leaf7119Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi363InputQChi innerPair801Input
    leaf7119InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7119LowerChecked :
    lowerCheck 24 leaf7119Box leaf7119Inputs = true := by
  rfl'

private theorem leaf7119CoversExact : CoversExact 8
    leaf7119Box leaf7119Certificate leaf7119InnerLog leaf7119Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi363RoundedFacts
    innerPair801RoundedFacts leaf7119RoundedFacts (by rfl)

private theorem leaf7119FlatSound : Sound leaf7119Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7119CertificateValid
    leaf7119InnerLogValid leaf7119CoversExact leaf7119LowerChecked

private noncomputable def leaf7120Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (53/64), chiHi := (27/32) }

private noncomputable def leaf7120Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109079/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353766400) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (251155271/134217728) }, upper := { exponent := 1, mantissa := (985/512) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi364LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68710948859/68707532800) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf7120InnerLog : WideLogData :=
  innerPair802Data

set_option maxRecDepth 1000000 in
private theorem leaf7120LocalValidity :
    LeafFacts leaf7120Box leaf7120Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7120Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353766400) }) = true
      norm_num [leaf7120Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7120CertificateValid :
    WideCertificateValid leaf7120Box leaf7120Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi364ValidityFacts
    leaf7120LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7120CoverageChecked :
    coverageCheck (innerAD leaf7120Box) leaf7120InnerLog = true := by
  rfl'

private theorem leaf7120InnerLogValid :
    leaf7120InnerLog.Valid 8 (innerAD leaf7120Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint504PositiveFacts.valid leaf7120CoverageChecked

private noncomputable def leaf7120InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629915/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7120InputLogOnePlusV_eq :
    leaf7120InputLogOnePlusV = outerEnclosure 24
      (leaf7120Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7120RoundedFacts : LeafRoundedFacts 8
    leaf7120Certificate.logOnePlusV leaf7120InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7120InputLogOnePlusV_eq }

private noncomputable def leaf7120Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi364InputQChi innerPair802Input
    leaf7120InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7120LowerChecked :
    lowerCheck 24 leaf7120Box leaf7120Inputs = true := by
  rfl'

private theorem leaf7120CoversExact : CoversExact 8
    leaf7120Box leaf7120Certificate leaf7120InnerLog leaf7120Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi364RoundedFacts
    innerPair802RoundedFacts leaf7120RoundedFacts (by rfl)

private theorem leaf7120FlatSound : Sound leaf7120Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7120CertificateValid
    leaf7120InnerLogValid leaf7120CoversExact leaf7120LowerChecked

private noncomputable def leaf7121Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (27/32), chiHi := (7/8) }

private noncomputable def leaf7121Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (33554593/33554432) }, vSqrt := { lower := (65529/65536), upper := (11452394153/11451219968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (125528433/67108864) }, upper := { exponent := 1, mantissa := (499/256) } }, logOuter := sk131LogOuterCertificate, logK := sk131LogKCertificate, logChi := chi91LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22903614121/22902439936) } }, logDArg := sk131LogDArgCertificate }

private noncomputable def leaf7121InnerLog : WideLogData :=
  innerPair862Data

set_option maxRecDepth 1000000 in
private theorem leaf7121LocalValidity :
    LeafFacts leaf7121Box leaf7121Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7121Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452394153/11451219968) }) = true
      norm_num [leaf7121Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7121CertificateValid :
    WideCertificateValid leaf7121Box leaf7121Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk131ValidityFacts chi91ValidityFacts
    leaf7121LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7121CoverageChecked :
    coverageCheck (innerAD leaf7121Box) leaf7121InnerLog = true := by
  rfl'

private theorem leaf7121InnerLogValid :
    leaf7121InnerLog.Valid 8 (innerAD leaf7121Box) :=
  wideLogDataValid_of_cachedCheck endpoint572PositiveFacts
    endpoint581PositiveFacts.valid leaf7121CoverageChecked

private noncomputable def leaf7121InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629941/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7121InputLogOnePlusV_eq :
    leaf7121InputLogOnePlusV = outerEnclosure 24
      (leaf7121Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7121RoundedFacts : LeafRoundedFacts 8
    leaf7121Certificate.logOnePlusV leaf7121InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7121InputLogOnePlusV_eq }

private noncomputable def leaf7121Inputs : Inputs :=
  inputsOfCaches globalInput sk131RoundedInputs
    chi91InputQChi innerPair862Input
    leaf7121InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7121LowerChecked :
    lowerCheck 24 leaf7121Box leaf7121Inputs = true := by
  rfl'

private theorem leaf7121CoversExact : CoversExact 8
    leaf7121Box leaf7121Certificate leaf7121InnerLog leaf7121Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk131RoundedFacts chi91RoundedFacts
    innerPair862RoundedFacts leaf7121RoundedFacts (by rfl)

private theorem leaf7121FlatSound : Sound leaf7121Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7121CertificateValid
    leaf7121InnerLogValid leaf7121CoversExact leaf7121LowerChecked

private noncomputable def leaf7122Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (27/32), chiHi := (55/64) }

private noncomputable def leaf7122Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109081/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353655808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (254628465/134217728) }, upper := { exponent := 1, mantissa := (1997/1024) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi365LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68710838267/68707311616) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf7122InnerLog : WideLogData :=
  innerPair806Data

set_option maxRecDepth 1000000 in
private theorem leaf7122LocalValidity :
    LeafFacts leaf7122Box leaf7122Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7122Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353655808) }) = true
      norm_num [leaf7122Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7122CertificateValid :
    WideCertificateValid leaf7122Box leaf7122Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi365ValidityFacts
    leaf7122LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7122CoverageChecked :
    coverageCheck (innerAD leaf7122Box) leaf7122InnerLog = true := by
  rfl'

private theorem leaf7122InnerLogValid :
    leaf7122InnerLog.Valid 8 (innerAD leaf7122Box) :=
  wideLogDataValid_of_cachedCheck endpoint502PositiveFacts
    endpoint505PositiveFacts.valid leaf7122CoverageChecked

private noncomputable def leaf7122InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814971/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7122InputLogOnePlusV_eq :
    leaf7122InputLogOnePlusV = outerEnclosure 24
      (leaf7122Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7122RoundedFacts : LeafRoundedFacts 8
    leaf7122Certificate.logOnePlusV leaf7122InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7122InputLogOnePlusV_eq }

private noncomputable def leaf7122Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi365InputQChi innerPair806Input
    leaf7122InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7122LowerChecked :
    lowerCheck 24 leaf7122Box leaf7122Inputs = true := by
  rfl'

private theorem leaf7122CoversExact : CoversExact 8
    leaf7122Box leaf7122Certificate leaf7122InnerLog leaf7122Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi365RoundedFacts
    innerPair806RoundedFacts leaf7122RoundedFacts (by rfl)

private theorem leaf7122FlatSound : Sound leaf7122Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7122CertificateValid
    leaf7122InnerLogValid leaf7122CoversExact leaf7122LowerChecked

private noncomputable def leaf7123Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (55/64), chiHi := (7/8) }

private noncomputable def leaf7123Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109083/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353545216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (258101659/134217728) }, upper := { exponent := 1, mantissa := (253/128) } }, logOuter := sk132LogOuterCertificate, logK := sk132LogKCertificate, logChi := chi366LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68710727675/68707090432) } }, logDArg := sk132LogDArgCertificate }

private noncomputable def leaf7123InnerLog : WideLogData :=
  innerPair809Data

set_option maxRecDepth 1000000 in
private theorem leaf7123LocalValidity :
    LeafFacts leaf7123Box leaf7123Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7123Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353545216) }) = true
      norm_num [leaf7123Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7123CertificateValid :
    WideCertificateValid leaf7123Box leaf7123Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk132ValidityFacts chi366ValidityFacts
    leaf7123LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7123CoverageChecked :
    coverageCheck (innerAD leaf7123Box) leaf7123InnerLog = true := by
  rfl'

private theorem leaf7123InnerLogValid :
    leaf7123InnerLog.Valid 8 (innerAD leaf7123Box) :=
  wideLogDataValid_of_cachedCheck endpoint503PositiveFacts
    endpoint506PositiveFacts.valid leaf7123CoverageChecked

private noncomputable def leaf7123InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629969/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7123InputLogOnePlusV_eq :
    leaf7123InputLogOnePlusV = outerEnclosure 24
      (leaf7123Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7123RoundedFacts : LeafRoundedFacts 8
    leaf7123Certificate.logOnePlusV leaf7123InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7123InputLogOnePlusV_eq }

private noncomputable def leaf7123Inputs : Inputs :=
  inputsOfCaches globalInput sk132RoundedInputs
    chi366InputQChi innerPair809Input
    leaf7123InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7123LowerChecked :
    lowerCheck 24 leaf7123Box leaf7123Inputs = true := by
  rfl'

private theorem leaf7123CoversExact : CoversExact 8
    leaf7123Box leaf7123Certificate leaf7123InnerLog leaf7123Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk132RoundedFacts chi366RoundedFacts
    innerPair809RoundedFacts leaf7123RoundedFacts (by rfl)

private theorem leaf7123FlatSound : Sound leaf7123Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7123CertificateValid
    leaf7123InnerLogValid leaf7123CoversExact leaf7123LowerChecked

private noncomputable def leaf7124Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (13/16), chiHi := (53/64) }

private noncomputable def leaf7124Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109079/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353768448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (251089739/134217728) }, upper := { exponent := 1, mantissa := (3939/2048) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi363LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68710950907/68707536896) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf7124InnerLog : WideLogData :=
  innerPair802Data

set_option maxRecDepth 1000000 in
private theorem leaf7124LocalValidity :
    LeafFacts leaf7124Box leaf7124Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7124Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353768448) }) = true
      norm_num [leaf7124Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7124CertificateValid :
    WideCertificateValid leaf7124Box leaf7124Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi363ValidityFacts
    leaf7124LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7124CoverageChecked :
    coverageCheck (innerAD leaf7124Box) leaf7124InnerLog = true := by
  rfl'

private theorem leaf7124InnerLogValid :
    leaf7124InnerLog.Valid 8 (innerAD leaf7124Box) :=
  wideLogDataValid_of_cachedCheck endpoint501PositiveFacts
    endpoint504PositiveFacts.valid leaf7124CoverageChecked

private noncomputable def leaf7124InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814957/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7124InputLogOnePlusV_eq :
    leaf7124InputLogOnePlusV = outerEnclosure 24
      (leaf7124Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7124RoundedFacts : LeafRoundedFacts 8
    leaf7124Certificate.logOnePlusV leaf7124InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7124InputLogOnePlusV_eq }

private noncomputable def leaf7124Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi363InputQChi innerPair802Input
    leaf7124InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7124LowerChecked :
    lowerCheck 24 leaf7124Box leaf7124Inputs = true := by
  rfl'

private theorem leaf7124CoversExact : CoversExact 8
    leaf7124Box leaf7124Certificate leaf7124InnerLog leaf7124Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi363RoundedFacts
    innerPair802RoundedFacts leaf7124RoundedFacts (by rfl)

private theorem leaf7124FlatSound : Sound leaf7124Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7124CertificateValid
    leaf7124InnerLogValid leaf7124CoversExact leaf7124LowerChecked

private noncomputable def leaf7125Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (53/64), chiHi := (27/32) }

private noncomputable def leaf7125Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109081/67108864) }, vSqrt := { lower := (65529/65536), upper := (34357182459/34353655808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (254628465/134217728) }, upper := { exponent := 1, mantissa := (1997/1024) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi364LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (68710838267/68707311616) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf7125InnerLog : WideLogData :=
  innerPair806Data

set_option maxRecDepth 1000000 in
private theorem leaf7125LocalValidity :
    LeafFacts leaf7125Box leaf7125Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7125Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (34357182459/34353655808) }) = true
      norm_num [leaf7125Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7125CertificateValid :
    WideCertificateValid leaf7125Box leaf7125Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi364ValidityFacts
    leaf7125LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7125CoverageChecked :
    coverageCheck (innerAD leaf7125Box) leaf7125InnerLog = true := by
  rfl'

private theorem leaf7125InnerLogValid :
    leaf7125InnerLog.Valid 8 (innerAD leaf7125Box) :=
  wideLogDataValid_of_cachedCheck endpoint502PositiveFacts
    endpoint505PositiveFacts.valid leaf7125CoverageChecked

private noncomputable def leaf7125InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (5814971/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf7125InputLogOnePlusV_eq :
    leaf7125InputLogOnePlusV = outerEnclosure 24
      (leaf7125Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7125RoundedFacts : LeafRoundedFacts 8
    leaf7125Certificate.logOnePlusV leaf7125InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7125InputLogOnePlusV_eq }

private noncomputable def leaf7125Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi364InputQChi innerPair806Input
    leaf7125InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7125LowerChecked :
    lowerCheck 24 leaf7125Box leaf7125Inputs = true := by
  rfl'

private theorem leaf7125CoversExact : CoversExact 8
    leaf7125Box leaf7125Certificate leaf7125InnerLog leaf7125Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi364RoundedFacts
    innerPair806RoundedFacts leaf7125RoundedFacts (by rfl)

private theorem leaf7125FlatSound : Sound leaf7125Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7125CertificateValid
    leaf7125InnerLogValid leaf7125CoversExact leaf7125LowerChecked

private noncomputable def leaf7126Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (13/16), chiHi := (53/64) }

private noncomputable def leaf7126Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109081/67108864) }, vSqrt := { lower := (8191/8192), upper := (11452394153/11451219968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (254497401/134217728) }, upper := { exponent := 1, mantissa := (499/256) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi363LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (22903614121/22902439936) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf7126InnerLog : WideLogData :=
  innerPair806Data

set_option maxRecDepth 1000000 in
private theorem leaf7126LocalValidity :
    LeafFacts leaf7126Box leaf7126Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7126Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (11452394153/11451219968) }) = true
      norm_num [leaf7126Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7126CertificateValid :
    WideCertificateValid leaf7126Box leaf7126Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi363ValidityFacts
    leaf7126LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7126CoverageChecked :
    coverageCheck (innerAD leaf7126Box) leaf7126InnerLog = true := by
  rfl'

private theorem leaf7126InnerLogValid :
    leaf7126InnerLog.Valid 8 (innerAD leaf7126Box) :=
  wideLogDataValid_of_cachedCheck endpoint502PositiveFacts
    endpoint505PositiveFacts.valid leaf7126CoverageChecked

private noncomputable def leaf7126InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629941/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7126InputLogOnePlusV_eq :
    leaf7126InputLogOnePlusV = outerEnclosure 24
      (leaf7126Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7126RoundedFacts : LeafRoundedFacts 8
    leaf7126Certificate.logOnePlusV leaf7126InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7126InputLogOnePlusV_eq }

private noncomputable def leaf7126Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi363InputQChi innerPair806Input
    leaf7126InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7126LowerChecked :
    lowerCheck 24 leaf7126Box leaf7126Inputs = true := by
  rfl'

private theorem leaf7126CoversExact : CoversExact 8
    leaf7126Box leaf7126Certificate leaf7126InnerLog leaf7126Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi363RoundedFacts
    innerPair806RoundedFacts leaf7126RoundedFacts (by rfl)

private theorem leaf7126FlatSound : Sound leaf7126Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7126CertificateValid
    leaf7126InnerLogValid leaf7126CoversExact leaf7126LowerChecked

private noncomputable def leaf7127Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (53/64), chiHi := (27/32) }

private noncomputable def leaf7127Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109083/67108864) }, vSqrt := { lower := (8191/8192), upper := (34357182459/34353545216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (258101659/134217728) }, upper := { exponent := 1, mantissa := (253/128) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi364LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (68710727675/68707090432) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf7127InnerLog : WideLogData :=
  innerPair809Data

set_option maxRecDepth 1000000 in
private theorem leaf7127LocalValidity :
    LeafFacts leaf7127Box leaf7127Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7127Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (34357182459/34353545216) }) = true
      norm_num [leaf7127Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7127CertificateValid :
    WideCertificateValid leaf7127Box leaf7127Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi364ValidityFacts
    leaf7127LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7127CoverageChecked :
    coverageCheck (innerAD leaf7127Box) leaf7127InnerLog = true := by
  rfl'

private theorem leaf7127InnerLogValid :
    leaf7127InnerLog.Valid 8 (innerAD leaf7127Box) :=
  wideLogDataValid_of_cachedCheck endpoint503PositiveFacts
    endpoint506PositiveFacts.valid leaf7127CoverageChecked

private noncomputable def leaf7127InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629969/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7127InputLogOnePlusV_eq :
    leaf7127InputLogOnePlusV = outerEnclosure 24
      (leaf7127Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7127RoundedFacts : LeafRoundedFacts 8
    leaf7127Certificate.logOnePlusV leaf7127InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7127InputLogOnePlusV_eq }

private noncomputable def leaf7127Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi364InputQChi innerPair809Input
    leaf7127InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7127LowerChecked :
    lowerCheck 24 leaf7127Box leaf7127Inputs = true := by
  rfl'

private theorem leaf7127CoversExact : CoversExact 8
    leaf7127Box leaf7127Certificate leaf7127InnerLog leaf7127Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi364RoundedFacts
    innerPair809RoundedFacts leaf7127RoundedFacts (by rfl)

private theorem leaf7127FlatSound : Sound leaf7127Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7127CertificateValid
    leaf7127InnerLogValid leaf7127CoversExact leaf7127LowerChecked

private noncomputable def leaf7128Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (27/32), chiHi := (55/64) }

private noncomputable def leaf7128Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32765/32768), upper := (67109083/67108864) }, vSqrt := { lower := (65529/65536), upper := (11452394153/11451181056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (258167191/134217728) }, upper := { exponent := 1, mantissa := (4049/2048) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi365LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (22903575209/22902362112) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf7128InnerLog : WideLogData :=
  innerPair809Data

set_option maxRecDepth 1000000 in
private theorem leaf7128LocalValidity :
    LeafFacts leaf7128Box leaf7128Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7128Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (11452394153/11451181056) }) = true
      norm_num [leaf7128Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7128CertificateValid :
    WideCertificateValid leaf7128Box leaf7128Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi365ValidityFacts
    leaf7128LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7128CoverageChecked :
    coverageCheck (innerAD leaf7128Box) leaf7128InnerLog = true := by
  rfl'

private theorem leaf7128InnerLogValid :
    leaf7128InnerLog.Valid 8 (innerAD leaf7128Box) :=
  wideLogDataValid_of_cachedCheck endpoint503PositiveFacts
    endpoint506PositiveFacts.valid leaf7128CoverageChecked

private noncomputable def leaf7128InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629969/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7128InputLogOnePlusV_eq :
    leaf7128InputLogOnePlusV = outerEnclosure 24
      (leaf7128Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7128RoundedFacts : LeafRoundedFacts 8
    leaf7128Certificate.logOnePlusV leaf7128InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7128InputLogOnePlusV_eq }

private noncomputable def leaf7128Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi365InputQChi innerPair809Input
    leaf7128InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7128LowerChecked :
    lowerCheck 24 leaf7128Box leaf7128Inputs = true := by
  rfl'

private theorem leaf7128CoversExact : CoversExact 8
    leaf7128Box leaf7128Certificate leaf7128InnerLog leaf7128Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi365RoundedFacts
    innerPair809RoundedFacts leaf7128RoundedFacts (by rfl)

private theorem leaf7128FlatSound : Sound leaf7128Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7128CertificateValid
    leaf7128InnerLogValid leaf7128CoversExact leaf7128LowerChecked

private noncomputable def leaf7129Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (55/64), chiHi := (7/8) }

private noncomputable def leaf7129Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109085/67108864) }, vSqrt := { lower := (65529/65536), upper := (17178329085/17176715264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (261705917/134217728) }, upper := { exponent := 2, mantissa := (513/512) } }, logOuter := sk129LogOuterCertificate, logK := sk129LogKCertificate, logChi := chi366LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131065/65536) }, upper := { exponent := 1, mantissa := (34355044349/34353430528) } }, logDArg := sk129LogDArgCertificate }

private noncomputable def leaf7129InnerLog : WideLogData :=
  innerPair812Data

set_option maxRecDepth 1000000 in
private theorem leaf7129LocalValidity :
    LeafFacts leaf7129Box leaf7129Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7129Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65529/65536), upper := (17178329085/17176715264) }) = true
      norm_num [leaf7129Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7129CertificateValid :
    WideCertificateValid leaf7129Box leaf7129Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk129ValidityFacts chi366ValidityFacts
    leaf7129LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7129CoverageChecked :
    coverageCheck (innerAD leaf7129Box) leaf7129InnerLog = true := by
  rfl'

private theorem leaf7129InnerLogValid :
    leaf7129InnerLog.Valid 8 (innerAD leaf7129Box) :=
  wideLogDataValid_of_cachedCheck endpoint504PositiveFacts
    endpoint582PositiveFacts.valid leaf7129CoverageChecked

private noncomputable def leaf7129InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628183/16777216), upper := (11629869/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7129InputLogOnePlusV_eq :
    leaf7129InputLogOnePlusV = outerEnclosure 24
      (leaf7129Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7129RoundedFacts : LeafRoundedFacts 8
    leaf7129Certificate.logOnePlusV leaf7129InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7129InputLogOnePlusV_eq }

private noncomputable def leaf7129Inputs : Inputs :=
  inputsOfCaches globalInput sk129RoundedInputs
    chi366InputQChi innerPair812Input
    leaf7129InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7129LowerChecked :
    lowerCheck 24 leaf7129Box leaf7129Inputs = true := by
  rfl'

private theorem leaf7129CoversExact : CoversExact 8
    leaf7129Box leaf7129Certificate leaf7129InnerLog leaf7129Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk129RoundedFacts chi366RoundedFacts
    innerPair812RoundedFacts leaf7129RoundedFacts (by rfl)

private theorem leaf7129FlatSound : Sound leaf7129Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7129CertificateValid
    leaf7129InnerLogValid leaf7129CoversExact leaf7129LowerChecked

private noncomputable def leaf7130Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (27/32), chiHi := (55/64) }

private noncomputable def leaf7130Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109085/67108864) }, vSqrt := { lower := (8191/8192), upper := (17178329085/17176715264) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (261705917/134217728) }, upper := { exponent := 2, mantissa := (513/512) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi365LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (34355044349/34353430528) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf7130InnerLog : WideLogData :=
  innerPair812Data

set_option maxRecDepth 1000000 in
private theorem leaf7130LocalValidity :
    LeafFacts leaf7130Box leaf7130Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7130Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (17178329085/17176715264) }) = true
      norm_num [leaf7130Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7130CertificateValid :
    WideCertificateValid leaf7130Box leaf7130Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi365ValidityFacts
    leaf7130LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7130CoverageChecked :
    coverageCheck (innerAD leaf7130Box) leaf7130InnerLog = true := by
  rfl'

private theorem leaf7130InnerLogValid :
    leaf7130InnerLog.Valid 8 (innerAD leaf7130Box) :=
  wideLogDataValid_of_cachedCheck endpoint504PositiveFacts
    endpoint582PositiveFacts.valid leaf7130CoverageChecked

private noncomputable def leaf7130InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629869/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7130InputLogOnePlusV_eq :
    leaf7130InputLogOnePlusV = outerEnclosure 24
      (leaf7130Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7130RoundedFacts : LeafRoundedFacts 8
    leaf7130Certificate.logOnePlusV leaf7130InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7130InputLogOnePlusV_eq }

private noncomputable def leaf7130Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi365InputQChi innerPair812Input
    leaf7130InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7130LowerChecked :
    lowerCheck 24 leaf7130Box leaf7130Inputs = true := by
  rfl'

private theorem leaf7130CoversExact : CoversExact 8
    leaf7130Box leaf7130Certificate leaf7130InnerLog leaf7130Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi365RoundedFacts
    innerPair812RoundedFacts leaf7130RoundedFacts (by rfl)

private theorem leaf7130FlatSound : Sound leaf7130Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7130CertificateValid
    leaf7130InnerLogValid leaf7130CoversExact leaf7130LowerChecked

private noncomputable def leaf7131Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (55/64), chiHi := (7/8) }

private noncomputable def leaf7131Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (65529/65536), upper := (67109087/67108864) }, vSqrt := { lower := (8191/8192), upper := (1145221939/1145110528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 1, mantissa := (265310175/134217728) }, upper := { exponent := 2, mantissa := (65/64) } }, logOuter := sk130LogOuterCertificate, logK := sk130LogKCertificate, logChi := chi366LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (2290332467/2290221056) } }, logDArg := sk130LogDArgCertificate }

private noncomputable def leaf7131InnerLog : WideLogData :=
  innerPair814Data

set_option maxRecDepth 1000000 in
private theorem leaf7131LocalValidity :
    LeafFacts leaf7131Box leaf7131Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf7131Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1145221939/1145110528) }) = true
      norm_num [leaf7131Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf7131CertificateValid :
    WideCertificateValid leaf7131Box leaf7131Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk130ValidityFacts chi366ValidityFacts
    leaf7131LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf7131CoverageChecked :
    coverageCheck (innerAD leaf7131Box) leaf7131InnerLog = true := by
  rfl'

private theorem leaf7131InnerLogValid :
    leaf7131InnerLog.Valid 8 (innerAD leaf7131Box) :=
  wideLogDataValid_of_cachedCheck endpoint505PositiveFacts
    endpoint582PositiveFacts.valid leaf7131CoverageChecked

private noncomputable def leaf7131InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629897/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf7131InputLogOnePlusV_eq :
    leaf7131InputLogOnePlusV = outerEnclosure 24
      (leaf7131Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf7131RoundedFacts : LeafRoundedFacts 8
    leaf7131Certificate.logOnePlusV leaf7131InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf7131InputLogOnePlusV_eq }

private noncomputable def leaf7131Inputs : Inputs :=
  inputsOfCaches globalInput sk130RoundedInputs
    chi366InputQChi innerPair814Input
    leaf7131InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf7131LowerChecked :
    lowerCheck 24 leaf7131Box leaf7131Inputs = true := by
  rfl'

private theorem leaf7131CoversExact : CoversExact 8
    leaf7131Box leaf7131Certificate leaf7131InnerLog leaf7131Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk130RoundedFacts chi366RoundedFacts
    innerPair814RoundedFacts leaf7131RoundedFacts (by rfl)

private theorem leaf7131FlatSound : Sound leaf7131Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf7131CertificateValid
    leaf7131InnerLogValid leaf7131CoversExact leaf7131LowerChecked

private noncomputable def component144Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node0_sound : Sound component144Node0Box :=
  sound_of_literal_split component144Node0Box leaf7076Box leaf7077Box
    .chi (49/64) (by rfl) (by rfl)
    leaf7076FlatSound leaf7077FlatSound

private noncomputable def component144Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node1_sound : Sound component144Node1Box :=
  sound_of_literal_split component144Node1Box leaf7078Box leaf7079Box
    .chi (49/64) (by rfl) (by rfl)
    leaf7078FlatSound leaf7079FlatSound

private noncomputable def component144Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node2_sound : Sound component144Node2Box :=
  sound_of_literal_split component144Node2Box component144Node0Box component144Node1Box
    .k (49/16) (by rfl) (by rfl)
    component144Node0_sound component144Node1_sound

private noncomputable def component144Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (49/16), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component144Node3_sound : Sound component144Node3Box :=
  sound_of_literal_split component144Node3Box leaf7080Box leaf7081Box
    .chi (51/64) (by rfl) (by rfl)
    leaf7080FlatSound leaf7081FlatSound

private noncomputable def component144Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (49/16), kHi := (25/8), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component144Node4_sound : Sound component144Node4Box :=
  sound_of_literal_split component144Node4Box leaf7082Box leaf7083Box
    .chi (51/64) (by rfl) (by rfl)
    leaf7082FlatSound leaf7083FlatSound

private noncomputable def component144Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component144Node5_sound : Sound component144Node5Box :=
  sound_of_literal_split component144Node5Box component144Node3Box component144Node4Box
    .k (49/16) (by rfl) (by rfl)
    component144Node3_sound component144Node4_sound

private noncomputable def component144Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component144Node6_sound : Sound component144Node6Box :=
  sound_of_literal_split component144Node6Box component144Node2Box component144Node5Box
    .chi (25/32) (by rfl) (by rfl)
    component144Node2_sound component144Node5_sound

private noncomputable def component144Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node7_sound : Sound component144Node7Box :=
  sound_of_literal_split component144Node7Box leaf7084Box leaf7085Box
    .chi (49/64) (by rfl) (by rfl)
    leaf7084FlatSound leaf7085FlatSound

private noncomputable def component144Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node8_sound : Sound component144Node8Box :=
  sound_of_literal_split component144Node8Box leaf7086Box leaf7087Box
    .chi (49/64) (by rfl) (by rfl)
    leaf7086FlatSound leaf7087FlatSound

private noncomputable def component144Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node9_sound : Sound component144Node9Box :=
  sound_of_literal_split component144Node9Box component144Node7Box component144Node8Box
    .k (51/16) (by rfl) (by rfl)
    component144Node7_sound component144Node8_sound

private noncomputable def component144Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (51/16), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component144Node10_sound : Sound component144Node10Box :=
  sound_of_literal_split component144Node10Box leaf7088Box leaf7089Box
    .chi (51/64) (by rfl) (by rfl)
    leaf7088FlatSound leaf7089FlatSound

private noncomputable def component144Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component144Node11_sound : Sound component144Node11Box :=
  sound_of_literal_split component144Node11Box leaf7090Box leaf7091Box
    .chi (51/64) (by rfl) (by rfl)
    leaf7090FlatSound leaf7091FlatSound

private noncomputable def component144Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component144Node12_sound : Sound component144Node12Box :=
  sound_of_literal_split component144Node12Box component144Node10Box component144Node11Box
    .k (51/16) (by rfl) (by rfl)
    component144Node10_sound component144Node11_sound

private noncomputable def component144Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component144Node13_sound : Sound component144Node13Box :=
  sound_of_literal_split component144Node13Box component144Node9Box component144Node12Box
    .chi (25/32) (by rfl) (by rfl)
    component144Node9_sound component144Node12_sound

private noncomputable def component144Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component144Node14_sound : Sound component144Node14Box :=
  sound_of_literal_split component144Node14Box component144Node6Box component144Node13Box
    .k (25/8) (by rfl) (by rfl)
    component144Node6_sound component144Node13_sound

private noncomputable def component144Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node15_sound : Sound component144Node15Box :=
  sound_of_literal_split component144Node15Box leaf7092Box leaf7093Box
    .k (49/16) (by rfl) (by rfl)
    leaf7092FlatSound leaf7093FlatSound

private noncomputable def component144Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component144Node16_sound : Sound component144Node16Box :=
  sound_of_literal_split component144Node16Box leaf7094Box leaf7095Box
    .k (49/16) (by rfl) (by rfl)
    leaf7094FlatSound leaf7095FlatSound

private noncomputable def component144Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (25/8), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component144Node17_sound : Sound component144Node17Box :=
  sound_of_literal_split component144Node17Box component144Node15Box component144Node16Box
    .chi (27/32) (by rfl) (by rfl)
    component144Node15_sound component144Node16_sound

private noncomputable def component144Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (51/16), kHi := (13/4), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node18_sound : Sound component144Node18Box :=
  sound_of_literal_split component144Node18Box leaf7097Box leaf7098Box
    .chi (53/64) (by rfl) (by rfl)
    leaf7097FlatSound leaf7098FlatSound

private noncomputable def component144Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node19_sound : Sound component144Node19Box :=
  sound_of_literal_split component144Node19Box leaf7096Box component144Node18Box
    .k (51/16) (by rfl) (by rfl)
    leaf7096FlatSound component144Node18_sound

private noncomputable def component144Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component144Node20_sound : Sound component144Node20Box :=
  sound_of_literal_split component144Node20Box leaf7099Box leaf7100Box
    .k (51/16) (by rfl) (by rfl)
    leaf7099FlatSound leaf7100FlatSound

private noncomputable def component144Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (25/8), kHi := (13/4), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component144Node21_sound : Sound component144Node21Box :=
  sound_of_literal_split component144Node21Box component144Node19Box component144Node20Box
    .chi (27/32) (by rfl) (by rfl)
    component144Node19_sound component144Node20_sound

private noncomputable def component144Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component144Node22_sound : Sound component144Node22Box :=
  sound_of_literal_split component144Node22Box component144Node17Box component144Node21Box
    .k (25/8) (by rfl) (by rfl)
    component144Node17_sound component144Node21_sound

private noncomputable def component144Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (13/4), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component144Node23_sound : Sound component144Node23Box :=
  sound_of_literal_split component144Node23Box component144Node14Box component144Node22Box
    .chi (13/16) (by rfl) (by rfl)
    component144Node14_sound component144Node22_sound

private noncomputable def component144Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node24_sound : Sound component144Node24Box :=
  sound_of_literal_split component144Node24Box leaf7101Box leaf7102Box
    .chi (49/64) (by rfl) (by rfl)
    leaf7101FlatSound leaf7102FlatSound

private noncomputable def component144Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node25_sound : Sound component144Node25Box :=
  sound_of_literal_split component144Node25Box leaf7103Box leaf7104Box
    .chi (49/64) (by rfl) (by rfl)
    leaf7103FlatSound leaf7104FlatSound

private noncomputable def component144Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node26_sound : Sound component144Node26Box :=
  sound_of_literal_split component144Node26Box component144Node24Box component144Node25Box
    .k (53/16) (by rfl) (by rfl)
    component144Node24_sound component144Node25_sound

private noncomputable def component144Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component144Node27_sound : Sound component144Node27Box :=
  sound_of_literal_split component144Node27Box leaf7105Box leaf7106Box
    .chi (51/64) (by rfl) (by rfl)
    leaf7105FlatSound leaf7106FlatSound

private noncomputable def component144Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component144Node28_sound : Sound component144Node28Box :=
  sound_of_literal_split component144Node28Box leaf7107Box leaf7108Box
    .chi (51/64) (by rfl) (by rfl)
    leaf7107FlatSound leaf7108FlatSound

private noncomputable def component144Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component144Node29_sound : Sound component144Node29Box :=
  sound_of_literal_split component144Node29Box component144Node27Box component144Node28Box
    .k (53/16) (by rfl) (by rfl)
    component144Node27_sound component144Node28_sound

private noncomputable def component144Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component144Node30_sound : Sound component144Node30Box :=
  sound_of_literal_split component144Node30Box component144Node26Box component144Node29Box
    .chi (25/32) (by rfl) (by rfl)
    component144Node26_sound component144Node29_sound

private noncomputable def component144Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (3/4), chiHi := (49/64) }

set_option maxRecDepth 1000000 in
private theorem component144Node31_sound : Sound component144Node31Box :=
  sound_of_literal_split component144Node31Box leaf7109Box leaf7110Box
    .k (55/16) (by rfl) (by rfl)
    leaf7109FlatSound leaf7110FlatSound

private noncomputable def component144Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (49/64), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node32_sound : Sound component144Node32Box :=
  sound_of_literal_split component144Node32Box leaf7111Box leaf7112Box
    .k (55/16) (by rfl) (by rfl)
    leaf7111FlatSound leaf7112FlatSound

private noncomputable def component144Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (3/4), chiHi := (25/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node33_sound : Sound component144Node33Box :=
  sound_of_literal_split component144Node33Box component144Node31Box component144Node32Box
    .chi (49/64) (by rfl) (by rfl)
    component144Node31_sound component144Node32_sound

private noncomputable def component144Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (25/32), chiHi := (51/64) }

set_option maxRecDepth 1000000 in
private theorem component144Node34_sound : Sound component144Node34Box :=
  sound_of_literal_split component144Node34Box leaf7113Box leaf7114Box
    .k (55/16) (by rfl) (by rfl)
    leaf7113FlatSound leaf7114FlatSound

private noncomputable def component144Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (51/64), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component144Node35_sound : Sound component144Node35Box :=
  sound_of_literal_split component144Node35Box leaf7115Box leaf7116Box
    .k (55/16) (by rfl) (by rfl)
    leaf7115FlatSound leaf7116FlatSound

private noncomputable def component144Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (25/32), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component144Node36_sound : Sound component144Node36Box :=
  sound_of_literal_split component144Node36Box component144Node34Box component144Node35Box
    .chi (51/64) (by rfl) (by rfl)
    component144Node34_sound component144Node35_sound

private noncomputable def component144Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component144Node37_sound : Sound component144Node37Box :=
  sound_of_literal_split component144Node37Box component144Node33Box component144Node36Box
    .chi (25/32) (by rfl) (by rfl)
    component144Node33_sound component144Node36_sound

private noncomputable def component144Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (3/4), chiHi := (13/16) }

set_option maxRecDepth 1000000 in
private theorem component144Node38_sound : Sound component144Node38Box :=
  sound_of_literal_split component144Node38Box component144Node30Box component144Node37Box
    .k (27/8) (by rfl) (by rfl)
    component144Node30_sound component144Node37_sound

private noncomputable def component144Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (53/16), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node39_sound : Sound component144Node39Box :=
  sound_of_literal_split component144Node39Box leaf7117Box leaf7118Box
    .chi (53/64) (by rfl) (by rfl)
    leaf7117FlatSound leaf7118FlatSound

private noncomputable def component144Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node40_sound : Sound component144Node40Box :=
  sound_of_literal_split component144Node40Box leaf7119Box leaf7120Box
    .chi (53/64) (by rfl) (by rfl)
    leaf7119FlatSound leaf7120FlatSound

private noncomputable def component144Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node41_sound : Sound component144Node41Box :=
  sound_of_literal_split component144Node41Box component144Node39Box component144Node40Box
    .k (53/16) (by rfl) (by rfl)
    component144Node39_sound component144Node40_sound

private noncomputable def component144Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (53/16), kHi := (27/8), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component144Node42_sound : Sound component144Node42Box :=
  sound_of_literal_split component144Node42Box leaf7122Box leaf7123Box
    .chi (55/64) (by rfl) (by rfl)
    leaf7122FlatSound leaf7123FlatSound

private noncomputable def component144Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component144Node43_sound : Sound component144Node43Box :=
  sound_of_literal_split component144Node43Box leaf7121Box component144Node42Box
    .k (53/16) (by rfl) (by rfl)
    leaf7121FlatSound component144Node42_sound

private noncomputable def component144Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (27/8), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component144Node44_sound : Sound component144Node44Box :=
  sound_of_literal_split component144Node44Box component144Node41Box component144Node43Box
    .chi (27/32) (by rfl) (by rfl)
    component144Node41_sound component144Node43_sound

private noncomputable def component144Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node45_sound : Sound component144Node45Box :=
  sound_of_literal_split component144Node45Box leaf7124Box leaf7125Box
    .chi (53/64) (by rfl) (by rfl)
    leaf7124FlatSound leaf7125FlatSound

private noncomputable def component144Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node46_sound : Sound component144Node46Box :=
  sound_of_literal_split component144Node46Box leaf7126Box leaf7127Box
    .chi (53/64) (by rfl) (by rfl)
    leaf7126FlatSound leaf7127FlatSound

private noncomputable def component144Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (13/16), chiHi := (27/32) }

set_option maxRecDepth 1000000 in
private theorem component144Node47_sound : Sound component144Node47Box :=
  sound_of_literal_split component144Node47Box component144Node45Box component144Node46Box
    .k (55/16) (by rfl) (by rfl)
    component144Node45_sound component144Node46_sound

private noncomputable def component144Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (55/16), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component144Node48_sound : Sound component144Node48Box :=
  sound_of_literal_split component144Node48Box leaf7128Box leaf7129Box
    .chi (55/64) (by rfl) (by rfl)
    leaf7128FlatSound leaf7129FlatSound

private noncomputable def component144Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (55/16), kHi := (7/2), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component144Node49_sound : Sound component144Node49Box :=
  sound_of_literal_split component144Node49Box leaf7130Box leaf7131Box
    .chi (55/64) (by rfl) (by rfl)
    leaf7130FlatSound leaf7131FlatSound

private noncomputable def component144Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (27/32), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component144Node50_sound : Sound component144Node50Box :=
  sound_of_literal_split component144Node50Box component144Node48Box component144Node49Box
    .k (55/16) (by rfl) (by rfl)
    component144Node48_sound component144Node49_sound

private noncomputable def component144Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (27/8), kHi := (7/2), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component144Node51_sound : Sound component144Node51Box :=
  sound_of_literal_split component144Node51Box component144Node47Box component144Node50Box
    .chi (27/32) (by rfl) (by rfl)
    component144Node47_sound component144Node50_sound

private noncomputable def component144Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (13/16), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component144Node52_sound : Sound component144Node52Box :=
  sound_of_literal_split component144Node52Box component144Node44Box component144Node51Box
    .k (27/8) (by rfl) (by rfl)
    component144Node44_sound component144Node51_sound

private noncomputable def component144Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (13/4), kHi := (7/2), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
private theorem component144Node53_sound : Sound component144Node53Box :=
  sound_of_literal_split component144Node53Box component144Node38Box component144Node52Box
    .chi (13/16) (by rfl) (by rfl)
    component144Node38_sound component144Node52_sound

noncomputable def component144Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (3), kHi := (7/2), chiLo := (3/4), chiHi := (7/8) }

set_option maxRecDepth 1000000 in
theorem component144_sound : Sound component144Box :=
  sound_of_literal_split component144Box component144Node23Box component144Node53Box
    .k (13/4) (by rfl) (by rfl)
    component144Node23_sound component144Node53_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
