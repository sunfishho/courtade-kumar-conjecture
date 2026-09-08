import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch7
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

private noncomputable def leaf3701Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf3701Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217915/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716337152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (228550855/134217728) }, upper := { exponent := 0, mantissa := (3581/2048) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434830847/137432674304) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf3701InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3701LocalValidity :
    LeafFacts leaf3701Box leaf3701Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3701Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716337152) }) = true
      norm_num [leaf3701Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3701CertificateValid :
    WideCertificateValid leaf3701Box leaf3701Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi58ValidityFacts
    leaf3701LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3701CoverageChecked :
    coverageCheck (innerAD leaf3701Box) leaf3701InnerLog = true := by
  rfl'

private theorem leaf3701InnerLogValid :
    leaf3701InnerLog.Valid 8 (innerAD leaf3701Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3701CoverageChecked

private noncomputable def leaf3701InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf3701InputLogOnePlusV_eq :
    leaf3701InputLogOnePlusV = outerEnclosure 24
      (leaf3701Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3701RoundedFacts : LeafRoundedFacts 8
    leaf3701Certificate.logOnePlusV leaf3701InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3701InputLogOnePlusV_eq }

private noncomputable def leaf3701Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi58InputQChi innerPair64Input
    leaf3701InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3701LowerChecked :
    lowerCheck 24 leaf3701Box leaf3701Inputs = true := by
  rfl'

private theorem leaf3701CoversExact : CoversExact 8
    leaf3701Box leaf3701Certificate leaf3701InnerLog leaf3701Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi58RoundedFacts
    innerPair64RoundedFacts leaf3701RoundedFacts (by rfl)

private theorem leaf3701FlatSound : Sound leaf3701Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3701CertificateValid
    leaf3701InnerLogValid leaf3701CoversExact leaf3701LowerChecked

private noncomputable def leaf3702Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf3702Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217917/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716294144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (229861493/134217728) }, upper := { exponent := 0, mantissa := (1801/1024) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434787839/137432588288) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf3702InnerLog : WideLogData :=
  innerPair89Data

set_option maxRecDepth 1000000 in
private theorem leaf3702LocalValidity :
    LeafFacts leaf3702Box leaf3702Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3702Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716294144) }) = true
      norm_num [leaf3702Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3702CertificateValid :
    WideCertificateValid leaf3702Box leaf3702Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi58ValidityFacts
    leaf3702LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3702CoverageChecked :
    coverageCheck (innerAD leaf3702Box) leaf3702InnerLog = true := by
  rfl'

private theorem leaf3702InnerLogValid :
    leaf3702InnerLog.Valid 8 (innerAD leaf3702Box) :=
  wideLogDataValid_of_cachedCheck endpoint20PositiveFacts
    endpoint63PositiveFacts.valid leaf3702CoverageChecked

private noncomputable def leaf3702InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3702InputLogOnePlusV_eq :
    leaf3702InputLogOnePlusV = outerEnclosure 24
      (leaf3702Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3702RoundedFacts : LeafRoundedFacts 8
    leaf3702Certificate.logOnePlusV leaf3702InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3702InputLogOnePlusV_eq }

private noncomputable def leaf3702Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi58InputQChi innerPair89Input
    leaf3702InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3702LowerChecked :
    lowerCheck 24 leaf3702Box leaf3702Inputs = true := by
  rfl'

private theorem leaf3702CoversExact : CoversExact 8
    leaf3702Box leaf3702Certificate leaf3702InnerLog leaf3702Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi58RoundedFacts
    innerPair89RoundedFacts leaf3702RoundedFacts (by rfl)

private theorem leaf3702FlatSound : Sound leaf3702Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3702CertificateValid
    leaf3702InnerLogValid leaf3702CoversExact leaf3702LowerChecked

private noncomputable def leaf3703Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3703Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217917/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716187648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (233269157/134217728) }, upper := { exponent := 0, mantissa := (1827/1024) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434681343/137432375296) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf3703InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3703LocalValidity :
    LeafFacts leaf3703Box leaf3703Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3703Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716187648) }) = true
      norm_num [leaf3703Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3703CertificateValid :
    WideCertificateValid leaf3703Box leaf3703Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi59ValidityFacts
    leaf3703LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3703CoverageChecked :
    coverageCheck (innerAD leaf3703Box) leaf3703InnerLog = true := by
  rfl'

private theorem leaf3703InnerLogValid :
    leaf3703InnerLog.Valid 8 (innerAD leaf3703Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3703CoverageChecked

private noncomputable def leaf3703InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814681/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3703InputLogOnePlusV_eq :
    leaf3703InputLogOnePlusV = outerEnclosure 24
      (leaf3703Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3703RoundedFacts : LeafRoundedFacts 8
    leaf3703Certificate.logOnePlusV leaf3703InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3703InputLogOnePlusV_eq }

private noncomputable def leaf3703Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi59InputQChi innerPair66Input
    leaf3703InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3703LowerChecked :
    lowerCheck 24 leaf3703Box leaf3703Inputs = true := by
  rfl'

private theorem leaf3703CoversExact : CoversExact 8
    leaf3703Box leaf3703Certificate leaf3703InnerLog leaf3703Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi59RoundedFacts
    innerPair66RoundedFacts leaf3703RoundedFacts (by rfl)

private theorem leaf3703FlatSound : Sound leaf3703Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3703CertificateValid
    leaf3703InnerLogValid leaf3703CoversExact leaf3703LowerChecked

private noncomputable def leaf3704Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3704Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217919/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905380864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (234645327/134217728) }, upper := { exponent := 0, mantissa := (919/512) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811545429/45810761728) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf3704InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3704LocalValidity :
    LeafFacts leaf3704Box leaf3704Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3704Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905380864) }) = true
      norm_num [leaf3704Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3704CertificateValid :
    WideCertificateValid leaf3704Box leaf3704Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi59ValidityFacts
    leaf3704LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3704CoverageChecked :
    coverageCheck (innerAD leaf3704Box) leaf3704InnerLog = true := by
  rfl'

private theorem leaf3704InnerLogValid :
    leaf3704InnerLog.Valid 8 (innerAD leaf3704Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3704CoverageChecked

private noncomputable def leaf3704InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3704InputLogOnePlusV_eq :
    leaf3704InputLogOnePlusV = outerEnclosure 24
      (leaf3704Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3704RoundedFacts : LeafRoundedFacts 8
    leaf3704Certificate.logOnePlusV leaf3704InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3704InputLogOnePlusV_eq }

private noncomputable def leaf3704Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi59InputQChi innerPair66Input
    leaf3704InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3704LowerChecked :
    lowerCheck 24 leaf3704Box leaf3704Inputs = true := by
  rfl'

private theorem leaf3704CoversExact : CoversExact 8
    leaf3704Box leaf3704Certificate leaf3704InnerLog leaf3704Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi59RoundedFacts
    innerPair66RoundedFacts leaf3704RoundedFacts (by rfl)

private theorem leaf3704FlatSound : Sound leaf3704Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3704CertificateValid
    leaf3704InnerLogValid leaf3704CoversExact leaf3704LowerChecked

private noncomputable def leaf3705Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf3705Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217919/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716251136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (231172131/134217728) }, upper := { exponent := 0, mantissa := (3623/2048) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434744831/137432502272) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf3705InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3705LocalValidity :
    LeafFacts leaf3705Box leaf3705Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3705Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716251136) }) = true
      norm_num [leaf3705Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3705CertificateValid :
    WideCertificateValid leaf3705Box leaf3705Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi58ValidityFacts
    leaf3705LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3705CoverageChecked :
    coverageCheck (innerAD leaf3705Box) leaf3705InnerLog = true := by
  rfl'

private theorem leaf3705InnerLogValid :
    leaf3705InnerLog.Valid 8 (innerAD leaf3705Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3705CoverageChecked

private noncomputable def leaf3705InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3705InputLogOnePlusV_eq :
    leaf3705InputLogOnePlusV = outerEnclosure 24
      (leaf3705Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3705RoundedFacts : LeafRoundedFacts 8
    leaf3705Certificate.logOnePlusV leaf3705InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3705InputLogOnePlusV_eq }

private noncomputable def leaf3705Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi58InputQChi innerPair66Input
    leaf3705InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3705LowerChecked :
    lowerCheck 24 leaf3705Box leaf3705Inputs = true := by
  rfl'

private theorem leaf3705CoversExact : CoversExact 8
    leaf3705Box leaf3705Certificate leaf3705InnerLog leaf3705Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi58RoundedFacts
    innerPair66RoundedFacts leaf3705RoundedFacts (by rfl)

private theorem leaf3705FlatSound : Sound leaf3705Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3705CertificateValid
    leaf3705InnerLogValid leaf3705CoversExact leaf3705LowerChecked

private noncomputable def leaf3706Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf3706Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217921/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716208128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (232482769/134217728) }, upper := { exponent := 0, mantissa := (911/512) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434701823/137432416256) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf3706InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3706LocalValidity :
    LeafFacts leaf3706Box leaf3706Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3706Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716208128) }) = true
      norm_num [leaf3706Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3706CertificateValid :
    WideCertificateValid leaf3706Box leaf3706Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi58ValidityFacts
    leaf3706LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3706CoverageChecked :
    coverageCheck (innerAD leaf3706Box) leaf3706InnerLog = true := by
  rfl'

private theorem leaf3706InnerLogValid :
    leaf3706InnerLog.Valid 8 (innerAD leaf3706Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3706CoverageChecked

private noncomputable def leaf3706InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (726835/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3706InputLogOnePlusV_eq :
    leaf3706InputLogOnePlusV = outerEnclosure 24
      (leaf3706Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3706RoundedFacts : LeafRoundedFacts 8
    leaf3706Certificate.logOnePlusV leaf3706InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3706InputLogOnePlusV_eq }

private noncomputable def leaf3706Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi58InputQChi innerPair66Input
    leaf3706InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3706LowerChecked :
    lowerCheck 24 leaf3706Box leaf3706Inputs = true := by
  rfl'

private theorem leaf3706CoversExact : CoversExact 8
    leaf3706Box leaf3706Certificate leaf3706InnerLog leaf3706Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi58RoundedFacts
    innerPair66RoundedFacts leaf3706RoundedFacts (by rfl)

private theorem leaf3706FlatSound : Sound leaf3706Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3706CertificateValid
    leaf3706InnerLogValid leaf3706CoversExact leaf3706LowerChecked

private noncomputable def leaf3707Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3707Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217921/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716097536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (236021497/134217728) }, upper := { exponent := 0, mantissa := (1849/1024) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434591231/137432195072) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf3707InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3707LocalValidity :
    LeafFacts leaf3707Box leaf3707Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3707Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716097536) }) = true
      norm_num [leaf3707Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3707CertificateValid :
    WideCertificateValid leaf3707Box leaf3707Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi59ValidityFacts
    leaf3707LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3707CoverageChecked :
    coverageCheck (innerAD leaf3707Box) leaf3707InnerLog = true := by
  rfl'

private theorem leaf3707InnerLogValid :
    leaf3707InnerLog.Valid 8 (innerAD leaf3707Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3707CoverageChecked

private noncomputable def leaf3707InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3707InputLogOnePlusV_eq :
    leaf3707InputLogOnePlusV = outerEnclosure 24
      (leaf3707Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3707RoundedFacts : LeafRoundedFacts 8
    leaf3707Certificate.logOnePlusV leaf3707InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3707InputLogOnePlusV_eq }

private noncomputable def leaf3707Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi59InputQChi innerPair71Input
    leaf3707InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3707LowerChecked :
    lowerCheck 24 leaf3707Box leaf3707Inputs = true := by
  rfl'

private theorem leaf3707CoversExact : CoversExact 8
    leaf3707Box leaf3707Certificate leaf3707InnerLog leaf3707Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi59RoundedFacts
    innerPair71RoundedFacts leaf3707RoundedFacts (by rfl)

private theorem leaf3707FlatSound : Sound leaf3707Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3707CertificateValid
    leaf3707InnerLogValid leaf3707CoversExact leaf3707LowerChecked

private noncomputable def leaf3708Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3708Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217923/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743210496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (237397667/134217728) }, upper := { exponent := 0, mantissa := (465/256) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27486909235/27486420992) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf3708InnerLog : WideLogData :=
  innerPair208Data

set_option maxRecDepth 1000000 in
private theorem leaf3708LocalValidity :
    LeafFacts leaf3708Box leaf3708Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3708Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743210496) }) = true
      norm_num [leaf3708Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3708CertificateValid :
    WideCertificateValid leaf3708Box leaf3708Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi59ValidityFacts
    leaf3708LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3708CoverageChecked :
    coverageCheck (innerAD leaf3708Box) leaf3708InnerLog = true := by
  rfl'

private theorem leaf3708InnerLogValid :
    leaf3708InnerLog.Valid 8 (innerAD leaf3708Box) :=
  wideLogDataValid_of_cachedCheck endpoint63PositiveFacts
    endpoint64PositiveFacts.valid leaf3708CoverageChecked

private noncomputable def leaf3708InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3708InputLogOnePlusV_eq :
    leaf3708InputLogOnePlusV = outerEnclosure 24
      (leaf3708Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3708RoundedFacts : LeafRoundedFacts 8
    leaf3708Certificate.logOnePlusV leaf3708InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3708InputLogOnePlusV_eq }

private noncomputable def leaf3708Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi59InputQChi innerPair208Input
    leaf3708InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3708LowerChecked :
    lowerCheck 24 leaf3708Box leaf3708Inputs = true := by
  rfl'

private theorem leaf3708CoversExact : CoversExact 8
    leaf3708Box leaf3708Certificate leaf3708InnerLog leaf3708Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi59RoundedFacts
    innerPair208RoundedFacts leaf3708RoundedFacts (by rfl)

private theorem leaf3708FlatSound : Sound leaf3708Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3708CertificateValid
    leaf3708InnerLogValid leaf3708CoversExact leaf3708LowerChecked

private noncomputable def leaf3709Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3709Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217919/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905346048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (237987459/134217728) }, upper := { exponent := 0, mantissa := (3727/2048) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811510613/45810692096) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf3709InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3709LocalValidity :
    LeafFacts leaf3709Box leaf3709Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3709Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905346048) }) = true
      norm_num [leaf3709Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3709CertificateValid :
    WideCertificateValid leaf3709Box leaf3709Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi60ValidityFacts
    leaf3709LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3709CoverageChecked :
    coverageCheck (innerAD leaf3709Box) leaf3709InnerLog = true := by
  rfl'

private theorem leaf3709InnerLogValid :
    leaf3709InnerLog.Valid 8 (innerAD leaf3709Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3709CoverageChecked

private noncomputable def leaf3709InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3709InputLogOnePlusV_eq :
    leaf3709InputLogOnePlusV = outerEnclosure 24
      (leaf3709Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3709RoundedFacts : LeafRoundedFacts 8
    leaf3709Certificate.logOnePlusV leaf3709InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3709InputLogOnePlusV_eq }

private noncomputable def leaf3709Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi60InputQChi innerPair72Input
    leaf3709InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3709LowerChecked :
    lowerCheck 24 leaf3709Box leaf3709Inputs = true := by
  rfl'

private theorem leaf3709CoversExact : CoversExact 8
    leaf3709Box leaf3709Certificate leaf3709InnerLog leaf3709Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi60RoundedFacts
    innerPair72RoundedFacts leaf3709RoundedFacts (by rfl)

private theorem leaf3709FlatSound : Sound leaf3709Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3709CertificateValid
    leaf3709InnerLogValid leaf3709CoversExact leaf3709LowerChecked

private noncomputable def leaf3710Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3710Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217921/134217728) }, vSqrt := { lower := (65531/65536), upper := (808452867/808423424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (239429161/134217728) }, upper := { exponent := 0, mantissa := (1875/1024) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (1616876291/1616846848) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf3710InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3710LocalValidity :
    LeafFacts leaf3710Box leaf3710Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3710Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (808452867/808423424) }) = true
      norm_num [leaf3710Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3710CertificateValid :
    WideCertificateValid leaf3710Box leaf3710Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi60ValidityFacts
    leaf3710LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3710CoverageChecked :
    coverageCheck (innerAD leaf3710Box) leaf3710InnerLog = true := by
  rfl'

private theorem leaf3710InnerLogValid :
    leaf3710InnerLog.Valid 8 (innerAD leaf3710Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3710CoverageChecked

private noncomputable def leaf3710InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3710InputLogOnePlusV_eq :
    leaf3710InputLogOnePlusV = outerEnclosure 24
      (leaf3710Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3710RoundedFacts : LeafRoundedFacts 8
    leaf3710Certificate.logOnePlusV leaf3710InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3710InputLogOnePlusV_eq }

private noncomputable def leaf3710Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi60InputQChi innerPair72Input
    leaf3710InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3710LowerChecked :
    lowerCheck 24 leaf3710Box leaf3710Inputs = true := by
  rfl'

private theorem leaf3710CoversExact : CoversExact 8
    leaf3710Box leaf3710Certificate leaf3710InnerLog leaf3710Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi60RoundedFacts
    innerPair72RoundedFacts leaf3710RoundedFacts (by rfl)

private theorem leaf3710FlatSound : Sound leaf3710Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3710CertificateValid
    leaf3710InnerLogValid leaf3710CoversExact leaf3710LowerChecked

private noncomputable def leaf3711Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (73/32), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3711Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217921/134217728) }, vSqrt := { lower := (65531/65536), upper := (13743698739/13743177728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (242705761/134217728) }, upper := { exponent := 0, mantissa := (475/256) } }, logOuter := sk85LogOuterCertificate, logK := sk85LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (27486876467/27486355456) } }, logDArg := sk85LogDArgCertificate }

private noncomputable def leaf3711InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3711LocalValidity :
    LeafFacts leaf3711Box leaf3711Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3711Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (13743698739/13743177728) }) = true
      norm_num [leaf3711Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3711CertificateValid :
    WideCertificateValid leaf3711Box leaf3711Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk85ValidityFacts chi61ValidityFacts
    leaf3711LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3711CoverageChecked :
    coverageCheck (innerAD leaf3711Box) leaf3711InnerLog = true := by
  rfl'

private theorem leaf3711InnerLogValid :
    leaf3711InnerLog.Valid 8 (innerAD leaf3711Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3711CoverageChecked

private noncomputable def leaf3711InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3711InputLogOnePlusV_eq :
    leaf3711InputLogOnePlusV = outerEnclosure 24
      (leaf3711Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3711RoundedFacts : LeafRoundedFacts 8
    leaf3711Certificate.logOnePlusV leaf3711InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3711InputLogOnePlusV_eq }

private noncomputable def leaf3711Inputs : Inputs :=
  inputsOfCaches globalInput sk85RoundedInputs
    chi61InputQChi innerPair72Input
    leaf3711InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3711LowerChecked :
    lowerCheck 24 leaf3711Box leaf3711Inputs = true := by
  rfl'

private theorem leaf3711CoversExact : CoversExact 8
    leaf3711Box leaf3711Certificate leaf3711InnerLog leaf3711Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk85RoundedFacts chi61RoundedFacts
    innerPair72RoundedFacts leaf3711RoundedFacts (by rfl)

private theorem leaf3711FlatSound : Sound leaf3711Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3711CertificateValid
    leaf3711InnerLogValid leaf3711CoversExact leaf3711LowerChecked

private noncomputable def leaf3712Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (73/32), kHi := (37/16), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3712Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217923/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715839488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (244212995/134217728) }, upper := { exponent := 0, mantissa := (239/128) } }, logOuter := sk86LogOuterCertificate, logK := sk86LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434333183/137431678976) } }, logDArg := sk86LogDArgCertificate }

private noncomputable def leaf3712InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3712LocalValidity :
    LeafFacts leaf3712Box leaf3712Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3712Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715839488) }) = true
      norm_num [leaf3712Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3712CertificateValid :
    WideCertificateValid leaf3712Box leaf3712Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk86ValidityFacts chi61ValidityFacts
    leaf3712LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3712CoverageChecked :
    coverageCheck (innerAD leaf3712Box) leaf3712InnerLog = true := by
  rfl'

private theorem leaf3712InnerLogValid :
    leaf3712InnerLog.Valid 8 (innerAD leaf3712Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3712CoverageChecked

private noncomputable def leaf3712InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3712InputLogOnePlusV_eq :
    leaf3712InputLogOnePlusV = outerEnclosure 24
      (leaf3712Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3712RoundedFacts : LeafRoundedFacts 8
    leaf3712Certificate.logOnePlusV leaf3712InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3712InputLogOnePlusV_eq }

private noncomputable def leaf3712Inputs : Inputs :=
  inputsOfCaches globalInput sk86RoundedInputs
    chi61InputQChi innerPair91Input
    leaf3712InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3712LowerChecked :
    lowerCheck 24 leaf3712Box leaf3712Inputs = true := by
  rfl'

private theorem leaf3712CoversExact : CoversExact 8
    leaf3712Box leaf3712Certificate leaf3712InnerLog leaf3712Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk86RoundedFacts chi61RoundedFacts
    innerPair91RoundedFacts leaf3712RoundedFacts (by rfl)

private theorem leaf3712FlatSound : Sound leaf3712Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3712CertificateValid
    leaf3712InnerLogValid leaf3712CoversExact leaf3712LowerChecked

private noncomputable def leaf3713Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3713Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217923/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715943936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (240870863/134217728) }, upper := { exponent := 0, mantissa := (3773/2048) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434437631/137431887872) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf3713InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3713LocalValidity :
    LeafFacts leaf3713Box leaf3713Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3713Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715943936) }) = true
      norm_num [leaf3713Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3713CertificateValid :
    WideCertificateValid leaf3713Box leaf3713Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi60ValidityFacts
    leaf3713LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3713CoverageChecked :
    coverageCheck (innerAD leaf3713Box) leaf3713InnerLog = true := by
  rfl'

private theorem leaf3713InnerLogValid :
    leaf3713InnerLog.Valid 8 (innerAD leaf3713Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3713CoverageChecked

private noncomputable def leaf3713InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (726837/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3713InputLogOnePlusV_eq :
    leaf3713InputLogOnePlusV = outerEnclosure 24
      (leaf3713Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3713RoundedFacts : LeafRoundedFacts 8
    leaf3713Certificate.logOnePlusV leaf3713InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3713InputLogOnePlusV_eq }

private noncomputable def leaf3713Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi60InputQChi innerPair72Input
    leaf3713InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3713LowerChecked :
    lowerCheck 24 leaf3713Box leaf3713Inputs = true := by
  rfl'

private theorem leaf3713CoversExact : CoversExact 8
    leaf3713Box leaf3713Certificate leaf3713InnerLog leaf3713Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi60RoundedFacts
    innerPair72RoundedFacts leaf3713RoundedFacts (by rfl)

private theorem leaf3713FlatSound : Sound leaf3713Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3713CertificateValid
    leaf3713InnerLogValid leaf3713CoversExact leaf3713LowerChecked

private noncomputable def leaf3714Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3714Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217925/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905298944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (242312565/134217728) }, upper := { exponent := 0, mantissa := (949/512) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811463509/45810597888) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf3714InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3714LocalValidity :
    LeafFacts leaf3714Box leaf3714Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3714Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905298944) }) = true
      norm_num [leaf3714Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3714CertificateValid :
    WideCertificateValid leaf3714Box leaf3714Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi60ValidityFacts
    leaf3714LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3714CoverageChecked :
    coverageCheck (innerAD leaf3714Box) leaf3714InnerLog = true := by
  rfl'

private theorem leaf3714InnerLogValid :
    leaf3714InnerLog.Valid 8 (innerAD leaf3714Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3714CoverageChecked

private noncomputable def leaf3714InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814699/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3714InputLogOnePlusV_eq :
    leaf3714InputLogOnePlusV = outerEnclosure 24
      (leaf3714Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3714RoundedFacts : LeafRoundedFacts 8
    leaf3714Certificate.logOnePlusV leaf3714InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3714InputLogOnePlusV_eq }

private noncomputable def leaf3714Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi60InputQChi innerPair72Input
    leaf3714InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3714LowerChecked :
    lowerCheck 24 leaf3714Box leaf3714Inputs = true := by
  rfl'

private theorem leaf3714CoversExact : CoversExact 8
    leaf3714Box leaf3714Certificate leaf3714InnerLog leaf3714Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi60RoundedFacts
    innerPair72RoundedFacts leaf3714RoundedFacts (by rfl)

private theorem leaf3714FlatSound : Sound leaf3714Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3714CertificateValid
    leaf3714InnerLogValid leaf3714CoversExact leaf3714LowerChecked

private noncomputable def leaf3715Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (75/32), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3715Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217925/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715790336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (245720229/134217728) }, upper := { exponent := 0, mantissa := (481/256) } }, logOuter := sk79LogOuterCertificate, logK := sk79LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434284031/137431580672) } }, logDArg := sk79LogDArgCertificate }

private noncomputable def leaf3715InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3715LocalValidity :
    LeafFacts leaf3715Box leaf3715Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3715Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715790336) }) = true
      norm_num [leaf3715Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3715CertificateValid :
    WideCertificateValid leaf3715Box leaf3715Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk79ValidityFacts chi61ValidityFacts
    leaf3715LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3715CoverageChecked :
    coverageCheck (innerAD leaf3715Box) leaf3715InnerLog = true := by
  rfl'

private theorem leaf3715InnerLogValid :
    leaf3715InnerLog.Valid 8 (innerAD leaf3715Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3715CoverageChecked

private noncomputable def leaf3715InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3715InputLogOnePlusV_eq :
    leaf3715InputLogOnePlusV = outerEnclosure 24
      (leaf3715Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3715RoundedFacts : LeafRoundedFacts 8
    leaf3715Certificate.logOnePlusV leaf3715InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3715InputLogOnePlusV_eq }

private noncomputable def leaf3715Inputs : Inputs :=
  inputsOfCaches globalInput sk79RoundedInputs
    chi61InputQChi innerPair92Input
    leaf3715InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3715LowerChecked :
    lowerCheck 24 leaf3715Box leaf3715Inputs = true := by
  rfl'

private theorem leaf3715CoversExact : CoversExact 8
    leaf3715Box leaf3715Certificate leaf3715InnerLog leaf3715Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk79RoundedFacts chi61RoundedFacts
    innerPair92RoundedFacts leaf3715RoundedFacts (by rfl)

private theorem leaf3715FlatSound : Sound leaf3715Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3715CertificateValid
    leaf3715InnerLogValid leaf3715CoversExact leaf3715LowerChecked

private noncomputable def leaf3716Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (75/32), kHi := (19/8), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3716Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217927/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715741184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (247227463/134217728) }, upper := { exponent := 0, mantissa := (121/64) } }, logOuter := sk80LogOuterCertificate, logK := sk80LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434234879/137431482368) } }, logDArg := sk80LogDArgCertificate }

private noncomputable def leaf3716InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3716LocalValidity :
    LeafFacts leaf3716Box leaf3716Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3716Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715741184) }) = true
      norm_num [leaf3716Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3716CertificateValid :
    WideCertificateValid leaf3716Box leaf3716Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk80ValidityFacts chi61ValidityFacts
    leaf3716LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3716CoverageChecked :
    coverageCheck (innerAD leaf3716Box) leaf3716InnerLog = true := by
  rfl'

private theorem leaf3716InnerLogValid :
    leaf3716InnerLog.Valid 8 (innerAD leaf3716Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3716CoverageChecked

private noncomputable def leaf3716InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3716InputLogOnePlusV_eq :
    leaf3716InputLogOnePlusV = outerEnclosure 24
      (leaf3716Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3716RoundedFacts : LeafRoundedFacts 8
    leaf3716Certificate.logOnePlusV leaf3716InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3716InputLogOnePlusV_eq }

private noncomputable def leaf3716Inputs : Inputs :=
  inputsOfCaches globalInput sk80RoundedInputs
    chi61InputQChi innerPair92Input
    leaf3716InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3716LowerChecked :
    lowerCheck 24 leaf3716Box leaf3716Inputs = true := by
  rfl'

private theorem leaf3716CoversExact : CoversExact 8
    leaf3716Box leaf3716Certificate leaf3716InnerLog leaf3716Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk80RoundedFacts chi61RoundedFacts
    innerPair92RoundedFacts leaf3716RoundedFacts (by rfl)

private theorem leaf3716FlatSound : Sound leaf3716Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3716CertificateValid
    leaf3716InnerLogValid leaf3716CoversExact leaf3716LowerChecked

private noncomputable def leaf3717Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf3717Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217923/134217728) }, vSqrt := { lower := (65531/65536), upper := (808452867/808425472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (233793407/134217728) }, upper := { exponent := 0, mantissa := (3665/2048) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (1616878339/1616850944) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf3717InnerLog : WideLogData :=
  innerPair66Data

set_option maxRecDepth 1000000 in
private theorem leaf3717LocalValidity :
    LeafFacts leaf3717Box leaf3717Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3717Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (808452867/808425472) }) = true
      norm_num [leaf3717Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3717CertificateValid :
    WideCertificateValid leaf3717Box leaf3717Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi58ValidityFacts
    leaf3717LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3717CoverageChecked :
    coverageCheck (innerAD leaf3717Box) leaf3717InnerLog = true := by
  rfl'

private theorem leaf3717InnerLogValid :
    leaf3717InnerLog.Valid 8 (innerAD leaf3717Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint21PositiveFacts.valid leaf3717CoverageChecked

private noncomputable def leaf3717InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3717InputLogOnePlusV_eq :
    leaf3717InputLogOnePlusV = outerEnclosure 24
      (leaf3717Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3717RoundedFacts : LeafRoundedFacts 8
    leaf3717Certificate.logOnePlusV leaf3717InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3717InputLogOnePlusV_eq }

private noncomputable def leaf3717Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi58InputQChi innerPair66Input
    leaf3717InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3717LowerChecked :
    lowerCheck 24 leaf3717Box leaf3717Inputs = true := by
  rfl'

private theorem leaf3717CoversExact : CoversExact 8
    leaf3717Box leaf3717Certificate leaf3717InnerLog leaf3717Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi58RoundedFacts
    innerPair66RoundedFacts leaf3717RoundedFacts (by rfl)

private theorem leaf3717FlatSound : Sound leaf3717Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3717CertificateValid
    leaf3717InnerLogValid leaf3717CoversExact leaf3717LowerChecked

private noncomputable def leaf3718Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf3718Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217925/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716122112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (235104045/134217728) }, upper := { exponent := 0, mantissa := (1843/1024) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434615807/137432244224) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3718InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3718LocalValidity :
    LeafFacts leaf3718Box leaf3718Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3718Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716122112) }) = true
      norm_num [leaf3718Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3718CertificateValid :
    WideCertificateValid leaf3718Box leaf3718Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi58ValidityFacts
    leaf3718LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3718CoverageChecked :
    coverageCheck (innerAD leaf3718Box) leaf3718InnerLog = true := by
  rfl'

private theorem leaf3718InnerLogValid :
    leaf3718InnerLog.Valid 8 (innerAD leaf3718Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3718CoverageChecked

private noncomputable def leaf3718InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3718InputLogOnePlusV_eq :
    leaf3718InputLogOnePlusV = outerEnclosure 24
      (leaf3718Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3718RoundedFacts : LeafRoundedFacts 8
    leaf3718Certificate.logOnePlusV leaf3718InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3718InputLogOnePlusV_eq }

private noncomputable def leaf3718Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi58InputQChi innerPair71Input
    leaf3718InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3718LowerChecked :
    lowerCheck 24 leaf3718Box leaf3718Inputs = true := by
  rfl'

private theorem leaf3718CoversExact : CoversExact 8
    leaf3718Box leaf3718Certificate leaf3718InnerLog leaf3718Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi58RoundedFacts
    innerPair71RoundedFacts leaf3718RoundedFacts (by rfl)

private theorem leaf3718FlatSound : Sound leaf3718Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3718CertificateValid
    leaf3718InnerLogValid leaf3718CoversExact leaf3718LowerChecked

private noncomputable def leaf3719Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3719Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217925/134217728) }, vSqrt := { lower := (65531/65536), upper := (22906164565/22905335808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (238773837/134217728) }, upper := { exponent := 0, mantissa := (1871/1024) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (45811500373/45810671616) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf3719InnerLog : WideLogData :=
  innerPair208Data

set_option maxRecDepth 1000000 in
private theorem leaf3719LocalValidity :
    LeafFacts leaf3719Box leaf3719Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3719Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (22906164565/22905335808) }) = true
      norm_num [leaf3719Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3719CertificateValid :
    WideCertificateValid leaf3719Box leaf3719Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi59ValidityFacts
    leaf3719LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3719CoverageChecked :
    coverageCheck (innerAD leaf3719Box) leaf3719InnerLog = true := by
  rfl'

private theorem leaf3719InnerLogValid :
    leaf3719InnerLog.Valid 8 (innerAD leaf3719Box) :=
  wideLogDataValid_of_cachedCheck endpoint63PositiveFacts
    endpoint64PositiveFacts.valid leaf3719CoverageChecked

private noncomputable def leaf3719InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3719InputLogOnePlusV_eq :
    leaf3719InputLogOnePlusV = outerEnclosure 24
      (leaf3719Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3719RoundedFacts : LeafRoundedFacts 8
    leaf3719Certificate.logOnePlusV leaf3719InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3719InputLogOnePlusV_eq }

private noncomputable def leaf3719Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi59InputQChi innerPair208Input
    leaf3719InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3719LowerChecked :
    lowerCheck 24 leaf3719Box leaf3719Inputs = true := by
  rfl'

private theorem leaf3719CoversExact : CoversExact 8
    leaf3719Box leaf3719Certificate leaf3719InnerLog leaf3719Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi59RoundedFacts
    innerPair208RoundedFacts leaf3719RoundedFacts (by rfl)

private theorem leaf3719FlatSound : Sound leaf3719Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3719CertificateValid
    leaf3719InnerLogValid leaf3719CoversExact leaf3719LowerChecked

private noncomputable def leaf3720Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3720Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217927/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715962368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (240150007/134217728) }, upper := { exponent := 0, mantissa := (941/512) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434456063/137431924736) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3720InnerLog : WideLogData :=
  innerPair225Data

set_option maxRecDepth 1000000 in
private theorem leaf3720LocalValidity :
    LeafFacts leaf3720Box leaf3720Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3720Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715962368) }) = true
      norm_num [leaf3720Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3720CertificateValid :
    WideCertificateValid leaf3720Box leaf3720Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi59ValidityFacts
    leaf3720LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3720CoverageChecked :
    coverageCheck (innerAD leaf3720Box) leaf3720InnerLog = true := by
  rfl'

private theorem leaf3720InnerLogValid :
    leaf3720InnerLog.Valid 8 (innerAD leaf3720Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint61PositiveFacts.valid leaf3720CoverageChecked

private noncomputable def leaf3720InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (5814695/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3720InputLogOnePlusV_eq :
    leaf3720InputLogOnePlusV = outerEnclosure 24
      (leaf3720Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3720RoundedFacts : LeafRoundedFacts 8
    leaf3720Certificate.logOnePlusV leaf3720InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3720InputLogOnePlusV_eq }

private noncomputable def leaf3720Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi59InputQChi innerPair225Input
    leaf3720InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3720LowerChecked :
    lowerCheck 24 leaf3720Box leaf3720Inputs = true := by
  rfl'

private theorem leaf3720CoversExact : CoversExact 8
    leaf3720Box leaf3720Certificate leaf3720InnerLog leaf3720Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi59RoundedFacts
    innerPair225RoundedFacts leaf3720RoundedFacts (by rfl)

private theorem leaf3720FlatSound : Sound leaf3720Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3720CertificateValid
    leaf3720InnerLogValid leaf3720CoversExact leaf3720LowerChecked

private noncomputable def leaf3721Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf3721Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217927/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68716079104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (236414683/134217728) }, upper := { exponent := 0, mantissa := (3707/2048) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434572799/137432158208) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3721InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3721LocalValidity :
    LeafFacts leaf3721Box leaf3721Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3721Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68716079104) }) = true
      norm_num [leaf3721Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3721CertificateValid :
    WideCertificateValid leaf3721Box leaf3721Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi58ValidityFacts
    leaf3721LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3721CoverageChecked :
    coverageCheck (innerAD leaf3721Box) leaf3721InnerLog = true := by
  rfl'

private theorem leaf3721InnerLogValid :
    leaf3721InnerLog.Valid 8 (innerAD leaf3721Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3721CoverageChecked

private noncomputable def leaf3721InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (181709/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf3721InputLogOnePlusV_eq :
    leaf3721InputLogOnePlusV = outerEnclosure 24
      (leaf3721Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3721RoundedFacts : LeafRoundedFacts 8
    leaf3721Certificate.logOnePlusV leaf3721InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3721InputLogOnePlusV_eq }

private noncomputable def leaf3721Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi58InputQChi innerPair71Input
    leaf3721InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3721LowerChecked :
    lowerCheck 24 leaf3721Box leaf3721Inputs = true := by
  rfl'

private theorem leaf3721CoversExact : CoversExact 8
    leaf3721Box leaf3721Certificate leaf3721InnerLog leaf3721Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi58RoundedFacts
    innerPair71RoundedFacts leaf3721RoundedFacts (by rfl)

private theorem leaf3721FlatSound : Sound leaf3721Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3721CertificateValid
    leaf3721InnerLogValid leaf3721CoversExact leaf3721LowerChecked

private noncomputable def leaf3722Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (5/16), chiHi := (21/64) }

private noncomputable def leaf3722Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217929/134217728) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68716036096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (237725321/134217728) }, upper := { exponent := 0, mantissa := (233/128) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi58LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434529791/137432072192) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3722InnerLog : WideLogData :=
  innerPair493Data

set_option maxRecDepth 1000000 in
private theorem leaf3722LocalValidity :
    LeafFacts leaf3722Box leaf3722Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3722Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68716036096) }) = true
      norm_num [leaf3722Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3722CertificateValid :
    WideCertificateValid leaf3722Box leaf3722Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi58ValidityFacts
    leaf3722LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3722CoverageChecked :
    coverageCheck (innerAD leaf3722Box) leaf3722InnerLog = true := by
  rfl'

private theorem leaf3722InnerLogValid :
    leaf3722InnerLog.Valid 8 (innerAD leaf3722Box) :=
  wideLogDataValid_of_cachedCheck endpoint216PositiveFacts
    endpoint220PositiveFacts.valid leaf3722CoverageChecked

private noncomputable def leaf3722InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3722InputLogOnePlusV_eq :
    leaf3722InputLogOnePlusV = outerEnclosure 24
      (leaf3722Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3722RoundedFacts : LeafRoundedFacts 8
    leaf3722Certificate.logOnePlusV leaf3722InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3722InputLogOnePlusV_eq }

private noncomputable def leaf3722Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi58InputQChi innerPair493Input
    leaf3722InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3722LowerChecked :
    lowerCheck 24 leaf3722Box leaf3722Inputs = true := by
  rfl'

private theorem leaf3722CoversExact : CoversExact 8
    leaf3722Box leaf3722Certificate leaf3722InnerLog leaf3722Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi58RoundedFacts
    innerPair493RoundedFacts leaf3722RoundedFacts (by rfl)

private theorem leaf3722FlatSound : Sound leaf3722Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3722CertificateValid
    leaf3722InnerLogValid leaf3722CoversExact leaf3722LowerChecked

private noncomputable def leaf3723Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3723Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217929/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715917312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (241526177/134217728) }, upper := { exponent := 0, mantissa := (1893/1024) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434411007/137431834624) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3723InnerLog : WideLogData :=
  innerPair223Data

set_option maxRecDepth 1000000 in
private theorem leaf3723LocalValidity :
    LeafFacts leaf3723Box leaf3723Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3723Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715917312) }) = true
      norm_num [leaf3723Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3723CertificateValid :
    WideCertificateValid leaf3723Box leaf3723Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi59ValidityFacts
    leaf3723LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3723CoverageChecked :
    coverageCheck (innerAD leaf3723Box) leaf3723InnerLog = true := by
  rfl'

private theorem leaf3723InnerLogValid :
    leaf3723InnerLog.Valid 8 (innerAD leaf3723Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint211PositiveFacts.valid leaf3723CoverageChecked

private noncomputable def leaf3723InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629395/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3723InputLogOnePlusV_eq :
    leaf3723InputLogOnePlusV = outerEnclosure 24
      (leaf3723Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3723RoundedFacts : LeafRoundedFacts 8
    leaf3723Certificate.logOnePlusV leaf3723InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3723InputLogOnePlusV_eq }

private noncomputable def leaf3723Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi59InputQChi innerPair223Input
    leaf3723InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3723LowerChecked :
    lowerCheck 24 leaf3723Box leaf3723Inputs = true := by
  rfl'

private theorem leaf3723CoversExact : CoversExact 8
    leaf3723Box leaf3723Certificate leaf3723InnerLog leaf3723Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi59RoundedFacts
    innerPair223RoundedFacts leaf3723RoundedFacts (by rfl)

private theorem leaf3723FlatSound : Sound leaf3723Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3723CertificateValid
    leaf3723InnerLogValid leaf3723CoversExact leaf3723LowerChecked

private noncomputable def leaf3724Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (21/64), chiHi := (11/32) }

private noncomputable def leaf3724Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217931/134217728) }, vSqrt := { lower := (32765/32768), upper := (22906164565/22905290752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (242902347/134217728) }, upper := { exponent := 0, mantissa := (119/64) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi59LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (45811455317/45810581504) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3724InnerLog : WideLogData :=
  innerPair72Data

set_option maxRecDepth 1000000 in
private theorem leaf3724LocalValidity :
    LeafFacts leaf3724Box leaf3724Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3724Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (22906164565/22905290752) }) = true
      norm_num [leaf3724Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3724CertificateValid :
    WideCertificateValid leaf3724Box leaf3724Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi59ValidityFacts
    leaf3724LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3724CoverageChecked :
    coverageCheck (innerAD leaf3724Box) leaf3724InnerLog = true := by
  rfl'

private theorem leaf3724InnerLogValid :
    leaf3724InnerLog.Valid 8 (innerAD leaf3724Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint22PositiveFacts.valid leaf3724CoverageChecked

private noncomputable def leaf3724InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3724InputLogOnePlusV_eq :
    leaf3724InputLogOnePlusV = outerEnclosure 24
      (leaf3724Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3724RoundedFacts : LeafRoundedFacts 8
    leaf3724Certificate.logOnePlusV leaf3724InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3724InputLogOnePlusV_eq }

private noncomputable def leaf3724Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi59InputQChi innerPair72Input
    leaf3724InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3724LowerChecked :
    lowerCheck 24 leaf3724Box leaf3724Inputs = true := by
  rfl'

private theorem leaf3724CoversExact : CoversExact 8
    leaf3724Box leaf3724Certificate leaf3724InnerLog leaf3724Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi59RoundedFacts
    innerPair72RoundedFacts leaf3724RoundedFacts (by rfl)

private theorem leaf3724FlatSound : Sound leaf3724Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3724CertificateValid
    leaf3724InnerLogValid leaf3724CoversExact leaf3724LowerChecked

private noncomputable def leaf3725Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3725Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217927/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715849728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (243754267/134217728) }, upper := { exponent := 0, mantissa := (3819/2048) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434343423/137431699456) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf3725InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3725LocalValidity :
    LeafFacts leaf3725Box leaf3725Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3725Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715849728) }) = true
      norm_num [leaf3725Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3725CertificateValid :
    WideCertificateValid leaf3725Box leaf3725Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi60ValidityFacts
    leaf3725LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3725CoverageChecked :
    coverageCheck (innerAD leaf3725Box) leaf3725InnerLog = true := by
  rfl'

private theorem leaf3725InnerLogValid :
    leaf3725InnerLog.Valid 8 (innerAD leaf3725Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3725CoverageChecked

private noncomputable def leaf3725InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (2907351/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3725InputLogOnePlusV_eq :
    leaf3725InputLogOnePlusV = outerEnclosure 24
      (leaf3725Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3725RoundedFacts : LeafRoundedFacts 8
    leaf3725Certificate.logOnePlusV leaf3725InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3725InputLogOnePlusV_eq }

private noncomputable def leaf3725Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi60InputQChi innerPair91Input
    leaf3725InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3725LowerChecked :
    lowerCheck 24 leaf3725Box leaf3725Inputs = true := by
  rfl'

private theorem leaf3725CoversExact : CoversExact 8
    leaf3725Box leaf3725Certificate leaf3725InnerLog leaf3725Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi60RoundedFacts
    innerPair91RoundedFacts leaf3725RoundedFacts (by rfl)

private theorem leaf3725FlatSound : Sound leaf3725Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3725CertificateValid
    leaf3725InnerLogValid leaf3725CoversExact leaf3725LowerChecked

private noncomputable def leaf3726Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3726Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217929/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715802624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (245195969/134217728) }, upper := { exponent := 0, mantissa := (1921/1024) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434296319/137431605248) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3726InnerLog : WideLogData :=
  innerPair96Data

set_option maxRecDepth 1000000 in
private theorem leaf3726LocalValidity :
    LeafFacts leaf3726Box leaf3726Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3726Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715802624) }) = true
      norm_num [leaf3726Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3726CertificateValid :
    WideCertificateValid leaf3726Box leaf3726Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi60ValidityFacts
    leaf3726LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3726CoverageChecked :
    coverageCheck (innerAD leaf3726Box) leaf3726InnerLog = true := by
  rfl'

private theorem leaf3726InnerLogValid :
    leaf3726InnerLog.Valid 8 (innerAD leaf3726Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint69PositiveFacts.valid leaf3726CoverageChecked

private noncomputable def leaf3726InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3726InputLogOnePlusV_eq :
    leaf3726InputLogOnePlusV = outerEnclosure 24
      (leaf3726Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3726RoundedFacts : LeafRoundedFacts 8
    leaf3726Certificate.logOnePlusV leaf3726InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3726InputLogOnePlusV_eq }

private noncomputable def leaf3726Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi60InputQChi innerPair96Input
    leaf3726InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3726LowerChecked :
    lowerCheck 24 leaf3726Box leaf3726Inputs = true := by
  rfl'

private theorem leaf3726CoversExact : CoversExact 8
    leaf3726Box leaf3726Certificate leaf3726InnerLog leaf3726Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi60RoundedFacts
    innerPair96RoundedFacts leaf3726RoundedFacts (by rfl)

private theorem leaf3726FlatSound : Sound leaf3726Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3726CertificateValid
    leaf3726InnerLogValid leaf3726CoversExact leaf3726LowerChecked

private noncomputable def leaf3727Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (77/32), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3727Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217929/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715692032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (248734697/134217728) }, upper := { exponent := 0, mantissa := (487/256) } }, logOuter := sk81LogOuterCertificate, logK := sk81LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434185727/137431384064) } }, logDArg := sk81LogDArgCertificate }

private noncomputable def leaf3727InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3727LocalValidity :
    LeafFacts leaf3727Box leaf3727Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3727Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715692032) }) = true
      norm_num [leaf3727Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3727CertificateValid :
    WideCertificateValid leaf3727Box leaf3727Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk81ValidityFacts chi61ValidityFacts
    leaf3727LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3727CoverageChecked :
    coverageCheck (innerAD leaf3727Box) leaf3727InnerLog = true := by
  rfl'

private theorem leaf3727InnerLogValid :
    leaf3727InnerLog.Valid 8 (innerAD leaf3727Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3727CoverageChecked

private noncomputable def leaf3727InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629423/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3727InputLogOnePlusV_eq :
    leaf3727InputLogOnePlusV = outerEnclosure 24
      (leaf3727Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3727RoundedFacts : LeafRoundedFacts 8
    leaf3727Certificate.logOnePlusV leaf3727InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3727InputLogOnePlusV_eq }

private noncomputable def leaf3727Inputs : Inputs :=
  inputsOfCaches globalInput sk81RoundedInputs
    chi61InputQChi innerPair92Input
    leaf3727InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3727LowerChecked :
    lowerCheck 24 leaf3727Box leaf3727Inputs = true := by
  rfl'

private theorem leaf3727CoversExact : CoversExact 8
    leaf3727Box leaf3727Certificate leaf3727InnerLog leaf3727Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk81RoundedFacts chi61RoundedFacts
    innerPair92RoundedFacts leaf3727RoundedFacts (by rfl)

private theorem leaf3727FlatSound : Sound leaf3727Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3727CertificateValid
    leaf3727InnerLogValid leaf3727CoversExact leaf3727LowerChecked

private noncomputable def leaf3728Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (77/32), kHi := (39/16), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3728Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217931/134217728) }, vSqrt := { lower := (65531/65536), upper := (808452867/808419328) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (250241931/134217728) }, upper := { exponent := 0, mantissa := (245/128) } }, logOuter := sk82LogOuterCertificate, logK := sk82LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (1616872195/1616838656) } }, logDArg := sk82LogDArgCertificate }

private noncomputable def leaf3728InnerLog : WideLogData :=
  innerPair92Data

set_option maxRecDepth 1000000 in
private theorem leaf3728LocalValidity :
    LeafFacts leaf3728Box leaf3728Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3728Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (808452867/808419328) }) = true
      norm_num [leaf3728Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3728CertificateValid :
    WideCertificateValid leaf3728Box leaf3728Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk82ValidityFacts chi61ValidityFacts
    leaf3728LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3728CoverageChecked :
    coverageCheck (innerAD leaf3728Box) leaf3728InnerLog = true := by
  rfl'

private theorem leaf3728InnerLogValid :
    leaf3728InnerLog.Valid 8 (innerAD leaf3728Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint23PositiveFacts.valid leaf3728CoverageChecked

private noncomputable def leaf3728InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3728InputLogOnePlusV_eq :
    leaf3728InputLogOnePlusV = outerEnclosure 24
      (leaf3728Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3728RoundedFacts : LeafRoundedFacts 8
    leaf3728Certificate.logOnePlusV leaf3728InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3728InputLogOnePlusV_eq }

private noncomputable def leaf3728Inputs : Inputs :=
  inputsOfCaches globalInput sk82RoundedInputs
    chi61InputQChi innerPair92Input
    leaf3728InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3728LowerChecked :
    lowerCheck 24 leaf3728Box leaf3728Inputs = true := by
  rfl'

private theorem leaf3728CoversExact : CoversExact 8
    leaf3728Box leaf3728Certificate leaf3728InnerLog leaf3728Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk82RoundedFacts chi61RoundedFacts
    innerPair92RoundedFacts leaf3728RoundedFacts (by rfl)

private theorem leaf3728FlatSound : Sound leaf3728Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3728CertificateValid
    leaf3728InnerLogValid leaf3728CoversExact leaf3728LowerChecked

private noncomputable def leaf3729Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3729Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217931/134217728) }, vSqrt := { lower := (65531/65536), upper := (4581232913/4581050368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (246637671/134217728) }, upper := { exponent := 0, mantissa := (3865/2048) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (9162283281/9162100736) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3729InnerLog : WideLogData :=
  innerPair213Data

set_option maxRecDepth 1000000 in
private theorem leaf3729LocalValidity :
    LeafFacts leaf3729Box leaf3729Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3729Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (4581232913/4581050368) }) = true
      norm_num [leaf3729Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3729CertificateValid :
    WideCertificateValid leaf3729Box leaf3729Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi60ValidityFacts
    leaf3729LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3729CoverageChecked :
    coverageCheck (innerAD leaf3729Box) leaf3729InnerLog = true := by
  rfl'

private theorem leaf3729InnerLogValid :
    leaf3729InnerLog.Valid 8 (innerAD leaf3729Box) :=
  wideLogDataValid_of_cachedCheck endpoint64PositiveFacts
    endpoint69PositiveFacts.valid leaf3729CoverageChecked

private noncomputable def leaf3729InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629415/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3729InputLogOnePlusV_eq :
    leaf3729InputLogOnePlusV = outerEnclosure 24
      (leaf3729Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3729RoundedFacts : LeafRoundedFacts 8
    leaf3729Certificate.logOnePlusV leaf3729InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3729InputLogOnePlusV_eq }

private noncomputable def leaf3729Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi60InputQChi innerPair213Input
    leaf3729InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3729LowerChecked :
    lowerCheck 24 leaf3729Box leaf3729Inputs = true := by
  rfl'

private theorem leaf3729CoversExact : CoversExact 8
    leaf3729Box leaf3729Certificate leaf3729InnerLog leaf3729Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi60RoundedFacts
    innerPair213RoundedFacts leaf3729RoundedFacts (by rfl)

private theorem leaf3729FlatSound : Sound leaf3729Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3729CertificateValid
    leaf3729InnerLogValid leaf3729CoversExact leaf3729LowerChecked

private noncomputable def leaf3730Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (11/32), chiHi := (23/64) }

private noncomputable def leaf3730Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217933/134217728) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715708416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (248079373/134217728) }, upper := { exponent := 0, mantissa := (243/128) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi60LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434202111/137431416832) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3730InnerLog : WideLogData :=
  innerPair200Data

set_option maxRecDepth 1000000 in
private theorem leaf3730LocalValidity :
    LeafFacts leaf3730Box leaf3730Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3730Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715708416) }) = true
      norm_num [leaf3730Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3730CertificateValid :
    WideCertificateValid leaf3730Box leaf3730Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi60ValidityFacts
    leaf3730LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3730CoverageChecked :
    coverageCheck (innerAD leaf3730Box) leaf3730InnerLog = true := by
  rfl'

private theorem leaf3730InnerLogValid :
    leaf3730InnerLog.Valid 8 (innerAD leaf3730Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint70PositiveFacts.valid leaf3730CoverageChecked

private noncomputable def leaf3730InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3730InputLogOnePlusV_eq :
    leaf3730InputLogOnePlusV = outerEnclosure 24
      (leaf3730Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3730RoundedFacts : LeafRoundedFacts 8
    leaf3730Certificate.logOnePlusV leaf3730InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3730InputLogOnePlusV_eq }

private noncomputable def leaf3730Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi60InputQChi innerPair200Input
    leaf3730InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3730LowerChecked :
    lowerCheck 24 leaf3730Box leaf3730Inputs = true := by
  rfl'

private theorem leaf3730CoversExact : CoversExact 8
    leaf3730Box leaf3730Certificate leaf3730InnerLog leaf3730Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi60RoundedFacts
    innerPair200RoundedFacts leaf3730RoundedFacts (by rfl)

private theorem leaf3730FlatSound : Sound leaf3730Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3730CertificateValid
    leaf3730InnerLogValid leaf3730CoversExact leaf3730LowerChecked

private noncomputable def leaf3731Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (79/32), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3731Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217933/134217728) }, vSqrt := { lower := (65531/65536), upper := (68718493695/68715593728) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (251749165/134217728) }, upper := { exponent := 0, mantissa := (493/256) } }, logOuter := sk83LogOuterCertificate, logK := sk83LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131067/65536) }, upper := { exponent := 1, mantissa := (137434087423/137431187456) } }, logDArg := sk83LogDArgCertificate }

private noncomputable def leaf3731InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3731LocalValidity :
    LeafFacts leaf3731Box leaf3731Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3731Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65531/65536), upper := (68718493695/68715593728) }) = true
      norm_num [leaf3731Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3731CertificateValid :
    WideCertificateValid leaf3731Box leaf3731Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk83ValidityFacts chi61ValidityFacts
    leaf3731LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3731CoverageChecked :
    coverageCheck (innerAD leaf3731Box) leaf3731InnerLog = true := by
  rfl'

private theorem leaf3731InnerLogValid :
    leaf3731InnerLog.Valid 8 (innerAD leaf3731Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3731CoverageChecked

private noncomputable def leaf3731InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628439/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3731InputLogOnePlusV_eq :
    leaf3731InputLogOnePlusV = outerEnclosure 24
      (leaf3731Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3731RoundedFacts : LeafRoundedFacts 8
    leaf3731Certificate.logOnePlusV leaf3731InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3731InputLogOnePlusV_eq }

private noncomputable def leaf3731Inputs : Inputs :=
  inputsOfCaches globalInput sk83RoundedInputs
    chi61InputQChi innerPair100Input
    leaf3731InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3731LowerChecked :
    lowerCheck 24 leaf3731Box leaf3731Inputs = true := by
  rfl'

private theorem leaf3731CoversExact : CoversExact 8
    leaf3731Box leaf3731Certificate leaf3731InnerLog leaf3731Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk83RoundedFacts chi61RoundedFacts
    innerPair100RoundedFacts leaf3731RoundedFacts (by rfl)

private theorem leaf3731FlatSound : Sound leaf3731Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3731CertificateValid
    leaf3731InnerLogValid leaf3731CoversExact leaf3731LowerChecked

private noncomputable def leaf3732Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (79/32), kHi := (5/2), chiLo := (23/64), chiHi := (3/8) }

private noncomputable def leaf3732Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (134217935/134217728) }, vSqrt := { lower := (32765/32768), upper := (68718493695/68715544576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (253256399/134217728) }, upper := { exponent := 0, mantissa := (31/16) } }, logOuter := sk84LogOuterCertificate, logK := sk84LogKCertificate, logChi := chi61LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (65533/32768) }, upper := { exponent := 1, mantissa := (137434038271/137431089152) } }, logDArg := sk84LogDArgCertificate }

private noncomputable def leaf3732InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3732LocalValidity :
    LeafFacts leaf3732Box leaf3732Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3732Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (32765/32768), upper := (68718493695/68715544576) }) = true
      norm_num [leaf3732Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3732CertificateValid :
    WideCertificateValid leaf3732Box leaf3732Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk84ValidityFacts chi61ValidityFacts
    leaf3732LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3732CoverageChecked :
    coverageCheck (innerAD leaf3732Box) leaf3732InnerLog = true := by
  rfl'

private theorem leaf3732InnerLogValid :
    leaf3732InnerLog.Valid 8 (innerAD leaf3732Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3732CoverageChecked

private noncomputable def leaf3732InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628311/16777216), upper := (11629441/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3732InputLogOnePlusV_eq :
    leaf3732InputLogOnePlusV = outerEnclosure 24
      (leaf3732Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3732RoundedFacts : LeafRoundedFacts 8
    leaf3732Certificate.logOnePlusV leaf3732InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3732InputLogOnePlusV_eq }

private noncomputable def leaf3732Inputs : Inputs :=
  inputsOfCaches globalInput sk84RoundedInputs
    chi61InputQChi innerPair100Input
    leaf3732InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3732LowerChecked :
    lowerCheck 24 leaf3732Box leaf3732Inputs = true := by
  rfl'

private theorem leaf3732CoversExact : CoversExact 8
    leaf3732Box leaf3732Certificate leaf3732InnerLog leaf3732Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk84RoundedFacts chi61RoundedFacts
    innerPair100RoundedFacts leaf3732RoundedFacts (by rfl)

private theorem leaf3732FlatSound : Sound leaf3732Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3732CertificateValid
    leaf3732InnerLogValid leaf3732CoversExact leaf3732LowerChecked

private noncomputable def component76Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component76Node0_sound : Sound component76Node0Box :=
  sound_of_literal_split component76Node0Box leaf3701Box leaf3702Box
    .k (73/32) (by rfl) (by rfl)
    leaf3701FlatSound leaf3702FlatSound

private noncomputable def component76Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component76Node1_sound : Sound component76Node1Box :=
  sound_of_literal_split component76Node1Box leaf3703Box leaf3704Box
    .k (73/32) (by rfl) (by rfl)
    leaf3703FlatSound leaf3704FlatSound

private noncomputable def component76Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component76Node2_sound : Sound component76Node2Box :=
  sound_of_literal_split component76Node2Box component76Node0Box component76Node1Box
    .chi (21/64) (by rfl) (by rfl)
    component76Node0_sound component76Node1_sound

private noncomputable def component76Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component76Node3_sound : Sound component76Node3Box :=
  sound_of_literal_split component76Node3Box leaf3705Box leaf3706Box
    .k (75/32) (by rfl) (by rfl)
    leaf3705FlatSound leaf3706FlatSound

private noncomputable def component76Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component76Node4_sound : Sound component76Node4Box :=
  sound_of_literal_split component76Node4Box leaf3707Box leaf3708Box
    .k (75/32) (by rfl) (by rfl)
    leaf3707FlatSound leaf3708FlatSound

private noncomputable def component76Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component76Node5_sound : Sound component76Node5Box :=
  sound_of_literal_split component76Node5Box component76Node3Box component76Node4Box
    .chi (21/64) (by rfl) (by rfl)
    component76Node3_sound component76Node4_sound

private noncomputable def component76Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component76Node6_sound : Sound component76Node6Box :=
  sound_of_literal_split component76Node6Box component76Node2Box component76Node5Box
    .k (37/16) (by rfl) (by rfl)
    component76Node2_sound component76Node5_sound

private noncomputable def component76Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component76Node7_sound : Sound component76Node7Box :=
  sound_of_literal_split component76Node7Box leaf3709Box leaf3710Box
    .k (73/32) (by rfl) (by rfl)
    leaf3709FlatSound leaf3710FlatSound

private noncomputable def component76Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component76Node8_sound : Sound component76Node8Box :=
  sound_of_literal_split component76Node8Box leaf3711Box leaf3712Box
    .k (73/32) (by rfl) (by rfl)
    leaf3711FlatSound leaf3712FlatSound

private noncomputable def component76Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (37/16), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component76Node9_sound : Sound component76Node9Box :=
  sound_of_literal_split component76Node9Box component76Node7Box component76Node8Box
    .chi (23/64) (by rfl) (by rfl)
    component76Node7_sound component76Node8_sound

private noncomputable def component76Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component76Node10_sound : Sound component76Node10Box :=
  sound_of_literal_split component76Node10Box leaf3713Box leaf3714Box
    .k (75/32) (by rfl) (by rfl)
    leaf3713FlatSound leaf3714FlatSound

private noncomputable def component76Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component76Node11_sound : Sound component76Node11Box :=
  sound_of_literal_split component76Node11Box leaf3715Box leaf3716Box
    .k (75/32) (by rfl) (by rfl)
    leaf3715FlatSound leaf3716FlatSound

private noncomputable def component76Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (37/16), kHi := (19/8), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component76Node12_sound : Sound component76Node12Box :=
  sound_of_literal_split component76Node12Box component76Node10Box component76Node11Box
    .chi (23/64) (by rfl) (by rfl)
    component76Node10_sound component76Node11_sound

private noncomputable def component76Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component76Node13_sound : Sound component76Node13Box :=
  sound_of_literal_split component76Node13Box component76Node9Box component76Node12Box
    .k (37/16) (by rfl) (by rfl)
    component76Node9_sound component76Node12_sound

private noncomputable def component76Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (19/8), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component76Node14_sound : Sound component76Node14Box :=
  sound_of_literal_split component76Node14Box component76Node6Box component76Node13Box
    .chi (11/32) (by rfl) (by rfl)
    component76Node6_sound component76Node13_sound

private noncomputable def component76Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component76Node15_sound : Sound component76Node15Box :=
  sound_of_literal_split component76Node15Box leaf3717Box leaf3718Box
    .k (77/32) (by rfl) (by rfl)
    leaf3717FlatSound leaf3718FlatSound

private noncomputable def component76Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component76Node16_sound : Sound component76Node16Box :=
  sound_of_literal_split component76Node16Box leaf3719Box leaf3720Box
    .k (77/32) (by rfl) (by rfl)
    leaf3719FlatSound leaf3720FlatSound

private noncomputable def component76Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component76Node17_sound : Sound component76Node17Box :=
  sound_of_literal_split component76Node17Box component76Node15Box component76Node16Box
    .chi (21/64) (by rfl) (by rfl)
    component76Node15_sound component76Node16_sound

private noncomputable def component76Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (5/16), chiHi := (21/64) }

set_option maxRecDepth 1000000 in
private theorem component76Node18_sound : Sound component76Node18Box :=
  sound_of_literal_split component76Node18Box leaf3721Box leaf3722Box
    .k (79/32) (by rfl) (by rfl)
    leaf3721FlatSound leaf3722FlatSound

private noncomputable def component76Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (21/64), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component76Node19_sound : Sound component76Node19Box :=
  sound_of_literal_split component76Node19Box leaf3723Box leaf3724Box
    .k (79/32) (by rfl) (by rfl)
    leaf3723FlatSound leaf3724FlatSound

private noncomputable def component76Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component76Node20_sound : Sound component76Node20Box :=
  sound_of_literal_split component76Node20Box component76Node18Box component76Node19Box
    .chi (21/64) (by rfl) (by rfl)
    component76Node18_sound component76Node19_sound

private noncomputable def component76Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (5/16), chiHi := (11/32) }

set_option maxRecDepth 1000000 in
private theorem component76Node21_sound : Sound component76Node21Box :=
  sound_of_literal_split component76Node21Box component76Node17Box component76Node20Box
    .k (39/16) (by rfl) (by rfl)
    component76Node17_sound component76Node20_sound

private noncomputable def component76Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component76Node22_sound : Sound component76Node22Box :=
  sound_of_literal_split component76Node22Box leaf3725Box leaf3726Box
    .k (77/32) (by rfl) (by rfl)
    leaf3725FlatSound leaf3726FlatSound

private noncomputable def component76Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component76Node23_sound : Sound component76Node23Box :=
  sound_of_literal_split component76Node23Box leaf3727Box leaf3728Box
    .k (77/32) (by rfl) (by rfl)
    leaf3727FlatSound leaf3728FlatSound

private noncomputable def component76Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (39/16), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component76Node24_sound : Sound component76Node24Box :=
  sound_of_literal_split component76Node24Box component76Node22Box component76Node23Box
    .chi (23/64) (by rfl) (by rfl)
    component76Node22_sound component76Node23_sound

private noncomputable def component76Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (11/32), chiHi := (23/64) }

set_option maxRecDepth 1000000 in
private theorem component76Node25_sound : Sound component76Node25Box :=
  sound_of_literal_split component76Node25Box leaf3729Box leaf3730Box
    .k (79/32) (by rfl) (by rfl)
    leaf3729FlatSound leaf3730FlatSound

private noncomputable def component76Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (23/64), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component76Node26_sound : Sound component76Node26Box :=
  sound_of_literal_split component76Node26Box leaf3731Box leaf3732Box
    .k (79/32) (by rfl) (by rfl)
    leaf3731FlatSound leaf3732FlatSound

private noncomputable def component76Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (39/16), kHi := (5/2), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component76Node27_sound : Sound component76Node27Box :=
  sound_of_literal_split component76Node27Box component76Node25Box component76Node26Box
    .chi (23/64) (by rfl) (by rfl)
    component76Node25_sound component76Node26_sound

private noncomputable def component76Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (11/32), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component76Node28_sound : Sound component76Node28Box :=
  sound_of_literal_split component76Node28Box component76Node24Box component76Node27Box
    .k (39/16) (by rfl) (by rfl)
    component76Node24_sound component76Node27_sound

private noncomputable def component76Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (19/8), kHi := (5/2), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
private theorem component76Node29_sound : Sound component76Node29Box :=
  sound_of_literal_split component76Node29Box component76Node21Box component76Node28Box
    .chi (11/32) (by rfl) (by rfl)
    component76Node21_sound component76Node28_sound

noncomputable def component76Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (9/4), kHi := (5/2), chiLo := (5/16), chiHi := (3/8) }

set_option maxRecDepth 1000000 in
theorem component76_sound : Sound component76Box :=
  sound_of_literal_split component76Box component76Node14Box component76Node29Box
    .k (19/8) (by rfl) (by rfl)
    component76Node14_sound component76Node29_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
