import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch2
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

private noncomputable def leaf2850Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2850Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742395/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084366848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1658778183/1073741824) }, upper := { exponent := 0, mantissa := (25597/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168891663/16168733696) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf2850InnerLog : WideLogData :=
  innerPair40Data

set_option maxRecDepth 1000000 in
private theorem leaf2850LocalValidity :
    LeafFacts leaf2850Box leaf2850Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2850Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084366848) }) = true
      norm_num [leaf2850Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2850CertificateValid :
    WideCertificateValid leaf2850Box leaf2850Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi175ValidityFacts
    leaf2850LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2850CoverageChecked :
    coverageCheck (innerAD leaf2850Box) leaf2850InnerLog = true := by
  rfl'

private theorem leaf2850InnerLogValid :
    leaf2850InnerLog.Valid 8 (innerAD leaf2850Box) :=
  wideLogDataValid_of_cachedCheck endpoint11PositiveFacts
    endpoint13PositiveFacts.valid leaf2850CoverageChecked

private noncomputable def leaf2850InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629245/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2850InputLogOnePlusV_eq :
    leaf2850InputLogOnePlusV = outerEnclosure 24
      (leaf2850Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2850RoundedFacts : LeafRoundedFacts 8
    leaf2850Certificate.logOnePlusV leaf2850InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2850InputLogOnePlusV_eq }

private noncomputable def leaf2850Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi175InputQChi innerPair40Input
    leaf2850InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2850LowerChecked :
    lowerCheck 24 leaf2850Box leaf2850Inputs = true := by
  rfl'

private theorem leaf2850CoversExact : CoversExact 8
    leaf2850Box leaf2850Certificate leaf2850InnerLog leaf2850Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi175RoundedFacts
    innerPair40RoundedFacts leaf2850RoundedFacts (by rfl)

private theorem leaf2850FlatSound : Sound leaf2850Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2850CertificateValid
    leaf2850InnerLogValid leaf2850CoversExact leaf2850LowerChecked

private noncomputable def leaf2851Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2851Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270468608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1661137333/1073741824) }, upper := { exponent := 0, mantissa := (12817/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541237703/30540937216) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf2851InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2851LocalValidity :
    LeafFacts leaf2851Box leaf2851Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2851Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270468608) }) = true
      norm_num [leaf2851Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2851CertificateValid :
    WideCertificateValid leaf2851Box leaf2851Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi175ValidityFacts
    leaf2851LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2851CoverageChecked :
    coverageCheck (innerAD leaf2851Box) leaf2851InnerLog = true := by
  rfl'

private theorem leaf2851InnerLogValid :
    leaf2851InnerLog.Valid 8 (innerAD leaf2851Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2851CoverageChecked

private noncomputable def leaf2851InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814623/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2851InputLogOnePlusV_eq :
    leaf2851InputLogOnePlusV = outerEnclosure 24
      (leaf2851Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2851RoundedFacts : LeafRoundedFacts 8
    leaf2851Certificate.logOnePlusV leaf2851InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2851InputLogOnePlusV_eq }

private noncomputable def leaf2851Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi175InputQChi innerPair156Input
    leaf2851InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2851LowerChecked :
    lowerCheck 24 leaf2851Box leaf2851Inputs = true := by
  rfl'

private theorem leaf2851CoversExact : CoversExact 8
    leaf2851Box leaf2851Certificate leaf2851InnerLog leaf2851Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi175RoundedFacts
    innerPair156RoundedFacts leaf2851RoundedFacts (by rfl)

private theorem leaf2851FlatSound : Sound leaf2851Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2851CertificateValid
    leaf2851InnerLogValid leaf2851CoversExact leaf2851LowerChecked

private noncomputable def leaf2852Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2852Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742397/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434108928) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1675030117/1073741824) }, upper := { exponent := 0, mantissa := (12923/8192) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871030783/274868217856) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf2852InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2852LocalValidity :
    LeafFacts leaf2852Box leaf2852Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2852Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434108928) }) = true
      norm_num [leaf2852Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2852CertificateValid :
    WideCertificateValid leaf2852Box leaf2852Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi176ValidityFacts
    leaf2852LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2852CoverageChecked :
    coverageCheck (innerAD leaf2852Box) leaf2852InnerLog = true := by
  rfl'

private theorem leaf2852InnerLogValid :
    leaf2852InnerLog.Valid 8 (innerAD leaf2852Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2852CoverageChecked

private noncomputable def leaf2852InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907313/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2852InputLogOnePlusV_eq :
    leaf2852InputLogOnePlusV = outerEnclosure 24
      (leaf2852Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2852RoundedFacts : LeafRoundedFacts 8
    leaf2852Certificate.logOnePlusV leaf2852InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2852InputLogOnePlusV_eq }

private noncomputable def leaf2852Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi176InputQChi innerPair156Input
    leaf2852InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2852LowerChecked :
    lowerCheck 24 leaf2852Box leaf2852Inputs = true := by
  rfl'

private theorem leaf2852CoversExact : CoversExact 8
    leaf2852Box leaf2852Certificate leaf2852InnerLog leaf2852Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi176RoundedFacts
    innerPair156RoundedFacts leaf2852RoundedFacts (by rfl)

private theorem leaf2852FlatSound : Sound leaf2852Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2852CertificateValid
    leaf2852InnerLogValid leaf2852CoversExact leaf2852LowerChecked

private noncomputable def leaf2853Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2853Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434089472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1677454799/1073741824) }, upper := { exponent := 0, mantissa := (6471/4096) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871011327/274868178944) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf2853InnerLog : WideLogData :=
  innerPair154Data

set_option maxRecDepth 1000000 in
private theorem leaf2853LocalValidity :
    LeafFacts leaf2853Box leaf2853Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2853Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434089472) }) = true
      norm_num [leaf2853Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2853CertificateValid :
    WideCertificateValid leaf2853Box leaf2853Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi176ValidityFacts
    leaf2853LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2853CoverageChecked :
    coverageCheck (innerAD leaf2853Box) leaf2853InnerLog = true := by
  rfl'

private theorem leaf2853InnerLogValid :
    leaf2853InnerLog.Valid 8 (innerAD leaf2853Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint44PositiveFacts.valid leaf2853CoverageChecked

private noncomputable def leaf2853InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814627/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2853InputLogOnePlusV_eq :
    leaf2853InputLogOnePlusV = outerEnclosure 24
      (leaf2853Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2853RoundedFacts : LeafRoundedFacts 8
    leaf2853Certificate.logOnePlusV leaf2853InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2853InputLogOnePlusV_eq }

private noncomputable def leaf2853Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi176InputQChi innerPair154Input
    leaf2853InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2853LowerChecked :
    lowerCheck 24 leaf2853Box leaf2853Inputs = true := by
  rfl'

private theorem leaf2853CoversExact : CoversExact 8
    leaf2853Box leaf2853Certificate leaf2853InnerLog leaf2853Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi176RoundedFacts
    innerPair154RoundedFacts leaf2853RoundedFacts (by rfl)

private theorem leaf2853FlatSound : Sound leaf2853Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2853CertificateValid
    leaf2853InnerLogValid leaf2853CoversExact leaf2853LowerChecked

private noncomputable def leaf2854Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2854Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434198528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1663496483/1073741824) }, upper := { exponent := 0, mantissa := (25671/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871120383/274868397056) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf2854InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2854LocalValidity :
    LeafFacts leaf2854Box leaf2854Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2854Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434198528) }) = true
      norm_num [leaf2854Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2854CertificateValid :
    WideCertificateValid leaf2854Box leaf2854Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi175ValidityFacts
    leaf2854LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2854CoverageChecked :
    coverageCheck (innerAD leaf2854Box) leaf2854InnerLog = true := by
  rfl'

private theorem leaf2854InnerLogValid :
    leaf2854InnerLog.Valid 8 (innerAD leaf2854Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2854CoverageChecked

private noncomputable def leaf2854InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629247/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2854InputLogOnePlusV_eq :
    leaf2854InputLogOnePlusV = outerEnclosure 24
      (leaf2854Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2854RoundedFacts : LeafRoundedFacts 8
    leaf2854Certificate.logOnePlusV leaf2854InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2854InputLogOnePlusV_eq }

private noncomputable def leaf2854Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi175InputQChi innerPair156Input
    leaf2854InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2854LowerChecked :
    lowerCheck 24 leaf2854Box leaf2854Inputs = true := by
  rfl'

private theorem leaf2854CoversExact : CoversExact 8
    leaf2854Box leaf2854Certificate leaf2854InnerLog leaf2854Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi175RoundedFacts
    innerPair156RoundedFacts leaf2854RoundedFacts (by rfl)

private theorem leaf2854FlatSound : Sound leaf2854Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2854CertificateValid
    leaf2854InnerLogValid leaf2854CoversExact leaf2854LowerChecked

private noncomputable def leaf2855Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2855Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434179584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1665855633/1073741824) }, upper := { exponent := 0, mantissa := (6427/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871101439/274868359168) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf2855InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2855LocalValidity :
    LeafFacts leaf2855Box leaf2855Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2855Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434179584) }) = true
      norm_num [leaf2855Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2855CertificateValid :
    WideCertificateValid leaf2855Box leaf2855Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi175ValidityFacts
    leaf2855LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2855CoverageChecked :
    coverageCheck (innerAD leaf2855Box) leaf2855InnerLog = true := by
  rfl'

private theorem leaf2855InnerLogValid :
    leaf2855InnerLog.Valid 8 (innerAD leaf2855Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2855CoverageChecked

private noncomputable def leaf2855InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181707/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf2855InputLogOnePlusV_eq :
    leaf2855InputLogOnePlusV = outerEnclosure 24
      (leaf2855Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2855RoundedFacts : LeafRoundedFacts 8
    leaf2855Certificate.logOnePlusV leaf2855InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2855InputLogOnePlusV_eq }

private noncomputable def leaf2855Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi175InputQChi innerPair156Input
    leaf2855InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2855LowerChecked :
    lowerCheck 24 leaf2855Box leaf2855Inputs = true := by
  rfl'

private theorem leaf2855CoversExact : CoversExact 8
    leaf2855Box leaf2855Certificate leaf2855InnerLog leaf2855Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi175RoundedFacts
    innerPair156RoundedFacts leaf2855RoundedFacts (by rfl)

private theorem leaf2855FlatSound : Sound leaf2855Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2855CertificateValid
    leaf2855InnerLogValid leaf2855CoversExact leaf2855LowerChecked

private noncomputable def leaf2856Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2856Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270452224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1679879481/1073741824) }, upper := { exponent := 0, mantissa := (12961/8192) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541221319/30540904448) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf2856InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2856LocalValidity :
    LeafFacts leaf2856Box leaf2856Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2856Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270452224) }) = true
      norm_num [leaf2856Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2856CertificateValid :
    WideCertificateValid leaf2856Box leaf2856Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi176ValidityFacts
    leaf2856LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2856CoverageChecked :
    coverageCheck (innerAD leaf2856Box) leaf2856InnerLog = true := by
  rfl'

private theorem leaf2856InnerLogValid :
    leaf2856InnerLog.Valid 8 (innerAD leaf2856Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2856CoverageChecked

private noncomputable def leaf2856InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629255/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2856InputLogOnePlusV_eq :
    leaf2856InputLogOnePlusV = outerEnclosure 24
      (leaf2856Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2856RoundedFacts : LeafRoundedFacts 8
    leaf2856Certificate.logOnePlusV leaf2856InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2856InputLogOnePlusV_eq }

private noncomputable def leaf2856Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi176InputQChi innerPair54Input
    leaf2856InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2856LowerChecked :
    lowerCheck 24 leaf2856Box leaf2856Inputs = true := by
  rfl'

private theorem leaf2856CoversExact : CoversExact 8
    leaf2856Box leaf2856Certificate leaf2856InnerLog leaf2856Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi176RoundedFacts
    innerPair54RoundedFacts leaf2856RoundedFacts (by rfl)

private theorem leaf2856FlatSound : Sound leaf2856Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2856CertificateValid
    leaf2856InnerLogValid leaf2856CoversExact leaf2856LowerChecked

private noncomputable def leaf2857Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2857Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486810112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1682304163/1073741824) }, upper := { exponent := 0, mantissa := (3245/2048) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974194483/54973620224) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf2857InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2857LocalValidity :
    LeafFacts leaf2857Box leaf2857Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2857Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486810112) }) = true
      norm_num [leaf2857Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2857CertificateValid :
    WideCertificateValid leaf2857Box leaf2857Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi176ValidityFacts
    leaf2857LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2857CoverageChecked :
    coverageCheck (innerAD leaf2857Box) leaf2857InnerLog = true := by
  rfl'

private theorem leaf2857InnerLogValid :
    leaf2857InnerLog.Valid 8 (innerAD leaf2857Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2857CoverageChecked

private noncomputable def leaf2857InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453657/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2857InputLogOnePlusV_eq :
    leaf2857InputLogOnePlusV = outerEnclosure 24
      (leaf2857Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2857RoundedFacts : LeafRoundedFacts 8
    leaf2857Certificate.logOnePlusV leaf2857InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2857InputLogOnePlusV_eq }

private noncomputable def leaf2857Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi176InputQChi innerPair54Input
    leaf2857InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2857LowerChecked :
    lowerCheck 24 leaf2857Box leaf2857Inputs = true := by
  rfl'

private theorem leaf2857CoversExact : CoversExact 8
    leaf2857Box leaf2857Certificate leaf2857InnerLog leaf2857Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi176RoundedFacts
    innerPair54RoundedFacts leaf2857RoundedFacts (by rfl)

private theorem leaf2857FlatSound : Sound leaf2857Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2857CertificateValid
    leaf2857InnerLogValid leaf2857CoversExact leaf2857LowerChecked

private noncomputable def leaf2858Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2858Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742399/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486796288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1691282051/1073741824) }, upper := { exponent := 0, mantissa := (26095/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974180659/54973592576) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf2858InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2858LocalValidity :
    LeafFacts leaf2858Box leaf2858Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2858Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486796288) }) = true
      norm_num [leaf2858Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2858CertificateValid :
    WideCertificateValid leaf2858Box leaf2858Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi177ValidityFacts
    leaf2858LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2858CoverageChecked :
    coverageCheck (innerAD leaf2858Box) leaf2858InnerLog = true := by
  rfl'

private theorem leaf2858InnerLogValid :
    leaf2858InnerLog.Valid 8 (innerAD leaf2858Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2858CoverageChecked

private noncomputable def leaf2858InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907315/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2858InputLogOnePlusV_eq :
    leaf2858InputLogOnePlusV = outerEnclosure 24
      (leaf2858Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2858RoundedFacts : LeafRoundedFacts 8
    leaf2858Certificate.logOnePlusV leaf2858InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2858InputLogOnePlusV_eq }

private noncomputable def leaf2858Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi177InputQChi innerPair54Input
    leaf2858InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2858LowerChecked :
    lowerCheck 24 leaf2858Box leaf2858Inputs = true := by
  rfl'

private theorem leaf2858CoversExact : CoversExact 8
    leaf2858Box leaf2858Certificate leaf2858InnerLog leaf2858Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi177RoundedFacts
    innerPair54RoundedFacts leaf2858RoundedFacts (by rfl)

private theorem leaf2858FlatSound : Sound leaf2858Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2858CertificateValid
    leaf2858InnerLogValid leaf2858CoversExact leaf2858LowerChecked

private noncomputable def leaf2859Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2859Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (534774015/534762496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1693772265/1073741824) }, upper := { exponent := 0, mantissa := (13067/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1069536511/1069524992) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf2859InnerLog : WideLogData :=
  innerPair55Data

set_option maxRecDepth 1000000 in
private theorem leaf2859LocalValidity :
    LeafFacts leaf2859Box leaf2859Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2859Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (534774015/534762496) }) = true
      norm_num [leaf2859Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2859CertificateValid :
    WideCertificateValid leaf2859Box leaf2859Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi177ValidityFacts
    leaf2859LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2859CoverageChecked :
    coverageCheck (innerAD leaf2859Box) leaf2859InnerLog = true := by
  rfl'

private theorem leaf2859InnerLogValid :
    leaf2859InnerLog.Valid 8 (innerAD leaf2859Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint46PositiveFacts.valid leaf2859CoverageChecked

private noncomputable def leaf2859InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2859InputLogOnePlusV_eq :
    leaf2859InputLogOnePlusV = outerEnclosure 24
      (leaf2859Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2859RoundedFacts : LeafRoundedFacts 8
    leaf2859Certificate.logOnePlusV leaf2859InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2859InputLogOnePlusV_eq }

private noncomputable def leaf2859Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi177InputQChi innerPair55Input
    leaf2859InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2859LowerChecked :
    lowerCheck 24 leaf2859Box leaf2859Inputs = true := by
  rfl'

private theorem leaf2859CoversExact : CoversExact 8
    leaf2859Box leaf2859Certificate leaf2859InnerLog leaf2859Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi177RoundedFacts
    innerPair55RoundedFacts leaf2859RoundedFacts (by rfl)

private theorem leaf2859FlatSound : Sound leaf2859Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2859CertificateValid
    leaf2859InnerLogValid leaf2859CoversExact leaf2859LowerChecked

private noncomputable def leaf2860Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2860Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742401/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433853952) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1707533985/1073741824) }, upper := { exponent := 0, mantissa := (3293/2048) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870775807/274867707904) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf2860InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2860LocalValidity :
    LeafFacts leaf2860Box leaf2860Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2860Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433853952) }) = true
      norm_num [leaf2860Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2860CertificateValid :
    WideCertificateValid leaf2860Box leaf2860Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi178ValidityFacts
    leaf2860LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2860CoverageChecked :
    coverageCheck (innerAD leaf2860Box) leaf2860InnerLog = true := by
  rfl'

private theorem leaf2860InnerLogValid :
    leaf2860InnerLog.Valid 8 (innerAD leaf2860Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2860CoverageChecked

private noncomputable def leaf2860InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2860InputLogOnePlusV_eq :
    leaf2860InputLogOnePlusV = outerEnclosure 24
      (leaf2860Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2860RoundedFacts : LeafRoundedFacts 8
    leaf2860Certificate.logOnePlusV leaf2860InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2860InputLogOnePlusV_eq }

private noncomputable def leaf2860Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2860InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2860LowerChecked :
    lowerCheck 24 leaf2860Box leaf2860Inputs = true := by
  rfl'

private theorem leaf2860CoversExact : CoversExact 8
    leaf2860Box leaf2860Certificate leaf2860InnerLog leaf2860Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2860RoundedFacts (by rfl)

private theorem leaf2860FlatSound : Sound leaf2860Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2860CertificateValid
    leaf2860InnerLogValid leaf2860CoversExact leaf2860LowerChecked

private noncomputable def leaf2861Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2861Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811277824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1710089731/1073741824) }, upper := { exponent := 0, mantissa := (1649/1024) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623585109/91622555648) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf2861InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2861LocalValidity :
    LeafFacts leaf2861Box leaf2861Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2861Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811277824) }) = true
      norm_num [leaf2861Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2861CertificateValid :
    WideCertificateValid leaf2861Box leaf2861Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi178ValidityFacts
    leaf2861LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2861CoverageChecked :
    coverageCheck (innerAD leaf2861Box) leaf2861InnerLog = true := by
  rfl'

private theorem leaf2861InnerLogValid :
    leaf2861InnerLog.Valid 8 (innerAD leaf2861Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2861CoverageChecked

private noncomputable def leaf2861InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2861InputLogOnePlusV_eq :
    leaf2861InputLogOnePlusV = outerEnclosure 24
      (leaf2861Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2861RoundedFacts : LeafRoundedFacts 8
    leaf2861Certificate.logOnePlusV leaf2861InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2861InputLogOnePlusV_eq }

private noncomputable def leaf2861Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2861InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2861LowerChecked :
    lowerCheck 24 leaf2861Box leaf2861Inputs = true := by
  rfl'

private theorem leaf2861CoversExact : CoversExact 8
    leaf2861Box leaf2861Certificate leaf2861InnerLog leaf2861Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2861RoundedFacts (by rfl)

private theorem leaf2861FlatSound : Sound leaf2861Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2861CertificateValid
    leaf2861InnerLogValid leaf2861CoversExact leaf2861LowerChecked

private noncomputable def leaf2862Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2862Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433941504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1696262479/1073741824) }, upper := { exponent := 0, mantissa := (26173/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870863359/274867883008) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf2862InnerLog : WideLogData :=
  innerPair171Data

set_option maxRecDepth 1000000 in
private theorem leaf2862LocalValidity :
    LeafFacts leaf2862Box leaf2862Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2862Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433941504) }) = true
      norm_num [leaf2862Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2862CertificateValid :
    WideCertificateValid leaf2862Box leaf2862Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi177ValidityFacts
    leaf2862LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2862CoverageChecked :
    coverageCheck (innerAD leaf2862Box) leaf2862InnerLog = true := by
  rfl'

private theorem leaf2862InnerLogValid :
    leaf2862InnerLog.Valid 8 (innerAD leaf2862Box) :=
  wideLogDataValid_of_cachedCheck endpoint47PositiveFacts
    endpoint46PositiveFacts.valid leaf2862CoverageChecked

private noncomputable def leaf2862InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629263/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2862InputLogOnePlusV_eq :
    leaf2862InputLogOnePlusV = outerEnclosure 24
      (leaf2862Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2862RoundedFacts : LeafRoundedFacts 8
    leaf2862Certificate.logOnePlusV leaf2862InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2862InputLogOnePlusV_eq }

private noncomputable def leaf2862Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi177InputQChi innerPair171Input
    leaf2862InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2862LowerChecked :
    lowerCheck 24 leaf2862Box leaf2862Inputs = true := by
  rfl'

private theorem leaf2862CoversExact : CoversExact 8
    leaf2862Box leaf2862Certificate leaf2862InnerLog leaf2862Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi177RoundedFacts
    innerPair171RoundedFacts leaf2862RoundedFacts (by rfl)

private theorem leaf2862FlatSound : Sound leaf2862Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2862CertificateValid
    leaf2862InnerLogValid leaf2862CoversExact leaf2862LowerChecked

private noncomputable def leaf2863Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2863Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433921536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1698752693/1073741824) }, upper := { exponent := 0, mantissa := (6553/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870843391/274867843072) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf2863InnerLog : WideLogData :=
  innerPair171Data

set_option maxRecDepth 1000000 in
private theorem leaf2863LocalValidity :
    LeafFacts leaf2863Box leaf2863Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2863Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433921536) }) = true
      norm_num [leaf2863Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2863CertificateValid :
    WideCertificateValid leaf2863Box leaf2863Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi177ValidityFacts
    leaf2863LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2863CoverageChecked :
    coverageCheck (innerAD leaf2863Box) leaf2863InnerLog = true := by
  rfl'

private theorem leaf2863InnerLogValid :
    leaf2863InnerLog.Valid 8 (innerAD leaf2863Box) :=
  wideLogDataValid_of_cachedCheck endpoint47PositiveFacts
    endpoint46PositiveFacts.valid leaf2863CoverageChecked

private noncomputable def leaf2863InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726829/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf2863InputLogOnePlusV_eq :
    leaf2863InputLogOnePlusV = outerEnclosure 24
      (leaf2863Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2863RoundedFacts : LeafRoundedFacts 8
    leaf2863Certificate.logOnePlusV leaf2863InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2863InputLogOnePlusV_eq }

private noncomputable def leaf2863Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi177InputQChi innerPair171Input
    leaf2863InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2863LowerChecked :
    lowerCheck 24 leaf2863Box leaf2863Inputs = true := by
  rfl'

private theorem leaf2863CoversExact : CoversExact 8
    leaf2863Box leaf2863Certificate leaf2863InnerLog leaf2863Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi177RoundedFacts
    innerPair171RoundedFacts leaf2863RoundedFacts (by rfl)

private theorem leaf2863FlatSound : Sound leaf2863Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2863CertificateValid
    leaf2863InnerLogValid leaf2863CoversExact leaf2863LowerChecked

private noncomputable def leaf2864Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2864Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433812992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1712645477/1073741824) }, upper := { exponent := 0, mantissa := (3303/2048) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870734847/274867625984) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf2864InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2864LocalValidity :
    LeafFacts leaf2864Box leaf2864Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2864Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433812992) }) = true
      norm_num [leaf2864Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2864CertificateValid :
    WideCertificateValid leaf2864Box leaf2864Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi178ValidityFacts
    leaf2864LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2864CoverageChecked :
    coverageCheck (innerAD leaf2864Box) leaf2864InnerLog = true := by
  rfl'

private theorem leaf2864InnerLogValid :
    leaf2864InnerLog.Valid 8 (innerAD leaf2864Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2864CoverageChecked

private noncomputable def leaf2864InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814635/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2864InputLogOnePlusV_eq :
    leaf2864InputLogOnePlusV = outerEnclosure 24
      (leaf2864Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2864RoundedFacts : LeafRoundedFacts 8
    leaf2864Certificate.logOnePlusV leaf2864InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2864InputLogOnePlusV_eq }

private noncomputable def leaf2864Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2864InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2864LowerChecked :
    lowerCheck 24 leaf2864Box leaf2864Inputs = true := by
  rfl'

private theorem leaf2864CoversExact : CoversExact 8
    leaf2864Box leaf2864Certificate leaf2864InnerLog leaf2864Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2864RoundedFacts (by rfl)

private theorem leaf2864FlatSound : Sound leaf2864Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2864CertificateValid
    leaf2864InnerLogValid leaf2864CoversExact leaf2864LowerChecked

private noncomputable def leaf2865Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2865Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084340736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1715201223/1073741824) }, upper := { exponent := 0, mantissa := (827/512) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168865551/16168681472) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf2865InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2865LocalValidity :
    LeafFacts leaf2865Box leaf2865Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2865Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084340736) }) = true
      norm_num [leaf2865Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2865CertificateValid :
    WideCertificateValid leaf2865Box leaf2865Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi178ValidityFacts
    leaf2865LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2865CoverageChecked :
    coverageCheck (innerAD leaf2865Box) leaf2865InnerLog = true := by
  rfl'

private theorem leaf2865InnerLogValid :
    leaf2865InnerLog.Valid 8 (innerAD leaf2865Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2865CoverageChecked

private noncomputable def leaf2865InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453659/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf2865InputLogOnePlusV_eq :
    leaf2865InputLogOnePlusV = outerEnclosure 24
      (leaf2865Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2865RoundedFacts : LeafRoundedFacts 8
    leaf2865Certificate.logOnePlusV leaf2865InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2865InputLogOnePlusV_eq }

private noncomputable def leaf2865Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2865InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2865LowerChecked :
    lowerCheck 24 leaf2865Box leaf2865Inputs = true := by
  rfl'

private theorem leaf2865CoversExact : CoversExact 8
    leaf2865Box leaf2865Certificate leaf2865InnerLog leaf2865Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2865RoundedFacts (by rfl)

private theorem leaf2865FlatSound : Sound leaf2865Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2865CertificateValid
    leaf2865InnerLogValid leaf2865CoversExact leaf2865LowerChecked

private noncomputable def leaf2866Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2866Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162277376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1668214783/1073741824) }, upper := { exponent := 0, mantissa := (25745/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324738833/18324554752) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf2866InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2866LocalValidity :
    LeafFacts leaf2866Box leaf2866Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2866Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162277376) }) = true
      norm_num [leaf2866Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2866CertificateValid :
    WideCertificateValid leaf2866Box leaf2866Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi175ValidityFacts
    leaf2866LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2866CoverageChecked :
    coverageCheck (innerAD leaf2866Box) leaf2866InnerLog = true := by
  rfl'

private theorem leaf2866InnerLogValid :
    leaf2866InnerLog.Valid 8 (innerAD leaf2866Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2866CoverageChecked

private noncomputable def leaf2866InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629249/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2866InputLogOnePlusV_eq :
    leaf2866InputLogOnePlusV = outerEnclosure 24
      (leaf2866Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2866RoundedFacts : LeafRoundedFacts 8
    leaf2866Certificate.logOnePlusV leaf2866InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2866InputLogOnePlusV_eq }

private noncomputable def leaf2866Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi175InputQChi innerPair156Input
    leaf2866InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2866LowerChecked :
    lowerCheck 24 leaf2866Box leaf2866Inputs = true := by
  rfl'

private theorem leaf2866CoversExact : CoversExact 8
    leaf2866Box leaf2866Certificate leaf2866InnerLog leaf2866Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi175RoundedFacts
    innerPair156RoundedFacts leaf2866RoundedFacts (by rfl)

private theorem leaf2866FlatSound : Sound leaf2866Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2866CertificateValid
    leaf2866InnerLogValid leaf2866CoversExact leaf2866LowerChecked

private noncomputable def leaf2867Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2867Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434141696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1670573933/1073741824) }, upper := { exponent := 0, mantissa := (12891/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871063551/274868283392) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf2867InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2867LocalValidity :
    LeafFacts leaf2867Box leaf2867Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2867Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434141696) }) = true
      norm_num [leaf2867Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2867CertificateValid :
    WideCertificateValid leaf2867Box leaf2867Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi175ValidityFacts
    leaf2867LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2867CoverageChecked :
    coverageCheck (innerAD leaf2867Box) leaf2867InnerLog = true := by
  rfl'

private theorem leaf2867InnerLogValid :
    leaf2867InnerLog.Valid 8 (innerAD leaf2867Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2867CoverageChecked

private noncomputable def leaf2867InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814625/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2867InputLogOnePlusV_eq :
    leaf2867InputLogOnePlusV = outerEnclosure 24
      (leaf2867Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2867RoundedFacts : LeafRoundedFacts 8
    leaf2867Certificate.logOnePlusV leaf2867InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2867InputLogOnePlusV_eq }

private noncomputable def leaf2867Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi175InputQChi innerPair156Input
    leaf2867InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2867LowerChecked :
    lowerCheck 24 leaf2867Box leaf2867Inputs = true := by
  rfl'

private theorem leaf2867CoversExact : CoversExact 8
    leaf2867Box leaf2867Certificate leaf2867InnerLog leaf2867Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi175RoundedFacts
    innerPair156RoundedFacts leaf2867RoundedFacts (by rfl)

private theorem leaf2867FlatSound : Sound leaf2867Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2867CertificateValid
    leaf2867InnerLogValid leaf2867CoversExact leaf2867LowerChecked

private noncomputable def leaf2868Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2868Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434031104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1684728845/1073741824) }, upper := { exponent := 0, mantissa := (12999/8192) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870952959/274868062208) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf2868InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2868LocalValidity :
    LeafFacts leaf2868Box leaf2868Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2868Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434031104) }) = true
      norm_num [leaf2868Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2868CertificateValid :
    WideCertificateValid leaf2868Box leaf2868Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi176ValidityFacts
    leaf2868LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2868CoverageChecked :
    coverageCheck (innerAD leaf2868Box) leaf2868InnerLog = true := by
  rfl'

private theorem leaf2868InnerLogValid :
    leaf2868InnerLog.Valid 8 (innerAD leaf2868Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2868CoverageChecked

private noncomputable def leaf2868InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629257/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2868InputLogOnePlusV_eq :
    leaf2868InputLogOnePlusV = outerEnclosure 24
      (leaf2868Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2868RoundedFacts : LeafRoundedFacts 8
    leaf2868Certificate.logOnePlusV leaf2868InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2868InputLogOnePlusV_eq }

private noncomputable def leaf2868Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi176InputQChi innerPair54Input
    leaf2868InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2868LowerChecked :
    lowerCheck 24 leaf2868Box leaf2868Inputs = true := by
  rfl'

private theorem leaf2868CoversExact : CoversExact 8
    leaf2868Box leaf2868Certificate leaf2868InnerLog leaf2868Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi176RoundedFacts
    innerPair54RoundedFacts leaf2868RoundedFacts (by rfl)

private theorem leaf2868FlatSound : Sound leaf2868Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2868CertificateValid
    leaf2868InnerLogValid leaf2868CoversExact leaf2868LowerChecked

private noncomputable def leaf2869Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2869Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811337216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1687153527/1073741824) }, upper := { exponent := 0, mantissa := (6509/4096) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623644501/91622674432) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf2869InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2869LocalValidity :
    LeafFacts leaf2869Box leaf2869Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2869Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811337216) }) = true
      norm_num [leaf2869Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2869CertificateValid :
    WideCertificateValid leaf2869Box leaf2869Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi176ValidityFacts
    leaf2869LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2869CoverageChecked :
    coverageCheck (innerAD leaf2869Box) leaf2869InnerLog = true := by
  rfl'

private theorem leaf2869InnerLogValid :
    leaf2869InnerLog.Valid 8 (innerAD leaf2869Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2869CoverageChecked

private noncomputable def leaf2869InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814629/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2869InputLogOnePlusV_eq :
    leaf2869InputLogOnePlusV = outerEnclosure 24
      (leaf2869Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2869RoundedFacts : LeafRoundedFacts 8
    leaf2869Certificate.logOnePlusV leaf2869InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2869InputLogOnePlusV_eq }

private noncomputable def leaf2869Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi176InputQChi innerPair54Input
    leaf2869InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2869LowerChecked :
    lowerCheck 24 leaf2869Box leaf2869Inputs = true := by
  rfl'

private theorem leaf2869CoversExact : CoversExact 8
    leaf2869Box leaf2869Certificate leaf2869InnerLog leaf2869Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi176RoundedFacts
    innerPair54RoundedFacts leaf2869RoundedFacts (by rfl)

private theorem leaf2869FlatSound : Sound leaf2869Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2869CertificateValid
    leaf2869InnerLogValid leaf2869CoversExact leaf2869LowerChecked

private noncomputable def leaf2870Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2870Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137434122752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1672933083/1073741824) }, upper := { exponent := 0, mantissa := (25819/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274871044607/274868245504) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf2870InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2870LocalValidity :
    LeafFacts leaf2870Box leaf2870Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2870Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137434122752) }) = true
      norm_num [leaf2870Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2870CertificateValid :
    WideCertificateValid leaf2870Box leaf2870Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi175ValidityFacts
    leaf2870LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2870CoverageChecked :
    coverageCheck (innerAD leaf2870Box) leaf2870InnerLog = true := by
  rfl'

private theorem leaf2870InnerLogValid :
    leaf2870InnerLog.Valid 8 (innerAD leaf2870Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2870CoverageChecked

private noncomputable def leaf2870InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907313/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2870InputLogOnePlusV_eq :
    leaf2870InputLogOnePlusV = outerEnclosure 24
      (leaf2870Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2870RoundedFacts : LeafRoundedFacts 8
    leaf2870Certificate.logOnePlusV leaf2870InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2870InputLogOnePlusV_eq }

private noncomputable def leaf2870Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi175InputQChi innerPair156Input
    leaf2870InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2870LowerChecked :
    lowerCheck 24 leaf2870Box leaf2870Inputs = true := by
  rfl'

private theorem leaf2870CoversExact : CoversExact 8
    leaf2870Box leaf2870Certificate leaf2870InnerLog leaf2870Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi175RoundedFacts
    innerPair156RoundedFacts leaf2870RoundedFacts (by rfl)

private theorem leaf2870FlatSound : Sound leaf2870Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2870CertificateValid
    leaf2870InnerLogValid leaf2870CoversExact leaf2870LowerChecked

private noncomputable def leaf2871Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (9/64), chiHi := (37/256) }

private noncomputable def leaf2871Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (65527/65536), upper := (45812307285/45811367936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1675292233/1073741824) }, upper := { exponent := 0, mantissa := (101/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi175LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (91623675221/91622735872) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf2871InnerLog : WideLogData :=
  innerPair156Data

set_option maxRecDepth 1000000 in
private theorem leaf2871LocalValidity :
    LeafFacts leaf2871Box leaf2871Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2871Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (45812307285/45811367936) }) = true
      norm_num [leaf2871Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2871CertificateValid :
    WideCertificateValid leaf2871Box leaf2871Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi175ValidityFacts
    leaf2871LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2871CoverageChecked :
    coverageCheck (innerAD leaf2871Box) leaf2871InnerLog = true := by
  rfl'

private theorem leaf2871InnerLogValid :
    leaf2871InnerLog.Valid 8 (innerAD leaf2871Box) :=
  wideLogDataValid_of_cachedCheck endpoint43PositiveFacts
    endpoint47PositiveFacts.valid leaf2871CoverageChecked

private noncomputable def leaf2871InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629253/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2871InputLogOnePlusV_eq :
    leaf2871InputLogOnePlusV = outerEnclosure 24
      (leaf2871Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2871RoundedFacts : LeafRoundedFacts 8
    leaf2871Certificate.logOnePlusV leaf2871InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2871InputLogOnePlusV_eq }

private noncomputable def leaf2871Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi175InputQChi innerPair156Input
    leaf2871InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2871LowerChecked :
    lowerCheck 24 leaf2871Box leaf2871Inputs = true := by
  rfl'

private theorem leaf2871CoversExact : CoversExact 8
    leaf2871Box leaf2871Certificate leaf2871InnerLog leaf2871Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi175RoundedFacts
    innerPair156RoundedFacts leaf2871RoundedFacts (by rfl)

private theorem leaf2871FlatSound : Sound leaf2871Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2871CertificateValid
    leaf2871InnerLogValid leaf2871CoversExact leaf2871LowerChecked

private noncomputable def leaf2872Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2872Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433992192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1689578209/1073741824) }, upper := { exponent := 0, mantissa := (13037/8192) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870914047/274867984384) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf2872InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2872LocalValidity :
    LeafFacts leaf2872Box leaf2872Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2872Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433992192) }) = true
      norm_num [leaf2872Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2872CertificateValid :
    WideCertificateValid leaf2872Box leaf2872Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi176ValidityFacts
    leaf2872LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2872CoverageChecked :
    coverageCheck (innerAD leaf2872Box) leaf2872InnerLog = true := by
  rfl'

private theorem leaf2872InnerLogValid :
    leaf2872InnerLog.Valid 8 (innerAD leaf2872Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2872CoverageChecked

private noncomputable def leaf2872InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907315/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2872InputLogOnePlusV_eq :
    leaf2872InputLogOnePlusV = outerEnclosure 24
      (leaf2872Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2872RoundedFacts : LeafRoundedFacts 8
    leaf2872Certificate.logOnePlusV leaf2872InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2872InputLogOnePlusV_eq }

private noncomputable def leaf2872Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi176InputQChi innerPair54Input
    leaf2872InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2872LowerChecked :
    lowerCheck 24 leaf2872Box leaf2872Inputs = true := by
  rfl'

private theorem leaf2872CoversExact : CoversExact 8
    leaf2872Box leaf2872Certificate leaf2872InnerLog leaf2872Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi176RoundedFacts
    innerPair54RoundedFacts leaf2872RoundedFacts (by rfl)

private theorem leaf2872FlatSound : Sound leaf2872Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2872CertificateValid
    leaf2872InnerLogValid leaf2872CoversExact leaf2872LowerChecked

private noncomputable def leaf2873Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (37/256), chiHi := (19/128) }

private noncomputable def leaf2873Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137433972736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1692002891/1073741824) }, upper := { exponent := 0, mantissa := (51/32) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi176LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274870894591/274867945472) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf2873InnerLog : WideLogData :=
  innerPair54Data

set_option maxRecDepth 1000000 in
private theorem leaf2873LocalValidity :
    LeafFacts leaf2873Box leaf2873Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2873Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137433972736) }) = true
      norm_num [leaf2873Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2873CertificateValid :
    WideCertificateValid leaf2873Box leaf2873Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi176ValidityFacts
    leaf2873LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2873CoverageChecked :
    coverageCheck (innerAD leaf2873Box) leaf2873InnerLog = true := by
  rfl'

private theorem leaf2873InnerLogValid :
    leaf2873InnerLog.Valid 8 (innerAD leaf2873Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint44PositiveFacts.valid leaf2873CoverageChecked

private noncomputable def leaf2873InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629261/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2873InputLogOnePlusV_eq :
    leaf2873InputLogOnePlusV = outerEnclosure 24
      (leaf2873Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2873RoundedFacts : LeafRoundedFacts 8
    leaf2873Certificate.logOnePlusV leaf2873InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2873InputLogOnePlusV_eq }

private noncomputable def leaf2873Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi176InputQChi innerPair54Input
    leaf2873InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2873LowerChecked :
    lowerCheck 24 leaf2873Box leaf2873Inputs = true := by
  rfl'

private theorem leaf2873CoversExact : CoversExact 8
    leaf2873Box leaf2873Certificate leaf2873InnerLog leaf2873Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi176RoundedFacts
    innerPair54RoundedFacts leaf2873RoundedFacts (by rfl)

private theorem leaf2873FlatSound : Sound leaf2873Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2873CertificateValid
    leaf2873InnerLogValid leaf2873CoversExact leaf2873LowerChecked

private noncomputable def leaf2874Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2874Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433901568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1701242907/1073741824) }, upper := { exponent := 0, mantissa := (26251/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870823423/274867803136) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf2874InnerLog : WideLogData :=
  innerPair171Data

set_option maxRecDepth 1000000 in
private theorem leaf2874LocalValidity :
    LeafFacts leaf2874Box leaf2874Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2874Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433901568) }) = true
      norm_num [leaf2874Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2874CertificateValid :
    WideCertificateValid leaf2874Box leaf2874Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi177ValidityFacts
    leaf2874LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2874CoverageChecked :
    coverageCheck (innerAD leaf2874Box) leaf2874InnerLog = true := by
  rfl'

private theorem leaf2874InnerLogValid :
    leaf2874InnerLog.Valid 8 (innerAD leaf2874Box) :=
  wideLogDataValid_of_cachedCheck endpoint47PositiveFacts
    endpoint46PositiveFacts.valid leaf2874CoverageChecked

private noncomputable def leaf2874InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629265/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2874InputLogOnePlusV_eq :
    leaf2874InputLogOnePlusV = outerEnclosure 24
      (leaf2874Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2874RoundedFacts : LeafRoundedFacts 8
    leaf2874Certificate.logOnePlusV leaf2874InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2874InputLogOnePlusV_eq }

private noncomputable def leaf2874Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi177InputQChi innerPair171Input
    leaf2874InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2874LowerChecked :
    lowerCheck 24 leaf2874Box leaf2874Inputs = true := by
  rfl'

private theorem leaf2874CoversExact : CoversExact 8
    leaf2874Box leaf2874Certificate leaf2874InnerLog leaf2874Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi177RoundedFacts
    innerPair171RoundedFacts leaf2874RoundedFacts (by rfl)

private theorem leaf2874FlatSound : Sound leaf2874Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2874CertificateValid
    leaf2874InnerLogValid leaf2874CoversExact leaf2874LowerChecked

private noncomputable def leaf2875Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2875Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486776320) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1703733121/1073741824) }, upper := { exponent := 0, mantissa := (13145/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54974160691/54973552640) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf2875InnerLog : WideLogData :=
  innerPair171Data

set_option maxRecDepth 1000000 in
private theorem leaf2875LocalValidity :
    LeafFacts leaf2875Box leaf2875Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2875Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486776320) }) = true
      norm_num [leaf2875Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2875CertificateValid :
    WideCertificateValid leaf2875Box leaf2875Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi177ValidityFacts
    leaf2875LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2875CoverageChecked :
    coverageCheck (innerAD leaf2875Box) leaf2875InnerLog = true := by
  rfl'

private theorem leaf2875InnerLogValid :
    leaf2875InnerLog.Valid 8 (innerAD leaf2875Box) :=
  wideLogDataValid_of_cachedCheck endpoint47PositiveFacts
    endpoint46PositiveFacts.valid leaf2875CoverageChecked

private noncomputable def leaf2875InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814633/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2875InputLogOnePlusV_eq :
    leaf2875InputLogOnePlusV = outerEnclosure 24
      (leaf2875Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2875RoundedFacts : LeafRoundedFacts 8
    leaf2875Certificate.logOnePlusV leaf2875InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2875InputLogOnePlusV_eq }

private noncomputable def leaf2875Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi177InputQChi innerPair171Input
    leaf2875InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2875LowerChecked :
    lowerCheck 24 leaf2875Box leaf2875Inputs = true := by
  rfl'

private theorem leaf2875CoversExact : CoversExact 8
    leaf2875Box leaf2875Certificate leaf2875InnerLog leaf2875Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi177RoundedFacts
    innerPair171RoundedFacts leaf2875RoundedFacts (by rfl)

private theorem leaf2875FlatSound : Sound leaf2875Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2875CertificateValid
    leaf2875InnerLogValid leaf2875CoversExact leaf2875LowerChecked

private noncomputable def leaf2876Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2876Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45811257344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1717756969/1073741824) }, upper := { exponent := 0, mantissa := (3313/2048) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623564629/91622514688) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf2876InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2876LocalValidity :
    LeafFacts leaf2876Box leaf2876Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2876Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45811257344) }) = true
      norm_num [leaf2876Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2876CertificateValid :
    WideCertificateValid leaf2876Box leaf2876Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi178ValidityFacts
    leaf2876LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2876CoverageChecked :
    coverageCheck (innerAD leaf2876Box) leaf2876InnerLog = true := by
  rfl'

private theorem leaf2876InnerLogValid :
    leaf2876InnerLog.Valid 8 (innerAD leaf2876Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2876CoverageChecked

private noncomputable def leaf2876InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629273/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2876InputLogOnePlusV_eq :
    leaf2876InputLogOnePlusV = outerEnclosure 24
      (leaf2876Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2876RoundedFacts : LeafRoundedFacts 8
    leaf2876Certificate.logOnePlusV leaf2876InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2876InputLogOnePlusV_eq }

private noncomputable def leaf2876Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2876InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2876LowerChecked :
    lowerCheck 24 leaf2876Box leaf2876Inputs = true := by
  rfl'

private theorem leaf2876CoversExact : CoversExact 8
    leaf2876Box leaf2876Certificate leaf2876InnerLog leaf2876Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2876RoundedFacts (by rfl)

private theorem leaf2876FlatSound : Sound leaf2876Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2876CertificateValid
    leaf2876InnerLogValid leaf2876CoversExact leaf2876LowerChecked

private noncomputable def leaf2877Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2877Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433751552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1720312715/1073741824) }, upper := { exponent := 0, mantissa := (1659/1024) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870673407/274867503104) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf2877InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2877LocalValidity :
    LeafFacts leaf2877Box leaf2877Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2877Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433751552) }) = true
      norm_num [leaf2877Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2877CertificateValid :
    WideCertificateValid leaf2877Box leaf2877Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi178ValidityFacts
    leaf2877LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2877CoverageChecked :
    coverageCheck (innerAD leaf2877Box) leaf2877InnerLog = true := by
  rfl'

private theorem leaf2877InnerLogValid :
    leaf2877InnerLog.Valid 8 (innerAD leaf2877Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2877CoverageChecked

private noncomputable def leaf2877InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814637/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf2877InputLogOnePlusV_eq :
    leaf2877InputLogOnePlusV = outerEnclosure 24
      (leaf2877Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2877RoundedFacts : LeafRoundedFacts 8
    leaf2877Certificate.logOnePlusV leaf2877InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2877InputLogOnePlusV_eq }

private noncomputable def leaf2877Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2877InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2877LowerChecked :
    lowerCheck 24 leaf2877Box leaf2877Inputs = true := by
  rfl'

private theorem leaf2877CoversExact : CoversExact 8
    leaf2877Box leaf2877Certificate leaf2877InnerLog leaf2877Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2877RoundedFacts (by rfl)

private theorem leaf2877FlatSound : Sound leaf2877Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2877CertificateValid
    leaf2877InnerLogValid leaf2877CoversExact leaf2877LowerChecked

private noncomputable def leaf2878Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2878Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433861632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1706223335/1073741824) }, upper := { exponent := 0, mantissa := (26329/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870783487/274867723264) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf2878InnerLog : WideLogData :=
  innerPair171Data

set_option maxRecDepth 1000000 in
private theorem leaf2878LocalValidity :
    LeafFacts leaf2878Box leaf2878Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2878Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433861632) }) = true
      norm_num [leaf2878Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2878CertificateValid :
    WideCertificateValid leaf2878Box leaf2878Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi177ValidityFacts
    leaf2878LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2878CoverageChecked :
    coverageCheck (innerAD leaf2878Box) leaf2878InnerLog = true := by
  rfl'

private theorem leaf2878InnerLogValid :
    leaf2878InnerLog.Valid 8 (innerAD leaf2878Box) :=
  wideLogDataValid_of_cachedCheck endpoint47PositiveFacts
    endpoint46PositiveFacts.valid leaf2878CoverageChecked

private noncomputable def leaf2878InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907317/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf2878InputLogOnePlusV_eq :
    leaf2878InputLogOnePlusV = outerEnclosure 24
      (leaf2878Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2878RoundedFacts : LeafRoundedFacts 8
    leaf2878Certificate.logOnePlusV leaf2878InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2878InputLogOnePlusV_eq }

private noncomputable def leaf2878Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi177InputQChi innerPair171Input
    leaf2878InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2878LowerChecked :
    lowerCheck 24 leaf2878Box leaf2878Inputs = true := by
  rfl'

private theorem leaf2878CoversExact : CoversExact 8
    leaf2878Box leaf2878Certificate leaf2878InnerLog leaf2878Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi177RoundedFacts
    innerPair171RoundedFacts leaf2878RoundedFacts (by rfl)

private theorem leaf2878FlatSound : Sound leaf2878Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2878CertificateValid
    leaf2878InnerLogValid leaf2878CoversExact leaf2878LowerChecked

private noncomputable def leaf2879Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (19/128), chiHi := (39/256) }

private noncomputable def leaf2879Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137433841664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1708713549/1073741824) }, upper := { exponent := 0, mantissa := (103/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi177LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274870763519/274867683328) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf2879InnerLog : WideLogData :=
  innerPair171Data

set_option maxRecDepth 1000000 in
private theorem leaf2879LocalValidity :
    LeafFacts leaf2879Box leaf2879Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2879Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137433841664) }) = true
      norm_num [leaf2879Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2879CertificateValid :
    WideCertificateValid leaf2879Box leaf2879Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi177ValidityFacts
    leaf2879LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2879CoverageChecked :
    coverageCheck (innerAD leaf2879Box) leaf2879InnerLog = true := by
  rfl'

private theorem leaf2879InnerLogValid :
    leaf2879InnerLog.Valid 8 (innerAD leaf2879Box) :=
  wideLogDataValid_of_cachedCheck endpoint47PositiveFacts
    endpoint46PositiveFacts.valid leaf2879CoverageChecked

private noncomputable def leaf2879InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629269/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2879InputLogOnePlusV_eq :
    leaf2879InputLogOnePlusV = outerEnclosure 24
      (leaf2879Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2879RoundedFacts : LeafRoundedFacts 8
    leaf2879Certificate.logOnePlusV leaf2879InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2879InputLogOnePlusV_eq }

private noncomputable def leaf2879Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi177InputQChi innerPair171Input
    leaf2879InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2879LowerChecked :
    lowerCheck 24 leaf2879Box leaf2879Inputs = true := by
  rfl'

private theorem leaf2879CoversExact : CoversExact 8
    leaf2879Box leaf2879Certificate leaf2879InnerLog leaf2879Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi177RoundedFacts
    innerPair171RoundedFacts leaf2879RoundedFacts (by rfl)

private theorem leaf2879FlatSound : Sound leaf2879Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2879CertificateValid
    leaf2879InnerLogValid leaf2879CoversExact leaf2879LowerChecked

private noncomputable def leaf2880Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2880Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137433731072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1722868461/1073741824) }, upper := { exponent := 0, mantissa := (3323/2048) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274870652927/274867462144) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf2880InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2880LocalValidity :
    LeafFacts leaf2880Box leaf2880Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2880Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137433731072) }) = true
      norm_num [leaf2880Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2880CertificateValid :
    WideCertificateValid leaf2880Box leaf2880Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi178ValidityFacts
    leaf2880LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2880CoverageChecked :
    coverageCheck (innerAD leaf2880Box) leaf2880InnerLog = true := by
  rfl'

private theorem leaf2880InnerLogValid :
    leaf2880InnerLog.Valid 8 (innerAD leaf2880Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2880CoverageChecked

private noncomputable def leaf2880InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629275/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2880InputLogOnePlusV_eq :
    leaf2880InputLogOnePlusV = outerEnclosure 24
      (leaf2880Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2880RoundedFacts : LeafRoundedFacts 8
    leaf2880Certificate.logOnePlusV leaf2880InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2880InputLogOnePlusV_eq }

private noncomputable def leaf2880Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2880InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2880LowerChecked :
    lowerCheck 24 leaf2880Box leaf2880Inputs = true := by
  rfl'

private theorem leaf2880CoversExact : CoversExact 8
    leaf2880Box leaf2880Certificate leaf2880InnerLog leaf2880Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2880RoundedFacts (by rfl)

private theorem leaf2880FlatSound : Sound leaf2880Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2880CertificateValid
    leaf2880InnerLogValid leaf2880CoversExact leaf2880LowerChecked

private noncomputable def leaf2881Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (39/256), chiHi := (5/32) }

private noncomputable def leaf2881Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (65527/65536), upper := (15270769095/15270412288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1725424207/1073741824) }, upper := { exponent := 0, mantissa := (13/8) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi178LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (30541181383/30540824576) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf2881InnerLog : WideLogData :=
  innerPair50Data

set_option maxRecDepth 1000000 in
private theorem leaf2881LocalValidity :
    LeafFacts leaf2881Box leaf2881Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf2881Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (15270769095/15270412288) }) = true
      norm_num [leaf2881Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf2881CertificateValid :
    WideCertificateValid leaf2881Box leaf2881Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi178ValidityFacts
    leaf2881LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf2881CoverageChecked :
    coverageCheck (innerAD leaf2881Box) leaf2881InnerLog = true := by
  rfl'

private theorem leaf2881InnerLogValid :
    leaf2881InnerLog.Valid 8 (innerAD leaf2881Box) :=
  wideLogDataValid_of_cachedCheck endpoint13PositiveFacts
    endpoint14PositiveFacts.valid leaf2881CoverageChecked

private noncomputable def leaf2881InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629277/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf2881InputLogOnePlusV_eq :
    leaf2881InputLogOnePlusV = outerEnclosure 24
      (leaf2881Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf2881RoundedFacts : LeafRoundedFacts 8
    leaf2881Certificate.logOnePlusV leaf2881InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf2881InputLogOnePlusV_eq }

private noncomputable def leaf2881Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi178InputQChi innerPair50Input
    leaf2881InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf2881LowerChecked :
    lowerCheck 24 leaf2881Box leaf2881Inputs = true := by
  rfl'

private theorem leaf2881CoversExact : CoversExact 8
    leaf2881Box leaf2881Certificate leaf2881InnerLog leaf2881Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi178RoundedFacts
    innerPair50RoundedFacts leaf2881RoundedFacts (by rfl)

private theorem leaf2881FlatSound : Sound leaf2881Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf2881CertificateValid
    leaf2881InnerLogValid leaf2881CoversExact leaf2881LowerChecked

private noncomputable def component60Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (9/64), chiHi := (37/256) }

set_option maxRecDepth 1000000 in
private theorem component60Node0_sound : Sound component60Node0Box :=
  sound_of_literal_split component60Node0Box leaf2850Box leaf2851Box
    .k (249/64) (by rfl) (by rfl)
    leaf2850FlatSound leaf2851FlatSound

private noncomputable def component60Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (37/256), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component60Node1_sound : Sound component60Node1Box :=
  sound_of_literal_split component60Node1Box leaf2852Box leaf2853Box
    .k (249/64) (by rfl) (by rfl)
    leaf2852FlatSound leaf2853FlatSound

private noncomputable def component60Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component60Node2_sound : Sound component60Node2Box :=
  sound_of_literal_split component60Node2Box component60Node0Box component60Node1Box
    .chi (37/256) (by rfl) (by rfl)
    component60Node0_sound component60Node1_sound

private noncomputable def component60Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (9/64), chiHi := (37/256) }

set_option maxRecDepth 1000000 in
private theorem component60Node3_sound : Sound component60Node3Box :=
  sound_of_literal_split component60Node3Box leaf2854Box leaf2855Box
    .k (251/64) (by rfl) (by rfl)
    leaf2854FlatSound leaf2855FlatSound

private noncomputable def component60Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (37/256), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component60Node4_sound : Sound component60Node4Box :=
  sound_of_literal_split component60Node4Box leaf2856Box leaf2857Box
    .k (251/64) (by rfl) (by rfl)
    leaf2856FlatSound leaf2857FlatSound

private noncomputable def component60Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component60Node5_sound : Sound component60Node5Box :=
  sound_of_literal_split component60Node5Box component60Node3Box component60Node4Box
    .chi (37/256) (by rfl) (by rfl)
    component60Node3_sound component60Node4_sound

private noncomputable def component60Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component60Node6_sound : Sound component60Node6Box :=
  sound_of_literal_split component60Node6Box component60Node2Box component60Node5Box
    .k (125/32) (by rfl) (by rfl)
    component60Node2_sound component60Node5_sound

private noncomputable def component60Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (19/128), chiHi := (39/256) }

set_option maxRecDepth 1000000 in
private theorem component60Node7_sound : Sound component60Node7Box :=
  sound_of_literal_split component60Node7Box leaf2858Box leaf2859Box
    .k (249/64) (by rfl) (by rfl)
    leaf2858FlatSound leaf2859FlatSound

private noncomputable def component60Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (39/256), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component60Node8_sound : Sound component60Node8Box :=
  sound_of_literal_split component60Node8Box leaf2860Box leaf2861Box
    .k (249/64) (by rfl) (by rfl)
    leaf2860FlatSound leaf2861FlatSound

private noncomputable def component60Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component60Node9_sound : Sound component60Node9Box :=
  sound_of_literal_split component60Node9Box component60Node7Box component60Node8Box
    .chi (39/256) (by rfl) (by rfl)
    component60Node7_sound component60Node8_sound

private noncomputable def component60Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (19/128), chiHi := (39/256) }

set_option maxRecDepth 1000000 in
private theorem component60Node10_sound : Sound component60Node10Box :=
  sound_of_literal_split component60Node10Box leaf2862Box leaf2863Box
    .k (251/64) (by rfl) (by rfl)
    leaf2862FlatSound leaf2863FlatSound

private noncomputable def component60Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (39/256), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component60Node11_sound : Sound component60Node11Box :=
  sound_of_literal_split component60Node11Box leaf2864Box leaf2865Box
    .k (251/64) (by rfl) (by rfl)
    leaf2864FlatSound leaf2865FlatSound

private noncomputable def component60Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component60Node12_sound : Sound component60Node12Box :=
  sound_of_literal_split component60Node12Box component60Node10Box component60Node11Box
    .chi (39/256) (by rfl) (by rfl)
    component60Node10_sound component60Node11_sound

private noncomputable def component60Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component60Node13_sound : Sound component60Node13Box :=
  sound_of_literal_split component60Node13Box component60Node9Box component60Node12Box
    .k (125/32) (by rfl) (by rfl)
    component60Node9_sound component60Node12_sound

private noncomputable def component60Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component60Node14_sound : Sound component60Node14Box :=
  sound_of_literal_split component60Node14Box component60Node6Box component60Node13Box
    .chi (19/128) (by rfl) (by rfl)
    component60Node6_sound component60Node13_sound

private noncomputable def component60Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (9/64), chiHi := (37/256) }

set_option maxRecDepth 1000000 in
private theorem component60Node15_sound : Sound component60Node15Box :=
  sound_of_literal_split component60Node15Box leaf2866Box leaf2867Box
    .k (253/64) (by rfl) (by rfl)
    leaf2866FlatSound leaf2867FlatSound

private noncomputable def component60Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (37/256), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component60Node16_sound : Sound component60Node16Box :=
  sound_of_literal_split component60Node16Box leaf2868Box leaf2869Box
    .k (253/64) (by rfl) (by rfl)
    leaf2868FlatSound leaf2869FlatSound

private noncomputable def component60Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component60Node17_sound : Sound component60Node17Box :=
  sound_of_literal_split component60Node17Box component60Node15Box component60Node16Box
    .chi (37/256) (by rfl) (by rfl)
    component60Node15_sound component60Node16_sound

private noncomputable def component60Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (9/64), chiHi := (37/256) }

set_option maxRecDepth 1000000 in
private theorem component60Node18_sound : Sound component60Node18Box :=
  sound_of_literal_split component60Node18Box leaf2870Box leaf2871Box
    .k (255/64) (by rfl) (by rfl)
    leaf2870FlatSound leaf2871FlatSound

private noncomputable def component60Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (37/256), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component60Node19_sound : Sound component60Node19Box :=
  sound_of_literal_split component60Node19Box leaf2872Box leaf2873Box
    .k (255/64) (by rfl) (by rfl)
    leaf2872FlatSound leaf2873FlatSound

private noncomputable def component60Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component60Node20_sound : Sound component60Node20Box :=
  sound_of_literal_split component60Node20Box component60Node18Box component60Node19Box
    .chi (37/256) (by rfl) (by rfl)
    component60Node18_sound component60Node19_sound

private noncomputable def component60Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (9/64), chiHi := (19/128) }

set_option maxRecDepth 1000000 in
private theorem component60Node21_sound : Sound component60Node21Box :=
  sound_of_literal_split component60Node21Box component60Node17Box component60Node20Box
    .k (127/32) (by rfl) (by rfl)
    component60Node17_sound component60Node20_sound

private noncomputable def component60Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (19/128), chiHi := (39/256) }

set_option maxRecDepth 1000000 in
private theorem component60Node22_sound : Sound component60Node22Box :=
  sound_of_literal_split component60Node22Box leaf2874Box leaf2875Box
    .k (253/64) (by rfl) (by rfl)
    leaf2874FlatSound leaf2875FlatSound

private noncomputable def component60Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (39/256), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component60Node23_sound : Sound component60Node23Box :=
  sound_of_literal_split component60Node23Box leaf2876Box leaf2877Box
    .k (253/64) (by rfl) (by rfl)
    leaf2876FlatSound leaf2877FlatSound

private noncomputable def component60Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component60Node24_sound : Sound component60Node24Box :=
  sound_of_literal_split component60Node24Box component60Node22Box component60Node23Box
    .chi (39/256) (by rfl) (by rfl)
    component60Node22_sound component60Node23_sound

private noncomputable def component60Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (19/128), chiHi := (39/256) }

set_option maxRecDepth 1000000 in
private theorem component60Node25_sound : Sound component60Node25Box :=
  sound_of_literal_split component60Node25Box leaf2878Box leaf2879Box
    .k (255/64) (by rfl) (by rfl)
    leaf2878FlatSound leaf2879FlatSound

private noncomputable def component60Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (39/256), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component60Node26_sound : Sound component60Node26Box :=
  sound_of_literal_split component60Node26Box leaf2880Box leaf2881Box
    .k (255/64) (by rfl) (by rfl)
    leaf2880FlatSound leaf2881FlatSound

private noncomputable def component60Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component60Node27_sound : Sound component60Node27Box :=
  sound_of_literal_split component60Node27Box component60Node25Box component60Node26Box
    .chi (39/256) (by rfl) (by rfl)
    component60Node25_sound component60Node26_sound

private noncomputable def component60Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (19/128), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component60Node28_sound : Sound component60Node28Box :=
  sound_of_literal_split component60Node28Box component60Node24Box component60Node27Box
    .k (127/32) (by rfl) (by rfl)
    component60Node24_sound component60Node27_sound

private noncomputable def component60Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
private theorem component60Node29_sound : Sound component60Node29Box :=
  sound_of_literal_split component60Node29Box component60Node21Box component60Node28Box
    .chi (19/128) (by rfl) (by rfl)
    component60Node21_sound component60Node28_sound

noncomputable def component60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (9/64), chiHi := (5/32) }

set_option maxRecDepth 1000000 in
theorem component60_sound : Sound component60Box :=
  sound_of_literal_split component60Box component60Node14Box component60Node29Box
    .k (63/16) (by rfl) (by rfl)
    component60Node14_sound component60Node29_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
