import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch8
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

private noncomputable def leaf3516Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3516Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742435/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431686656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1983816863/1073741824) }, upper := { exponent := 0, mantissa := (30577/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868608511/274863373312) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf3516InnerLog : WideLogData :=
  innerPair203Data

set_option maxRecDepth 1000000 in
private theorem leaf3516LocalValidity :
    LeafFacts leaf3516Box leaf3516Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3516Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431686656) }) = true
      norm_num [leaf3516Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3516CertificateValid :
    WideCertificateValid leaf3516Box leaf3516Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi201ValidityFacts
    leaf3516LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3516CoverageChecked :
    coverageCheck (innerAD leaf3516Box) leaf3516InnerLog = true := by
  rfl'

private theorem leaf3516InnerLogValid :
    leaf3516InnerLog.Valid 8 (innerAD leaf3516Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint251PositiveFacts.valid leaf3516CoverageChecked

private noncomputable def leaf3516InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453675/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3516InputLogOnePlusV_eq :
    leaf3516InputLogOnePlusV = outerEnclosure 24
      (leaf3516Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3516RoundedFacts : LeafRoundedFacts 8
    leaf3516Certificate.logOnePlusV leaf3516InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3516InputLogOnePlusV_eq }

private noncomputable def leaf3516Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi201InputQChi innerPair203Input
    leaf3516InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3516LowerChecked :
    lowerCheck 24 leaf3516Box leaf3516Inputs = true := by
  rfl'

private theorem leaf3516CoversExact : CoversExact 8
    leaf3516Box leaf3516Certificate leaf3516InnerLog leaf3516Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi201RoundedFacts
    innerPair203RoundedFacts leaf3516RoundedFacts (by rfl)

private theorem leaf3516FlatSound : Sound leaf3516Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3516CertificateValid
    leaf3516InnerLogValid leaf3516CoversExact leaf3516LowerChecked

private noncomputable def leaf3517Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3517Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431657472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1987486653/1073741824) }, upper := { exponent := 0, mantissa := (15317/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868579327/274863314944) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf3517InnerLog : WideLogData :=
  innerPair500Data

set_option maxRecDepth 1000000 in
private theorem leaf3517LocalValidity :
    LeafFacts leaf3517Box leaf3517Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3517Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431657472) }) = true
      norm_num [leaf3517Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3517CertificateValid :
    WideCertificateValid leaf3517Box leaf3517Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi201ValidityFacts
    leaf3517LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3517CoverageChecked :
    coverageCheck (innerAD leaf3517Box) leaf3517InnerLog = true := by
  rfl'

private theorem leaf3517InnerLogValid :
    leaf3517InnerLog.Valid 8 (innerAD leaf3517Box) :=
  wideLogDataValid_of_cachedCheck endpoint223PositiveFacts
    endpoint243PositiveFacts.valid leaf3517CoverageChecked

private noncomputable def leaf3517InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814701/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3517InputLogOnePlusV_eq :
    leaf3517InputLogOnePlusV = outerEnclosure 24
      (leaf3517Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3517RoundedFacts : LeafRoundedFacts 8
    leaf3517Certificate.logOnePlusV leaf3517InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3517InputLogOnePlusV_eq }

private noncomputable def leaf3517Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi201InputQChi innerPair500Input
    leaf3517InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3517LowerChecked :
    lowerCheck 24 leaf3517Box leaf3517Inputs = true := by
  rfl'

private theorem leaf3517CoversExact : CoversExact 8
    leaf3517Box leaf3517Certificate leaf3517InnerLog leaf3517Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi201RoundedFacts
    innerPair500RoundedFacts leaf3517RoundedFacts (by rfl)

private theorem leaf3517FlatSound : Sound leaf3517Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3517CertificateValid
    leaf3517InnerLogValid leaf3517CoversExact leaf3517LowerChecked

private noncomputable def leaf3518Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3518Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742437/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431559168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2000068797/1073741824) }, upper := { exponent := 0, mantissa := (15413/8192) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868481023/274863118336) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf3518InnerLog : WideLogData :=
  innerPair486Data

set_option maxRecDepth 1000000 in
private theorem leaf3518LocalValidity :
    LeafFacts leaf3518Box leaf3518Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3518Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431559168) }) = true
      norm_num [leaf3518Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3518CertificateValid :
    WideCertificateValid leaf3518Box leaf3518Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi202ValidityFacts
    leaf3518LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3518CoverageChecked :
    coverageCheck (innerAD leaf3518Box) leaf3518InnerLog = true := by
  rfl'

private theorem leaf3518InnerLogValid :
    leaf3518InnerLog.Valid 8 (innerAD leaf3518Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint252PositiveFacts.valid leaf3518CoverageChecked

private noncomputable def leaf3518InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363419/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf3518InputLogOnePlusV_eq :
    leaf3518InputLogOnePlusV = outerEnclosure 24
      (leaf3518Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3518RoundedFacts : LeafRoundedFacts 8
    leaf3518Certificate.logOnePlusV leaf3518InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3518InputLogOnePlusV_eq }

private noncomputable def leaf3518Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi202InputQChi innerPair486Input
    leaf3518InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3518LowerChecked :
    lowerCheck 24 leaf3518Box leaf3518Inputs = true := by
  rfl'

private theorem leaf3518CoversExact : CoversExact 8
    leaf3518Box leaf3518Certificate leaf3518InnerLog leaf3518Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi202RoundedFacts
    innerPair486RoundedFacts leaf3518RoundedFacts (by rfl)

private theorem leaf3518FlatSound : Sound leaf3518Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3518CertificateValid
    leaf3518InnerLogValid leaf3518CoversExact leaf3518LowerChecked

private noncomputable def leaf3519Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3519Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (2694841605/2694735872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2003804119/1073741824) }, upper := { exponent := 0, mantissa := (7721/4096) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5389577477/5389471744) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf3519InnerLog : WideLogData :=
  innerPair512Data

set_option maxRecDepth 1000000 in
private theorem leaf3519LocalValidity :
    LeafFacts leaf3519Box leaf3519Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3519Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2694841605/2694735872) }) = true
      norm_num [leaf3519Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3519CertificateValid :
    WideCertificateValid leaf3519Box leaf3519Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi202ValidityFacts
    leaf3519LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3519CoverageChecked :
    coverageCheck (innerAD leaf3519Box) leaf3519InnerLog = true := by
  rfl'

private theorem leaf3519InnerLogValid :
    leaf3519InnerLog.Valid 8 (innerAD leaf3519Box) :=
  wideLogDataValid_of_cachedCheck endpoint241PositiveFacts
    endpoint245PositiveFacts.valid leaf3519CoverageChecked

private noncomputable def leaf3519InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814705/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3519InputLogOnePlusV_eq :
    leaf3519InputLogOnePlusV = outerEnclosure 24
      (leaf3519Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3519RoundedFacts : LeafRoundedFacts 8
    leaf3519Certificate.logOnePlusV leaf3519InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3519InputLogOnePlusV_eq }

private noncomputable def leaf3519Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi202InputQChi innerPair512Input
    leaf3519InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3519LowerChecked :
    lowerCheck 24 leaf3519Box leaf3519Inputs = true := by
  rfl'

private theorem leaf3519CoversExact : CoversExact 8
    leaf3519Box leaf3519Certificate leaf3519InnerLog leaf3519Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi202RoundedFacts
    innerPair512RoundedFacts leaf3519RoundedFacts (by rfl)

private theorem leaf3519FlatSound : Sound leaf3519Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3519CertificateValid
    leaf3519InnerLogValid leaf3519CoversExact leaf3519LowerChecked

private noncomputable def leaf3520Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3520Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431628288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1991156443/1073741824) }, upper := { exponent := 0, mantissa := (30691/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868550143/274863256576) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf3520InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3520LocalValidity :
    LeafFacts leaf3520Box leaf3520Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3520Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431628288) }) = true
      norm_num [leaf3520Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3520CertificateValid :
    WideCertificateValid leaf3520Box leaf3520Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi201ValidityFacts
    leaf3520LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3520CoverageChecked :
    coverageCheck (innerAD leaf3520Box) leaf3520InnerLog = true := by
  rfl'

private theorem leaf3520InnerLogValid :
    leaf3520InnerLog.Valid 8 (innerAD leaf3520Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3520CoverageChecked

private noncomputable def leaf3520InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907351/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3520InputLogOnePlusV_eq :
    leaf3520InputLogOnePlusV = outerEnclosure 24
      (leaf3520Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3520RoundedFacts : LeafRoundedFacts 8
    leaf3520Certificate.logOnePlusV leaf3520InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3520InputLogOnePlusV_eq }

private noncomputable def leaf3520Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi201InputQChi innerPair91Input
    leaf3520InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3520LowerChecked :
    lowerCheck 24 leaf3520Box leaf3520Inputs = true := by
  rfl'

private theorem leaf3520CoversExact : CoversExact 8
    leaf3520Box leaf3520Certificate leaf3520InnerLog leaf3520Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi201RoundedFacts
    innerPair91RoundedFacts leaf3520RoundedFacts (by rfl)

private theorem leaf3520FlatSound : Sound leaf3520Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3520CertificateValid
    leaf3520InnerLogValid leaf3520CoversExact leaf3520LowerChecked

private noncomputable def leaf3521Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3521Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084211712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1994826233/1073741824) }, upper := { exponent := 0, mantissa := (7687/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168736527/16168423424) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf3521InnerLog : WideLogData :=
  innerPair521Data

set_option maxRecDepth 1000000 in
private theorem leaf3521LocalValidity :
    LeafFacts leaf3521Box leaf3521Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3521Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084211712) }) = true
      norm_num [leaf3521Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3521CertificateValid :
    WideCertificateValid leaf3521Box leaf3521Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi201ValidityFacts
    leaf3521LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3521CoverageChecked :
    coverageCheck (innerAD leaf3521Box) leaf3521InnerLog = true := by
  rfl'

private theorem leaf3521InnerLogValid :
    leaf3521InnerLog.Valid 8 (innerAD leaf3521Box) :=
  wideLogDataValid_of_cachedCheck endpoint253PositiveFacts
    endpoint254PositiveFacts.valid leaf3521CoverageChecked

private noncomputable def leaf3521InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814703/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3521InputLogOnePlusV_eq :
    leaf3521InputLogOnePlusV = outerEnclosure 24
      (leaf3521Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3521RoundedFacts : LeafRoundedFacts 8
    leaf3521Certificate.logOnePlusV leaf3521InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3521InputLogOnePlusV_eq }

private noncomputable def leaf3521Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi201InputQChi innerPair521Input
    leaf3521InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3521LowerChecked :
    lowerCheck 24 leaf3521Box leaf3521Inputs = true := by
  rfl'

private theorem leaf3521CoversExact : CoversExact 8
    leaf3521Box leaf3521Certificate leaf3521InnerLog leaf3521Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi201RoundedFacts
    innerPair521RoundedFacts leaf3521RoundedFacts (by rfl)

private theorem leaf3521FlatSound : Sound leaf3521Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3521CertificateValid
    leaf3521InnerLogValid leaf3521CoversExact leaf3521LowerChecked

private noncomputable def leaf3522Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3522Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431499776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2007539441/1073741824) }, upper := { exponent := 0, mantissa := (15471/8192) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868421631/274862999552) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf3522InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3522LocalValidity :
    LeafFacts leaf3522Box leaf3522Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3522Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431499776) }) = true
      norm_num [leaf3522Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3522CertificateValid :
    WideCertificateValid leaf3522Box leaf3522Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi202ValidityFacts
    leaf3522LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3522CoverageChecked :
    coverageCheck (innerAD leaf3522Box) leaf3522InnerLog = true := by
  rfl'

private theorem leaf3522InnerLogValid :
    leaf3522InnerLog.Valid 8 (innerAD leaf3522Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3522CoverageChecked

private noncomputable def leaf3522InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3522InputLogOnePlusV_eq :
    leaf3522InputLogOnePlusV = outerEnclosure 24
      (leaf3522Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3522RoundedFacts : LeafRoundedFacts 8
    leaf3522Certificate.logOnePlusV leaf3522InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3522InputLogOnePlusV_eq }

private noncomputable def leaf3522Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi202InputQChi innerPair482Input
    leaf3522InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3522LowerChecked :
    lowerCheck 24 leaf3522Box leaf3522Inputs = true := by
  rfl'

private theorem leaf3522CoversExact : CoversExact 8
    leaf3522Box leaf3522Certificate leaf3522InnerLog leaf3522Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi202RoundedFacts
    innerPair482RoundedFacts leaf3522RoundedFacts (by rfl)

private theorem leaf3522FlatSound : Sound leaf3522Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3522CertificateValid
    leaf3522InnerLogValid leaf3522CoversExact leaf3522LowerChecked

private noncomputable def leaf3523Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3523Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486294016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2011274763/1073741824) }, upper := { exponent := 0, mantissa := (3875/2048) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973678387/54972588032) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf3523InnerLog : WideLogData :=
  innerPair522Data

set_option maxRecDepth 1000000 in
private theorem leaf3523LocalValidity :
    LeafFacts leaf3523Box leaf3523Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3523Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486294016) }) = true
      norm_num [leaf3523Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3523CertificateValid :
    WideCertificateValid leaf3523Box leaf3523Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi202ValidityFacts
    leaf3523LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3523CoverageChecked :
    coverageCheck (innerAD leaf3523Box) leaf3523InnerLog = true := by
  rfl'

private theorem leaf3523InnerLogValid :
    leaf3523InnerLog.Valid 8 (innerAD leaf3523Box) :=
  wideLogDataValid_of_cachedCheck endpoint255PositiveFacts
    endpoint256PositiveFacts.valid leaf3523CoverageChecked

private noncomputable def leaf3523InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3523InputLogOnePlusV_eq :
    leaf3523InputLogOnePlusV = outerEnclosure 24
      (leaf3523Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3523RoundedFacts : LeafRoundedFacts 8
    leaf3523Certificate.logOnePlusV leaf3523InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3523InputLogOnePlusV_eq }

private noncomputable def leaf3523Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi202InputQChi innerPair522Input
    leaf3523InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3523LowerChecked :
    lowerCheck 24 leaf3523Box leaf3523Inputs = true := by
  rfl'

private theorem leaf3523CoversExact : CoversExact 8
    leaf3523Box leaf3523Certificate leaf3523InnerLog leaf3523Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi202RoundedFacts
    innerPair522RoundedFacts leaf3523RoundedFacts (by rfl)

private theorem leaf3523FlatSound : Sound leaf3523Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3523CertificateValid
    leaf3523InnerLogValid leaf3523CoversExact leaf3523LowerChecked

private noncomputable def leaf3524Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3524Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742439/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486286336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2016320731/1073741824) }, upper := { exponent := 0, mantissa := (31075/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973670707/54972572672) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf3524InnerLog : WideLogData :=
  innerPair107Data

set_option maxRecDepth 1000000 in
private theorem leaf3524LocalValidity :
    LeafFacts leaf3524Box leaf3524Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3524Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486286336) }) = true
      norm_num [leaf3524Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3524CertificateValid :
    WideCertificateValid leaf3524Box leaf3524Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi199ValidityFacts
    leaf3524LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3524CoverageChecked :
    coverageCheck (innerAD leaf3524Box) leaf3524InnerLog = true := by
  rfl'

private theorem leaf3524InnerLogValid :
    leaf3524InnerLog.Valid 8 (innerAD leaf3524Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint257PositiveFacts.valid leaf3524CoverageChecked

private noncomputable def leaf3524InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453677/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3524InputLogOnePlusV_eq :
    leaf3524InputLogOnePlusV = outerEnclosure 24
      (leaf3524Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3524RoundedFacts : LeafRoundedFacts 8
    leaf3524Certificate.logOnePlusV leaf3524InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3524InputLogOnePlusV_eq }

private noncomputable def leaf3524Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi199InputQChi innerPair107Input
    leaf3524InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3524LowerChecked :
    lowerCheck 24 leaf3524Box leaf3524Inputs = true := by
  rfl'

private theorem leaf3524CoversExact : CoversExact 8
    leaf3524Box leaf3524Certificate leaf3524InnerLog leaf3524Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi199RoundedFacts
    innerPair107RoundedFacts leaf3524RoundedFacts (by rfl)

private theorem leaf3524FlatSound : Sound leaf3524Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3524CertificateValid
    leaf3524InnerLogValid leaf3524CoversExact leaf3524LowerChecked

private noncomputable def leaf3525Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3525Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3196207485/3196079104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2020121585/1073741824) }, upper := { exponent := 0, mantissa := (15567/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6392286589/6392158208) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf3525InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf3525LocalValidity :
    LeafFacts leaf3525Box leaf3525Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3525Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3196207485/3196079104) }) = true
      norm_num [leaf3525Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3525CertificateValid :
    WideCertificateValid leaf3525Box leaf3525Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi199ValidityFacts
    leaf3525LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3525CoverageChecked :
    coverageCheck (innerAD leaf3525Box) leaf3525InnerLog = true := by
  rfl'

private theorem leaf3525InnerLogValid :
    leaf3525InnerLog.Valid 8 (innerAD leaf3525Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf3525CoverageChecked

private noncomputable def leaf3525InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3525InputLogOnePlusV_eq :
    leaf3525InputLogOnePlusV = outerEnclosure 24
      (leaf3525Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3525RoundedFacts : LeafRoundedFacts 8
    leaf3525Certificate.logOnePlusV leaf3525InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3525InputLogOnePlusV_eq }

private noncomputable def leaf3525Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi199InputQChi innerPair103Input
    leaf3525InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3525LowerChecked :
    lowerCheck 24 leaf3525Box leaf3525Inputs = true := by
  rfl'

private theorem leaf3525CoversExact : CoversExact 8
    leaf3525Box leaf3525Certificate leaf3525InnerLog leaf3525Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi199RoundedFacts
    innerPair103RoundedFacts leaf3525RoundedFacts (by rfl)

private theorem leaf3525FlatSound : Sound leaf3525Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3525CertificateValid
    leaf3525InnerLogValid leaf3525CoversExact leaf3525LowerChecked

private noncomputable def leaf3526Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3526Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742441/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431304192) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2032572665/1073741824) }, upper := { exponent := 0, mantissa := (7831/4096) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868226047/274862608384) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf3526InnerLog : WideLogData :=
  innerPair231Data

set_option maxRecDepth 1000000 in
private theorem leaf3526LocalValidity :
    LeafFacts leaf3526Box leaf3526Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3526Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431304192) }) = true
      norm_num [leaf3526Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3526CertificateValid :
    WideCertificateValid leaf3526Box leaf3526Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi200ValidityFacts
    leaf3526LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3526CoverageChecked :
    coverageCheck (innerAD leaf3526Box) leaf3526InnerLog = true := by
  rfl'

private theorem leaf3526InnerLogValid :
    leaf3526InnerLog.Valid 8 (innerAD leaf3526Box) :=
  wideLogDataValid_of_cachedCheck endpoint69PositiveFacts
    endpoint258PositiveFacts.valid leaf3526CoverageChecked

private noncomputable def leaf3526InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726839/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3526InputLogOnePlusV_eq :
    leaf3526InputLogOnePlusV = outerEnclosure 24
      (leaf3526Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3526RoundedFacts : LeafRoundedFacts 8
    leaf3526Certificate.logOnePlusV leaf3526InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3526InputLogOnePlusV_eq }

private noncomputable def leaf3526Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi200InputQChi innerPair231Input
    leaf3526InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3526LowerChecked :
    lowerCheck 24 leaf3526Box leaf3526Inputs = true := by
  rfl'

private theorem leaf3526CoversExact : CoversExact 8
    leaf3526Box leaf3526Certificate leaf3526InnerLog leaf3526Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi200RoundedFacts
    innerPair231RoundedFacts leaf3526RoundedFacts (by rfl)

private theorem leaf3526FlatSound : Sound leaf3526Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3526CertificateValid
    leaf3526InnerLogValid leaf3526CoversExact leaf3526LowerChecked

private noncomputable def leaf3527Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3527Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431273472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2036439051/1073741824) }, upper := { exponent := 0, mantissa := (3923/2048) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868195327/274862546944) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf3527InnerLog : WideLogData :=
  innerPair229Data

set_option maxRecDepth 1000000 in
private theorem leaf3527LocalValidity :
    LeafFacts leaf3527Box leaf3527Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3527Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431273472) }) = true
      norm_num [leaf3527Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3527CertificateValid :
    WideCertificateValid leaf3527Box leaf3527Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi200ValidityFacts
    leaf3527LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3527CoverageChecked :
    coverageCheck (innerAD leaf3527Box) leaf3527InnerLog = true := by
  rfl'

private theorem leaf3527InnerLogValid :
    leaf3527InnerLog.Valid 8 (innerAD leaf3527Box) :=
  wideLogDataValid_of_cachedCheck endpoint69PositiveFacts
    endpoint81PositiveFacts.valid leaf3527CoverageChecked

private noncomputable def leaf3527InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814713/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3527InputLogOnePlusV_eq :
    leaf3527InputLogOnePlusV = outerEnclosure 24
      (leaf3527Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3527RoundedFacts : LeafRoundedFacts 8
    leaf3527Certificate.logOnePlusV leaf3527InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3527InputLogOnePlusV_eq }

private noncomputable def leaf3527Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi200InputQChi innerPair229Input
    leaf3527InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3527LowerChecked :
    lowerCheck 24 leaf3527Box leaf3527Inputs = true := by
  rfl'

private theorem leaf3527CoversExact : CoversExact 8
    leaf3527Box leaf3527Certificate leaf3527InnerLog leaf3527Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi200RoundedFacts
    innerPair229RoundedFacts leaf3527RoundedFacts (by rfl)

private theorem leaf3527FlatSound : Sound leaf3527Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3527CertificateValid
    leaf3527InnerLogValid leaf3527CoversExact leaf3527LowerChecked

private noncomputable def leaf3528Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3528Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742443/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810457088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2023922439/1073741824) }, upper := { exponent := 0, mantissa := (31193/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622764373/91620914176) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf3528InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf3528LocalValidity :
    LeafFacts leaf3528Box leaf3528Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3528Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810457088) }) = true
      norm_num [leaf3528Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3528CertificateValid :
    WideCertificateValid leaf3528Box leaf3528Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi199ValidityFacts
    leaf3528LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3528CoverageChecked :
    coverageCheck (innerAD leaf3528Box) leaf3528InnerLog = true := by
  rfl'

private theorem leaf3528InnerLogValid :
    leaf3528InnerLog.Valid 8 (innerAD leaf3528Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf3528CoverageChecked

private noncomputable def leaf3528InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907355/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3528InputLogOnePlusV_eq :
    leaf3528InputLogOnePlusV = outerEnclosure 24
      (leaf3528Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3528RoundedFacts : LeafRoundedFacts 8
    leaf3528Certificate.logOnePlusV leaf3528InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3528InputLogOnePlusV_eq }

private noncomputable def leaf3528Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi199InputQChi innerPair103Input
    leaf3528InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3528LowerChecked :
    lowerCheck 24 leaf3528Box leaf3528Inputs = true := by
  rfl'

private theorem leaf3528CoversExact : CoversExact 8
    leaf3528Box leaf3528Certificate leaf3528InnerLog leaf3528Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi199RoundedFacts
    innerPair103RoundedFacts leaf3528RoundedFacts (by rfl)

private theorem leaf3528FlatSound : Sound leaf3528Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3528CertificateValid
    leaf3528InnerLogValid leaf3528CoversExact leaf3528LowerChecked

private noncomputable def leaf3529Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3529Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431341056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2027723293/1073741824) }, upper := { exponent := 0, mantissa := (7813/4096) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868262911/274862682112) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf3529InnerLog : WideLogData :=
  innerPair515Data

set_option maxRecDepth 1000000 in
private theorem leaf3529LocalValidity :
    LeafFacts leaf3529Box leaf3529Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3529Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431341056) }) = true
      norm_num [leaf3529Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3529CertificateValid :
    WideCertificateValid leaf3529Box leaf3529Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi199ValidityFacts
    leaf3529LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3529CoverageChecked :
    coverageCheck (innerAD leaf3529Box) leaf3529InnerLog = true := by
  rfl'

private theorem leaf3529InnerLogValid :
    leaf3529InnerLog.Valid 8 (innerAD leaf3529Box) :=
  wideLogDataValid_of_cachedCheck endpoint245PositiveFacts
    endpoint246PositiveFacts.valid leaf3529CoverageChecked

private noncomputable def leaf3529InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3529InputLogOnePlusV_eq :
    leaf3529InputLogOnePlusV = outerEnclosure 24
      (leaf3529Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3529RoundedFacts : LeafRoundedFacts 8
    leaf3529Certificate.logOnePlusV leaf3529InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3529InputLogOnePlusV_eq }

private noncomputable def leaf3529Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi199InputQChi innerPair515Input
    leaf3529InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3529LowerChecked :
    lowerCheck 24 leaf3529Box leaf3529Inputs = true := by
  rfl'

private theorem leaf3529CoversExact : CoversExact 8
    leaf3529Box leaf3529Certificate leaf3529InnerLog leaf3529Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi199RoundedFacts
    innerPair515RoundedFacts leaf3529RoundedFacts (by rfl)

private theorem leaf3529FlatSound : Sound leaf3529Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3529CertificateValid
    leaf3529InnerLogValid leaf3529CoversExact leaf3529LowerChecked

private noncomputable def leaf3530Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3530Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742445/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431242752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2040305437/1073741824) }, upper := { exponent := 0, mantissa := (7861/4096) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868164607/274862485504) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf3530InnerLog : WideLogData :=
  innerPair229Data

set_option maxRecDepth 1000000 in
private theorem leaf3530LocalValidity :
    LeafFacts leaf3530Box leaf3530Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3530Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431242752) }) = true
      norm_num [leaf3530Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3530CertificateValid :
    WideCertificateValid leaf3530Box leaf3530Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi200ValidityFacts
    leaf3530LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3530CoverageChecked :
    coverageCheck (innerAD leaf3530Box) leaf3530InnerLog = true := by
  rfl'

private theorem leaf3530InnerLogValid :
    leaf3530InnerLog.Valid 8 (innerAD leaf3530Box) :=
  wideLogDataValid_of_cachedCheck endpoint69PositiveFacts
    endpoint81PositiveFacts.valid leaf3530CoverageChecked

private noncomputable def leaf3530InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3530InputLogOnePlusV_eq :
    leaf3530InputLogOnePlusV = outerEnclosure 24
      (leaf3530Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3530RoundedFacts : LeafRoundedFacts 8
    leaf3530Certificate.logOnePlusV leaf3530InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3530InputLogOnePlusV_eq }

private noncomputable def leaf3530Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi200InputQChi innerPair229Input
    leaf3530InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3530LowerChecked :
    lowerCheck 24 leaf3530Box leaf3530Inputs = true := by
  rfl'

private theorem leaf3530CoversExact : CoversExact 8
    leaf3530Box leaf3530Certificate leaf3530InnerLog leaf3530Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi200RoundedFacts
    innerPair229RoundedFacts leaf3530RoundedFacts (by rfl)

private theorem leaf3530FlatSound : Sound leaf3530Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3530CertificateValid
    leaf3530InnerLogValid leaf3530CoversExact leaf3530LowerChecked

private noncomputable def leaf3531Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3531Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431212032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2044171823/1073741824) }, upper := { exponent := 0, mantissa := (1969/1024) } }, logOuter := sk236LogOuterCertificate, logK := sk236LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868133887/274862424064) } }, logDArg := sk236LogDArgCertificate }

private noncomputable def leaf3531InnerLog : WideLogData :=
  innerPair517Data

set_option maxRecDepth 1000000 in
private theorem leaf3531LocalValidity :
    LeafFacts leaf3531Box leaf3531Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3531Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431212032) }) = true
      norm_num [leaf3531Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3531CertificateValid :
    WideCertificateValid leaf3531Box leaf3531Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk236ValidityFacts chi200ValidityFacts
    leaf3531LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3531CoverageChecked :
    coverageCheck (innerAD leaf3531Box) leaf3531InnerLog = true := by
  rfl'

private theorem leaf3531InnerLogValid :
    leaf3531InnerLog.Valid 8 (innerAD leaf3531Box) :=
  wideLogDataValid_of_cachedCheck endpoint247PositiveFacts
    endpoint248PositiveFacts.valid leaf3531CoverageChecked

private noncomputable def leaf3531InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3531InputLogOnePlusV_eq :
    leaf3531InputLogOnePlusV = outerEnclosure 24
      (leaf3531Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3531RoundedFacts : LeafRoundedFacts 8
    leaf3531Certificate.logOnePlusV leaf3531InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3531InputLogOnePlusV_eq }

private noncomputable def leaf3531Inputs : Inputs :=
  inputsOfCaches globalInput sk236RoundedInputs
    chi200InputQChi innerPair517Input
    leaf3531InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3531LowerChecked :
    lowerCheck 24 leaf3531Box leaf3531Inputs = true := by
  rfl'

private theorem leaf3531CoversExact : CoversExact 8
    leaf3531Box leaf3531Certificate leaf3531InnerLog leaf3531Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk236RoundedFacts chi200RoundedFacts
    innerPair517RoundedFacts leaf3531RoundedFacts (by rfl)

private theorem leaf3531FlatSound : Sound leaf3531Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3531CertificateValid
    leaf3531InnerLogValid leaf3531CoversExact leaf3531LowerChecked

private noncomputable def leaf3532Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (7/32), chiHi := (113/512) }

private noncomputable def leaf3532Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484379/2147483648) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090060544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3997025319/2147483648) }, upper := { exponent := 0, mantissa := (61357/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi229LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180316909/10180121088) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3532InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3532LocalValidity :
    LeafFacts leaf3532Box leaf3532Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3532Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090060544) }) = true
      norm_num [leaf3532Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3532CertificateValid :
    WideCertificateValid leaf3532Box leaf3532Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi229ValidityFacts
    leaf3532LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3532CoverageChecked :
    coverageCheck (innerAD leaf3532Box) leaf3532InnerLog = true := by
  rfl'

private theorem leaf3532InnerLogValid :
    leaf3532InnerLog.Valid 8 (innerAD leaf3532Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3532CoverageChecked

private noncomputable def leaf3532InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3532InputLogOnePlusV_eq :
    leaf3532InputLogOnePlusV = outerEnclosure 24
      (leaf3532Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3532RoundedFacts : LeafRoundedFacts 8
    leaf3532Certificate.logOnePlusV leaf3532InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3532InputLogOnePlusV_eq }

private noncomputable def leaf3532Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi229InputQChi innerPair91Input
    leaf3532InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3532LowerChecked :
    lowerCheck 24 leaf3532Box leaf3532Inputs = true := by
  rfl'

private theorem leaf3532CoversExact : CoversExact 8
    leaf3532Box leaf3532Certificate leaf3532InnerLog leaf3532Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi229RoundedFacts
    innerPair91RoundedFacts leaf3532RoundedFacts (by rfl)

private theorem leaf3532FlatSound : Sound leaf3532Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3532CertificateValid
    leaf3532InnerLogValid leaf3532CoversExact leaf3532LowerChecked

private noncomputable def leaf3533Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (113/512), chiHi := (57/256) }

private noncomputable def leaf3533Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484381/2147483648) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486313984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4013539381/2147483648) }, upper := { exponent := 0, mantissa := (30805/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi230LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973698355/54972627968) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3533InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3533LocalValidity :
    LeafFacts leaf3533Box leaf3533Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3533Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486313984) }) = true
      norm_num [leaf3533Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3533CertificateValid :
    WideCertificateValid leaf3533Box leaf3533Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi230ValidityFacts
    leaf3533LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3533CoverageChecked :
    coverageCheck (innerAD leaf3533Box) leaf3533InnerLog = true := by
  rfl'

private theorem leaf3533InnerLogValid :
    leaf3533InnerLog.Valid 8 (innerAD leaf3533Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3533CoverageChecked

private noncomputable def leaf3533InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3533InputLogOnePlusV_eq :
    leaf3533InputLogOnePlusV = outerEnclosure 24
      (leaf3533Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3533RoundedFacts : LeafRoundedFacts 8
    leaf3533Certificate.logOnePlusV leaf3533InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3533InputLogOnePlusV_eq }

private noncomputable def leaf3533Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi230InputQChi innerPair482Input
    leaf3533InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3533LowerChecked :
    lowerCheck 24 leaf3533Box leaf3533Inputs = true := by
  rfl'

private theorem leaf3533CoversExact : CoversExact 8
    leaf3533Box leaf3533Certificate leaf3533InnerLog leaf3533Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi230RoundedFacts
    innerPair482RoundedFacts leaf3533RoundedFacts (by rfl)

private theorem leaf3533FlatSound : Sound leaf3533Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3533CertificateValid
    leaf3533InnerLogValid leaf3533CoversExact leaf3533LowerChecked

private noncomputable def leaf3534Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (7/32), chiHi := (113/512) }

private noncomputable def leaf3534Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484381/2147483648) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486321152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4004364901/2147483648) }, upper := { exponent := 0, mantissa := (30735/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi229LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973705523/54972642304) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3534InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3534LocalValidity :
    LeafFacts leaf3534Box leaf3534Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3534Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486321152) }) = true
      norm_num [leaf3534Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3534CertificateValid :
    WideCertificateValid leaf3534Box leaf3534Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi229ValidityFacts
    leaf3534LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3534CoverageChecked :
    coverageCheck (innerAD leaf3534Box) leaf3534InnerLog = true := by
  rfl'

private theorem leaf3534InnerLogValid :
    leaf3534InnerLog.Valid 8 (innerAD leaf3534Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3534CoverageChecked

private noncomputable def leaf3534InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3534InputLogOnePlusV_eq :
    leaf3534InputLogOnePlusV = outerEnclosure 24
      (leaf3534Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3534RoundedFacts : LeafRoundedFacts 8
    leaf3534Certificate.logOnePlusV leaf3534InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3534InputLogOnePlusV_eq }

private noncomputable def leaf3534Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi229InputQChi innerPair482Input
    leaf3534InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3534LowerChecked :
    lowerCheck 24 leaf3534Box leaf3534Inputs = true := by
  rfl'

private theorem leaf3534CoversExact : CoversExact 8
    leaf3534Box leaf3534Certificate leaf3534InnerLog leaf3534Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi229RoundedFacts
    innerPair482RoundedFacts leaf3534RoundedFacts (by rfl)

private theorem leaf3534FlatSound : Sound leaf3534Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3534CertificateValid
    leaf3534InnerLogValid leaf3534CoversExact leaf3534LowerChecked

private noncomputable def leaf3535Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (113/512), chiHi := (57/256) }

private noncomputable def leaf3535Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484383/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431540736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4020944495/2147483648) }, upper := { exponent := 0, mantissa := (15431/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi230LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868462591/274863081472) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3535InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3535LocalValidity :
    LeafFacts leaf3535Box leaf3535Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3535Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431540736) }) = true
      norm_num [leaf3535Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3535CertificateValid :
    WideCertificateValid leaf3535Box leaf3535Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi230ValidityFacts
    leaf3535LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3535CoverageChecked :
    coverageCheck (innerAD leaf3535Box) leaf3535InnerLog = true := by
  rfl'

private theorem leaf3535InnerLogValid :
    leaf3535InnerLog.Valid 8 (innerAD leaf3535Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3535CoverageChecked

private noncomputable def leaf3535InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3535InputLogOnePlusV_eq :
    leaf3535InputLogOnePlusV = outerEnclosure 24
      (leaf3535Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3535RoundedFacts : LeafRoundedFacts 8
    leaf3535Certificate.logOnePlusV leaf3535InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3535InputLogOnePlusV_eq }

private noncomputable def leaf3535Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi230InputQChi innerPair482Input
    leaf3535InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3535LowerChecked :
    lowerCheck 24 leaf3535Box leaf3535Inputs = true := by
  rfl'

private theorem leaf3535CoversExact : CoversExact 8
    leaf3535Box leaf3535Certificate leaf3535InnerLog leaf3535Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi230RoundedFacts
    innerPair482RoundedFacts leaf3535RoundedFacts (by rfl)

private theorem leaf3535FlatSound : Sound leaf3535Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3535CertificateValid
    leaf3535InnerLogValid leaf3535CoversExact leaf3535LowerChecked

private noncomputable def leaf3536Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (57/256), chiHi := (115/512) }

private noncomputable def leaf3536Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484383/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431505152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4030053443/2147483648) }, upper := { exponent := 0, mantissa := (61863/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi231LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868427007/274863010304) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3536InnerLog : WideLogData :=
  innerPair102Data

set_option maxRecDepth 1000000 in
private theorem leaf3536LocalValidity :
    LeafFacts leaf3536Box leaf3536Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3536Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431505152) }) = true
      norm_num [leaf3536Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3536CertificateValid :
    WideCertificateValid leaf3536Box leaf3536Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi231ValidityFacts
    leaf3536LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3536CoverageChecked :
    coverageCheck (innerAD leaf3536Box) leaf3536InnerLog = true := by
  rfl'

private theorem leaf3536InnerLogValid :
    leaf3536InnerLog.Valid 8 (innerAD leaf3536Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint69PositiveFacts.valid leaf3536CoverageChecked

private noncomputable def leaf3536InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3536InputLogOnePlusV_eq :
    leaf3536InputLogOnePlusV = outerEnclosure 24
      (leaf3536Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3536RoundedFacts : LeafRoundedFacts 8
    leaf3536Certificate.logOnePlusV leaf3536InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3536InputLogOnePlusV_eq }

private noncomputable def leaf3536Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi231InputQChi innerPair102Input
    leaf3536InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3536LowerChecked :
    lowerCheck 24 leaf3536Box leaf3536Inputs = true := by
  rfl'

private theorem leaf3536CoversExact : CoversExact 8
    leaf3536Box leaf3536Certificate leaf3536InnerLog leaf3536Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi231RoundedFacts
    innerPair102RoundedFacts leaf3536RoundedFacts (by rfl)

private theorem leaf3536FlatSound : Sound leaf3536Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3536CertificateValid
    leaf3536InnerLogValid leaf3536CoversExact leaf3536LowerChecked

private noncomputable def leaf3537Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (115/512), chiHi := (29/128) }

private noncomputable def leaf3537Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484385/2147483648) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810480128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4046567505/2147483648) }, upper := { exponent := 0, mantissa := (15529/8192) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi232LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622787413/91620960256) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3537InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3537LocalValidity :
    LeafFacts leaf3537Box leaf3537Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3537Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810480128) }) = true
      norm_num [leaf3537Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3537CertificateValid :
    WideCertificateValid leaf3537Box leaf3537Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi232ValidityFacts
    leaf3537LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3537CoverageChecked :
    coverageCheck (innerAD leaf3537Box) leaf3537InnerLog = true := by
  rfl'

private theorem leaf3537InnerLogValid :
    leaf3537InnerLog.Valid 8 (innerAD leaf3537Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3537CoverageChecked

private noncomputable def leaf3537InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629415/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3537InputLogOnePlusV_eq :
    leaf3537InputLogOnePlusV = outerEnclosure 24
      (leaf3537Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3537RoundedFacts : LeafRoundedFacts 8
    leaf3537Certificate.logOnePlusV leaf3537InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3537InputLogOnePlusV_eq }

private noncomputable def leaf3537Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi232InputQChi innerPair100Input
    leaf3537InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3537LowerChecked :
    lowerCheck 24 leaf3537Box leaf3537Inputs = true := by
  rfl'

private theorem leaf3537CoversExact : CoversExact 8
    leaf3537Box leaf3537Certificate leaf3537InnerLog leaf3537Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi232RoundedFacts
    innerPair100RoundedFacts leaf3537RoundedFacts (by rfl)

private theorem leaf3537FlatSound : Sound leaf3537Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3537CertificateValid
    leaf3537InnerLogValid leaf3537CoversExact leaf3537LowerChecked

private noncomputable def leaf3538Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (57/256), chiHi := (115/512) }

private noncomputable def leaf3538Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484385/2147483648) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090054656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4037524089/2147483648) }, upper := { exponent := 0, mantissa := (30989/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi231LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180311021/10180109312) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3538InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf3538LocalValidity :
    LeafFacts leaf3538Box leaf3538Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3538Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090054656) }) = true
      norm_num [leaf3538Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3538CertificateValid :
    WideCertificateValid leaf3538Box leaf3538Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi231ValidityFacts
    leaf3538LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3538CoverageChecked :
    coverageCheck (innerAD leaf3538Box) leaf3538InnerLog = true := by
  rfl'

private theorem leaf3538InnerLogValid :
    leaf3538InnerLog.Valid 8 (innerAD leaf3538Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf3538CoverageChecked

private noncomputable def leaf3538InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629413/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3538InputLogOnePlusV_eq :
    leaf3538InputLogOnePlusV = outerEnclosure 24
      (leaf3538Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3538RoundedFacts : LeafRoundedFacts 8
    leaf3538Certificate.logOnePlusV leaf3538InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3538InputLogOnePlusV_eq }

private noncomputable def leaf3538Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi231InputQChi innerPair103Input
    leaf3538InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3538LowerChecked :
    lowerCheck 24 leaf3538Box leaf3538Inputs = true := by
  rfl'

private theorem leaf3538CoversExact : CoversExact 8
    leaf3538Box leaf3538Certificate leaf3538InnerLog leaf3538Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi231RoundedFacts
    innerPair103RoundedFacts leaf3538RoundedFacts (by rfl)

private theorem leaf3538FlatSound : Sound leaf3538Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3538CertificateValid
    leaf3538InnerLogValid leaf3538CoversExact leaf3538LowerChecked

private noncomputable def leaf3539Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (115/512), chiHi := (29/128) }

private noncomputable def leaf3539Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484387/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431410688) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4054103683/2147483648) }, upper := { exponent := 0, mantissa := (7779/4096) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi232LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868332543/274862821376) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3539InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3539LocalValidity :
    LeafFacts leaf3539Box leaf3539Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3539Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431410688) }) = true
      norm_num [leaf3539Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3539CertificateValid :
    WideCertificateValid leaf3539Box leaf3539Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi232ValidityFacts
    leaf3539LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3539CoverageChecked :
    coverageCheck (innerAD leaf3539Box) leaf3539InnerLog = true := by
  rfl'

private theorem leaf3539InnerLogValid :
    leaf3539InnerLog.Valid 8 (innerAD leaf3539Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3539CoverageChecked

private noncomputable def leaf3539InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3539InputLogOnePlusV_eq :
    leaf3539InputLogOnePlusV = outerEnclosure 24
      (leaf3539Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3539RoundedFacts : LeafRoundedFacts 8
    leaf3539Certificate.logOnePlusV leaf3539InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3539InputLogOnePlusV_eq }

private noncomputable def leaf3539Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi232InputQChi innerPair100Input
    leaf3539InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3539LowerChecked :
    lowerCheck 24 leaf3539Box leaf3539Inputs = true := by
  rfl'

private theorem leaf3539CoversExact : CoversExact 8
    leaf3539Box leaf3539Certificate leaf3539InnerLog leaf3539Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi232RoundedFacts
    innerPair100RoundedFacts leaf3539RoundedFacts (by rfl)

private theorem leaf3539FlatSound : Sound leaf3539Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3539CertificateValid
    leaf3539InnerLogValid leaf3539CoversExact leaf3539LowerChecked

private noncomputable def leaf3540Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (7/32), chiHi := (113/512) }

private noncomputable def leaf3540Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484383/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431576832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4011704483/2147483648) }, upper := { exponent := 0, mantissa := (61583/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi229LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868498687/274863153664) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3540InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3540LocalValidity :
    LeafFacts leaf3540Box leaf3540Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3540Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431576832) }) = true
      norm_num [leaf3540Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3540CertificateValid :
    WideCertificateValid leaf3540Box leaf3540Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi229ValidityFacts
    leaf3540LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3540CoverageChecked :
    coverageCheck (innerAD leaf3540Box) leaf3540InnerLog = true := by
  rfl'

private theorem leaf3540InnerLogValid :
    leaf3540InnerLog.Valid 8 (innerAD leaf3540Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3540CoverageChecked

private noncomputable def leaf3540InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3540InputLogOnePlusV_eq :
    leaf3540InputLogOnePlusV = outerEnclosure 24
      (leaf3540Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3540RoundedFacts : LeafRoundedFacts 8
    leaf3540Certificate.logOnePlusV leaf3540InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3540InputLogOnePlusV_eq }

private noncomputable def leaf3540Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi229InputQChi innerPair482Input
    leaf3540InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3540LowerChecked :
    lowerCheck 24 leaf3540Box leaf3540Inputs = true := by
  rfl'

private theorem leaf3540CoversExact : CoversExact 8
    leaf3540Box leaf3540Certificate leaf3540InnerLog leaf3540Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi229RoundedFacts
    innerPair482RoundedFacts leaf3540RoundedFacts (by rfl)

private theorem leaf3540FlatSound : Sound leaf3540Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3540CertificateValid
    leaf3540InnerLogValid leaf3540CoversExact leaf3540LowerChecked

private noncomputable def leaf3541Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (113/512), chiHi := (57/256) }

private noncomputable def leaf3541Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484385/2147483648) }, vSqrt := { lower := (8191/8192), upper := (3196207485/3196081664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4028349609/2147483648) }, upper := { exponent := 0, mantissa := (30919/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi230LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6392289149/6392163328) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3541InnerLog : WideLogData :=
  innerPair102Data

set_option maxRecDepth 1000000 in
private theorem leaf3541LocalValidity :
    LeafFacts leaf3541Box leaf3541Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3541Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3196207485/3196081664) }) = true
      norm_num [leaf3541Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3541CertificateValid :
    WideCertificateValid leaf3541Box leaf3541Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi230ValidityFacts
    leaf3541LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3541CoverageChecked :
    coverageCheck (innerAD leaf3541Box) leaf3541InnerLog = true := by
  rfl'

private theorem leaf3541InnerLogValid :
    leaf3541InnerLog.Valid 8 (innerAD leaf3541Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint69PositiveFacts.valid leaf3541CoverageChecked

private noncomputable def leaf3541InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629411/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3541InputLogOnePlusV_eq :
    leaf3541InputLogOnePlusV = outerEnclosure 24
      (leaf3541Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3541RoundedFacts : LeafRoundedFacts 8
    leaf3541Certificate.logOnePlusV leaf3541InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3541InputLogOnePlusV_eq }

private noncomputable def leaf3541Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi230InputQChi innerPair102Input
    leaf3541InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3541LowerChecked :
    lowerCheck 24 leaf3541Box leaf3541Inputs = true := by
  rfl'

private theorem leaf3541CoversExact : CoversExact 8
    leaf3541Box leaf3541Certificate leaf3541InnerLog leaf3541Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi230RoundedFacts
    innerPair102RoundedFacts leaf3541RoundedFacts (by rfl)

private theorem leaf3541FlatSound : Sound leaf3541Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3541CertificateValid
    leaf3541InnerLogValid leaf3541CoversExact leaf3541LowerChecked

private noncomputable def leaf3542Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (7/32), chiHi := (113/512) }

private noncomputable def leaf3542Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484385/2147483648) }, vSqrt := { lower := (65527/65536), upper := (45812307285/45810515968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4019044065/2147483648) }, upper := { exponent := 0, mantissa := (241/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi229LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (91622823253/91621031936) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3542InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3542LocalValidity :
    LeafFacts leaf3542Box leaf3542Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3542Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (45812307285/45810515968) }) = true
      norm_num [leaf3542Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3542CertificateValid :
    WideCertificateValid leaf3542Box leaf3542Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi229ValidityFacts
    leaf3542LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3542CoverageChecked :
    coverageCheck (innerAD leaf3542Box) leaf3542InnerLog = true := by
  rfl'

private theorem leaf3542InnerLogValid :
    leaf3542InnerLog.Valid 8 (innerAD leaf3542Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3542CoverageChecked

private noncomputable def leaf3542InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3542InputLogOnePlusV_eq :
    leaf3542InputLogOnePlusV = outerEnclosure 24
      (leaf3542Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3542RoundedFacts : LeafRoundedFacts 8
    leaf3542Certificate.logOnePlusV leaf3542InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3542InputLogOnePlusV_eq }

private noncomputable def leaf3542Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi229InputQChi innerPair482Input
    leaf3542InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3542LowerChecked :
    lowerCheck 24 leaf3542Box leaf3542Inputs = true := by
  rfl'

private theorem leaf3542CoversExact : CoversExact 8
    leaf3542Box leaf3542Certificate leaf3542InnerLog leaf3542Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi229RoundedFacts
    innerPair482RoundedFacts leaf3542RoundedFacts (by rfl)

private theorem leaf3542FlatSound : Sound leaf3542Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3542CertificateValid
    leaf3542InnerLogValid leaf3542CoversExact leaf3542LowerChecked

private noncomputable def leaf3543Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (113/512), chiHi := (57/256) }

private noncomputable def leaf3543Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484387/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137431482368) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4035754723/2147483648) }, upper := { exponent := 0, mantissa := (121/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi230LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274868404223/274862964736) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3543InnerLog : WideLogData :=
  innerPair102Data

set_option maxRecDepth 1000000 in
private theorem leaf3543LocalValidity :
    LeafFacts leaf3543Box leaf3543Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3543Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137431482368) }) = true
      norm_num [leaf3543Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3543CertificateValid :
    WideCertificateValid leaf3543Box leaf3543Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi230ValidityFacts
    leaf3543LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3543CoverageChecked :
    coverageCheck (innerAD leaf3543Box) leaf3543InnerLog = true := by
  rfl'

private theorem leaf3543InnerLogValid :
    leaf3543InnerLog.Valid 8 (innerAD leaf3543Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint69PositiveFacts.valid leaf3543CoverageChecked

private noncomputable def leaf3543InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629413/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3543InputLogOnePlusV_eq :
    leaf3543InputLogOnePlusV = outerEnclosure 24
      (leaf3543Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3543RoundedFacts : LeafRoundedFacts 8
    leaf3543Certificate.logOnePlusV leaf3543InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3543InputLogOnePlusV_eq }

private noncomputable def leaf3543Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi230InputQChi innerPair102Input
    leaf3543InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3543LowerChecked :
    lowerCheck 24 leaf3543Box leaf3543Inputs = true := by
  rfl'

private theorem leaf3543CoversExact : CoversExact 8
    leaf3543Box leaf3543Certificate leaf3543InnerLog leaf3543Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi230RoundedFacts
    innerPair102RoundedFacts leaf3543RoundedFacts (by rfl)

private theorem leaf3543FlatSound : Sound leaf3543Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3543CertificateValid
    leaf3543InnerLogValid leaf3543CoversExact leaf3543LowerChecked

private noncomputable def leaf3544Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (57/256), chiHi := (115/512) }

private noncomputable def leaf3544Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484387/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431446272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4044994735/2147483648) }, upper := { exponent := 0, mantissa := (62093/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi231LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868368127/274862892544) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3544InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf3544LocalValidity :
    LeafFacts leaf3544Box leaf3544Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3544Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431446272) }) = true
      norm_num [leaf3544Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3544CertificateValid :
    WideCertificateValid leaf3544Box leaf3544Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi231ValidityFacts
    leaf3544LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3544CoverageChecked :
    coverageCheck (innerAD leaf3544Box) leaf3544InnerLog = true := by
  rfl'

private theorem leaf3544InnerLogValid :
    leaf3544InnerLog.Valid 8 (innerAD leaf3544Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf3544CoverageChecked

private noncomputable def leaf3544InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629415/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3544InputLogOnePlusV_eq :
    leaf3544InputLogOnePlusV = outerEnclosure 24
      (leaf3544Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3544RoundedFacts : LeafRoundedFacts 8
    leaf3544Certificate.logOnePlusV leaf3544InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3544InputLogOnePlusV_eq }

private noncomputable def leaf3544Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi231InputQChi innerPair103Input
    leaf3544InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3544LowerChecked :
    lowerCheck 24 leaf3544Box leaf3544Inputs = true := by
  rfl'

private theorem leaf3544CoversExact : CoversExact 8
    leaf3544Box leaf3544Certificate leaf3544InnerLog leaf3544Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi231RoundedFacts
    innerPair103RoundedFacts leaf3544RoundedFacts (by rfl)

private theorem leaf3544FlatSound : Sound leaf3544Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3544CertificateValid
    leaf3544InnerLogValid leaf3544CoversExact leaf3544LowerChecked

private noncomputable def leaf3545Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (115/512), chiHi := (29/128) }

private noncomputable def leaf3545Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484389/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431380992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4061639861/2147483648) }, upper := { exponent := 0, mantissa := (15587/8192) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi232LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868302847/274862761984) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3545InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3545LocalValidity :
    LeafFacts leaf3545Box leaf3545Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3545Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431380992) }) = true
      norm_num [leaf3545Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3545CertificateValid :
    WideCertificateValid leaf3545Box leaf3545Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi232ValidityFacts
    leaf3545LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3545CoverageChecked :
    coverageCheck (innerAD leaf3545Box) leaf3545InnerLog = true := by
  rfl'

private theorem leaf3545InnerLogValid :
    leaf3545InnerLog.Valid 8 (innerAD leaf3545Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3545CoverageChecked

private noncomputable def leaf3545InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3545InputLogOnePlusV_eq :
    leaf3545InputLogOnePlusV = outerEnclosure 24
      (leaf3545Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3545RoundedFacts : LeafRoundedFacts 8
    leaf3545Certificate.logOnePlusV leaf3545InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3545InputLogOnePlusV_eq }

private noncomputable def leaf3545Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi232InputQChi innerPair100Input
    leaf3545InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3545LowerChecked :
    lowerCheck 24 leaf3545Box leaf3545Inputs = true := by
  rfl'

private theorem leaf3545CoversExact : CoversExact 8
    leaf3545Box leaf3545Certificate leaf3545InnerLog leaf3545Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi232RoundedFacts
    innerPair100RoundedFacts leaf3545RoundedFacts (by rfl)

private theorem leaf3545FlatSound : Sound leaf3545Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3545CertificateValid
    leaf3545InnerLogValid leaf3545CoversExact leaf3545LowerChecked

private noncomputable def leaf3546Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (57/256), chiHi := (115/512) }

private noncomputable def leaf3546Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484389/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137431416832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4052465381/2147483648) }, upper := { exponent := 0, mantissa := (243/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi231LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274868338687/274862833664) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3546InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf3546LocalValidity :
    LeafFacts leaf3546Box leaf3546Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3546Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137431416832) }) = true
      norm_num [leaf3546Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3546CertificateValid :
    WideCertificateValid leaf3546Box leaf3546Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi231ValidityFacts
    leaf3546LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3546CoverageChecked :
    coverageCheck (innerAD leaf3546Box) leaf3546InnerLog = true := by
  rfl'

private theorem leaf3546InnerLogValid :
    leaf3546InnerLog.Valid 8 (innerAD leaf3546Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf3546CoverageChecked

private noncomputable def leaf3546InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3546InputLogOnePlusV_eq :
    leaf3546InputLogOnePlusV = outerEnclosure 24
      (leaf3546Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3546RoundedFacts : LeafRoundedFacts 8
    leaf3546Certificate.logOnePlusV leaf3546InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3546InputLogOnePlusV_eq }

private noncomputable def leaf3546Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi231InputQChi innerPair103Input
    leaf3546InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3546LowerChecked :
    lowerCheck 24 leaf3546Box leaf3546Inputs = true := by
  rfl'

private theorem leaf3546CoversExact : CoversExact 8
    leaf3546Box leaf3546Certificate leaf3546InnerLog leaf3546Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi231RoundedFacts
    innerPair103RoundedFacts leaf3546RoundedFacts (by rfl)

private theorem leaf3546FlatSound : Sound leaf3546Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3546CertificateValid
    leaf3546InnerLogValid leaf3546CoversExact leaf3546LowerChecked

private noncomputable def leaf3547Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (115/512), chiHi := (29/128) }

private noncomputable def leaf3547Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484391/2147483648) }, vSqrt := { lower := (65527/65536), upper := (5090256365/5090050048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4069176039/2147483648) }, upper := { exponent := 0, mantissa := (61/32) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi232LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (10180306413/10180100096) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3547InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3547LocalValidity :
    LeafFacts leaf3547Box leaf3547Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3547Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (5090256365/5090050048) }) = true
      norm_num [leaf3547Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3547CertificateValid :
    WideCertificateValid leaf3547Box leaf3547Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi232ValidityFacts
    leaf3547LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3547CoverageChecked :
    coverageCheck (innerAD leaf3547Box) leaf3547InnerLog = true := by
  rfl'

private theorem leaf3547InnerLogValid :
    leaf3547InnerLog.Valid 8 (innerAD leaf3547Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3547CoverageChecked

private noncomputable def leaf3547InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3547InputLogOnePlusV_eq :
    leaf3547InputLogOnePlusV = outerEnclosure 24
      (leaf3547Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3547RoundedFacts : LeafRoundedFacts 8
    leaf3547Certificate.logOnePlusV leaf3547InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3547InputLogOnePlusV_eq }

private noncomputable def leaf3547Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi232InputQChi innerPair100Input
    leaf3547InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3547LowerChecked :
    lowerCheck 24 leaf3547Box leaf3547Inputs = true := by
  rfl'

private theorem leaf3547CoversExact : CoversExact 8
    leaf3547Box leaf3547Certificate leaf3547InnerLog leaf3547Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi232RoundedFacts
    innerPair100RoundedFacts leaf3547RoundedFacts (by rfl)

private theorem leaf3547FlatSound : Sound leaf3547Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3547CertificateValid
    leaf3547InnerLogValid leaf3547CoversExact leaf3547LowerChecked

private noncomputable def leaf3548Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3548Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742447/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431310848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2031524147/1073741824) }, upper := { exponent := 0, mantissa := (31311/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868232703/274862621696) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3548InnerLog : WideLogData :=
  innerPair525Data

set_option maxRecDepth 1000000 in
private theorem leaf3548LocalValidity :
    LeafFacts leaf3548Box leaf3548Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3548Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431310848) }) = true
      norm_num [leaf3548Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3548CertificateValid :
    WideCertificateValid leaf3548Box leaf3548Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi199ValidityFacts
    leaf3548LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3548CoverageChecked :
    coverageCheck (innerAD leaf3548Box) leaf3548InnerLog = true := by
  rfl'

private theorem leaf3548InnerLogValid :
    leaf3548InnerLog.Valid 8 (innerAD leaf3548Box) :=
  wideLogDataValid_of_cachedCheck endpoint259PositiveFacts
    endpoint260PositiveFacts.valid leaf3548CoverageChecked

private noncomputable def leaf3548InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629423/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3548InputLogOnePlusV_eq :
    leaf3548InputLogOnePlusV = outerEnclosure 24
      (leaf3548Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3548RoundedFacts : LeafRoundedFacts 8
    leaf3548Certificate.logOnePlusV leaf3548InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3548InputLogOnePlusV_eq }

private noncomputable def leaf3548Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi199InputQChi innerPair525Input
    leaf3548InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3548LowerChecked :
    lowerCheck 24 leaf3548Box leaf3548Inputs = true := by
  rfl'

private theorem leaf3548CoversExact : CoversExact 8
    leaf3548Box leaf3548Certificate leaf3548InnerLog leaf3548Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi199RoundedFacts
    innerPair525RoundedFacts leaf3548RoundedFacts (by rfl)

private theorem leaf3548FlatSound : Sound leaf3548Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3548CertificateValid
    leaf3548InnerLogValid leaf3548CoversExact leaf3548LowerChecked

private noncomputable def leaf3549Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (29/128), chiHi := (117/512) }

private noncomputable def leaf3549Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484389/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431345664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4070683277/2147483648) }, upper := { exponent := 0, mantissa := (31243/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi233LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868267519/274862691328) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3549InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3549LocalValidity :
    LeafFacts leaf3549Box leaf3549Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3549Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431345664) }) = true
      norm_num [leaf3549Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3549CertificateValid :
    WideCertificateValid leaf3549Box leaf3549Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi233ValidityFacts
    leaf3549LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3549CoverageChecked :
    coverageCheck (innerAD leaf3549Box) leaf3549InnerLog = true := by
  rfl'

private theorem leaf3549InnerLogValid :
    leaf3549InnerLog.Valid 8 (innerAD leaf3549Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3549CoverageChecked

private noncomputable def leaf3549InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3549InputLogOnePlusV_eq :
    leaf3549InputLogOnePlusV = outerEnclosure 24
      (leaf3549Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3549RoundedFacts : LeafRoundedFacts 8
    leaf3549Certificate.logOnePlusV leaf3549InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3549InputLogOnePlusV_eq }

private noncomputable def leaf3549Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi233InputQChi innerPair100Input
    leaf3549InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3549LowerChecked :
    lowerCheck 24 leaf3549Box leaf3549Inputs = true := by
  rfl'

private theorem leaf3549CoversExact : CoversExact 8
    leaf3549Box leaf3549Certificate leaf3549InnerLog leaf3549Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi233RoundedFacts
    innerPair100RoundedFacts leaf3549RoundedFacts (by rfl)

private theorem leaf3549FlatSound : Sound leaf3549Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3549CertificateValid
    leaf3549InnerLogValid leaf3549CoversExact leaf3549LowerChecked

private noncomputable def leaf3550Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (117/512), chiHi := (59/256) }

private noncomputable def leaf3550Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484391/2147483648) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162085376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4087262871/2147483648) }, upper := { exponent := 0, mantissa := (15685/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi234LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324546833/18324170752) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3550InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3550LocalValidity :
    LeafFacts leaf3550Box leaf3550Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3550Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162085376) }) = true
      norm_num [leaf3550Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3550CertificateValid :
    WideCertificateValid leaf3550Box leaf3550Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi234ValidityFacts
    leaf3550LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3550CoverageChecked :
    coverageCheck (innerAD leaf3550Box) leaf3550InnerLog = true := by
  rfl'

private theorem leaf3550InnerLogValid :
    leaf3550InnerLog.Valid 8 (innerAD leaf3550Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3550CoverageChecked

private noncomputable def leaf3550InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629425/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3550InputLogOnePlusV_eq :
    leaf3550InputLogOnePlusV = outerEnclosure 24
      (leaf3550Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3550RoundedFacts : LeafRoundedFacts 8
    leaf3550Certificate.logOnePlusV leaf3550InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3550InputLogOnePlusV_eq }

private noncomputable def leaf3550Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi234InputQChi innerPair100Input
    leaf3550InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3550LowerChecked :
    lowerCheck 24 leaf3550Box leaf3550Inputs = true := by
  rfl'

private theorem leaf3550CoversExact : CoversExact 8
    leaf3550Box leaf3550Certificate leaf3550InnerLog leaf3550Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi234RoundedFacts
    innerPair100RoundedFacts leaf3550RoundedFacts (by rfl)

private theorem leaf3550FlatSound : Sound leaf3550Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3550CertificateValid
    leaf3550InnerLogValid leaf3550CoversExact leaf3550LowerChecked

private noncomputable def leaf3551Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3551Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742449/1073741824) }, vSqrt := { lower := (8191/8192), upper := (188012205/188004352) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2048038209/1073741824) }, upper := { exponent := 0, mantissa := (7891/4096) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (376016557/376008704) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3551InnerLog : WideLogData :=
  innerPair526Data

set_option maxRecDepth 1000000 in
private theorem leaf3551LocalValidity :
    LeafFacts leaf3551Box leaf3551Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3551Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (188012205/188004352) }) = true
      norm_num [leaf3551Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3551CertificateValid :
    WideCertificateValid leaf3551Box leaf3551Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi200ValidityFacts
    leaf3551LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3551CoverageChecked :
    coverageCheck (innerAD leaf3551Box) leaf3551InnerLog = true := by
  rfl'

private theorem leaf3551InnerLogValid :
    leaf3551InnerLog.Valid 8 (innerAD leaf3551Box) :=
  wideLogDataValid_of_cachedCheck endpoint261PositiveFacts
    endpoint262PositiveFacts.valid leaf3551CoverageChecked

private noncomputable def leaf3551InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3551InputLogOnePlusV_eq :
    leaf3551InputLogOnePlusV = outerEnclosure 24
      (leaf3551Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3551RoundedFacts : LeafRoundedFacts 8
    leaf3551Certificate.logOnePlusV leaf3551InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3551InputLogOnePlusV_eq }

private noncomputable def leaf3551Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi200InputQChi innerPair526Input
    leaf3551InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3551LowerChecked :
    lowerCheck 24 leaf3551Box leaf3551Inputs = true := by
  rfl'

private theorem leaf3551CoversExact : CoversExact 8
    leaf3551Box leaf3551Certificate leaf3551InnerLog leaf3551Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi200RoundedFacts
    innerPair526RoundedFacts leaf3551RoundedFacts (by rfl)

private theorem leaf3551FlatSound : Sound leaf3551Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3551CertificateValid
    leaf3551InnerLogValid leaf3551CoversExact leaf3551LowerChecked

private noncomputable def leaf3552Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3552Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742451/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431150592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2051904595/1073741824) }, upper := { exponent := 0, mantissa := (3953/2048) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868072447/274862301184) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3552InnerLog : WideLogData :=
  innerPair527Data

set_option maxRecDepth 1000000 in
private theorem leaf3552LocalValidity :
    LeafFacts leaf3552Box leaf3552Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3552Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431150592) }) = true
      norm_num [leaf3552Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3552CertificateValid :
    WideCertificateValid leaf3552Box leaf3552Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi200ValidityFacts
    leaf3552LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3552CoverageChecked :
    coverageCheck (innerAD leaf3552Box) leaf3552InnerLog = true := by
  rfl'

private theorem leaf3552InnerLogValid :
    leaf3552InnerLog.Valid 8 (innerAD leaf3552Box) :=
  wideLogDataValid_of_cachedCheck endpoint263PositiveFacts
    endpoint264PositiveFacts.valid leaf3552CoverageChecked

private noncomputable def leaf3552InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3552InputLogOnePlusV_eq :
    leaf3552InputLogOnePlusV = outerEnclosure 24
      (leaf3552Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3552RoundedFacts : LeafRoundedFacts 8
    leaf3552Certificate.logOnePlusV leaf3552InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3552InputLogOnePlusV_eq }

private noncomputable def leaf3552Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi200InputQChi innerPair527Input
    leaf3552InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3552LowerChecked :
    lowerCheck 24 leaf3552Box leaf3552Inputs = true := by
  rfl'

private theorem leaf3552CoversExact : CoversExact 8
    leaf3552Box leaf3552Certificate leaf3552InnerLog leaf3552Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi200RoundedFacts
    innerPair527RoundedFacts leaf3552RoundedFacts (by rfl)

private theorem leaf3552FlatSound : Sound leaf3552Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3552CertificateValid
    leaf3552InnerLogValid leaf3552CoversExact leaf3552LowerChecked

private noncomputable def leaf3553Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (29/128), chiHi := (117/512) }

private noncomputable def leaf3553Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484391/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431315712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4078284987/2147483648) }, upper := { exponent := 0, mantissa := (62603/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi233LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868237567/274862631424) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3553InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3553LocalValidity :
    LeafFacts leaf3553Box leaf3553Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3553Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431315712) }) = true
      norm_num [leaf3553Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3553CertificateValid :
    WideCertificateValid leaf3553Box leaf3553Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi233ValidityFacts
    leaf3553LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3553CoverageChecked :
    coverageCheck (innerAD leaf3553Box) leaf3553InnerLog = true := by
  rfl'

private theorem leaf3553InnerLogValid :
    leaf3553InnerLog.Valid 8 (innerAD leaf3553Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3553CoverageChecked

private noncomputable def leaf3553InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629423/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3553InputLogOnePlusV_eq :
    leaf3553InputLogOnePlusV = outerEnclosure 24
      (leaf3553Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3553RoundedFacts : LeafRoundedFacts 8
    leaf3553Certificate.logOnePlusV leaf3553InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3553InputLogOnePlusV_eq }

private noncomputable def leaf3553Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi233InputQChi innerPair100Input
    leaf3553InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3553LowerChecked :
    lowerCheck 24 leaf3553Box leaf3553Inputs = true := by
  rfl'

private theorem leaf3553CoversExact : CoversExact 8
    leaf3553Box leaf3553Certificate leaf3553InnerLog leaf3553Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi233RoundedFacts
    innerPair100RoundedFacts leaf3553RoundedFacts (by rfl)

private theorem leaf3553FlatSound : Sound leaf3553Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3553CertificateValid
    leaf3553InnerLogValid leaf3553CoversExact leaf3553LowerChecked

private noncomputable def leaf3554Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (117/512), chiHi := (59/256) }

private noncomputable def leaf3554Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484393/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431250432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4094930113/2147483648) }, upper := { exponent := 0, mantissa := (31429/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi234LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868172287/274862500864) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3554InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3554LocalValidity :
    LeafFacts leaf3554Box leaf3554Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3554Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431250432) }) = true
      norm_num [leaf3554Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3554CertificateValid :
    WideCertificateValid leaf3554Box leaf3554Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi234ValidityFacts
    leaf3554LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3554CoverageChecked :
    coverageCheck (innerAD leaf3554Box) leaf3554InnerLog = true := by
  rfl'

private theorem leaf3554InnerLogValid :
    leaf3554InnerLog.Valid 8 (innerAD leaf3554Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3554CoverageChecked

private noncomputable def leaf3554InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3554InputLogOnePlusV_eq :
    leaf3554InputLogOnePlusV = outerEnclosure 24
      (leaf3554Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3554RoundedFacts : LeafRoundedFacts 8
    leaf3554Certificate.logOnePlusV leaf3554InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3554InputLogOnePlusV_eq }

private noncomputable def leaf3554Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi234InputQChi innerPair100Input
    leaf3554InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3554LowerChecked :
    lowerCheck 24 leaf3554Box leaf3554Inputs = true := by
  rfl'

private theorem leaf3554CoversExact : CoversExact 8
    leaf3554Box leaf3554Certificate leaf3554InnerLog leaf3554Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi234RoundedFacts
    innerPair100RoundedFacts leaf3554RoundedFacts (by rfl)

private theorem leaf3554FlatSound : Sound leaf3554Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3554CertificateValid
    leaf3554InnerLogValid leaf3554CoversExact leaf3554LowerChecked

private noncomputable def leaf3555Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (29/128), chiHi := (117/512) }

private noncomputable def leaf3555Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484393/2147483648) }, vSqrt := { lower := (65527/65536), upper := (1616904963/1616838656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4085886697/2147483648) }, upper := { exponent := 0, mantissa := (245/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi233LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (3233743619/3233677312) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3555InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3555LocalValidity :
    LeafFacts leaf3555Box leaf3555Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3555Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (1616904963/1616838656) }) = true
      norm_num [leaf3555Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3555CertificateValid :
    WideCertificateValid leaf3555Box leaf3555Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi233ValidityFacts
    leaf3555LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3555CoverageChecked :
    coverageCheck (innerAD leaf3555Box) leaf3555InnerLog = true := by
  rfl'

private theorem leaf3555InnerLogValid :
    leaf3555InnerLog.Valid 8 (innerAD leaf3555Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3555CoverageChecked

private noncomputable def leaf3555InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629425/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3555InputLogOnePlusV_eq :
    leaf3555InputLogOnePlusV = outerEnclosure 24
      (leaf3555Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3555RoundedFacts : LeafRoundedFacts 8
    leaf3555Certificate.logOnePlusV leaf3555InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3555InputLogOnePlusV_eq }

private noncomputable def leaf3555Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi233InputQChi innerPair100Input
    leaf3555InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3555LowerChecked :
    lowerCheck 24 leaf3555Box leaf3555Inputs = true := by
  rfl'

private theorem leaf3555CoversExact : CoversExact 8
    leaf3555Box leaf3555Certificate leaf3555InnerLog leaf3555Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi233RoundedFacts
    innerPair100RoundedFacts leaf3555RoundedFacts (by rfl)

private theorem leaf3555FlatSound : Sound leaf3555Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3555CertificateValid
    leaf3555InnerLogValid leaf3555CoversExact leaf3555LowerChecked

private noncomputable def leaf3556Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (117/512), chiHi := (59/256) }

private noncomputable def leaf3556Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484395/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137431220224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4102597355/2147483648) }, upper := { exponent := 0, mantissa := (123/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi234LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274868142079/274862440448) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3556InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3556LocalValidity :
    LeafFacts leaf3556Box leaf3556Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3556Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137431220224) }) = true
      norm_num [leaf3556Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3556CertificateValid :
    WideCertificateValid leaf3556Box leaf3556Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi234ValidityFacts
    leaf3556LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3556CoverageChecked :
    coverageCheck (innerAD leaf3556Box) leaf3556InnerLog = true := by
  rfl'

private theorem leaf3556InnerLogValid :
    leaf3556InnerLog.Valid 8 (innerAD leaf3556Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3556CoverageChecked

private noncomputable def leaf3556InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3556InputLogOnePlusV_eq :
    leaf3556InputLogOnePlusV = outerEnclosure 24
      (leaf3556Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3556RoundedFacts : LeafRoundedFacts 8
    leaf3556Certificate.logOnePlusV leaf3556InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3556InputLogOnePlusV_eq }

private noncomputable def leaf3556Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi234InputQChi innerPair100Input
    leaf3556InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3556LowerChecked :
    lowerCheck 24 leaf3556Box leaf3556Inputs = true := by
  rfl'

private theorem leaf3556CoversExact : CoversExact 8
    leaf3556Box leaf3556Certificate leaf3556InnerLog leaf3556Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi234RoundedFacts
    innerPair100RoundedFacts leaf3556RoundedFacts (by rfl)

private theorem leaf3556FlatSound : Sound leaf3556Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3556CertificateValid
    leaf3556InnerLogValid leaf3556CoversExact leaf3556LowerChecked

private noncomputable def leaf3557Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (59/256), chiHi := (119/512) }

private noncomputable def leaf3557Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484395/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431185152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4111575239/2147483648) }, upper := { exponent := 0, mantissa := (63113/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi235LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868107007/274862370304) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3557InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3557LocalValidity :
    LeafFacts leaf3557Box leaf3557Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3557Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431185152) }) = true
      norm_num [leaf3557Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3557CertificateValid :
    WideCertificateValid leaf3557Box leaf3557Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi235ValidityFacts
    leaf3557LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3557CoverageChecked :
    coverageCheck (innerAD leaf3557Box) leaf3557InnerLog = true := by
  rfl'

private theorem leaf3557InnerLogValid :
    leaf3557InnerLog.Valid 8 (innerAD leaf3557Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3557CoverageChecked

private noncomputable def leaf3557InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3557InputLogOnePlusV_eq :
    leaf3557InputLogOnePlusV = outerEnclosure 24
      (leaf3557Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3557RoundedFacts : LeafRoundedFacts 8
    leaf3557Certificate.logOnePlusV leaf3557InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3557InputLogOnePlusV_eq }

private noncomputable def leaf3557Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi235InputQChi innerPair100Input
    leaf3557InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3557LowerChecked :
    lowerCheck 24 leaf3557Box leaf3557Inputs = true := by
  rfl'

private theorem leaf3557CoversExact : CoversExact 8
    leaf3557Box leaf3557Certificate leaf3557InnerLog leaf3557Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi235RoundedFacts
    innerPair100RoundedFacts leaf3557RoundedFacts (by rfl)

private theorem leaf3557FlatSound : Sound leaf3557Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3557CertificateValid
    leaf3557InnerLogValid leaf3557CoversExact leaf3557LowerChecked

private noncomputable def leaf3558Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (119/512), chiHi := (15/64) }

private noncomputable def leaf3558Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484397/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431119872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4128220365/2147483648) }, upper := { exponent := 0, mantissa := (7921/4096) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi236LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868041727/274862239744) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3558InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3558LocalValidity :
    LeafFacts leaf3558Box leaf3558Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3558Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431119872) }) = true
      norm_num [leaf3558Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3558CertificateValid :
    WideCertificateValid leaf3558Box leaf3558Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi236ValidityFacts
    leaf3558LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3558CoverageChecked :
    coverageCheck (innerAD leaf3558Box) leaf3558InnerLog = true := by
  rfl'

private theorem leaf3558InnerLogValid :
    leaf3558InnerLog.Valid 8 (innerAD leaf3558Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3558CoverageChecked

private noncomputable def leaf3558InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3558InputLogOnePlusV_eq :
    leaf3558InputLogOnePlusV = outerEnclosure 24
      (leaf3558Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3558RoundedFacts : LeafRoundedFacts 8
    leaf3558Certificate.logOnePlusV leaf3558InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3558InputLogOnePlusV_eq }

private noncomputable def leaf3558Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi236InputQChi innerPair100Input
    leaf3558InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3558LowerChecked :
    lowerCheck 24 leaf3558Box leaf3558Inputs = true := by
  rfl'

private theorem leaf3558CoversExact : CoversExact 8
    leaf3558Box leaf3558Certificate leaf3558InnerLog leaf3558Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi236RoundedFacts
    innerPair100RoundedFacts leaf3558RoundedFacts (by rfl)

private theorem leaf3558FlatSound : Sound leaf3558Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3558CertificateValid
    leaf3558InnerLogValid leaf3558CoversExact leaf3558LowerChecked

private noncomputable def leaf3559Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (59/256), chiHi := (119/512) }

private noncomputable def leaf3559Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484397/2147483648) }, vSqrt := { lower := (65527/65536), upper := (45812307285/45810384896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4119308013/2147483648) }, upper := { exponent := 0, mantissa := (247/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi235LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (91622692181/91620769792) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3559InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3559LocalValidity :
    LeafFacts leaf3559Box leaf3559Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3559Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (45812307285/45810384896) }) = true
      norm_num [leaf3559Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3559CertificateValid :
    WideCertificateValid leaf3559Box leaf3559Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi235ValidityFacts
    leaf3559LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3559CoverageChecked :
    coverageCheck (innerAD leaf3559Box) leaf3559InnerLog = true := by
  rfl'

private theorem leaf3559InnerLogValid :
    leaf3559InnerLog.Valid 8 (innerAD leaf3559Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3559CoverageChecked

private noncomputable def leaf3559InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3559InputLogOnePlusV_eq :
    leaf3559InputLogOnePlusV = outerEnclosure 24
      (leaf3559Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3559RoundedFacts : LeafRoundedFacts 8
    leaf3559Certificate.logOnePlusV leaf3559InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3559InputLogOnePlusV_eq }

private noncomputable def leaf3559Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi235InputQChi innerPair100Input
    leaf3559InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3559LowerChecked :
    lowerCheck 24 leaf3559Box leaf3559Inputs = true := by
  rfl'

private theorem leaf3559CoversExact : CoversExact 8
    leaf3559Box leaf3559Certificate leaf3559InnerLog leaf3559Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi235RoundedFacts
    innerPair100RoundedFacts leaf3559RoundedFacts (by rfl)

private theorem leaf3559FlatSound : Sound leaf3559Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3559CertificateValid
    leaf3559InnerLogValid leaf3559CoversExact leaf3559LowerChecked

private noncomputable def leaf3560Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (119/512), chiHi := (15/64) }

private noncomputable def leaf3560Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484399/2147483648) }, vSqrt := { lower := (65527/65536), upper := (137436921855/137431089152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (4136018671/2147483648) }, upper := { exponent := 0, mantissa := (31/16) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi236LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (274868011007/274862178304) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3560InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3560LocalValidity :
    LeafFacts leaf3560Box leaf3560Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3560Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (137436921855/137431089152) }) = true
      norm_num [leaf3560Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3560CertificateValid :
    WideCertificateValid leaf3560Box leaf3560Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi236ValidityFacts
    leaf3560LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3560CoverageChecked :
    coverageCheck (innerAD leaf3560Box) leaf3560InnerLog = true := by
  rfl'

private theorem leaf3560InnerLogValid :
    leaf3560InnerLog.Valid 8 (innerAD leaf3560Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3560CoverageChecked

private noncomputable def leaf3560InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3560InputLogOnePlusV_eq :
    leaf3560InputLogOnePlusV = outerEnclosure 24
      (leaf3560Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3560RoundedFacts : LeafRoundedFacts 8
    leaf3560Certificate.logOnePlusV leaf3560InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3560InputLogOnePlusV_eq }

private noncomputable def leaf3560Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi236InputQChi innerPair100Input
    leaf3560InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3560LowerChecked :
    lowerCheck 24 leaf3560Box leaf3560Inputs = true := by
  rfl'

private theorem leaf3560CoversExact : CoversExact 8
    leaf3560Box leaf3560Certificate leaf3560InnerLog leaf3560Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi236RoundedFacts
    innerPair100RoundedFacts leaf3560RoundedFacts (by rfl)

private theorem leaf3560FlatSound : Sound leaf3560Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3560CertificateValid
    leaf3560InnerLogValid leaf3560CoversExact leaf3560LowerChecked

private noncomputable def component72Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component72Node0_sound : Sound component72Node0Box :=
  sound_of_literal_split component72Node0Box leaf3516Box leaf3517Box
    .k (249/64) (by rfl) (by rfl)
    leaf3516FlatSound leaf3517FlatSound

private noncomputable def component72Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component72Node1_sound : Sound component72Node1Box :=
  sound_of_literal_split component72Node1Box leaf3518Box leaf3519Box
    .k (249/64) (by rfl) (by rfl)
    leaf3518FlatSound leaf3519FlatSound

private noncomputable def component72Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component72Node2_sound : Sound component72Node2Box :=
  sound_of_literal_split component72Node2Box component72Node0Box component72Node1Box
    .chi (57/256) (by rfl) (by rfl)
    component72Node0_sound component72Node1_sound

private noncomputable def component72Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component72Node3_sound : Sound component72Node3Box :=
  sound_of_literal_split component72Node3Box leaf3520Box leaf3521Box
    .k (251/64) (by rfl) (by rfl)
    leaf3520FlatSound leaf3521FlatSound

private noncomputable def component72Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component72Node4_sound : Sound component72Node4Box :=
  sound_of_literal_split component72Node4Box leaf3522Box leaf3523Box
    .k (251/64) (by rfl) (by rfl)
    leaf3522FlatSound leaf3523FlatSound

private noncomputable def component72Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component72Node5_sound : Sound component72Node5Box :=
  sound_of_literal_split component72Node5Box component72Node3Box component72Node4Box
    .chi (57/256) (by rfl) (by rfl)
    component72Node3_sound component72Node4_sound

private noncomputable def component72Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component72Node6_sound : Sound component72Node6Box :=
  sound_of_literal_split component72Node6Box component72Node2Box component72Node5Box
    .k (125/32) (by rfl) (by rfl)
    component72Node2_sound component72Node5_sound

private noncomputable def component72Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component72Node7_sound : Sound component72Node7Box :=
  sound_of_literal_split component72Node7Box leaf3524Box leaf3525Box
    .k (249/64) (by rfl) (by rfl)
    leaf3524FlatSound leaf3525FlatSound

private noncomputable def component72Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component72Node8_sound : Sound component72Node8Box :=
  sound_of_literal_split component72Node8Box leaf3526Box leaf3527Box
    .k (249/64) (by rfl) (by rfl)
    leaf3526FlatSound leaf3527FlatSound

private noncomputable def component72Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component72Node9_sound : Sound component72Node9Box :=
  sound_of_literal_split component72Node9Box component72Node7Box component72Node8Box
    .chi (59/256) (by rfl) (by rfl)
    component72Node7_sound component72Node8_sound

private noncomputable def component72Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component72Node10_sound : Sound component72Node10Box :=
  sound_of_literal_split component72Node10Box leaf3528Box leaf3529Box
    .k (251/64) (by rfl) (by rfl)
    leaf3528FlatSound leaf3529FlatSound

private noncomputable def component72Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component72Node11_sound : Sound component72Node11Box :=
  sound_of_literal_split component72Node11Box leaf3530Box leaf3531Box
    .k (251/64) (by rfl) (by rfl)
    leaf3530FlatSound leaf3531FlatSound

private noncomputable def component72Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component72Node12_sound : Sound component72Node12Box :=
  sound_of_literal_split component72Node12Box component72Node10Box component72Node11Box
    .chi (59/256) (by rfl) (by rfl)
    component72Node10_sound component72Node11_sound

private noncomputable def component72Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component72Node13_sound : Sound component72Node13Box :=
  sound_of_literal_split component72Node13Box component72Node9Box component72Node12Box
    .k (125/32) (by rfl) (by rfl)
    component72Node9_sound component72Node12_sound

private noncomputable def component72Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component72Node14_sound : Sound component72Node14Box :=
  sound_of_literal_split component72Node14Box component72Node6Box component72Node13Box
    .chi (29/128) (by rfl) (by rfl)
    component72Node6_sound component72Node13_sound

private noncomputable def component72Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component72Node15_sound : Sound component72Node15Box :=
  sound_of_literal_split component72Node15Box leaf3532Box leaf3533Box
    .chi (113/512) (by rfl) (by rfl)
    leaf3532FlatSound leaf3533FlatSound

private noncomputable def component72Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component72Node16_sound : Sound component72Node16Box :=
  sound_of_literal_split component72Node16Box leaf3534Box leaf3535Box
    .chi (113/512) (by rfl) (by rfl)
    leaf3534FlatSound leaf3535FlatSound

private noncomputable def component72Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component72Node17_sound : Sound component72Node17Box :=
  sound_of_literal_split component72Node17Box component72Node15Box component72Node16Box
    .k (253/64) (by rfl) (by rfl)
    component72Node15_sound component72Node16_sound

private noncomputable def component72Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component72Node18_sound : Sound component72Node18Box :=
  sound_of_literal_split component72Node18Box leaf3536Box leaf3537Box
    .chi (115/512) (by rfl) (by rfl)
    leaf3536FlatSound leaf3537FlatSound

private noncomputable def component72Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component72Node19_sound : Sound component72Node19Box :=
  sound_of_literal_split component72Node19Box leaf3538Box leaf3539Box
    .chi (115/512) (by rfl) (by rfl)
    leaf3538FlatSound leaf3539FlatSound

private noncomputable def component72Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component72Node20_sound : Sound component72Node20Box :=
  sound_of_literal_split component72Node20Box component72Node18Box component72Node19Box
    .k (253/64) (by rfl) (by rfl)
    component72Node18_sound component72Node19_sound

private noncomputable def component72Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component72Node21_sound : Sound component72Node21Box :=
  sound_of_literal_split component72Node21Box component72Node17Box component72Node20Box
    .chi (57/256) (by rfl) (by rfl)
    component72Node17_sound component72Node20_sound

private noncomputable def component72Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component72Node22_sound : Sound component72Node22Box :=
  sound_of_literal_split component72Node22Box leaf3540Box leaf3541Box
    .chi (113/512) (by rfl) (by rfl)
    leaf3540FlatSound leaf3541FlatSound

private noncomputable def component72Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component72Node23_sound : Sound component72Node23Box :=
  sound_of_literal_split component72Node23Box leaf3542Box leaf3543Box
    .chi (113/512) (by rfl) (by rfl)
    leaf3542FlatSound leaf3543FlatSound

private noncomputable def component72Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component72Node24_sound : Sound component72Node24Box :=
  sound_of_literal_split component72Node24Box component72Node22Box component72Node23Box
    .k (255/64) (by rfl) (by rfl)
    component72Node22_sound component72Node23_sound

private noncomputable def component72Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component72Node25_sound : Sound component72Node25Box :=
  sound_of_literal_split component72Node25Box leaf3544Box leaf3545Box
    .chi (115/512) (by rfl) (by rfl)
    leaf3544FlatSound leaf3545FlatSound

private noncomputable def component72Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component72Node26_sound : Sound component72Node26Box :=
  sound_of_literal_split component72Node26Box leaf3546Box leaf3547Box
    .chi (115/512) (by rfl) (by rfl)
    leaf3546FlatSound leaf3547FlatSound

private noncomputable def component72Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component72Node27_sound : Sound component72Node27Box :=
  sound_of_literal_split component72Node27Box component72Node25Box component72Node26Box
    .k (255/64) (by rfl) (by rfl)
    component72Node25_sound component72Node26_sound

private noncomputable def component72Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component72Node28_sound : Sound component72Node28Box :=
  sound_of_literal_split component72Node28Box component72Node24Box component72Node27Box
    .chi (57/256) (by rfl) (by rfl)
    component72Node24_sound component72Node27_sound

private noncomputable def component72Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component72Node29_sound : Sound component72Node29Box :=
  sound_of_literal_split component72Node29Box component72Node21Box component72Node28Box
    .k (127/32) (by rfl) (by rfl)
    component72Node21_sound component72Node28_sound

private noncomputable def component72Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component72Node30_sound : Sound component72Node30Box :=
  sound_of_literal_split component72Node30Box leaf3549Box leaf3550Box
    .chi (117/512) (by rfl) (by rfl)
    leaf3549FlatSound leaf3550FlatSound

private noncomputable def component72Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component72Node31_sound : Sound component72Node31Box :=
  sound_of_literal_split component72Node31Box leaf3548Box component72Node30Box
    .k (253/64) (by rfl) (by rfl)
    leaf3548FlatSound component72Node30_sound

private noncomputable def component72Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component72Node32_sound : Sound component72Node32Box :=
  sound_of_literal_split component72Node32Box leaf3551Box leaf3552Box
    .k (253/64) (by rfl) (by rfl)
    leaf3551FlatSound leaf3552FlatSound

private noncomputable def component72Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component72Node33_sound : Sound component72Node33Box :=
  sound_of_literal_split component72Node33Box component72Node31Box component72Node32Box
    .chi (59/256) (by rfl) (by rfl)
    component72Node31_sound component72Node32_sound

private noncomputable def component72Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component72Node34_sound : Sound component72Node34Box :=
  sound_of_literal_split component72Node34Box leaf3553Box leaf3554Box
    .chi (117/512) (by rfl) (by rfl)
    leaf3553FlatSound leaf3554FlatSound

private noncomputable def component72Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component72Node35_sound : Sound component72Node35Box :=
  sound_of_literal_split component72Node35Box leaf3555Box leaf3556Box
    .chi (117/512) (by rfl) (by rfl)
    leaf3555FlatSound leaf3556FlatSound

private noncomputable def component72Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component72Node36_sound : Sound component72Node36Box :=
  sound_of_literal_split component72Node36Box component72Node34Box component72Node35Box
    .k (255/64) (by rfl) (by rfl)
    component72Node34_sound component72Node35_sound

private noncomputable def component72Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component72Node37_sound : Sound component72Node37Box :=
  sound_of_literal_split component72Node37Box leaf3557Box leaf3558Box
    .chi (119/512) (by rfl) (by rfl)
    leaf3557FlatSound leaf3558FlatSound

private noncomputable def component72Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component72Node38_sound : Sound component72Node38Box :=
  sound_of_literal_split component72Node38Box leaf3559Box leaf3560Box
    .chi (119/512) (by rfl) (by rfl)
    leaf3559FlatSound leaf3560FlatSound

private noncomputable def component72Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component72Node39_sound : Sound component72Node39Box :=
  sound_of_literal_split component72Node39Box component72Node37Box component72Node38Box
    .k (255/64) (by rfl) (by rfl)
    component72Node37_sound component72Node38_sound

private noncomputable def component72Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component72Node40_sound : Sound component72Node40Box :=
  sound_of_literal_split component72Node40Box component72Node36Box component72Node39Box
    .chi (59/256) (by rfl) (by rfl)
    component72Node36_sound component72Node39_sound

private noncomputable def component72Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component72Node41_sound : Sound component72Node41Box :=
  sound_of_literal_split component72Node41Box component72Node33Box component72Node40Box
    .k (127/32) (by rfl) (by rfl)
    component72Node33_sound component72Node40_sound

private noncomputable def component72Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component72Node42_sound : Sound component72Node42Box :=
  sound_of_literal_split component72Node42Box component72Node29Box component72Node41Box
    .chi (29/128) (by rfl) (by rfl)
    component72Node29_sound component72Node41_sound

noncomputable def component72Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
theorem component72_sound : Sound component72Box :=
  sound_of_literal_split component72Box component72Node14Box component72Node42Box
    .k (63/16) (by rfl) (by rfl)
    component72Node14_sound component72Node42_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
