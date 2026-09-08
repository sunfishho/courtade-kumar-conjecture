import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedFlatTopologyCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheChiBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheGlobal
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheInnerBatch6
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

private noncomputable def leaf3349Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3349Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486541312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1853801391/1073741824) }, upper := { exponent := 0, mantissa := (28585/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973925683/54973082624) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf3349InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3349LocalValidity :
    LeafFacts leaf3349Box leaf3349Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3349Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486541312) }) = true
      norm_num [leaf3349Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3349CertificateValid :
    WideCertificateValid leaf3349Box leaf3349Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi187ValidityFacts
    leaf3349LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3349CoverageChecked :
    coverageCheck (innerAD leaf3349Box) leaf3349InnerLog = true := by
  rfl'

private theorem leaf3349InnerLogValid :
    leaf3349InnerLog.Valid 8 (innerAD leaf3349Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3349CoverageChecked

private noncomputable def leaf3349InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814669/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3349InputLogOnePlusV_eq :
    leaf3349InputLogOnePlusV = outerEnclosure 24
      (leaf3349Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3349RoundedFacts : LeafRoundedFacts 8
    leaf3349Certificate.logOnePlusV leaf3349InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3349InputLogOnePlusV_eq }

private noncomputable def leaf3349Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi187InputQChi innerPair64Input
    leaf3349InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3349LowerChecked :
    lowerCheck 24 leaf3349Box leaf3349Inputs = true := by
  rfl'

private theorem leaf3349CoversExact : CoversExact 8
    leaf3349Box leaf3349Certificate leaf3349InnerLog leaf3349Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi187RoundedFacts
    innerPair64RoundedFacts leaf3349RoundedFacts (by rfl)

private theorem leaf3349FlatSound : Sound leaf3349Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3349CertificateValid
    leaf3349InnerLogValid leaf3349CoversExact leaf3349LowerChecked

private noncomputable def leaf3350Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3350Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810893824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1856946925/1073741824) }, upper := { exponent := 0, mantissa := (14317/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623201109/91621787648) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf3350InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3350LocalValidity :
    LeafFacts leaf3350Box leaf3350Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3350Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810893824) }) = true
      norm_num [leaf3350Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3350CertificateValid :
    WideCertificateValid leaf3350Box leaf3350Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi187ValidityFacts
    leaf3350LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3350CoverageChecked :
    coverageCheck (innerAD leaf3350Box) leaf3350InnerLog = true := by
  rfl'

private theorem leaf3350InnerLogValid :
    leaf3350InnerLog.Valid 8 (innerAD leaf3350Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3350CoverageChecked

private noncomputable def leaf3350InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3350InputLogOnePlusV_eq :
    leaf3350InputLogOnePlusV = outerEnclosure 24
      (leaf3350Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3350RoundedFacts : LeafRoundedFacts 8
    leaf3350Certificate.logOnePlusV leaf3350InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3350InputLogOnePlusV_eq }

private noncomputable def leaf3350Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi187InputQChi innerPair64Input
    leaf3350InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3350LowerChecked :
    lowerCheck 24 leaf3350Box leaf3350Inputs = true := by
  rfl'

private theorem leaf3350CoversExact : CoversExact 8
    leaf3350Box leaf3350Certificate leaf3350InnerLog leaf3350Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi187RoundedFacts
    innerPair64RoundedFacts leaf3350RoundedFacts (by rfl)

private theorem leaf3350FlatSound : Sound leaf3350Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3350CertificateValid
    leaf3350InnerLogValid leaf3350CoversExact leaf3350LowerChecked

private noncomputable def leaf3351Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3351Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432579072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1870053325/1073741824) }, upper := { exponent := 0, mantissa := (14417/8192) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869500927/274865158144) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf3351InnerLog : WideLogData :=
  innerPair488Data

set_option maxRecDepth 1000000 in
private theorem leaf3351LocalValidity :
    LeafFacts leaf3351Box leaf3351Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3351Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432579072) }) = true
      norm_num [leaf3351Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3351CertificateValid :
    WideCertificateValid leaf3351Box leaf3351Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi188ValidityFacts
    leaf3351LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3351CoverageChecked :
    coverageCheck (innerAD leaf3351Box) leaf3351InnerLog = true := by
  rfl'

private theorem leaf3351InnerLogValid :
    leaf3351InnerLog.Valid 8 (innerAD leaf3351Box) :=
  wideLogDataValid_of_cachedCheck endpoint213PositiveFacts
    endpoint60PositiveFacts.valid leaf3351CoverageChecked

private noncomputable def leaf3351InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3351InputLogOnePlusV_eq :
    leaf3351InputLogOnePlusV = outerEnclosure 24
      (leaf3351Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3351RoundedFacts : LeafRoundedFacts 8
    leaf3351Certificate.logOnePlusV leaf3351InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3351InputLogOnePlusV_eq }

private noncomputable def leaf3351Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi188InputQChi innerPair488Input
    leaf3351InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3351LowerChecked :
    lowerCheck 24 leaf3351Box leaf3351Inputs = true := by
  rfl'

private theorem leaf3351CoversExact : CoversExact 8
    leaf3351Box leaf3351Certificate leaf3351InnerLog leaf3351Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi188RoundedFacts
    innerPair488RoundedFacts leaf3351RoundedFacts (by rfl)

private theorem leaf3351FlatSound : Sound leaf3351Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3351CertificateValid
    leaf3351InnerLogValid leaf3351CoversExact leaf3351LowerChecked

private noncomputable def leaf3352Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3352Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432553472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1873264391/1073741824) }, upper := { exponent := 0, mantissa := (7221/4096) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869475327/274865106944) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf3352InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3352LocalValidity :
    LeafFacts leaf3352Box leaf3352Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3352Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432553472) }) = true
      norm_num [leaf3352Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3352CertificateValid :
    WideCertificateValid leaf3352Box leaf3352Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi188ValidityFacts
    leaf3352LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3352CoverageChecked :
    coverageCheck (innerAD leaf3352Box) leaf3352InnerLog = true := by
  rfl'

private theorem leaf3352InnerLogValid :
    leaf3352InnerLog.Valid 8 (innerAD leaf3352Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3352CoverageChecked

private noncomputable def leaf3352InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3352InputLogOnePlusV_eq :
    leaf3352InputLogOnePlusV = outerEnclosure 24
      (leaf3352Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3352RoundedFacts : LeafRoundedFacts 8
    leaf3352Certificate.logOnePlusV leaf3352InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3352InputLogOnePlusV_eq }

private noncomputable def leaf3352Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi188InputQChi innerPair430Input
    leaf3352InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3352LowerChecked :
    lowerCheck 24 leaf3352Box leaf3352Inputs = true := by
  rfl'

private theorem leaf3352CoversExact : CoversExact 8
    leaf3352Box leaf3352Certificate leaf3352InnerLog leaf3352Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi188RoundedFacts
    innerPair430RoundedFacts leaf3352RoundedFacts (by rfl)

private theorem leaf3352FlatSound : Sound leaf3352Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3352CertificateValid
    leaf3352InnerLogValid leaf3352CoversExact leaf3352LowerChecked

private noncomputable def leaf3353Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3353Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3196207485/3196108288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1860092459/1073741824) }, upper := { exponent := 0, mantissa := (28683/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6392315773/6392216576) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf3353InnerLog : WideLogData :=
  innerPair501Data

set_option maxRecDepth 1000000 in
private theorem leaf3353LocalValidity :
    LeafFacts leaf3353Box leaf3353Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3353Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3196207485/3196108288) }) = true
      norm_num [leaf3353Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3353CertificateValid :
    WideCertificateValid leaf3353Box leaf3353Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi187ValidityFacts
    leaf3353LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3353CoverageChecked :
    coverageCheck (innerAD leaf3353Box) leaf3353InnerLog = true := by
  rfl'

private theorem leaf3353InnerLogValid :
    leaf3353InnerLog.Valid 8 (innerAD leaf3353Box) :=
  wideLogDataValid_of_cachedCheck endpoint224PositiveFacts
    endpoint225PositiveFacts.valid leaf3353CoverageChecked

private noncomputable def leaf3353InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3353InputLogOnePlusV_eq :
    leaf3353InputLogOnePlusV = outerEnclosure 24
      (leaf3353Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3353RoundedFacts : LeafRoundedFacts 8
    leaf3353Certificate.logOnePlusV leaf3353InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3353InputLogOnePlusV_eq }

private noncomputable def leaf3353Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi187InputQChi innerPair501Input
    leaf3353InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3353LowerChecked :
    lowerCheck 24 leaf3353Box leaf3353Inputs = true := by
  rfl'

private theorem leaf3353CoversExact : CoversExact 8
    leaf3353Box leaf3353Certificate leaf3353InnerLog leaf3353Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi187RoundedFacts
    innerPair501RoundedFacts leaf3353RoundedFacts (by rfl)

private theorem leaf3353FlatSound : Sound leaf3353Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3353CertificateValid
    leaf3353InnerLogValid leaf3353CoversExact leaf3353LowerChecked

private noncomputable def leaf3354Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (503/128), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3354Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484751/2147483648) }, vSqrt := { lower := (8191/8192), upper := (18324918545/18324352512) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3726508851/2147483648) }, upper := { exponent := 0, mantissa := (57415/32768) } }, logOuter := sk241LogOuterCertificate, logK := sk241LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (36649271057/36648705024) } }, logDArg := sk241LogDArgCertificate }

private noncomputable def leaf3354InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3354LocalValidity :
    LeafFacts leaf3354Box leaf3354Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3354Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (18324918545/18324352512) }) = true
      norm_num [leaf3354Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3354CertificateValid :
    WideCertificateValid leaf3354Box leaf3354Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk241ValidityFacts chi187ValidityFacts
    leaf3354LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3354CoverageChecked :
    coverageCheck (innerAD leaf3354Box) leaf3354InnerLog = true := by
  rfl'

private theorem leaf3354InnerLogValid :
    leaf3354InnerLog.Valid 8 (innerAD leaf3354Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3354CoverageChecked

private noncomputable def leaf3354InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3354InputLogOnePlusV_eq :
    leaf3354InputLogOnePlusV = outerEnclosure 24
      (leaf3354Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3354RoundedFacts : LeafRoundedFacts 8
    leaf3354Certificate.logOnePlusV leaf3354InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3354InputLogOnePlusV_eq }

private noncomputable def leaf3354Inputs : Inputs :=
  inputsOfCaches globalInput sk241RoundedInputs
    chi187InputQChi innerPair430Input
    leaf3354InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3354LowerChecked :
    lowerCheck 24 leaf3354Box leaf3354Inputs = true := by
  rfl'

private theorem leaf3354CoversExact : CoversExact 8
    leaf3354Box leaf3354Certificate leaf3354InnerLog leaf3354Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk241RoundedFacts chi187RoundedFacts
    innerPair430RoundedFacts leaf3354RoundedFacts (by rfl)

private theorem leaf3354FlatSound : Sound leaf3354Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3354CertificateValid
    leaf3354InnerLogValid leaf3354CoversExact leaf3354LowerChecked

private noncomputable def leaf3355Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (503/128), kHi := (63/16), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3355Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484753/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274865262592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3729654385/2147483648) }, upper := { exponent := 0, mantissa := (7183/4096) } }, logOuter := sk242LogOuterCertificate, logK := sk242LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549739040767/549730525184) } }, logDArg := sk242LogDArgCertificate }

private noncomputable def leaf3355InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3355LocalValidity :
    LeafFacts leaf3355Box leaf3355Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3355Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274865262592) }) = true
      norm_num [leaf3355Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3355CertificateValid :
    WideCertificateValid leaf3355Box leaf3355Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk242ValidityFacts chi187ValidityFacts
    leaf3355LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3355CoverageChecked :
    coverageCheck (innerAD leaf3355Box) leaf3355InnerLog = true := by
  rfl'

private theorem leaf3355InnerLogValid :
    leaf3355InnerLog.Valid 8 (innerAD leaf3355Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3355CoverageChecked

private noncomputable def leaf3355InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3355InputLogOnePlusV_eq :
    leaf3355InputLogOnePlusV = outerEnclosure 24
      (leaf3355Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3355RoundedFacts : LeafRoundedFacts 8
    leaf3355Certificate.logOnePlusV leaf3355InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3355InputLogOnePlusV_eq }

private noncomputable def leaf3355Inputs : Inputs :=
  inputsOfCaches globalInput sk242RoundedInputs
    chi187InputQChi innerPair430Input
    leaf3355InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3355LowerChecked :
    lowerCheck 24 leaf3355Box leaf3355Inputs = true := by
  rfl'

private theorem leaf3355CoversExact : CoversExact 8
    leaf3355Box leaf3355Certificate leaf3355InnerLog leaf3355Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk242RoundedFacts chi187RoundedFacts
    innerPair430RoundedFacts leaf3355RoundedFacts (by rfl)

private theorem leaf3355FlatSound : Sound leaf3355Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3355CertificateValid
    leaf3355InnerLogValid leaf3355CoversExact leaf3355LowerChecked

private noncomputable def leaf3356Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3356Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810842624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1876475457/1073741824) }, upper := { exponent := 0, mantissa := (14467/8192) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623149909/91621685248) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf3356InnerLog : WideLogData :=
  innerPair502Data

set_option maxRecDepth 1000000 in
private theorem leaf3356LocalValidity :
    LeafFacts leaf3356Box leaf3356Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3356Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810842624) }) = true
      norm_num [leaf3356Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3356CertificateValid :
    WideCertificateValid leaf3356Box leaf3356Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi188ValidityFacts
    leaf3356LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3356CoverageChecked :
    coverageCheck (innerAD leaf3356Box) leaf3356InnerLog = true := by
  rfl'

private theorem leaf3356InnerLogValid :
    leaf3356InnerLog.Valid 8 (innerAD leaf3356Box) :=
  wideLogDataValid_of_cachedCheck endpoint226PositiveFacts
    endpoint227PositiveFacts.valid leaf3356CoverageChecked

private noncomputable def leaf3356InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3356InputLogOnePlusV_eq :
    leaf3356InputLogOnePlusV = outerEnclosure 24
      (leaf3356Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3356RoundedFacts : LeafRoundedFacts 8
    leaf3356Certificate.logOnePlusV leaf3356InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3356InputLogOnePlusV_eq }

private noncomputable def leaf3356Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi188InputQChi innerPair502Input
    leaf3356InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3356LowerChecked :
    lowerCheck 24 leaf3356Box leaf3356Inputs = true := by
  rfl'

private theorem leaf3356CoversExact : CoversExact 8
    leaf3356Box leaf3356Certificate leaf3356InnerLog leaf3356Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi188RoundedFacts
    innerPair502RoundedFacts leaf3356RoundedFacts (by rfl)

private theorem leaf3356FlatSound : Sound leaf3356Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3356CertificateValid
    leaf3356InnerLogValid leaf3356CoversExact leaf3356LowerChecked

private noncomputable def leaf3357Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (503/128), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3357Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484753/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274865030144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3759405913/2147483648) }, upper := { exponent := 0, mantissa := (28959/16384) } }, logOuter := sk241LogOuterCertificate, logK := sk241LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738808319/549730060288) } }, logDArg := sk241LogDArgCertificate }

private noncomputable def leaf3357InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3357LocalValidity :
    LeafFacts leaf3357Box leaf3357Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3357Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274865030144) }) = true
      norm_num [leaf3357Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3357CertificateValid :
    WideCertificateValid leaf3357Box leaf3357Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk241ValidityFacts chi188ValidityFacts
    leaf3357LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3357CoverageChecked :
    coverageCheck (innerAD leaf3357Box) leaf3357InnerLog = true := by
  rfl'

private theorem leaf3357InnerLogValid :
    leaf3357InnerLog.Valid 8 (innerAD leaf3357Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3357CoverageChecked

private noncomputable def leaf3357InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907337/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3357InputLogOnePlusV_eq :
    leaf3357InputLogOnePlusV = outerEnclosure 24
      (leaf3357Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3357RoundedFacts : LeafRoundedFacts 8
    leaf3357Certificate.logOnePlusV leaf3357InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3357InputLogOnePlusV_eq }

private noncomputable def leaf3357Inputs : Inputs :=
  inputsOfCaches globalInput sk241RoundedInputs
    chi188InputQChi innerPair78Input
    leaf3357InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3357LowerChecked :
    lowerCheck 24 leaf3357Box leaf3357Inputs = true := by
  rfl'

private theorem leaf3357CoversExact : CoversExact 8
    leaf3357Box leaf3357Certificate leaf3357InnerLog leaf3357Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk241RoundedFacts chi188RoundedFacts
    innerPair78RoundedFacts leaf3357RoundedFacts (by rfl)

private theorem leaf3357FlatSound : Sound leaf3357Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3357CertificateValid
    leaf3357InnerLogValid leaf3357CoversExact leaf3357LowerChecked

private noncomputable def leaf3358Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (503/128), kHi := (63/16), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3358Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484755/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274865004544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3762616979/2147483648) }, upper := { exponent := 0, mantissa := (3623/2048) } }, logOuter := sk242LogOuterCertificate, logK := sk242LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738782719/549730009088) } }, logDArg := sk242LogDArgCertificate }

private noncomputable def leaf3358InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3358LocalValidity :
    LeafFacts leaf3358Box leaf3358Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3358Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274865004544) }) = true
      norm_num [leaf3358Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3358CertificateValid :
    WideCertificateValid leaf3358Box leaf3358Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk242ValidityFacts chi188ValidityFacts
    leaf3358LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3358CoverageChecked :
    coverageCheck (innerAD leaf3358Box) leaf3358InnerLog = true := by
  rfl'

private theorem leaf3358InnerLogValid :
    leaf3358InnerLog.Valid 8 (innerAD leaf3358Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3358CoverageChecked

private noncomputable def leaf3358InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3358InputLogOnePlusV_eq :
    leaf3358InputLogOnePlusV = outerEnclosure 24
      (leaf3358Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3358RoundedFacts : LeafRoundedFacts 8
    leaf3358Certificate.logOnePlusV leaf3358InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3358InputLogOnePlusV_eq }

private noncomputable def leaf3358Inputs : Inputs :=
  inputsOfCaches globalInput sk242RoundedInputs
    chi188InputQChi innerPair78Input
    leaf3358InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3358LowerChecked :
    lowerCheck 24 leaf3358Box leaf3358Inputs = true := by
  rfl'

private theorem leaf3358CoversExact : CoversExact 8
    leaf3358Box leaf3358Certificate leaf3358InnerLog leaf3358Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk242RoundedFacts chi188RoundedFacts
    innerPair78RoundedFacts leaf3358RoundedFacts (by rfl)

private theorem leaf3358FlatSound : Sound leaf3358Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3358CertificateValid
    leaf3358InnerLogValid leaf3358CoversExact leaf3358LowerChecked

private noncomputable def leaf3359Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3359Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432451584) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1886305259/1073741824) }, upper := { exponent := 0, mantissa := (29083/16384) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869373439/274864903168) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf3359InnerLog : WideLogData :=
  innerPair458Data

set_option maxRecDepth 1000000 in
private theorem leaf3359LocalValidity :
    LeafFacts leaf3359Box leaf3359Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3359Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432451584) }) = true
      norm_num [leaf3359Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3359CertificateValid :
    WideCertificateValid leaf3359Box leaf3359Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi193ValidityFacts
    leaf3359LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3359CoverageChecked :
    coverageCheck (innerAD leaf3359Box) leaf3359InnerLog = true := by
  rfl'

private theorem leaf3359InnerLogValid :
    leaf3359InnerLog.Valid 8 (innerAD leaf3359Box) :=
  wideLogDataValid_of_cachedCheck endpoint178PositiveFacts
    endpoint219PositiveFacts.valid leaf3359CoverageChecked

private noncomputable def leaf3359InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3359InputLogOnePlusV_eq :
    leaf3359InputLogOnePlusV = outerEnclosure 24
      (leaf3359Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3359RoundedFacts : LeafRoundedFacts 8
    leaf3359Certificate.logOnePlusV leaf3359InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3359InputLogOnePlusV_eq }

private noncomputable def leaf3359Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi193InputQChi innerPair458Input
    leaf3359InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3359LowerChecked :
    lowerCheck 24 leaf3359Box leaf3359Inputs = true := by
  rfl'

private theorem leaf3359CoversExact : CoversExact 8
    leaf3359Box leaf3359Certificate leaf3359InnerLog leaf3359Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi193RoundedFacts
    innerPair458RoundedFacts leaf3359RoundedFacts (by rfl)

private theorem leaf3359FlatSound : Sound leaf3359Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3359CertificateValid
    leaf3359InnerLogValid leaf3359CoversExact leaf3359LowerChecked

private noncomputable def leaf3360Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3360Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432425472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1889581857/1073741824) }, upper := { exponent := 0, mantissa := (14567/8192) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869347327/274864850944) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf3360InnerLog : WideLogData :=
  innerPair503Data

set_option maxRecDepth 1000000 in
private theorem leaf3360LocalValidity :
    LeafFacts leaf3360Box leaf3360Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3360Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432425472) }) = true
      norm_num [leaf3360Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3360CertificateValid :
    WideCertificateValid leaf3360Box leaf3360Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi193ValidityFacts
    leaf3360LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3360CoverageChecked :
    coverageCheck (innerAD leaf3360Box) leaf3360InnerLog = true := by
  rfl'

private theorem leaf3360InnerLogValid :
    leaf3360InnerLog.Valid 8 (innerAD leaf3360Box) :=
  wideLogDataValid_of_cachedCheck endpoint228PositiveFacts
    endpoint229PositiveFacts.valid leaf3360CoverageChecked

private noncomputable def leaf3360InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3360InputLogOnePlusV_eq :
    leaf3360InputLogOnePlusV = outerEnclosure 24
      (leaf3360Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3360RoundedFacts : LeafRoundedFacts 8
    leaf3360Certificate.logOnePlusV leaf3360InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3360InputLogOnePlusV_eq }

private noncomputable def leaf3360Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi193InputQChi innerPair503Input
    leaf3360InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3360LowerChecked :
    lowerCheck 24 leaf3360Box leaf3360Inputs = true := by
  rfl'

private theorem leaf3360CoversExact : CoversExact 8
    leaf3360Box leaf3360Certificate leaf3360InnerLog leaf3360Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi193RoundedFacts
    innerPair503RoundedFacts leaf3360RoundedFacts (by rfl)

private theorem leaf3360FlatSound : Sound leaf3360Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3360CertificateValid
    leaf3360InnerLogValid leaf3360CoversExact leaf3360LowerChecked

private noncomputable def leaf3361Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (249/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3361Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432324096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1902557193/1073741824) }, upper := { exponent := 0, mantissa := (7333/4096) } }, logOuter := sk233LogOuterCertificate, logK := sk233LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869245951/274864648192) } }, logDArg := sk233LogDArgCertificate }

private noncomputable def leaf3361InnerLog : WideLogData :=
  innerPair491Data

set_option maxRecDepth 1000000 in
private theorem leaf3361LocalValidity :
    LeafFacts leaf3361Box leaf3361Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3361Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432324096) }) = true
      norm_num [leaf3361Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3361CertificateValid :
    WideCertificateValid leaf3361Box leaf3361Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk233ValidityFacts chi194ValidityFacts
    leaf3361LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3361CoverageChecked :
    coverageCheck (innerAD leaf3361Box) leaf3361InnerLog = true := by
  rfl'

private theorem leaf3361InnerLogValid :
    leaf3361InnerLog.Valid 8 (innerAD leaf3361Box) :=
  wideLogDataValid_of_cachedCheck endpoint216PositiveFacts
    endpoint184PositiveFacts.valid leaf3361CoverageChecked

private noncomputable def leaf3361InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3361InputLogOnePlusV_eq :
    leaf3361InputLogOnePlusV = outerEnclosure 24
      (leaf3361Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3361RoundedFacts : LeafRoundedFacts 8
    leaf3361Certificate.logOnePlusV leaf3361InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3361InputLogOnePlusV_eq }

private noncomputable def leaf3361Inputs : Inputs :=
  inputsOfCaches globalInput sk233RoundedInputs
    chi194InputQChi innerPair491Input
    leaf3361InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3361LowerChecked :
    lowerCheck 24 leaf3361Box leaf3361Inputs = true := by
  rfl'

private theorem leaf3361CoversExact : CoversExact 8
    leaf3361Box leaf3361Certificate leaf3361InnerLog leaf3361Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk233RoundedFacts chi194RoundedFacts
    innerPair491RoundedFacts leaf3361RoundedFacts (by rfl)

private theorem leaf3361FlatSound : Sound leaf3361Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3361CertificateValid
    leaf3361InnerLogValid leaf3361CoversExact leaf3361LowerChecked

private noncomputable def leaf3362Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (249/64), kHi := (125/32), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3362Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810765824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1905899323/1073741824) }, upper := { exponent := 0, mantissa := (3673/2048) } }, logOuter := sk234LogOuterCertificate, logK := sk234LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623073109/91621531648) } }, logDArg := sk234LogDArgCertificate }

private noncomputable def leaf3362InnerLog : WideLogData :=
  innerPair504Data

set_option maxRecDepth 1000000 in
private theorem leaf3362LocalValidity :
    LeafFacts leaf3362Box leaf3362Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3362Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810765824) }) = true
      norm_num [leaf3362Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3362CertificateValid :
    WideCertificateValid leaf3362Box leaf3362Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk234ValidityFacts chi194ValidityFacts
    leaf3362LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3362CoverageChecked :
    coverageCheck (innerAD leaf3362Box) leaf3362InnerLog = true := by
  rfl'

private theorem leaf3362InnerLogValid :
    leaf3362InnerLog.Valid 8 (innerAD leaf3362Box) :=
  wideLogDataValid_of_cachedCheck endpoint230PositiveFacts
    endpoint231PositiveFacts.valid leaf3362CoverageChecked

private noncomputable def leaf3362InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3362InputLogOnePlusV_eq :
    leaf3362InputLogOnePlusV = outerEnclosure 24
      (leaf3362Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3362RoundedFacts : LeafRoundedFacts 8
    leaf3362Certificate.logOnePlusV leaf3362InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3362InputLogOnePlusV_eq }

private noncomputable def leaf3362Inputs : Inputs :=
  inputsOfCaches globalInput sk234RoundedInputs
    chi194InputQChi innerPair504Input
    leaf3362InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3362LowerChecked :
    lowerCheck 24 leaf3362Box leaf3362Inputs = true := by
  rfl'

private theorem leaf3362CoversExact : CoversExact 8
    leaf3362Box leaf3362Certificate leaf3362InnerLog leaf3362Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk234RoundedFacts chi194RoundedFacts
    innerPair504RoundedFacts leaf3362RoundedFacts (by rfl)

private theorem leaf3362FlatSound : Sound leaf3362Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3362CertificateValid
    leaf3362InnerLogValid leaf3362CoversExact leaf3362LowerChecked

private noncomputable def leaf3363Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3363Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486479872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1892858455/1073741824) }, upper := { exponent := 0, mantissa := (29185/16384) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973864243/54972959744) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf3363InnerLog : WideLogData :=
  innerPair505Data

set_option maxRecDepth 1000000 in
private theorem leaf3363LocalValidity :
    LeafFacts leaf3363Box leaf3363Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3363Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486479872) }) = true
      norm_num [leaf3363Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3363CertificateValid :
    WideCertificateValid leaf3363Box leaf3363Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi193ValidityFacts
    leaf3363LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3363CoverageChecked :
    coverageCheck (innerAD leaf3363Box) leaf3363InnerLog = true := by
  rfl'

private theorem leaf3363InnerLogValid :
    leaf3363InnerLog.Valid 8 (innerAD leaf3363Box) :=
  wideLogDataValid_of_cachedCheck endpoint232PositiveFacts
    endpoint233PositiveFacts.valid leaf3363CoverageChecked

private noncomputable def leaf3363InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629357/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3363InputLogOnePlusV_eq :
    leaf3363InputLogOnePlusV = outerEnclosure 24
      (leaf3363Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3363RoundedFacts : LeafRoundedFacts 8
    leaf3363Certificate.logOnePlusV leaf3363InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3363InputLogOnePlusV_eq }

private noncomputable def leaf3363Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi193InputQChi innerPair505Input
    leaf3363InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3363LowerChecked :
    lowerCheck 24 leaf3363Box leaf3363Inputs = true := by
  rfl'

private theorem leaf3363CoversExact : CoversExact 8
    leaf3363Box leaf3363Certificate leaf3363InnerLog leaf3363Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi193RoundedFacts
    innerPair505RoundedFacts leaf3363RoundedFacts (by rfl)

private theorem leaf3363FlatSound : Sound leaf3363Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3363CertificateValid
    leaf3363InnerLogValid leaf3363CoversExact leaf3363LowerChecked

private noncomputable def leaf3364Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (503/128), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3364Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484755/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864772608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3792302975/2147483648) }, upper := { exponent := 0, mantissa := (58421/32768) } }, logOuter := sk241LogOuterCertificate, logK := sk241LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738550783/549729545216) } }, logDArg := sk241LogDArgCertificate }

private noncomputable def leaf3364InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3364LocalValidity :
    LeafFacts leaf3364Box leaf3364Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3364Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864772608) }) = true
      norm_num [leaf3364Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3364CertificateValid :
    WideCertificateValid leaf3364Box leaf3364Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk241ValidityFacts chi193ValidityFacts
    leaf3364LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3364CoverageChecked :
    coverageCheck (innerAD leaf3364Box) leaf3364InnerLog = true := by
  rfl'

private theorem leaf3364InnerLogValid :
    leaf3364InnerLog.Valid 8 (innerAD leaf3364Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3364CoverageChecked

private noncomputable def leaf3364InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3364InputLogOnePlusV_eq :
    leaf3364InputLogOnePlusV = outerEnclosure 24
      (leaf3364Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3364RoundedFacts : LeafRoundedFacts 8
    leaf3364Certificate.logOnePlusV leaf3364InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3364InputLogOnePlusV_eq }

private noncomputable def leaf3364Inputs : Inputs :=
  inputsOfCaches globalInput sk241RoundedInputs
    chi193InputQChi innerPair71Input
    leaf3364InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3364LowerChecked :
    lowerCheck 24 leaf3364Box leaf3364Inputs = true := by
  rfl'

private theorem leaf3364CoversExact : CoversExact 8
    leaf3364Box leaf3364Certificate leaf3364InnerLog leaf3364Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk241RoundedFacts chi193RoundedFacts
    innerPair71RoundedFacts leaf3364RoundedFacts (by rfl)

private theorem leaf3364FlatSound : Sound leaf3364Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3364CertificateValid
    leaf3364InnerLogValid leaf3364CoversExact leaf3364LowerChecked

private noncomputable def leaf3365Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (503/128), kHi := (63/16), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3365Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484757/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864746496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3795579573/2147483648) }, upper := { exponent := 0, mantissa := (7309/4096) } }, logOuter := sk242LogOuterCertificate, logK := sk242LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738524671/549729492992) } }, logDArg := sk242LogDArgCertificate }

private noncomputable def leaf3365InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3365LocalValidity :
    LeafFacts leaf3365Box leaf3365Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3365Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864746496) }) = true
      norm_num [leaf3365Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3365CertificateValid :
    WideCertificateValid leaf3365Box leaf3365Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk242ValidityFacts chi193ValidityFacts
    leaf3365LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3365CoverageChecked :
    coverageCheck (innerAD leaf3365Box) leaf3365InnerLog = true := by
  rfl'

private theorem leaf3365InnerLogValid :
    leaf3365InnerLog.Valid 8 (innerAD leaf3365Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3365CoverageChecked

private noncomputable def leaf3365InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3365InputLogOnePlusV_eq :
    leaf3365InputLogOnePlusV = outerEnclosure 24
      (leaf3365Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3365RoundedFacts : LeafRoundedFacts 8
    leaf3365Certificate.logOnePlusV leaf3365InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3365InputLogOnePlusV_eq }

private noncomputable def leaf3365Inputs : Inputs :=
  inputsOfCaches globalInput sk242RoundedInputs
    chi193InputQChi innerPair71Input
    leaf3365InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3365LowerChecked :
    lowerCheck 24 leaf3365Box leaf3365Inputs = true := by
  rfl'

private theorem leaf3365CoversExact : CoversExact 8
    leaf3365Box leaf3365Certificate leaf3365InnerLog leaf3365Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk242RoundedFacts chi193RoundedFacts
    innerPair71RoundedFacts leaf3365RoundedFacts (by rfl)

private theorem leaf3365FlatSound : Sound leaf3365Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3365CertificateValid
    leaf3365InnerLogValid leaf3365CoversExact leaf3365LowerChecked

private noncomputable def leaf3366Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (251/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3366Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432270848) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1909241453/1073741824) }, upper := { exponent := 0, mantissa := (7359/4096) } }, logOuter := sk235LogOuterCertificate, logK := sk235LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869192703/274864541696) } }, logDArg := sk235LogDArgCertificate }

private noncomputable def leaf3366InnerLog : WideLogData :=
  innerPair209Data

set_option maxRecDepth 1000000 in
private theorem leaf3366LocalValidity :
    LeafFacts leaf3366Box leaf3366Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3366Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432270848) }) = true
      norm_num [leaf3366Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3366CertificateValid :
    WideCertificateValid leaf3366Box leaf3366Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk235ValidityFacts chi194ValidityFacts
    leaf3366LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3366CoverageChecked :
    coverageCheck (innerAD leaf3366Box) leaf3366InnerLog = true := by
  rfl'

private theorem leaf3366InnerLogValid :
    leaf3366InnerLog.Valid 8 (innerAD leaf3366Box) :=
  wideLogDataValid_of_cachedCheck endpoint63PositiveFacts
    endpoint67PositiveFacts.valid leaf3366CoverageChecked

private noncomputable def leaf3366InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3366InputLogOnePlusV_eq :
    leaf3366InputLogOnePlusV = outerEnclosure 24
      (leaf3366Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3366RoundedFacts : LeafRoundedFacts 8
    leaf3366Certificate.logOnePlusV leaf3366InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3366InputLogOnePlusV_eq }

private noncomputable def leaf3366Inputs : Inputs :=
  inputsOfCaches globalInput sk235RoundedInputs
    chi194InputQChi innerPair209Input
    leaf3366InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3366LowerChecked :
    lowerCheck 24 leaf3366Box leaf3366Inputs = true := by
  rfl'

private theorem leaf3366CoversExact : CoversExact 8
    leaf3366Box leaf3366Certificate leaf3366InnerLog leaf3366Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk235RoundedFacts chi194RoundedFacts
    innerPair209RoundedFacts leaf3366RoundedFacts (by rfl)

private theorem leaf3366FlatSound : Sound leaf3366Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3366CertificateValid
    leaf3366InnerLogValid leaf3366CoversExact leaf3366LowerChecked

private noncomputable def leaf3367Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (503/128), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3367Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484757/2147483648) }, vSqrt := { lower := (8191/8192), upper := (91624592725/91621505024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3825200037/2147483648) }, upper := { exponent := 0, mantissa := (14731/8192) } }, logOuter := sk241LogOuterCertificate, logK := sk241LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (183246097749/183243010048) } }, logDArg := sk241LogDArgCertificate }

private noncomputable def leaf3367InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3367LocalValidity :
    LeafFacts leaf3367Box leaf3367Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3367Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (91624592725/91621505024) }) = true
      norm_num [leaf3367Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3367CertificateValid :
    WideCertificateValid leaf3367Box leaf3367Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk241ValidityFacts chi194ValidityFacts
    leaf3367LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3367CoverageChecked :
    coverageCheck (innerAD leaf3367Box) leaf3367InnerLog = true := by
  rfl'

private theorem leaf3367InnerLogValid :
    leaf3367InnerLog.Valid 8 (innerAD leaf3367Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3367CoverageChecked

private noncomputable def leaf3367InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3367InputLogOnePlusV_eq :
    leaf3367InputLogOnePlusV = outerEnclosure 24
      (leaf3367Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3367RoundedFacts : LeafRoundedFacts 8
    leaf3367Certificate.logOnePlusV leaf3367InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3367InputLogOnePlusV_eq }

private noncomputable def leaf3367Inputs : Inputs :=
  inputsOfCaches globalInput sk241RoundedInputs
    chi194InputQChi innerPair71Input
    leaf3367InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3367LowerChecked :
    lowerCheck 24 leaf3367Box leaf3367Inputs = true := by
  rfl'

private theorem leaf3367CoversExact : CoversExact 8
    leaf3367Box leaf3367Certificate leaf3367InnerLog leaf3367Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk241RoundedFacts chi194RoundedFacts
    innerPair71RoundedFacts leaf3367RoundedFacts (by rfl)

private theorem leaf3367FlatSound : Sound leaf3367Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3367CertificateValid
    leaf3367InnerLogValid leaf3367CoversExact leaf3367LowerChecked

private noncomputable def leaf3368Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (503/128), kHi := (63/16), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3368Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484759/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864488448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3828542167/2147483648) }, upper := { exponent := 0, mantissa := (1843/1024) } }, logOuter := sk242LogOuterCertificate, logK := sk242LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738266623/549728976896) } }, logDArg := sk242LogDArgCertificate }

private noncomputable def leaf3368InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3368LocalValidity :
    LeafFacts leaf3368Box leaf3368Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3368Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864488448) }) = true
      norm_num [leaf3368Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3368CertificateValid :
    WideCertificateValid leaf3368Box leaf3368Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk242ValidityFacts chi194ValidityFacts
    leaf3368LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3368CoverageChecked :
    coverageCheck (innerAD leaf3368Box) leaf3368InnerLog = true := by
  rfl'

private theorem leaf3368InnerLogValid :
    leaf3368InnerLog.Valid 8 (innerAD leaf3368Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3368CoverageChecked

private noncomputable def leaf3368InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907341/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3368InputLogOnePlusV_eq :
    leaf3368InputLogOnePlusV = outerEnclosure 24
      (leaf3368Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3368RoundedFacts : LeafRoundedFacts 8
    leaf3368Certificate.logOnePlusV leaf3368InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3368InputLogOnePlusV_eq }

private noncomputable def leaf3368Inputs : Inputs :=
  inputsOfCaches globalInput sk242RoundedInputs
    chi194InputQChi innerPair71Input
    leaf3368InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3368LowerChecked :
    lowerCheck 24 leaf3368Box leaf3368Inputs = true := by
  rfl'

private theorem leaf3368CoversExact : CoversExact 8
    leaf3368Box leaf3368Certificate leaf3368InnerLog leaf3368Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk242RoundedFacts chi194RoundedFacts
    innerPair71RoundedFacts leaf3368RoundedFacts (by rfl)

private theorem leaf3368FlatSound : Sound leaf3368Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3368CertificateValid
    leaf3368InnerLogValid leaf3368CoversExact leaf3368LowerChecked

private noncomputable def leaf3369Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (3/16), chiHi := (97/512) }

private noncomputable def leaf3369Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484347/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432670976) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3732800327/2147483648) }, upper := { exponent := 0, mantissa := (57309/32768) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi221LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869592831/274865341952) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3369InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3369LocalValidity :
    LeafFacts leaf3369Box leaf3369Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3369Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432670976) }) = true
      norm_num [leaf3369Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3369CertificateValid :
    WideCertificateValid leaf3369Box leaf3369Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi221ValidityFacts
    leaf3369LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3369CoverageChecked :
    coverageCheck (innerAD leaf3369Box) leaf3369InnerLog = true := by
  rfl'

private theorem leaf3369InnerLogValid :
    leaf3369InnerLog.Valid 8 (innerAD leaf3369Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3369CoverageChecked

private noncomputable def leaf3369InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3369InputLogOnePlusV_eq :
    leaf3369InputLogOnePlusV = outerEnclosure 24
      (leaf3369Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3369RoundedFacts : LeafRoundedFacts 8
    leaf3369Certificate.logOnePlusV leaf3369InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3369InputLogOnePlusV_eq }

private noncomputable def leaf3369Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi221InputQChi innerPair64Input
    leaf3369InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3369LowerChecked :
    lowerCheck 24 leaf3369Box leaf3369Inputs = true := by
  rfl'

private theorem leaf3369CoversExact : CoversExact 8
    leaf3369Box leaf3369Certificate leaf3369InnerLog leaf3369Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi221RoundedFacts
    innerPair64RoundedFacts leaf3369RoundedFacts (by rfl)

private theorem leaf3369FlatSound : Sound leaf3369Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3369CertificateValid
    leaf3369InnerLogValid leaf3369CoversExact leaf3369LowerChecked

private noncomputable def leaf3370Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (97/512), chiHi := (49/256) }

private noncomputable def leaf3370Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484349/2147483648) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810868736) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3749314389/2147483648) }, upper := { exponent := 0, mantissa := (28781/16384) } }, logOuter := sk237LogOuterCertificate, logK := sk237LogKCertificate, logChi := chi222LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623176021/91621737472) } }, logDArg := sk237LogDArgCertificate }

private noncomputable def leaf3370InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3370LocalValidity :
    LeafFacts leaf3370Box leaf3370Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3370Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810868736) }) = true
      norm_num [leaf3370Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3370CertificateValid :
    WideCertificateValid leaf3370Box leaf3370Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk237ValidityFacts chi222ValidityFacts
    leaf3370LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3370CoverageChecked :
    coverageCheck (innerAD leaf3370Box) leaf3370InnerLog = true := by
  rfl'

private theorem leaf3370InnerLogValid :
    leaf3370InnerLog.Valid 8 (innerAD leaf3370Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3370CoverageChecked

private noncomputable def leaf3370InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf3370InputLogOnePlusV_eq :
    leaf3370InputLogOnePlusV = outerEnclosure 24
      (leaf3370Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3370RoundedFacts : LeafRoundedFacts 8
    leaf3370Certificate.logOnePlusV leaf3370InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3370InputLogOnePlusV_eq }

private noncomputable def leaf3370Inputs : Inputs :=
  inputsOfCaches globalInput sk237RoundedInputs
    chi222InputQChi innerPair430Input
    leaf3370InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3370LowerChecked :
    lowerCheck 24 leaf3370Box leaf3370Inputs = true := by
  rfl'

private theorem leaf3370CoversExact : CoversExact 8
    leaf3370Box leaf3370Certificate leaf3370InnerLog leaf3370Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk237RoundedFacts chi222RoundedFacts
    innerPair430RoundedFacts leaf3370RoundedFacts (by rfl)

private theorem leaf3370FlatSound : Sound leaf3370Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3370CertificateValid
    leaf3370InnerLogValid leaf3370CoversExact leaf3370LowerChecked

private noncomputable def leaf3371Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (3/16), chiHi := (97/512) }

private noncomputable def leaf3371Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484349/2147483648) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270294016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3739091397/2147483648) }, upper := { exponent := 0, mantissa := (28703/16384) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi221LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541063111/30540588032) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3371InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3371LocalValidity :
    LeafFacts leaf3371Box leaf3371Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3371Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270294016) }) = true
      norm_num [leaf3371Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3371CertificateValid :
    WideCertificateValid leaf3371Box leaf3371Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi221ValidityFacts
    leaf3371LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3371CoverageChecked :
    coverageCheck (innerAD leaf3371Box) leaf3371InnerLog = true := by
  rfl'

private theorem leaf3371InnerLogValid :
    leaf3371InnerLog.Valid 8 (innerAD leaf3371Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3371CoverageChecked

private noncomputable def leaf3371InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814671/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3371InputLogOnePlusV_eq :
    leaf3371InputLogOnePlusV = outerEnclosure 24
      (leaf3371Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3371RoundedFacts : LeafRoundedFacts 8
    leaf3371Certificate.logOnePlusV leaf3371InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3371InputLogOnePlusV_eq }

private noncomputable def leaf3371Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi221InputQChi innerPair430Input
    leaf3371InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3371LowerChecked :
    lowerCheck 24 leaf3371Box leaf3371Inputs = true := by
  rfl'

private theorem leaf3371CoversExact : CoversExact 8
    leaf3371Box leaf3371Certificate leaf3371InnerLog leaf3371Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi221RoundedFacts
    innerPair430RoundedFacts leaf3371RoundedFacts (by rfl)

private theorem leaf3371FlatSound : Sound leaf3371Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3371CertificateValid
    leaf3371InnerLogValid leaf3371CoversExact leaf3371LowerChecked

private noncomputable def leaf3372Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (97/512), chiHi := (49/256) }

private noncomputable def leaf3372Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484351/2147483648) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486516224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3755670991/2147483648) }, upper := { exponent := 0, mantissa := (14415/8192) } }, logOuter := sk238LogOuterCertificate, logK := sk238LogKCertificate, logChi := chi222LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973900595/54973032448) } }, logDArg := sk238LogDArgCertificate }

private noncomputable def leaf3372InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3372LocalValidity :
    LeafFacts leaf3372Box leaf3372Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3372Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486516224) }) = true
      norm_num [leaf3372Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3372CertificateValid :
    WideCertificateValid leaf3372Box leaf3372Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk238ValidityFacts chi222ValidityFacts
    leaf3372LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3372CoverageChecked :
    coverageCheck (innerAD leaf3372Box) leaf3372InnerLog = true := by
  rfl'

private theorem leaf3372InnerLogValid :
    leaf3372InnerLog.Valid 8 (innerAD leaf3372Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3372CoverageChecked

private noncomputable def leaf3372InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3372InputLogOnePlusV_eq :
    leaf3372InputLogOnePlusV = outerEnclosure 24
      (leaf3372Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3372RoundedFacts : LeafRoundedFacts 8
    leaf3372Certificate.logOnePlusV leaf3372InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3372InputLogOnePlusV_eq }

private noncomputable def leaf3372Inputs : Inputs :=
  inputsOfCaches globalInput sk238RoundedInputs
    chi222InputQChi innerPair430Input
    leaf3372InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3372LowerChecked :
    lowerCheck 24 leaf3372Box leaf3372Inputs = true := by
  rfl'

private theorem leaf3372CoversExact : CoversExact 8
    leaf3372Box leaf3372Certificate leaf3372InnerLog leaf3372Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk238RoundedFacts chi222RoundedFacts
    innerPair430RoundedFacts leaf3372RoundedFacts (by rfl)

private theorem leaf3372FlatSound : Sound leaf3372Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3372CertificateValid
    leaf3372InnerLogValid leaf3372CoversExact leaf3372LowerChecked

private noncomputable def leaf3373Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (505/128), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3373Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484757/2147483648) }, vSqrt := { lower := (8191/8192), upper := (91624592725/91621659648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3765828045/2147483648) }, upper := { exponent := 0, mantissa := (29009/16384) } }, logOuter := sk243LogOuterCertificate, logK := sk243LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (183246252373/183243319296) } }, logDArg := sk243LogDArgCertificate }

private noncomputable def leaf3373InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3373LocalValidity :
    LeafFacts leaf3373Box leaf3373Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3373Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (91624592725/91621659648) }) = true
      norm_num [leaf3373Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3373CertificateValid :
    WideCertificateValid leaf3373Box leaf3373Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk243ValidityFacts chi188ValidityFacts
    leaf3373LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3373CoverageChecked :
    coverageCheck (innerAD leaf3373Box) leaf3373InnerLog = true := by
  rfl'

private theorem leaf3373InnerLogValid :
    leaf3373InnerLog.Valid 8 (innerAD leaf3373Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3373CoverageChecked

private noncomputable def leaf3373InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3373InputLogOnePlusV_eq :
    leaf3373InputLogOnePlusV = outerEnclosure 24
      (leaf3373Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3373RoundedFacts : LeafRoundedFacts 8
    leaf3373Certificate.logOnePlusV leaf3373InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3373InputLogOnePlusV_eq }

private noncomputable def leaf3373Inputs : Inputs :=
  inputsOfCaches globalInput sk243RoundedInputs
    chi188InputQChi innerPair78Input
    leaf3373InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3373LowerChecked :
    lowerCheck 24 leaf3373Box leaf3373Inputs = true := by
  rfl'

private theorem leaf3373CoversExact : CoversExact 8
    leaf3373Box leaf3373Certificate leaf3373InnerLog leaf3373Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk243RoundedFacts chi188RoundedFacts
    innerPair78RoundedFacts leaf3373RoundedFacts (by rfl)

private theorem leaf3373FlatSound : Sound leaf3373Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3373CertificateValid
    leaf3373InnerLogValid leaf3373CoversExact leaf3373LowerChecked

private noncomputable def leaf3374Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (505/128), kHi := (253/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3374Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484759/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864953344) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3769039111/2147483648) }, upper := { exponent := 0, mantissa := (14517/8192) } }, logOuter := sk244LogOuterCertificate, logK := sk244LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738731519/549729906688) } }, logDArg := sk244LogDArgCertificate }

private noncomputable def leaf3374InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3374LocalValidity :
    LeafFacts leaf3374Box leaf3374Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3374Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864953344) }) = true
      norm_num [leaf3374Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3374CertificateValid :
    WideCertificateValid leaf3374Box leaf3374Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk244ValidityFacts chi188ValidityFacts
    leaf3374LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3374CoverageChecked :
    coverageCheck (innerAD leaf3374Box) leaf3374InnerLog = true := by
  rfl'

private theorem leaf3374InnerLogValid :
    leaf3374InnerLog.Valid 8 (innerAD leaf3374Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3374CoverageChecked

private noncomputable def leaf3374InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3374InputLogOnePlusV_eq :
    leaf3374InputLogOnePlusV = outerEnclosure 24
      (leaf3374Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3374RoundedFacts : LeafRoundedFacts 8
    leaf3374Certificate.logOnePlusV leaf3374InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3374InputLogOnePlusV_eq }

private noncomputable def leaf3374Inputs : Inputs :=
  inputsOfCaches globalInput sk244RoundedInputs
    chi188InputQChi innerPair78Input
    leaf3374InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3374LowerChecked :
    lowerCheck 24 leaf3374Box leaf3374Inputs = true := by
  rfl'

private theorem leaf3374CoversExact : CoversExact 8
    leaf3374Box leaf3374Certificate leaf3374InnerLog leaf3374Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk244RoundedFacts chi188RoundedFacts
    innerPair78RoundedFacts leaf3374RoundedFacts (by rfl)

private theorem leaf3374FlatSound : Sound leaf3374Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3374CertificateValid
    leaf3374InnerLogValid leaf3374CoversExact leaf3374LowerChecked

private noncomputable def leaf3375Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (507/128), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3375Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484761/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864927744) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3772250177/2147483648) }, upper := { exponent := 0, mantissa := (29059/16384) } }, logOuter := sk245LogOuterCertificate, logK := sk245LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738705919/549729855488) } }, logDArg := sk245LogDArgCertificate }

private noncomputable def leaf3375InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3375LocalValidity :
    LeafFacts leaf3375Box leaf3375Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3375Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864927744) }) = true
      norm_num [leaf3375Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3375CertificateValid :
    WideCertificateValid leaf3375Box leaf3375Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk245ValidityFacts chi188ValidityFacts
    leaf3375LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3375CoverageChecked :
    coverageCheck (innerAD leaf3375Box) leaf3375InnerLog = true := by
  rfl'

private theorem leaf3375InnerLogValid :
    leaf3375InnerLog.Valid 8 (innerAD leaf3375Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3375CoverageChecked

private noncomputable def leaf3375InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629351/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3375InputLogOnePlusV_eq :
    leaf3375InputLogOnePlusV = outerEnclosure 24
      (leaf3375Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3375RoundedFacts : LeafRoundedFacts 8
    leaf3375Certificate.logOnePlusV leaf3375InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3375InputLogOnePlusV_eq }

private noncomputable def leaf3375Inputs : Inputs :=
  inputsOfCaches globalInput sk245RoundedInputs
    chi188InputQChi innerPair78Input
    leaf3375InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3375LowerChecked :
    lowerCheck 24 leaf3375Box leaf3375Inputs = true := by
  rfl'

private theorem leaf3375CoversExact : CoversExact 8
    leaf3375Box leaf3375Certificate leaf3375InnerLog leaf3375Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk245RoundedFacts chi188RoundedFacts
    innerPair78RoundedFacts leaf3375RoundedFacts (by rfl)

private theorem leaf3375FlatSound : Sound leaf3375Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3375CertificateValid
    leaf3375InnerLogValid leaf3375CoversExact leaf3375LowerChecked

private noncomputable def leaf3376Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (507/128), kHi := (127/32), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3376Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484763/2147483648) }, vSqrt := { lower := (8191/8192), upper := (91624592725/91621634048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3775461243/2147483648) }, upper := { exponent := 0, mantissa := (7271/4096) } }, logOuter := sk246LogOuterCertificate, logK := sk246LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (183246226773/183243268096) } }, logDArg := sk246LogDArgCertificate }

private noncomputable def leaf3376InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3376LocalValidity :
    LeafFacts leaf3376Box leaf3376Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3376Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (91624592725/91621634048) }) = true
      norm_num [leaf3376Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3376CertificateValid :
    WideCertificateValid leaf3376Box leaf3376Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk246ValidityFacts chi188ValidityFacts
    leaf3376LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3376CoverageChecked :
    coverageCheck (innerAD leaf3376Box) leaf3376InnerLog = true := by
  rfl'

private theorem leaf3376InnerLogValid :
    leaf3376InnerLog.Valid 8 (innerAD leaf3376Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3376CoverageChecked

private noncomputable def leaf3376InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3376InputLogOnePlusV_eq :
    leaf3376InputLogOnePlusV = outerEnclosure 24
      (leaf3376Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3376RoundedFacts : LeafRoundedFacts 8
    leaf3376Certificate.logOnePlusV leaf3376InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3376InputLogOnePlusV_eq }

private noncomputable def leaf3376Inputs : Inputs :=
  inputsOfCaches globalInput sk246RoundedInputs
    chi188InputQChi innerPair78Input
    leaf3376InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3376LowerChecked :
    lowerCheck 24 leaf3376Box leaf3376Inputs = true := by
  rfl'

private theorem leaf3376CoversExact : CoversExact 8
    leaf3376Box leaf3376Certificate leaf3376InnerLog leaf3376Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk246RoundedFacts chi188RoundedFacts
    innerPair78RoundedFacts leaf3376RoundedFacts (by rfl)

private theorem leaf3376FlatSound : Sound leaf3376Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3376CertificateValid
    leaf3376InnerLogValid leaf3376CoversExact leaf3376LowerChecked

private noncomputable def leaf3377Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (3/16), chiHi := (97/512) }

private noncomputable def leaf3377Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484351/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432621312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3745382467/2147483648) }, upper := { exponent := 0, mantissa := (57503/32768) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi221LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869543167/274865242624) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3377InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3377LocalValidity :
    LeafFacts leaf3377Box leaf3377Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3377Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432621312) }) = true
      norm_num [leaf3377Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3377CertificateValid :
    WideCertificateValid leaf3377Box leaf3377Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi221ValidityFacts
    leaf3377LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3377CoverageChecked :
    coverageCheck (innerAD leaf3377Box) leaf3377InnerLog = true := by
  rfl'

private theorem leaf3377InnerLogValid :
    leaf3377InnerLog.Valid 8 (innerAD leaf3377Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3377CoverageChecked

private noncomputable def leaf3377InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3377InputLogOnePlusV_eq :
    leaf3377InputLogOnePlusV = outerEnclosure 24
      (leaf3377Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3377RoundedFacts : LeafRoundedFacts 8
    leaf3377Certificate.logOnePlusV leaf3377InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3377InputLogOnePlusV_eq }

private noncomputable def leaf3377Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi221InputQChi innerPair430Input
    leaf3377InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3377LowerChecked :
    lowerCheck 24 leaf3377Box leaf3377Inputs = true := by
  rfl'

private theorem leaf3377CoversExact : CoversExact 8
    leaf3377Box leaf3377Certificate leaf3377InnerLog leaf3377Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi221RoundedFacts
    innerPair430RoundedFacts leaf3377RoundedFacts (by rfl)

private theorem leaf3377FlatSound : Sound leaf3377Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3377CertificateValid
    leaf3377InnerLogValid leaf3377CoversExact leaf3377LowerChecked

private noncomputable def leaf3378Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (97/512), chiHi := (49/256) }

private noncomputable def leaf3378Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484353/2147483648) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432556032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3762027593/2147483648) }, upper := { exponent := 0, mantissa := (28879/16384) } }, logOuter := sk239LogOuterCertificate, logK := sk239LogKCertificate, logChi := chi222LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869477887/274865112064) } }, logDArg := sk239LogDArgCertificate }

private noncomputable def leaf3378InnerLog : WideLogData :=
  innerPair75Data

set_option maxRecDepth 1000000 in
private theorem leaf3378LocalValidity :
    LeafFacts leaf3378Box leaf3378Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3378Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432556032) }) = true
      norm_num [leaf3378Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3378CertificateValid :
    WideCertificateValid leaf3378Box leaf3378Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk239ValidityFacts chi222ValidityFacts
    leaf3378LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3378CoverageChecked :
    coverageCheck (innerAD leaf3378Box) leaf3378InnerLog = true := by
  rfl'

private theorem leaf3378InnerLogValid :
    leaf3378InnerLog.Valid 8 (innerAD leaf3378Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint63PositiveFacts.valid leaf3378CoverageChecked

private noncomputable def leaf3378InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3378InputLogOnePlusV_eq :
    leaf3378InputLogOnePlusV = outerEnclosure 24
      (leaf3378Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3378RoundedFacts : LeafRoundedFacts 8
    leaf3378Certificate.logOnePlusV leaf3378InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3378InputLogOnePlusV_eq }

private noncomputable def leaf3378Inputs : Inputs :=
  inputsOfCaches globalInput sk239RoundedInputs
    chi222InputQChi innerPair75Input
    leaf3378InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3378LowerChecked :
    lowerCheck 24 leaf3378Box leaf3378Inputs = true := by
  rfl'

private theorem leaf3378CoversExact : CoversExact 8
    leaf3378Box leaf3378Certificate leaf3378InnerLog leaf3378Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk239RoundedFacts chi222RoundedFacts
    innerPair75RoundedFacts leaf3378RoundedFacts (by rfl)

private theorem leaf3378FlatSound : Sound leaf3378Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3378CertificateValid
    leaf3378InnerLogValid leaf3378CoversExact leaf3378LowerChecked

private noncomputable def leaf3379Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (3/16), chiHi := (97/512) }

private noncomputable def leaf3379Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484353/2147483648) }, vSqrt := { lower := (65527/65536), upper := (27487384371/27486519296) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3751673537/2147483648) }, upper := { exponent := 0, mantissa := (225/128) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi221LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (54973903667/54973038592) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3379InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3379LocalValidity :
    LeafFacts leaf3379Box leaf3379Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3379Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (27487384371/27486519296) }) = true
      norm_num [leaf3379Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3379CertificateValid :
    WideCertificateValid leaf3379Box leaf3379Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi221ValidityFacts
    leaf3379LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3379CoverageChecked :
    coverageCheck (innerAD leaf3379Box) leaf3379InnerLog = true := by
  rfl'

private theorem leaf3379InnerLogValid :
    leaf3379InnerLog.Valid 8 (innerAD leaf3379Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3379CoverageChecked

private noncomputable def leaf3379InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629345/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3379InputLogOnePlusV_eq :
    leaf3379InputLogOnePlusV = outerEnclosure 24
      (leaf3379Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3379RoundedFacts : LeafRoundedFacts 8
    leaf3379Certificate.logOnePlusV leaf3379InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3379InputLogOnePlusV_eq }

private noncomputable def leaf3379Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi221InputQChi innerPair430Input
    leaf3379InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3379LowerChecked :
    lowerCheck 24 leaf3379Box leaf3379Inputs = true := by
  rfl'

private theorem leaf3379CoversExact : CoversExact 8
    leaf3379Box leaf3379Certificate leaf3379InnerLog leaf3379Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi221RoundedFacts
    innerPair430RoundedFacts leaf3379RoundedFacts (by rfl)

private theorem leaf3379FlatSound : Sound leaf3379Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3379CertificateValid
    leaf3379InnerLogValid leaf3379CoversExact leaf3379LowerChecked

private noncomputable def leaf3380Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (97/512), chiHi := (49/256) }

private noncomputable def leaf3380Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484355/2147483648) }, vSqrt := { lower := (65527/65536), upper := (15270769095/15270281216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3768384195/2147483648) }, upper := { exponent := 0, mantissa := (113/64) } }, logOuter := sk240LogOuterCertificate, logK := sk240LogKCertificate, logChi := chi222LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (30541050311/30540562432) } }, logDArg := sk240LogDArgCertificate }

private noncomputable def leaf3380InnerLog : WideLogData :=
  innerPair75Data

set_option maxRecDepth 1000000 in
private theorem leaf3380LocalValidity :
    LeafFacts leaf3380Box leaf3380Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3380Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (15270769095/15270281216) }) = true
      norm_num [leaf3380Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3380CertificateValid :
    WideCertificateValid leaf3380Box leaf3380Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk240ValidityFacts chi222ValidityFacts
    leaf3380LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3380CoverageChecked :
    coverageCheck (innerAD leaf3380Box) leaf3380InnerLog = true := by
  rfl'

private theorem leaf3380InnerLogValid :
    leaf3380InnerLog.Valid 8 (innerAD leaf3380Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint63PositiveFacts.valid leaf3380CoverageChecked

private noncomputable def leaf3380InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3380InputLogOnePlusV_eq :
    leaf3380InputLogOnePlusV = outerEnclosure 24
      (leaf3380Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3380RoundedFacts : LeafRoundedFacts 8
    leaf3380Certificate.logOnePlusV leaf3380InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3380InputLogOnePlusV_eq }

private noncomputable def leaf3380Inputs : Inputs :=
  inputsOfCaches globalInput sk240RoundedInputs
    chi222InputQChi innerPair75Input
    leaf3380InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3380LowerChecked :
    lowerCheck 24 leaf3380Box leaf3380Inputs = true := by
  rfl'

private theorem leaf3380CoversExact : CoversExact 8
    leaf3380Box leaf3380Certificate leaf3380InnerLog leaf3380Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk240RoundedFacts chi222RoundedFacts
    innerPair75RoundedFacts leaf3380RoundedFacts (by rfl)

private theorem leaf3380FlatSound : Sound leaf3380Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3380CertificateValid
    leaf3380InnerLogValid leaf3380CoversExact leaf3380LowerChecked

private noncomputable def leaf3381Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (509/128), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3381Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484765/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864876544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3778672309/2147483648) }, upper := { exponent := 0, mantissa := (29109/16384) } }, logOuter := sk247LogOuterCertificate, logK := sk247LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738654719/549729753088) } }, logDArg := sk247LogDArgCertificate }

private noncomputable def leaf3381InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3381LocalValidity :
    LeafFacts leaf3381Box leaf3381Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3381Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864876544) }) = true
      norm_num [leaf3381Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3381CertificateValid :
    WideCertificateValid leaf3381Box leaf3381Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk247ValidityFacts chi188ValidityFacts
    leaf3381LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3381CoverageChecked :
    coverageCheck (innerAD leaf3381Box) leaf3381InnerLog = true := by
  rfl'

private theorem leaf3381InnerLogValid :
    leaf3381InnerLog.Valid 8 (innerAD leaf3381Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3381CoverageChecked

private noncomputable def leaf3381InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3381InputLogOnePlusV_eq :
    leaf3381InputLogOnePlusV = outerEnclosure 24
      (leaf3381Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3381RoundedFacts : LeafRoundedFacts 8
    leaf3381Certificate.logOnePlusV leaf3381InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3381InputLogOnePlusV_eq }

private noncomputable def leaf3381Inputs : Inputs :=
  inputsOfCaches globalInput sk247RoundedInputs
    chi188InputQChi innerPair78Input
    leaf3381InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3381LowerChecked :
    lowerCheck 24 leaf3381Box leaf3381Inputs = true := by
  rfl'

private theorem leaf3381CoversExact : CoversExact 8
    leaf3381Box leaf3381Certificate leaf3381InnerLog leaf3381Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk247RoundedFacts chi188RoundedFacts
    innerPair78RoundedFacts leaf3381RoundedFacts (by rfl)

private theorem leaf3381FlatSound : Sound leaf3381Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3381CertificateValid
    leaf3381InnerLogValid leaf3381CoversExact leaf3381LowerChecked

private noncomputable def leaf3382Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (509/128), kHi := (255/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3382Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484767/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864850944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3781883375/2147483648) }, upper := { exponent := 0, mantissa := (14567/8192) } }, logOuter := sk248LogOuterCertificate, logK := sk248LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738629119/549729701888) } }, logDArg := sk248LogDArgCertificate }

private noncomputable def leaf3382InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3382LocalValidity :
    LeafFacts leaf3382Box leaf3382Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3382Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864850944) }) = true
      norm_num [leaf3382Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3382CertificateValid :
    WideCertificateValid leaf3382Box leaf3382Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk248ValidityFacts chi188ValidityFacts
    leaf3382LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3382CoverageChecked :
    coverageCheck (innerAD leaf3382Box) leaf3382InnerLog = true := by
  rfl'

private theorem leaf3382InnerLogValid :
    leaf3382InnerLog.Valid 8 (innerAD leaf3382Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3382CoverageChecked

private noncomputable def leaf3382InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3382InputLogOnePlusV_eq :
    leaf3382InputLogOnePlusV = outerEnclosure 24
      (leaf3382Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3382RoundedFacts : LeafRoundedFacts 8
    leaf3382Certificate.logOnePlusV leaf3382InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3382InputLogOnePlusV_eq }

private noncomputable def leaf3382Inputs : Inputs :=
  inputsOfCaches globalInput sk248RoundedInputs
    chi188InputQChi innerPair78Input
    leaf3382InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3382LowerChecked :
    lowerCheck 24 leaf3382Box leaf3382Inputs = true := by
  rfl'

private theorem leaf3382CoversExact : CoversExact 8
    leaf3382Box leaf3382Certificate leaf3382InnerLog leaf3382Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk248RoundedFacts chi188RoundedFacts
    innerPair78RoundedFacts leaf3382RoundedFacts (by rfl)

private theorem leaf3382FlatSound : Sound leaf3382Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3382CertificateValid
    leaf3382InnerLogValid leaf3382CoversExact leaf3382LowerChecked

private noncomputable def leaf3383Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (511/128), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3383Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484769/2147483648) }, vSqrt := { lower := (65527/65536), upper := (91624592725/91621608448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3785094441/2147483648) }, upper := { exponent := 0, mantissa := (29159/16384) } }, logOuter := sk249LogOuterCertificate, logK := sk249LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (183246201173/183243216896) } }, logDArg := sk249LogDArgCertificate }

private noncomputable def leaf3383InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3383LocalValidity :
    LeafFacts leaf3383Box leaf3383Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3383Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (91624592725/91621608448) }) = true
      norm_num [leaf3383Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3383CertificateValid :
    WideCertificateValid leaf3383Box leaf3383Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk249ValidityFacts chi188ValidityFacts
    leaf3383LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3383CoverageChecked :
    coverageCheck (innerAD leaf3383Box) leaf3383InnerLog = true := by
  rfl'

private theorem leaf3383InnerLogValid :
    leaf3383InnerLog.Valid 8 (innerAD leaf3383Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3383CoverageChecked

private noncomputable def leaf3383InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (5814677/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3383InputLogOnePlusV_eq :
    leaf3383InputLogOnePlusV = outerEnclosure 24
      (leaf3383Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3383RoundedFacts : LeafRoundedFacts 8
    leaf3383Certificate.logOnePlusV leaf3383InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3383InputLogOnePlusV_eq }

private noncomputable def leaf3383Inputs : Inputs :=
  inputsOfCaches globalInput sk249RoundedInputs
    chi188InputQChi innerPair78Input
    leaf3383InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3383LowerChecked :
    lowerCheck 24 leaf3383Box leaf3383Inputs = true := by
  rfl'

private theorem leaf3383CoversExact : CoversExact 8
    leaf3383Box leaf3383Certificate leaf3383InnerLog leaf3383Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk249RoundedFacts chi188RoundedFacts
    innerPair78RoundedFacts leaf3383RoundedFacts (by rfl)

private theorem leaf3383FlatSound : Sound leaf3383Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3383CertificateValid
    leaf3383InnerLogValid leaf3383CoversExact leaf3383LowerChecked

private noncomputable def leaf3384Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (511/128), kHi := (4), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3384Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484771/2147483648) }, vSqrt := { lower := (65527/65536), upper := (16169045775/16168517632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3788305507/2147483648) }, upper := { exponent := 0, mantissa := (57/32) } }, logOuter := sk250LogOuterCertificate, logK := sk250LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (32337563407/32337035264) } }, logDArg := sk250LogDArgCertificate }

private noncomputable def leaf3384InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3384LocalValidity :
    LeafFacts leaf3384Box leaf3384Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3384Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (16169045775/16168517632) }) = true
      norm_num [leaf3384Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3384CertificateValid :
    WideCertificateValid leaf3384Box leaf3384Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk250ValidityFacts chi188ValidityFacts
    leaf3384LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3384CoverageChecked :
    coverageCheck (innerAD leaf3384Box) leaf3384InnerLog = true := by
  rfl'

private theorem leaf3384InnerLogValid :
    leaf3384InnerLog.Valid 8 (innerAD leaf3384Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3384CoverageChecked

private noncomputable def leaf3384InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3384InputLogOnePlusV_eq :
    leaf3384InputLogOnePlusV = outerEnclosure 24
      (leaf3384Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3384RoundedFacts : LeafRoundedFacts 8
    leaf3384Certificate.logOnePlusV leaf3384InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3384InputLogOnePlusV_eq }

private noncomputable def leaf3384Inputs : Inputs :=
  inputsOfCaches globalInput sk250RoundedInputs
    chi188InputQChi innerPair78Input
    leaf3384InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3384LowerChecked :
    lowerCheck 24 leaf3384Box leaf3384Inputs = true := by
  rfl'

private theorem leaf3384CoversExact : CoversExact 8
    leaf3384Box leaf3384Certificate leaf3384InnerLog leaf3384Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk250RoundedFacts chi188RoundedFacts
    innerPair78RoundedFacts leaf3384RoundedFacts (by rfl)

private theorem leaf3384FlatSound : Sound leaf3384Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3384CertificateValid
    leaf3384InnerLogValid leaf3384CoversExact leaf3384LowerChecked

private noncomputable def leaf3385Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (505/128), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3385Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484759/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864720384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3798856171/2147483648) }, upper := { exponent := 0, mantissa := (58523/32768) } }, logOuter := sk243LogOuterCertificate, logK := sk243LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738498559/549729440768) } }, logDArg := sk243LogDArgCertificate }

private noncomputable def leaf3385InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3385LocalValidity :
    LeafFacts leaf3385Box leaf3385Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3385Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864720384) }) = true
      norm_num [leaf3385Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3385CertificateValid :
    WideCertificateValid leaf3385Box leaf3385Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk243ValidityFacts chi193ValidityFacts
    leaf3385LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3385CoverageChecked :
    coverageCheck (innerAD leaf3385Box) leaf3385InnerLog = true := by
  rfl'

private theorem leaf3385InnerLogValid :
    leaf3385InnerLog.Valid 8 (innerAD leaf3385Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3385CoverageChecked

private noncomputable def leaf3385InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629357/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3385InputLogOnePlusV_eq :
    leaf3385InputLogOnePlusV = outerEnclosure 24
      (leaf3385Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3385RoundedFacts : LeafRoundedFacts 8
    leaf3385Certificate.logOnePlusV leaf3385InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3385InputLogOnePlusV_eq }

private noncomputable def leaf3385Inputs : Inputs :=
  inputsOfCaches globalInput sk243RoundedInputs
    chi193InputQChi innerPair71Input
    leaf3385InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3385LowerChecked :
    lowerCheck 24 leaf3385Box leaf3385Inputs = true := by
  rfl'

private theorem leaf3385CoversExact : CoversExact 8
    leaf3385Box leaf3385Certificate leaf3385InnerLog leaf3385Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk243RoundedFacts chi193RoundedFacts
    innerPair71RoundedFacts leaf3385RoundedFacts (by rfl)

private theorem leaf3385FlatSound : Sound leaf3385Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3385CertificateValid
    leaf3385InnerLogValid leaf3385CoversExact leaf3385LowerChecked

private noncomputable def leaf3386Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (505/128), kHi := (253/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3386Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484761/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864694272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3802132769/2147483648) }, upper := { exponent := 0, mantissa := (29287/16384) } }, logOuter := sk244LogOuterCertificate, logK := sk244LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738472447/549729388544) } }, logDArg := sk244LogDArgCertificate }

private noncomputable def leaf3386InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3386LocalValidity :
    LeafFacts leaf3386Box leaf3386Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3386Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864694272) }) = true
      norm_num [leaf3386Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3386CertificateValid :
    WideCertificateValid leaf3386Box leaf3386Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk244ValidityFacts chi193ValidityFacts
    leaf3386LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3386CoverageChecked :
    coverageCheck (innerAD leaf3386Box) leaf3386InnerLog = true := by
  rfl'

private theorem leaf3386InnerLogValid :
    leaf3386InnerLog.Valid 8 (innerAD leaf3386Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3386CoverageChecked

private noncomputable def leaf3386InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3386InputLogOnePlusV_eq :
    leaf3386InputLogOnePlusV = outerEnclosure 24
      (leaf3386Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3386RoundedFacts : LeafRoundedFacts 8
    leaf3386Certificate.logOnePlusV leaf3386InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3386InputLogOnePlusV_eq }

private noncomputable def leaf3386Inputs : Inputs :=
  inputsOfCaches globalInput sk244RoundedInputs
    chi193InputQChi innerPair71Input
    leaf3386InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3386LowerChecked :
    lowerCheck 24 leaf3386Box leaf3386Inputs = true := by
  rfl'

private theorem leaf3386CoversExact : CoversExact 8
    leaf3386Box leaf3386Certificate leaf3386InnerLog leaf3386Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk244RoundedFacts chi193RoundedFacts
    innerPair71RoundedFacts leaf3386RoundedFacts (by rfl)

private theorem leaf3386FlatSound : Sound leaf3386Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3386CertificateValid
    leaf3386InnerLogValid leaf3386CoversExact leaf3386LowerChecked

private noncomputable def leaf3387Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (507/128), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3387Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484763/2147483648) }, vSqrt := { lower := (8191/8192), upper := (54974755635/54972933632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3805409367/2147483648) }, upper := { exponent := 0, mantissa := (58625/32768) } }, logOuter := sk245LogOuterCertificate, logK := sk245LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (109947689267/109945867264) } }, logDArg := sk245LogDArgCertificate }

private noncomputable def leaf3387InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3387LocalValidity :
    LeafFacts leaf3387Box leaf3387Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3387Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (54974755635/54972933632) }) = true
      norm_num [leaf3387Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3387CertificateValid :
    WideCertificateValid leaf3387Box leaf3387Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk245ValidityFacts chi193ValidityFacts
    leaf3387LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3387CoverageChecked :
    coverageCheck (innerAD leaf3387Box) leaf3387InnerLog = true := by
  rfl'

private theorem leaf3387InnerLogValid :
    leaf3387InnerLog.Valid 8 (innerAD leaf3387Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3387CoverageChecked

private noncomputable def leaf3387InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3387InputLogOnePlusV_eq :
    leaf3387InputLogOnePlusV = outerEnclosure 24
      (leaf3387Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3387RoundedFacts : LeafRoundedFacts 8
    leaf3387Certificate.logOnePlusV leaf3387InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3387InputLogOnePlusV_eq }

private noncomputable def leaf3387Inputs : Inputs :=
  inputsOfCaches globalInput sk245RoundedInputs
    chi193InputQChi innerPair71Input
    leaf3387InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3387LowerChecked :
    lowerCheck 24 leaf3387Box leaf3387Inputs = true := by
  rfl'

private theorem leaf3387CoversExact : CoversExact 8
    leaf3387Box leaf3387Certificate leaf3387InnerLog leaf3387Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk245RoundedFacts chi193RoundedFacts
    innerPair71RoundedFacts leaf3387RoundedFacts (by rfl)

private theorem leaf3387FlatSound : Sound leaf3387Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3387CertificateValid
    leaf3387InnerLogValid leaf3387CoversExact leaf3387LowerChecked

private noncomputable def leaf3388Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (507/128), kHi := (127/32), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3388Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484765/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864642048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3808685965/2147483648) }, upper := { exponent := 0, mantissa := (14669/8192) } }, logOuter := sk246LogOuterCertificate, logK := sk246LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738420223/549729284096) } }, logDArg := sk246LogDArgCertificate }

private noncomputable def leaf3388InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3388LocalValidity :
    LeafFacts leaf3388Box leaf3388Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3388Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864642048) }) = true
      norm_num [leaf3388Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3388CertificateValid :
    WideCertificateValid leaf3388Box leaf3388Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk246ValidityFacts chi193ValidityFacts
    leaf3388LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3388CoverageChecked :
    coverageCheck (innerAD leaf3388Box) leaf3388InnerLog = true := by
  rfl'

private theorem leaf3388InnerLogValid :
    leaf3388InnerLog.Valid 8 (innerAD leaf3388Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3388CoverageChecked

private noncomputable def leaf3388InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726835/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3388InputLogOnePlusV_eq :
    leaf3388InputLogOnePlusV = outerEnclosure 24
      (leaf3388Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3388RoundedFacts : LeafRoundedFacts 8
    leaf3388Certificate.logOnePlusV leaf3388InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3388InputLogOnePlusV_eq }

private noncomputable def leaf3388Inputs : Inputs :=
  inputsOfCaches globalInput sk246RoundedInputs
    chi193InputQChi innerPair71Input
    leaf3388InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3388LowerChecked :
    lowerCheck 24 leaf3388Box leaf3388Inputs = true := by
  rfl'

private theorem leaf3388CoversExact : CoversExact 8
    leaf3388Box leaf3388Certificate leaf3388InnerLog leaf3388Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk246RoundedFacts chi193RoundedFacts
    innerPair71RoundedFacts leaf3388RoundedFacts (by rfl)

private theorem leaf3388FlatSound : Sound leaf3388Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3388CertificateValid
    leaf3388InnerLogValid leaf3388CoversExact leaf3388LowerChecked

private noncomputable def leaf3389Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (505/128), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3389Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484761/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864461824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3831884297/2147483648) }, upper := { exponent := 0, mantissa := (14757/8192) } }, logOuter := sk243LogOuterCertificate, logK := sk243LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738239999/549728923648) } }, logDArg := sk243LogDArgCertificate }

private noncomputable def leaf3389InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3389LocalValidity :
    LeafFacts leaf3389Box leaf3389Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3389Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864461824) }) = true
      norm_num [leaf3389Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3389CertificateValid :
    WideCertificateValid leaf3389Box leaf3389Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk243ValidityFacts chi194ValidityFacts
    leaf3389LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3389CoverageChecked :
    coverageCheck (innerAD leaf3389Box) leaf3389InnerLog = true := by
  rfl'

private theorem leaf3389InnerLogValid :
    leaf3389InnerLog.Valid 8 (innerAD leaf3389Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3389CoverageChecked

private noncomputable def leaf3389InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3389InputLogOnePlusV_eq :
    leaf3389InputLogOnePlusV = outerEnclosure 24
      (leaf3389Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3389RoundedFacts : LeafRoundedFacts 8
    leaf3389Certificate.logOnePlusV leaf3389InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3389InputLogOnePlusV_eq }

private noncomputable def leaf3389Inputs : Inputs :=
  inputsOfCaches globalInput sk243RoundedInputs
    chi194InputQChi innerPair71Input
    leaf3389InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3389LowerChecked :
    lowerCheck 24 leaf3389Box leaf3389Inputs = true := by
  rfl'

private theorem leaf3389CoversExact : CoversExact 8
    leaf3389Box leaf3389Certificate leaf3389InnerLog leaf3389Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk243RoundedFacts chi194RoundedFacts
    innerPair71RoundedFacts leaf3389RoundedFacts (by rfl)

private theorem leaf3389FlatSound : Sound leaf3389Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3389CertificateValid
    leaf3389InnerLogValid leaf3389CoversExact leaf3389LowerChecked

private noncomputable def leaf3390Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (505/128), kHi := (253/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3390Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484763/2147483648) }, vSqrt := { lower := (8191/8192), upper := (3664983709/3664859136) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3835226427/2147483648) }, upper := { exponent := 0, mantissa := (7385/4096) } }, logOuter := sk244LogOuterCertificate, logK := sk244LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (7329842845/7329718272) } }, logDArg := sk244LogDArgCertificate }

private noncomputable def leaf3390InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3390LocalValidity :
    LeafFacts leaf3390Box leaf3390Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3390Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3664983709/3664859136) }) = true
      norm_num [leaf3390Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3390CertificateValid :
    WideCertificateValid leaf3390Box leaf3390Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk244ValidityFacts chi194ValidityFacts
    leaf3390LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3390CoverageChecked :
    coverageCheck (innerAD leaf3390Box) leaf3390InnerLog = true := by
  rfl'

private theorem leaf3390InnerLogValid :
    leaf3390InnerLog.Valid 8 (innerAD leaf3390Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3390CoverageChecked

private noncomputable def leaf3390InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3390InputLogOnePlusV_eq :
    leaf3390InputLogOnePlusV = outerEnclosure 24
      (leaf3390Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3390RoundedFacts : LeafRoundedFacts 8
    leaf3390Certificate.logOnePlusV leaf3390InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3390InputLogOnePlusV_eq }

private noncomputable def leaf3390Inputs : Inputs :=
  inputsOfCaches globalInput sk244RoundedInputs
    chi194InputQChi innerPair71Input
    leaf3390InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3390LowerChecked :
    lowerCheck 24 leaf3390Box leaf3390Inputs = true := by
  rfl'

private theorem leaf3390CoversExact : CoversExact 8
    leaf3390Box leaf3390Certificate leaf3390InnerLog leaf3390Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk244RoundedFacts chi194RoundedFacts
    innerPair71RoundedFacts leaf3390RoundedFacts (by rfl)

private theorem leaf3390FlatSound : Sound leaf3390Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3390CertificateValid
    leaf3390InnerLogValid leaf3390CoversExact leaf3390LowerChecked

private noncomputable def leaf3391Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (507/128), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3391Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484765/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864408576) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3838568557/2147483648) }, upper := { exponent := 0, mantissa := (14783/8192) } }, logOuter := sk245LogOuterCertificate, logK := sk245LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738186751/549728817152) } }, logDArg := sk245LogDArgCertificate }

private noncomputable def leaf3391InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3391LocalValidity :
    LeafFacts leaf3391Box leaf3391Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3391Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864408576) }) = true
      norm_num [leaf3391Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3391CertificateValid :
    WideCertificateValid leaf3391Box leaf3391Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk245ValidityFacts chi194ValidityFacts
    leaf3391LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3391CoverageChecked :
    coverageCheck (innerAD leaf3391Box) leaf3391InnerLog = true := by
  rfl'

private theorem leaf3391InnerLogValid :
    leaf3391InnerLog.Valid 8 (innerAD leaf3391Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3391CoverageChecked

private noncomputable def leaf3391InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629367/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3391InputLogOnePlusV_eq :
    leaf3391InputLogOnePlusV = outerEnclosure 24
      (leaf3391Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3391RoundedFacts : LeafRoundedFacts 8
    leaf3391Certificate.logOnePlusV leaf3391InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3391InputLogOnePlusV_eq }

private noncomputable def leaf3391Inputs : Inputs :=
  inputsOfCaches globalInput sk245RoundedInputs
    chi194InputQChi innerPair71Input
    leaf3391InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3391LowerChecked :
    lowerCheck 24 leaf3391Box leaf3391Inputs = true := by
  rfl'

private theorem leaf3391CoversExact : CoversExact 8
    leaf3391Box leaf3391Certificate leaf3391InnerLog leaf3391Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk245RoundedFacts chi194RoundedFacts
    innerPair71RoundedFacts leaf3391RoundedFacts (by rfl)

private theorem leaf3391FlatSound : Sound leaf3391Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3391CertificateValid
    leaf3391InnerLogValid leaf3391CoversExact leaf3391LowerChecked

private noncomputable def leaf3392Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (507/128), kHi := (127/32), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3392Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484767/2147483648) }, vSqrt := { lower := (8191/8192), upper := (16169045775/16168493056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3841910687/2147483648) }, upper := { exponent := 0, mantissa := (3699/2048) } }, logOuter := sk246LogOuterCertificate, logK := sk246LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (32337538831/32336986112) } }, logDArg := sk246LogDArgCertificate }

private noncomputable def leaf3392InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3392LocalValidity :
    LeafFacts leaf3392Box leaf3392Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3392Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (16169045775/16168493056) }) = true
      norm_num [leaf3392Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3392CertificateValid :
    WideCertificateValid leaf3392Box leaf3392Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk246ValidityFacts chi194ValidityFacts
    leaf3392LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3392CoverageChecked :
    coverageCheck (innerAD leaf3392Box) leaf3392InnerLog = true := by
  rfl'

private theorem leaf3392InnerLogValid :
    leaf3392InnerLog.Valid 8 (innerAD leaf3392Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3392CoverageChecked

private noncomputable def leaf3392InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3392InputLogOnePlusV_eq :
    leaf3392InputLogOnePlusV = outerEnclosure 24
      (leaf3392Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3392RoundedFacts : LeafRoundedFacts 8
    leaf3392Certificate.logOnePlusV leaf3392InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3392InputLogOnePlusV_eq }

private noncomputable def leaf3392Inputs : Inputs :=
  inputsOfCaches globalInput sk246RoundedInputs
    chi194InputQChi innerPair71Input
    leaf3392InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3392LowerChecked :
    lowerCheck 24 leaf3392Box leaf3392Inputs = true := by
  rfl'

private theorem leaf3392CoversExact : CoversExact 8
    leaf3392Box leaf3392Certificate leaf3392InnerLog leaf3392Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk246RoundedFacts chi194RoundedFacts
    innerPair71RoundedFacts leaf3392RoundedFacts (by rfl)

private theorem leaf3392FlatSound : Sound leaf3392Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3392CertificateValid
    leaf3392InnerLogValid leaf3392CoversExact leaf3392LowerChecked

private noncomputable def leaf3393Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (509/128), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3393Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484767/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864615936) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3811962563/2147483648) }, upper := { exponent := 0, mantissa := (58727/32768) } }, logOuter := sk247LogOuterCertificate, logK := sk247LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738394111/549729231872) } }, logDArg := sk247LogDArgCertificate }

private noncomputable def leaf3393InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3393LocalValidity :
    LeafFacts leaf3393Box leaf3393Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3393Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864615936) }) = true
      norm_num [leaf3393Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3393CertificateValid :
    WideCertificateValid leaf3393Box leaf3393Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk247ValidityFacts chi193ValidityFacts
    leaf3393LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3393CoverageChecked :
    coverageCheck (innerAD leaf3393Box) leaf3393InnerLog = true := by
  rfl'

private theorem leaf3393InnerLogValid :
    leaf3393InnerLog.Valid 8 (innerAD leaf3393Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3393CoverageChecked

private noncomputable def leaf3393InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726835/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3393InputLogOnePlusV_eq :
    leaf3393InputLogOnePlusV = outerEnclosure 24
      (leaf3393Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3393RoundedFacts : LeafRoundedFacts 8
    leaf3393Certificate.logOnePlusV leaf3393InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3393InputLogOnePlusV_eq }

private noncomputable def leaf3393Inputs : Inputs :=
  inputsOfCaches globalInput sk247RoundedInputs
    chi193InputQChi innerPair71Input
    leaf3393InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3393LowerChecked :
    lowerCheck 24 leaf3393Box leaf3393Inputs = true := by
  rfl'

private theorem leaf3393CoversExact : CoversExact 8
    leaf3393Box leaf3393Certificate leaf3393InnerLog leaf3393Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk247RoundedFacts chi193RoundedFacts
    innerPair71RoundedFacts leaf3393RoundedFacts (by rfl)

private theorem leaf3393FlatSound : Sound leaf3393Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3393CertificateValid
    leaf3393InnerLogValid leaf3393CoversExact leaf3393LowerChecked

private noncomputable def leaf3394Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (509/128), kHi := (255/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3394Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484769/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864589824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3815239161/2147483648) }, upper := { exponent := 0, mantissa := (29389/16384) } }, logOuter := sk248LogOuterCertificate, logK := sk248LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738367999/549729179648) } }, logDArg := sk248LogDArgCertificate }

private noncomputable def leaf3394InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3394LocalValidity :
    LeafFacts leaf3394Box leaf3394Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3394Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864589824) }) = true
      norm_num [leaf3394Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3394CertificateValid :
    WideCertificateValid leaf3394Box leaf3394Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk248ValidityFacts chi193ValidityFacts
    leaf3394LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3394CoverageChecked :
    coverageCheck (innerAD leaf3394Box) leaf3394InnerLog = true := by
  rfl'

private theorem leaf3394InnerLogValid :
    leaf3394InnerLog.Valid 8 (innerAD leaf3394Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3394CoverageChecked

private noncomputable def leaf3394InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3394InputLogOnePlusV_eq :
    leaf3394InputLogOnePlusV = outerEnclosure 24
      (leaf3394Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3394RoundedFacts : LeafRoundedFacts 8
    leaf3394Certificate.logOnePlusV leaf3394InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3394InputLogOnePlusV_eq }

private noncomputable def leaf3394Inputs : Inputs :=
  inputsOfCaches globalInput sk248RoundedInputs
    chi193InputQChi innerPair71Input
    leaf3394InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3394LowerChecked :
    lowerCheck 24 leaf3394Box leaf3394Inputs = true := by
  rfl'

private theorem leaf3394CoversExact : CoversExact 8
    leaf3394Box leaf3394Certificate leaf3394InnerLog leaf3394Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk248RoundedFacts chi193RoundedFacts
    innerPair71RoundedFacts leaf3394RoundedFacts (by rfl)

private theorem leaf3394FlatSound : Sound leaf3394Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3394CertificateValid
    leaf3394InnerLogValid leaf3394CoversExact leaf3394LowerChecked

private noncomputable def leaf3395Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (511/128), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3395Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484771/2147483648) }, vSqrt := { lower := (65527/65536), upper := (274873778175/274864563712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3818515759/2147483648) }, upper := { exponent := 0, mantissa := (58829/32768) } }, logOuter := sk249LogOuterCertificate, logK := sk249LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (549738341887/549729127424) } }, logDArg := sk249LogDArgCertificate }

private noncomputable def leaf3395InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3395LocalValidity :
    LeafFacts leaf3395Box leaf3395Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3395Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (274873778175/274864563712) }) = true
      norm_num [leaf3395Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3395CertificateValid :
    WideCertificateValid leaf3395Box leaf3395Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk249ValidityFacts chi193ValidityFacts
    leaf3395LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3395CoverageChecked :
    coverageCheck (innerAD leaf3395Box) leaf3395InnerLog = true := by
  rfl'

private theorem leaf3395InnerLogValid :
    leaf3395InnerLog.Valid 8 (innerAD leaf3395Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3395CoverageChecked

private noncomputable def leaf3395InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (5814681/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3395InputLogOnePlusV_eq :
    leaf3395InputLogOnePlusV = outerEnclosure 24
      (leaf3395Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3395RoundedFacts : LeafRoundedFacts 8
    leaf3395Certificate.logOnePlusV leaf3395InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3395InputLogOnePlusV_eq }

private noncomputable def leaf3395Inputs : Inputs :=
  inputsOfCaches globalInput sk249RoundedInputs
    chi193InputQChi innerPair71Input
    leaf3395InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3395LowerChecked :
    lowerCheck 24 leaf3395Box leaf3395Inputs = true := by
  rfl'

private theorem leaf3395CoversExact : CoversExact 8
    leaf3395Box leaf3395Certificate leaf3395InnerLog leaf3395Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk249RoundedFacts chi193RoundedFacts
    innerPair71RoundedFacts leaf3395RoundedFacts (by rfl)

private theorem leaf3395FlatSound : Sound leaf3395Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3395CertificateValid
    leaf3395InnerLogValid leaf3395CoversExact leaf3395LowerChecked

private noncomputable def leaf3396Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (511/128), kHi := (4), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3396Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484773/2147483648) }, vSqrt := { lower := (65527/65536), upper := (10994951127/10994581504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3821792357/2147483648) }, upper := { exponent := 0, mantissa := (115/64) } }, logOuter := sk250LogOuterCertificate, logK := sk250LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (21989532631/21989163008) } }, logDArg := sk250LogDArgCertificate }

private noncomputable def leaf3396InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3396LocalValidity :
    LeafFacts leaf3396Box leaf3396Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3396Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (10994951127/10994581504) }) = true
      norm_num [leaf3396Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3396CertificateValid :
    WideCertificateValid leaf3396Box leaf3396Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk250ValidityFacts chi193ValidityFacts
    leaf3396LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3396CoverageChecked :
    coverageCheck (innerAD leaf3396Box) leaf3396InnerLog = true := by
  rfl'

private theorem leaf3396InnerLogValid :
    leaf3396InnerLog.Valid 8 (innerAD leaf3396Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3396CoverageChecked

private noncomputable def leaf3396InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3396InputLogOnePlusV_eq :
    leaf3396InputLogOnePlusV = outerEnclosure 24
      (leaf3396Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3396RoundedFacts : LeafRoundedFacts 8
    leaf3396Certificate.logOnePlusV leaf3396InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3396InputLogOnePlusV_eq }

private noncomputable def leaf3396Inputs : Inputs :=
  inputsOfCaches globalInput sk250RoundedInputs
    chi193InputQChi innerPair71Input
    leaf3396InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3396LowerChecked :
    lowerCheck 24 leaf3396Box leaf3396Inputs = true := by
  rfl'

private theorem leaf3396CoversExact : CoversExact 8
    leaf3396Box leaf3396Certificate leaf3396InnerLog leaf3396Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk250RoundedFacts chi193RoundedFacts
    innerPair71RoundedFacts leaf3396RoundedFacts (by rfl)

private theorem leaf3396FlatSound : Sound leaf3396Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3396CertificateValid
    leaf3396InnerLogValid leaf3396CoversExact leaf3396LowerChecked

private noncomputable def leaf3397Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (509/128), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3397Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484769/2147483648) }, vSqrt := { lower := (8191/8192), upper := (91624592725/91621451776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3845252817/2147483648) }, upper := { exponent := 0, mantissa := (14809/8192) } }, logOuter := sk247LogOuterCertificate, logK := sk247LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (183246044501/183242903552) } }, logDArg := sk247LogDArgCertificate }

private noncomputable def leaf3397InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3397LocalValidity :
    LeafFacts leaf3397Box leaf3397Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3397Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (91624592725/91621451776) }) = true
      norm_num [leaf3397Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3397CertificateValid :
    WideCertificateValid leaf3397Box leaf3397Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk247ValidityFacts chi194ValidityFacts
    leaf3397LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3397CoverageChecked :
    coverageCheck (innerAD leaf3397Box) leaf3397InnerLog = true := by
  rfl'

private theorem leaf3397InnerLogValid :
    leaf3397InnerLog.Valid 8 (innerAD leaf3397Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3397CoverageChecked

private noncomputable def leaf3397InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3397InputLogOnePlusV_eq :
    leaf3397InputLogOnePlusV = outerEnclosure 24
      (leaf3397Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3397RoundedFacts : LeafRoundedFacts 8
    leaf3397Certificate.logOnePlusV leaf3397InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3397InputLogOnePlusV_eq }

private noncomputable def leaf3397Inputs : Inputs :=
  inputsOfCaches globalInput sk247RoundedInputs
    chi194InputQChi innerPair71Input
    leaf3397InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3397LowerChecked :
    lowerCheck 24 leaf3397Box leaf3397Inputs = true := by
  rfl'

private theorem leaf3397CoversExact : CoversExact 8
    leaf3397Box leaf3397Certificate leaf3397InnerLog leaf3397Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk247RoundedFacts chi194RoundedFacts
    innerPair71RoundedFacts leaf3397RoundedFacts (by rfl)

private theorem leaf3397FlatSound : Sound leaf3397Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3397CertificateValid
    leaf3397InnerLogValid leaf3397CoversExact leaf3397LowerChecked

private noncomputable def leaf3398Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (509/128), kHi := (255/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3398Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484771/2147483648) }, vSqrt := { lower := (8191/8192), upper := (274873778175/274864328704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3848594947/2147483648) }, upper := { exponent := 0, mantissa := (7411/4096) } }, logOuter := sk248LogOuterCertificate, logK := sk248LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (549738106879/549728657408) } }, logDArg := sk248LogDArgCertificate }

private noncomputable def leaf3398InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3398LocalValidity :
    LeafFacts leaf3398Box leaf3398Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3398Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (274873778175/274864328704) }) = true
      norm_num [leaf3398Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3398CertificateValid :
    WideCertificateValid leaf3398Box leaf3398Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk248ValidityFacts chi194ValidityFacts
    leaf3398LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3398CoverageChecked :
    coverageCheck (innerAD leaf3398Box) leaf3398InnerLog = true := by
  rfl'

private theorem leaf3398InnerLogValid :
    leaf3398InnerLog.Valid 8 (innerAD leaf3398Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3398CoverageChecked

private noncomputable def leaf3398InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3398InputLogOnePlusV_eq :
    leaf3398InputLogOnePlusV = outerEnclosure 24
      (leaf3398Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3398RoundedFacts : LeafRoundedFacts 8
    leaf3398Certificate.logOnePlusV leaf3398InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3398InputLogOnePlusV_eq }

private noncomputable def leaf3398Inputs : Inputs :=
  inputsOfCaches globalInput sk248RoundedInputs
    chi194InputQChi innerPair71Input
    leaf3398InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3398LowerChecked :
    lowerCheck 24 leaf3398Box leaf3398Inputs = true := by
  rfl'

private theorem leaf3398CoversExact : CoversExact 8
    leaf3398Box leaf3398Certificate leaf3398InnerLog leaf3398Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk248RoundedFacts chi194RoundedFacts
    innerPair71RoundedFacts leaf3398RoundedFacts (by rfl)

private theorem leaf3398FlatSound : Sound leaf3398Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3398CertificateValid
    leaf3398InnerLogValid leaf3398CoversExact leaf3398LowerChecked

private noncomputable def leaf3399Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (511/128), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3399Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484773/2147483648) }, vSqrt := { lower := (65527/65536), upper := (54974755635/54972860416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3851937077/2147483648) }, upper := { exponent := 0, mantissa := (14835/8192) } }, logOuter := sk249LogOuterCertificate, logK := sk249LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (109947616051/109945720832) } }, logDArg := sk249LogDArgCertificate }

private noncomputable def leaf3399InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3399LocalValidity :
    LeafFacts leaf3399Box leaf3399Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3399Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (54974755635/54972860416) }) = true
      norm_num [leaf3399Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3399CertificateValid :
    WideCertificateValid leaf3399Box leaf3399Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk249ValidityFacts chi194ValidityFacts
    leaf3399LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3399CoverageChecked :
    coverageCheck (innerAD leaf3399Box) leaf3399InnerLog = true := by
  rfl'

private theorem leaf3399InnerLogValid :
    leaf3399InnerLog.Valid 8 (innerAD leaf3399Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3399CoverageChecked

private noncomputable def leaf3399InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3399InputLogOnePlusV_eq :
    leaf3399InputLogOnePlusV = outerEnclosure 24
      (leaf3399Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3399RoundedFacts : LeafRoundedFacts 8
    leaf3399Certificate.logOnePlusV leaf3399InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3399InputLogOnePlusV_eq }

private noncomputable def leaf3399Inputs : Inputs :=
  inputsOfCaches globalInput sk249RoundedInputs
    chi194InputQChi innerPair71Input
    leaf3399InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3399LowerChecked :
    lowerCheck 24 leaf3399Box leaf3399Inputs = true := by
  rfl'

private theorem leaf3399CoversExact : CoversExact 8
    leaf3399Box leaf3399Certificate leaf3399InnerLog leaf3399Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk249RoundedFacts chi194RoundedFacts
    innerPair71RoundedFacts leaf3399RoundedFacts (by rfl)

private theorem leaf3399FlatSound : Sound leaf3399Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3399CertificateValid
    leaf3399InnerLogValid leaf3399CoversExact leaf3399LowerChecked

private noncomputable def leaf3400Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (511/128), kHi := (4), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3400Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (2147484775/2147483648) }, vSqrt := { lower := (65527/65536), upper := (91624592725/91621425152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (3855279207/2147483648) }, upper := { exponent := 0, mantissa := (29/16) } }, logOuter := sk250LogOuterCertificate, logK := sk250LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (131063/65536) }, upper := { exponent := 1, mantissa := (183246017877/183242850304) } }, logDArg := sk250LogDArgCertificate }

private noncomputable def leaf3400InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3400LocalValidity :
    LeafFacts leaf3400Box leaf3400Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3400Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (65527/65536), upper := (91624592725/91621425152) }) = true
      norm_num [leaf3400Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3400CertificateValid :
    WideCertificateValid leaf3400Box leaf3400Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk250ValidityFacts chi194ValidityFacts
    leaf3400LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3400CoverageChecked :
    coverageCheck (innerAD leaf3400Box) leaf3400InnerLog = true := by
  rfl'

private theorem leaf3400InnerLogValid :
    leaf3400InnerLog.Valid 8 (innerAD leaf3400Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3400CoverageChecked

private noncomputable def leaf3400InputLogOnePlusV : RationalEnclosure :=
  { lower := (11627927/16777216), upper := (11629371/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3400InputLogOnePlusV_eq :
    leaf3400InputLogOnePlusV = outerEnclosure 24
      (leaf3400Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3400RoundedFacts : LeafRoundedFacts 8
    leaf3400Certificate.logOnePlusV leaf3400InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3400InputLogOnePlusV_eq }

private noncomputable def leaf3400Inputs : Inputs :=
  inputsOfCaches globalInput sk250RoundedInputs
    chi194InputQChi innerPair71Input
    leaf3400InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3400LowerChecked :
    lowerCheck 24 leaf3400Box leaf3400Inputs = true := by
  rfl'

private theorem leaf3400CoversExact : CoversExact 8
    leaf3400Box leaf3400Certificate leaf3400InnerLog leaf3400Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk250RoundedFacts chi194RoundedFacts
    innerPair71RoundedFacts leaf3400RoundedFacts (by rfl)

private theorem leaf3400FlatSound : Sound leaf3400Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3400CertificateValid
    leaf3400InnerLogValid leaf3400CoversExact leaf3400LowerChecked

private noncomputable def component69Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node0_sound : Sound component69Node0Box :=
  sound_of_literal_split component69Node0Box leaf3349Box leaf3350Box
    .k (249/64) (by rfl) (by rfl)
    leaf3349FlatSound leaf3350FlatSound

private noncomputable def component69Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component69Node1_sound : Sound component69Node1Box :=
  sound_of_literal_split component69Node1Box leaf3351Box leaf3352Box
    .k (249/64) (by rfl) (by rfl)
    leaf3351FlatSound leaf3352FlatSound

private noncomputable def component69Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component69Node2_sound : Sound component69Node2Box :=
  sound_of_literal_split component69Node2Box component69Node0Box component69Node1Box
    .chi (49/256) (by rfl) (by rfl)
    component69Node0_sound component69Node1_sound

private noncomputable def component69Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node3_sound : Sound component69Node3Box :=
  sound_of_literal_split component69Node3Box leaf3354Box leaf3355Box
    .k (503/128) (by rfl) (by rfl)
    leaf3354FlatSound leaf3355FlatSound

private noncomputable def component69Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node4_sound : Sound component69Node4Box :=
  sound_of_literal_split component69Node4Box leaf3353Box component69Node3Box
    .k (251/64) (by rfl) (by rfl)
    leaf3353FlatSound component69Node3_sound

private noncomputable def component69Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component69Node5_sound : Sound component69Node5Box :=
  sound_of_literal_split component69Node5Box leaf3357Box leaf3358Box
    .k (503/128) (by rfl) (by rfl)
    leaf3357FlatSound leaf3358FlatSound

private noncomputable def component69Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component69Node6_sound : Sound component69Node6Box :=
  sound_of_literal_split component69Node6Box leaf3356Box component69Node5Box
    .k (251/64) (by rfl) (by rfl)
    leaf3356FlatSound component69Node5_sound

private noncomputable def component69Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component69Node7_sound : Sound component69Node7Box :=
  sound_of_literal_split component69Node7Box component69Node4Box component69Node6Box
    .chi (49/256) (by rfl) (by rfl)
    component69Node4_sound component69Node6_sound

private noncomputable def component69Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component69Node8_sound : Sound component69Node8Box :=
  sound_of_literal_split component69Node8Box component69Node2Box component69Node7Box
    .k (125/32) (by rfl) (by rfl)
    component69Node2_sound component69Node7_sound

private noncomputable def component69Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node9_sound : Sound component69Node9Box :=
  sound_of_literal_split component69Node9Box leaf3359Box leaf3360Box
    .k (249/64) (by rfl) (by rfl)
    leaf3359FlatSound leaf3360FlatSound

private noncomputable def component69Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component69Node10_sound : Sound component69Node10Box :=
  sound_of_literal_split component69Node10Box leaf3361Box leaf3362Box
    .k (249/64) (by rfl) (by rfl)
    leaf3361FlatSound leaf3362FlatSound

private noncomputable def component69Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (125/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component69Node11_sound : Sound component69Node11Box :=
  sound_of_literal_split component69Node11Box component69Node9Box component69Node10Box
    .chi (51/256) (by rfl) (by rfl)
    component69Node9_sound component69Node10_sound

private noncomputable def component69Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node12_sound : Sound component69Node12Box :=
  sound_of_literal_split component69Node12Box leaf3364Box leaf3365Box
    .k (503/128) (by rfl) (by rfl)
    leaf3364FlatSound leaf3365FlatSound

private noncomputable def component69Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node13_sound : Sound component69Node13Box :=
  sound_of_literal_split component69Node13Box leaf3363Box component69Node12Box
    .k (251/64) (by rfl) (by rfl)
    leaf3363FlatSound component69Node12_sound

private noncomputable def component69Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (251/64), kHi := (63/16), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component69Node14_sound : Sound component69Node14Box :=
  sound_of_literal_split component69Node14Box leaf3367Box leaf3368Box
    .k (503/128) (by rfl) (by rfl)
    leaf3367FlatSound leaf3368FlatSound

private noncomputable def component69Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component69Node15_sound : Sound component69Node15Box :=
  sound_of_literal_split component69Node15Box leaf3366Box component69Node14Box
    .k (251/64) (by rfl) (by rfl)
    leaf3366FlatSound component69Node14_sound

private noncomputable def component69Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (125/32), kHi := (63/16), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component69Node16_sound : Sound component69Node16Box :=
  sound_of_literal_split component69Node16Box component69Node13Box component69Node15Box
    .chi (51/256) (by rfl) (by rfl)
    component69Node13_sound component69Node15_sound

private noncomputable def component69Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component69Node17_sound : Sound component69Node17Box :=
  sound_of_literal_split component69Node17Box component69Node11Box component69Node16Box
    .k (125/32) (by rfl) (by rfl)
    component69Node11_sound component69Node16_sound

private noncomputable def component69Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (63/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component69Node18_sound : Sound component69Node18Box :=
  sound_of_literal_split component69Node18Box component69Node8Box component69Node17Box
    .chi (25/128) (by rfl) (by rfl)
    component69Node8_sound component69Node17_sound

private noncomputable def component69Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node19_sound : Sound component69Node19Box :=
  sound_of_literal_split component69Node19Box leaf3369Box leaf3370Box
    .chi (97/512) (by rfl) (by rfl)
    leaf3369FlatSound leaf3370FlatSound

private noncomputable def component69Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node20_sound : Sound component69Node20Box :=
  sound_of_literal_split component69Node20Box leaf3371Box leaf3372Box
    .chi (97/512) (by rfl) (by rfl)
    leaf3371FlatSound leaf3372FlatSound

private noncomputable def component69Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node21_sound : Sound component69Node21Box :=
  sound_of_literal_split component69Node21Box component69Node19Box component69Node20Box
    .k (253/64) (by rfl) (by rfl)
    component69Node19_sound component69Node20_sound

private noncomputable def component69Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component69Node22_sound : Sound component69Node22Box :=
  sound_of_literal_split component69Node22Box leaf3373Box leaf3374Box
    .k (505/128) (by rfl) (by rfl)
    leaf3373FlatSound leaf3374FlatSound

private noncomputable def component69Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component69Node23_sound : Sound component69Node23Box :=
  sound_of_literal_split component69Node23Box leaf3375Box leaf3376Box
    .k (507/128) (by rfl) (by rfl)
    leaf3375FlatSound leaf3376FlatSound

private noncomputable def component69Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component69Node24_sound : Sound component69Node24Box :=
  sound_of_literal_split component69Node24Box component69Node22Box component69Node23Box
    .k (253/64) (by rfl) (by rfl)
    component69Node22_sound component69Node23_sound

private noncomputable def component69Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component69Node25_sound : Sound component69Node25Box :=
  sound_of_literal_split component69Node25Box component69Node21Box component69Node24Box
    .chi (49/256) (by rfl) (by rfl)
    component69Node21_sound component69Node24_sound

private noncomputable def component69Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node26_sound : Sound component69Node26Box :=
  sound_of_literal_split component69Node26Box leaf3377Box leaf3378Box
    .chi (97/512) (by rfl) (by rfl)
    leaf3377FlatSound leaf3378FlatSound

private noncomputable def component69Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node27_sound : Sound component69Node27Box :=
  sound_of_literal_split component69Node27Box leaf3379Box leaf3380Box
    .chi (97/512) (by rfl) (by rfl)
    leaf3379FlatSound leaf3380FlatSound

private noncomputable def component69Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node28_sound : Sound component69Node28Box :=
  sound_of_literal_split component69Node28Box component69Node26Box component69Node27Box
    .k (255/64) (by rfl) (by rfl)
    component69Node26_sound component69Node27_sound

private noncomputable def component69Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component69Node29_sound : Sound component69Node29Box :=
  sound_of_literal_split component69Node29Box leaf3381Box leaf3382Box
    .k (509/128) (by rfl) (by rfl)
    leaf3381FlatSound leaf3382FlatSound

private noncomputable def component69Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component69Node30_sound : Sound component69Node30Box :=
  sound_of_literal_split component69Node30Box leaf3383Box leaf3384Box
    .k (511/128) (by rfl) (by rfl)
    leaf3383FlatSound leaf3384FlatSound

private noncomputable def component69Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component69Node31_sound : Sound component69Node31Box :=
  sound_of_literal_split component69Node31Box component69Node29Box component69Node30Box
    .k (255/64) (by rfl) (by rfl)
    component69Node29_sound component69Node30_sound

private noncomputable def component69Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component69Node32_sound : Sound component69Node32Box :=
  sound_of_literal_split component69Node32Box component69Node28Box component69Node31Box
    .chi (49/256) (by rfl) (by rfl)
    component69Node28_sound component69Node31_sound

private noncomputable def component69Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component69Node33_sound : Sound component69Node33Box :=
  sound_of_literal_split component69Node33Box component69Node25Box component69Node32Box
    .k (127/32) (by rfl) (by rfl)
    component69Node25_sound component69Node32_sound

private noncomputable def component69Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node34_sound : Sound component69Node34Box :=
  sound_of_literal_split component69Node34Box leaf3385Box leaf3386Box
    .k (505/128) (by rfl) (by rfl)
    leaf3385FlatSound leaf3386FlatSound

private noncomputable def component69Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node35_sound : Sound component69Node35Box :=
  sound_of_literal_split component69Node35Box leaf3387Box leaf3388Box
    .k (507/128) (by rfl) (by rfl)
    leaf3387FlatSound leaf3388FlatSound

private noncomputable def component69Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node36_sound : Sound component69Node36Box :=
  sound_of_literal_split component69Node36Box component69Node34Box component69Node35Box
    .k (253/64) (by rfl) (by rfl)
    component69Node34_sound component69Node35_sound

private noncomputable def component69Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (253/64), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component69Node37_sound : Sound component69Node37Box :=
  sound_of_literal_split component69Node37Box leaf3389Box leaf3390Box
    .k (505/128) (by rfl) (by rfl)
    leaf3389FlatSound leaf3390FlatSound

private noncomputable def component69Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (253/64), kHi := (127/32), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component69Node38_sound : Sound component69Node38Box :=
  sound_of_literal_split component69Node38Box leaf3391Box leaf3392Box
    .k (507/128) (by rfl) (by rfl)
    leaf3391FlatSound leaf3392FlatSound

private noncomputable def component69Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component69Node39_sound : Sound component69Node39Box :=
  sound_of_literal_split component69Node39Box component69Node37Box component69Node38Box
    .k (253/64) (by rfl) (by rfl)
    component69Node37_sound component69Node38_sound

private noncomputable def component69Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (127/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component69Node40_sound : Sound component69Node40Box :=
  sound_of_literal_split component69Node40Box component69Node36Box component69Node39Box
    .chi (51/256) (by rfl) (by rfl)
    component69Node36_sound component69Node39_sound

private noncomputable def component69Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node41_sound : Sound component69Node41Box :=
  sound_of_literal_split component69Node41Box leaf3393Box leaf3394Box
    .k (509/128) (by rfl) (by rfl)
    leaf3393FlatSound leaf3394FlatSound

private noncomputable def component69Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node42_sound : Sound component69Node42Box :=
  sound_of_literal_split component69Node42Box leaf3395Box leaf3396Box
    .k (511/128) (by rfl) (by rfl)
    leaf3395FlatSound leaf3396FlatSound

private noncomputable def component69Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component69Node43_sound : Sound component69Node43Box :=
  sound_of_literal_split component69Node43Box component69Node41Box component69Node42Box
    .k (255/64) (by rfl) (by rfl)
    component69Node41_sound component69Node42_sound

private noncomputable def component69Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (255/64), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component69Node44_sound : Sound component69Node44Box :=
  sound_of_literal_split component69Node44Box leaf3397Box leaf3398Box
    .k (509/128) (by rfl) (by rfl)
    leaf3397FlatSound leaf3398FlatSound

private noncomputable def component69Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (255/64), kHi := (4), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component69Node45_sound : Sound component69Node45Box :=
  sound_of_literal_split component69Node45Box leaf3399Box leaf3400Box
    .k (511/128) (by rfl) (by rfl)
    leaf3399FlatSound leaf3400FlatSound

private noncomputable def component69Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component69Node46_sound : Sound component69Node46Box :=
  sound_of_literal_split component69Node46Box component69Node44Box component69Node45Box
    .k (255/64) (by rfl) (by rfl)
    component69Node44_sound component69Node45_sound

private noncomputable def component69Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (127/32), kHi := (4), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component69Node47_sound : Sound component69Node47Box :=
  sound_of_literal_split component69Node47Box component69Node43Box component69Node46Box
    .chi (51/256) (by rfl) (by rfl)
    component69Node43_sound component69Node46_sound

private noncomputable def component69Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component69Node48_sound : Sound component69Node48Box :=
  sound_of_literal_split component69Node48Box component69Node40Box component69Node47Box
    .k (127/32) (by rfl) (by rfl)
    component69Node40_sound component69Node47_sound

private noncomputable def component69Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (63/16), kHi := (4), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component69Node49_sound : Sound component69Node49Box :=
  sound_of_literal_split component69Node49Box component69Node33Box component69Node48Box
    .chi (25/128) (by rfl) (by rfl)
    component69Node33_sound component69Node48_sound

noncomputable def component69Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (31/8), kHi := (4), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
theorem component69_sound : Sound component69Box :=
  sound_of_literal_split component69Box component69Node18Box component69Node49Box
    .k (63/16) (by rfl) (by rfl)
    component69Node18_sound component69Node49_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
