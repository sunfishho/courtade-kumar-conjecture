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

private noncomputable def leaf3285Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3285Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810969088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1828637119/1073741824) }, upper := { exponent := 0, mantissa := (28193/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623276373/91621938176) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf3285InnerLog : WideLogData :=
  innerPair70Data

set_option maxRecDepth 1000000 in
private theorem leaf3285LocalValidity :
    LeafFacts leaf3285Box leaf3285Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3285Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810969088) }) = true
      norm_num [leaf3285Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3285CertificateValid :
    WideCertificateValid leaf3285Box leaf3285Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi187ValidityFacts
    leaf3285LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3285CoverageChecked :
    coverageCheck (innerAD leaf3285Box) leaf3285InnerLog = true := by
  rfl'

private theorem leaf3285InnerLogValid :
    leaf3285InnerLog.Valid 8 (innerAD leaf3285Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint139PositiveFacts.valid leaf3285CoverageChecked

private noncomputable def leaf3285InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814663/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3285InputLogOnePlusV_eq :
    leaf3285InputLogOnePlusV = outerEnclosure 24
      (leaf3285Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3285RoundedFacts : LeafRoundedFacts 8
    leaf3285Certificate.logOnePlusV leaf3285InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3285InputLogOnePlusV_eq }

private noncomputable def leaf3285Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi187InputQChi innerPair70Input
    leaf3285InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3285LowerChecked :
    lowerCheck 24 leaf3285Box leaf3285Inputs = true := by
  rfl'

private theorem leaf3285CoversExact : CoversExact 8
    leaf3285Box leaf3285Certificate leaf3285InnerLog leaf3285Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi187RoundedFacts
    innerPair70RoundedFacts leaf3285RoundedFacts (by rfl)

private theorem leaf3285FlatSound : Sound leaf3285Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3285CertificateValid
    leaf3285InnerLogValid leaf3285CoversExact leaf3285LowerChecked

private noncomputable def leaf3286Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3286Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432882176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1831782653/1073741824) }, upper := { exponent := 0, mantissa := (14121/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869804031/274865764352) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf3286InnerLog : WideLogData :=
  innerPair90Data

set_option maxRecDepth 1000000 in
private theorem leaf3286LocalValidity :
    LeafFacts leaf3286Box leaf3286Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3286Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432882176) }) = true
      norm_num [leaf3286Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3286CertificateValid :
    WideCertificateValid leaf3286Box leaf3286Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi187ValidityFacts
    leaf3286LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3286CoverageChecked :
    coverageCheck (innerAD leaf3286Box) leaf3286InnerLog = true := by
  rfl'

private theorem leaf3286InnerLogValid :
    leaf3286InnerLog.Valid 8 (innerAD leaf3286Box) :=
  wideLogDataValid_of_cachedCheck endpoint20PositiveFacts
    endpoint139PositiveFacts.valid leaf3286CoverageChecked

private noncomputable def leaf3286InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629327/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3286InputLogOnePlusV_eq :
    leaf3286InputLogOnePlusV = outerEnclosure 24
      (leaf3286Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3286RoundedFacts : LeafRoundedFacts 8
    leaf3286Certificate.logOnePlusV leaf3286InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3286InputLogOnePlusV_eq }

private noncomputable def leaf3286Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi187InputQChi innerPair90Input
    leaf3286InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3286LowerChecked :
    lowerCheck 24 leaf3286Box leaf3286Inputs = true := by
  rfl'

private theorem leaf3286CoversExact : CoversExact 8
    leaf3286Box leaf3286Certificate leaf3286InnerLog leaf3286Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi187RoundedFacts
    innerPair90RoundedFacts leaf3286RoundedFacts (by rfl)

private theorem leaf3286FlatSound : Sound leaf3286Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3286CertificateValid
    leaf3286InnerLogValid leaf3286CoversExact leaf3286LowerChecked

private noncomputable def leaf3287Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3287Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432783872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1844364797/1073741824) }, upper := { exponent := 0, mantissa := (14217/8192) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869705727/274865567744) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf3287InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3287LocalValidity :
    LeafFacts leaf3287Box leaf3287Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3287Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432783872) }) = true
      norm_num [leaf3287Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3287CertificateValid :
    WideCertificateValid leaf3287Box leaf3287Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi188ValidityFacts
    leaf3287LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3287CoverageChecked :
    coverageCheck (innerAD leaf3287Box) leaf3287InnerLog = true := by
  rfl'

private theorem leaf3287InnerLogValid :
    leaf3287InnerLog.Valid 8 (innerAD leaf3287Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3287CoverageChecked

private noncomputable def leaf3287InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3287InputLogOnePlusV_eq :
    leaf3287InputLogOnePlusV = outerEnclosure 24
      (leaf3287Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3287RoundedFacts : LeafRoundedFacts 8
    leaf3287Certificate.logOnePlusV leaf3287InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3287InputLogOnePlusV_eq }

private noncomputable def leaf3287Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi188InputQChi innerPair64Input
    leaf3287InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3287LowerChecked :
    lowerCheck 24 leaf3287Box leaf3287Inputs = true := by
  rfl'

private theorem leaf3287CoversExact : CoversExact 8
    leaf3287Box leaf3287Certificate leaf3287InnerLog leaf3287Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi188RoundedFacts
    innerPair64RoundedFacts leaf3287RoundedFacts (by rfl)

private theorem leaf3287FlatSound : Sound leaf3287Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3287CertificateValid
    leaf3287InnerLogValid leaf3287CoversExact leaf3287LowerChecked

private noncomputable def leaf3288Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3288Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810919424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1847575863/1073741824) }, upper := { exponent := 0, mantissa := (7121/4096) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623226709/91621838848) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf3288InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3288LocalValidity :
    LeafFacts leaf3288Box leaf3288Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3288Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810919424) }) = true
      norm_num [leaf3288Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3288CertificateValid :
    WideCertificateValid leaf3288Box leaf3288Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi188ValidityFacts
    leaf3288LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3288CoverageChecked :
    coverageCheck (innerAD leaf3288Box) leaf3288InnerLog = true := by
  rfl'

private theorem leaf3288InnerLogValid :
    leaf3288InnerLog.Valid 8 (innerAD leaf3288Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3288CoverageChecked

private noncomputable def leaf3288InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3288InputLogOnePlusV_eq :
    leaf3288InputLogOnePlusV = outerEnclosure 24
      (leaf3288Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3288RoundedFacts : LeafRoundedFacts 8
    leaf3288Certificate.logOnePlusV leaf3288InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3288InputLogOnePlusV_eq }

private noncomputable def leaf3288Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi188InputQChi innerPair64Input
    leaf3288InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3288LowerChecked :
    lowerCheck 24 leaf3288Box leaf3288Inputs = true := by
  rfl'

private theorem leaf3288CoversExact : CoversExact 8
    leaf3288Box leaf3288Certificate leaf3288InnerLog leaf3288Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi188RoundedFacts
    innerPair64RoundedFacts leaf3288RoundedFacts (by rfl)

private theorem leaf3288FlatSound : Sound leaf3288Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3288CertificateValid
    leaf3288InnerLogValid leaf3288CoversExact leaf3288LowerChecked

private noncomputable def leaf3289Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3289Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432857088) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1834928187/1073741824) }, upper := { exponent := 0, mantissa := (28291/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869778943/274865714176) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf3289InnerLog : WideLogData :=
  innerPair90Data

set_option maxRecDepth 1000000 in
private theorem leaf3289LocalValidity :
    LeafFacts leaf3289Box leaf3289Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3289Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432857088) }) = true
      norm_num [leaf3289Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3289CertificateValid :
    WideCertificateValid leaf3289Box leaf3289Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi187ValidityFacts
    leaf3289LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3289CoverageChecked :
    coverageCheck (innerAD leaf3289Box) leaf3289InnerLog = true := by
  rfl'

private theorem leaf3289InnerLogValid :
    leaf3289InnerLog.Valid 8 (innerAD leaf3289Box) :=
  wideLogDataValid_of_cachedCheck endpoint20PositiveFacts
    endpoint139PositiveFacts.valid leaf3289CoverageChecked

private noncomputable def leaf3289InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629329/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3289InputLogOnePlusV_eq :
    leaf3289InputLogOnePlusV = outerEnclosure 24
      (leaf3289Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3289RoundedFacts : LeafRoundedFacts 8
    leaf3289Certificate.logOnePlusV leaf3289InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3289InputLogOnePlusV_eq }

private noncomputable def leaf3289Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi187InputQChi innerPair90Input
    leaf3289InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3289LowerChecked :
    lowerCheck 24 leaf3289Box leaf3289Inputs = true := by
  rfl'

private theorem leaf3289CoversExact : CoversExact 8
    leaf3289Box leaf3289Certificate leaf3289InnerLog leaf3289Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi187RoundedFacts
    innerPair90RoundedFacts leaf3289RoundedFacts (by rfl)

private theorem leaf3289FlatSound : Sound leaf3289Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3289CertificateValid
    leaf3289InnerLogValid leaf3289CoversExact leaf3289LowerChecked

private noncomputable def leaf3290Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3290Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162188800) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1838073721/1073741824) }, upper := { exponent := 0, mantissa := (7085/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324650257/18324377600) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf3290InnerLog : WideLogData :=
  innerPair90Data

set_option maxRecDepth 1000000 in
private theorem leaf3290LocalValidity :
    LeafFacts leaf3290Box leaf3290Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3290Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162188800) }) = true
      norm_num [leaf3290Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3290CertificateValid :
    WideCertificateValid leaf3290Box leaf3290Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi187ValidityFacts
    leaf3290LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3290CoverageChecked :
    coverageCheck (innerAD leaf3290Box) leaf3290InnerLog = true := by
  rfl'

private theorem leaf3290InnerLogValid :
    leaf3290InnerLog.Valid 8 (innerAD leaf3290Box) :=
  wideLogDataValid_of_cachedCheck endpoint20PositiveFacts
    endpoint139PositiveFacts.valid leaf3290CoverageChecked

private noncomputable def leaf3290InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814665/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3290InputLogOnePlusV_eq :
    leaf3290InputLogOnePlusV = outerEnclosure 24
      (leaf3290Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3290RoundedFacts : LeafRoundedFacts 8
    leaf3290Certificate.logOnePlusV leaf3290InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3290InputLogOnePlusV_eq }

private noncomputable def leaf3290Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi187InputQChi innerPair90Input
    leaf3290InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3290LowerChecked :
    lowerCheck 24 leaf3290Box leaf3290Inputs = true := by
  rfl'

private theorem leaf3290CoversExact : CoversExact 8
    leaf3290Box leaf3290Certificate leaf3290InnerLog leaf3290Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi187RoundedFacts
    innerPair90RoundedFacts leaf3290RoundedFacts (by rfl)

private theorem leaf3290FlatSound : Sound leaf3290Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3290CertificateValid
    leaf3290InnerLogValid leaf3290CoversExact leaf3290LowerChecked

private noncomputable def leaf3291Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3291Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432732672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1850786929/1073741824) }, upper := { exponent := 0, mantissa := (14267/8192) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869654527/274865465344) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf3291InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3291LocalValidity :
    LeafFacts leaf3291Box leaf3291Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3291Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432732672) }) = true
      norm_num [leaf3291Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3291CertificateValid :
    WideCertificateValid leaf3291Box leaf3291Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi188ValidityFacts
    leaf3291LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3291CoverageChecked :
    coverageCheck (innerAD leaf3291Box) leaf3291InnerLog = true := by
  rfl'

private theorem leaf3291InnerLogValid :
    leaf3291InnerLog.Valid 8 (innerAD leaf3291Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3291CoverageChecked

private noncomputable def leaf3291InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453667/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3291InputLogOnePlusV_eq :
    leaf3291InputLogOnePlusV = outerEnclosure 24
      (leaf3291Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3291RoundedFacts : LeafRoundedFacts 8
    leaf3291Certificate.logOnePlusV leaf3291InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3291InputLogOnePlusV_eq }

private noncomputable def leaf3291Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi188InputQChi innerPair64Input
    leaf3291InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3291LowerChecked :
    lowerCheck 24 leaf3291Box leaf3291Inputs = true := by
  rfl'

private theorem leaf3291CoversExact : CoversExact 8
    leaf3291Box leaf3291Certificate leaf3291InnerLog leaf3291Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi188RoundedFacts
    innerPair64RoundedFacts leaf3291RoundedFacts (by rfl)

private theorem leaf3291FlatSound : Sound leaf3291Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3291CertificateValid
    leaf3291InnerLogValid leaf3291CoversExact leaf3291LowerChecked

private noncomputable def leaf3292Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3292Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432707072) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1853997995/1073741824) }, upper := { exponent := 0, mantissa := (3573/2048) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869628927/274865414144) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf3292InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3292LocalValidity :
    LeafFacts leaf3292Box leaf3292Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3292Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432707072) }) = true
      norm_num [leaf3292Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3292CertificateValid :
    WideCertificateValid leaf3292Box leaf3292Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi188ValidityFacts
    leaf3292LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3292CoverageChecked :
    coverageCheck (innerAD leaf3292Box) leaf3292InnerLog = true := by
  rfl'

private theorem leaf3292InnerLogValid :
    leaf3292InnerLog.Valid 8 (innerAD leaf3292Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3292CoverageChecked

private noncomputable def leaf3292InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814669/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3292InputLogOnePlusV_eq :
    leaf3292InputLogOnePlusV = outerEnclosure 24
      (leaf3292Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3292RoundedFacts : LeafRoundedFacts 8
    leaf3292Certificate.logOnePlusV leaf3292InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3292InputLogOnePlusV_eq }

private noncomputable def leaf3292Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi188InputQChi innerPair64Input
    leaf3292InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3292LowerChecked :
    lowerCheck 24 leaf3292Box leaf3292Inputs = true := by
  rfl'

private theorem leaf3292CoversExact : CoversExact 8
    leaf3292Box leaf3292Certificate leaf3292InnerLog leaf3292Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi188RoundedFacts
    innerPair64RoundedFacts leaf3292RoundedFacts (by rfl)

private theorem leaf3292FlatSound : Sound leaf3292Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3292CertificateValid
    leaf3292InnerLogValid leaf3292CoversExact leaf3292LowerChecked

private noncomputable def leaf3293Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3293Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486532096) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1860092475/1073741824) }, upper := { exponent := 0, mantissa := (28675/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973916467/54973064192) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf3293InnerLog : WideLogData :=
  innerPair204Data

set_option maxRecDepth 1000000 in
private theorem leaf3293LocalValidity :
    LeafFacts leaf3293Box leaf3293Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3293Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486532096) }) = true
      norm_num [leaf3293Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3293CertificateValid :
    WideCertificateValid leaf3293Box leaf3293Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi193ValidityFacts
    leaf3293LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3293CoverageChecked :
    coverageCheck (innerAD leaf3293Box) leaf3293InnerLog = true := by
  rfl'

private theorem leaf3293InnerLogValid :
    leaf3293InnerLog.Valid 8 (innerAD leaf3293Box) :=
  wideLogDataValid_of_cachedCheck endpoint62PositiveFacts
    endpoint63PositiveFacts.valid leaf3293CoverageChecked

private noncomputable def leaf3293InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3293InputLogOnePlusV_eq :
    leaf3293InputLogOnePlusV = outerEnclosure 24
      (leaf3293Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3293RoundedFacts : LeafRoundedFacts 8
    leaf3293Certificate.logOnePlusV leaf3293InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3293InputLogOnePlusV_eq }

private noncomputable def leaf3293Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi193InputQChi innerPair204Input
    leaf3293InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3293LowerChecked :
    lowerCheck 24 leaf3293Box leaf3293Inputs = true := by
  rfl'

private theorem leaf3293CoversExact : CoversExact 8
    leaf3293Box leaf3293Certificate leaf3293InnerLog leaf3293Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi193RoundedFacts
    innerPair204RoundedFacts leaf3293RoundedFacts (by rfl)

private theorem leaf3293FlatSound : Sound leaf3293Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3293CertificateValid
    leaf3293InnerLogValid leaf3293CoversExact leaf3293LowerChecked

private noncomputable def leaf3294Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3294Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3196207485/3196107776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1863369073/1073741824) }, upper := { exponent := 0, mantissa := (14363/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6392315261/6392215552) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf3294InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3294LocalValidity :
    LeafFacts leaf3294Box leaf3294Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3294Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3196207485/3196107776) }) = true
      norm_num [leaf3294Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3294CertificateValid :
    WideCertificateValid leaf3294Box leaf3294Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi193ValidityFacts
    leaf3294LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3294CoverageChecked :
    coverageCheck (innerAD leaf3294Box) leaf3294InnerLog = true := by
  rfl'

private theorem leaf3294InnerLogValid :
    leaf3294InnerLog.Valid 8 (innerAD leaf3294Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3294CoverageChecked

private noncomputable def leaf3294InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814671/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3294InputLogOnePlusV_eq :
    leaf3294InputLogOnePlusV = outerEnclosure 24
      (leaf3294Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3294RoundedFacts : LeafRoundedFacts 8
    leaf3294Certificate.logOnePlusV leaf3294InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3294InputLogOnePlusV_eq }

private noncomputable def leaf3294Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi193InputQChi innerPair430Input
    leaf3294InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3294LowerChecked :
    lowerCheck 24 leaf3294Box leaf3294Inputs = true := by
  rfl'

private theorem leaf3294CoversExact : CoversExact 8
    leaf3294Box leaf3294Certificate leaf3294InnerLog leaf3294Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi193RoundedFacts
    innerPair430RoundedFacts leaf3294RoundedFacts (by rfl)

private theorem leaf3294FlatSound : Sound leaf3294Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3294CertificateValid
    leaf3294InnerLogValid leaf3294CoversExact leaf3294LowerChecked

private noncomputable def leaf3295Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3295Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810845696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1875820153/1073741824) }, upper := { exponent := 0, mantissa := (7229/4096) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623152981/91621691392) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf3295InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3295LocalValidity :
    LeafFacts leaf3295Box leaf3295Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3295Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810845696) }) = true
      norm_num [leaf3295Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3295CertificateValid :
    WideCertificateValid leaf3295Box leaf3295Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi194ValidityFacts
    leaf3295LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3295CoverageChecked :
    coverageCheck (innerAD leaf3295Box) leaf3295InnerLog = true := by
  rfl'

private theorem leaf3295InnerLogValid :
    leaf3295InnerLog.Valid 8 (innerAD leaf3295Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3295CoverageChecked

private noncomputable def leaf3295InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907337/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3295InputLogOnePlusV_eq :
    leaf3295InputLogOnePlusV = outerEnclosure 24
      (leaf3295Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3295RoundedFacts : LeafRoundedFacts 8
    leaf3295Certificate.logOnePlusV leaf3295InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3295InputLogOnePlusV_eq }

private noncomputable def leaf3295Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi194InputQChi innerPair430Input
    leaf3295InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3295LowerChecked :
    lowerCheck 24 leaf3295Box leaf3295Inputs = true := by
  rfl'

private theorem leaf3295CoversExact : CoversExact 8
    leaf3295Box leaf3295Certificate leaf3295InnerLog leaf3295Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi194RoundedFacts
    innerPair430RoundedFacts leaf3295RoundedFacts (by rfl)

private theorem leaf3295FlatSound : Sound leaf3295Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3295CertificateValid
    leaf3295InnerLogValid leaf3295CoversExact leaf3295LowerChecked

private noncomputable def leaf3296Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3296Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432510464) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1879162283/1073741824) }, upper := { exponent := 0, mantissa := (3621/2048) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869432319/274865020928) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf3296InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3296LocalValidity :
    LeafFacts leaf3296Box leaf3296Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3296Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432510464) }) = true
      norm_num [leaf3296Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3296CertificateValid :
    WideCertificateValid leaf3296Box leaf3296Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi194ValidityFacts
    leaf3296LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3296CoverageChecked :
    coverageCheck (innerAD leaf3296Box) leaf3296InnerLog = true := by
  rfl'

private theorem leaf3296InnerLogValid :
    leaf3296InnerLog.Valid 8 (innerAD leaf3296Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3296CoverageChecked

private noncomputable def leaf3296InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3296InputLogOnePlusV_eq :
    leaf3296InputLogOnePlusV = outerEnclosure 24
      (leaf3296Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3296RoundedFacts : LeafRoundedFacts 8
    leaf3296Certificate.logOnePlusV leaf3296InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3296InputLogOnePlusV_eq }

private noncomputable def leaf3296Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi194InputQChi innerPair78Input
    leaf3296InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3296LowerChecked :
    lowerCheck 24 leaf3296Box leaf3296Inputs = true := by
  rfl'

private theorem leaf3296CoversExact : CoversExact 8
    leaf3296Box leaf3296Certificate leaf3296InnerLog leaf3296Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi194RoundedFacts
    innerPair78RoundedFacts leaf3296RoundedFacts (by rfl)

private theorem leaf3296FlatSound : Sound leaf3296Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3296CertificateValid
    leaf3296InnerLogValid leaf3296CoversExact leaf3296LowerChecked

private noncomputable def leaf3297Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3297Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432608256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1866645671/1073741824) }, upper := { exponent := 0, mantissa := (28777/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869530111/274865216512) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf3297InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3297LocalValidity :
    LeafFacts leaf3297Box leaf3297Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3297Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432608256) }) = true
      norm_num [leaf3297Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3297CertificateValid :
    WideCertificateValid leaf3297Box leaf3297Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi193ValidityFacts
    leaf3297LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3297CoverageChecked :
    coverageCheck (innerAD leaf3297Box) leaf3297InnerLog = true := by
  rfl'

private theorem leaf3297InnerLogValid :
    leaf3297InnerLog.Valid 8 (innerAD leaf3297Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3297CoverageChecked

private noncomputable def leaf3297InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf3297InputLogOnePlusV_eq :
    leaf3297InputLogOnePlusV = outerEnclosure 24
      (leaf3297Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3297RoundedFacts : LeafRoundedFacts 8
    leaf3297Certificate.logOnePlusV leaf3297InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3297InputLogOnePlusV_eq }

private noncomputable def leaf3297Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi193InputQChi innerPair430Input
    leaf3297InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3297LowerChecked :
    lowerCheck 24 leaf3297Box leaf3297Inputs = true := by
  rfl'

private theorem leaf3297CoversExact : CoversExact 8
    leaf3297Box leaf3297Certificate leaf3297InnerLog leaf3297Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi193RoundedFacts
    innerPair430RoundedFacts leaf3297RoundedFacts (by rfl)

private theorem leaf3297FlatSound : Sound leaf3297Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3297CertificateValid
    leaf3297InnerLogValid leaf3297CoversExact leaf3297LowerChecked

private noncomputable def leaf3298Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3298Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432582144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1869922269/1073741824) }, upper := { exponent := 0, mantissa := (7207/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869503999/274865164288) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf3298InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3298LocalValidity :
    LeafFacts leaf3298Box leaf3298Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3298Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432582144) }) = true
      norm_num [leaf3298Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3298CertificateValid :
    WideCertificateValid leaf3298Box leaf3298Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi193ValidityFacts
    leaf3298LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3298CoverageChecked :
    coverageCheck (innerAD leaf3298Box) leaf3298InnerLog = true := by
  rfl'

private theorem leaf3298InnerLogValid :
    leaf3298InnerLog.Valid 8 (innerAD leaf3298Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3298CoverageChecked

private noncomputable def leaf3298InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814673/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3298InputLogOnePlusV_eq :
    leaf3298InputLogOnePlusV = outerEnclosure 24
      (leaf3298Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3298RoundedFacts : LeafRoundedFacts 8
    leaf3298Certificate.logOnePlusV leaf3298InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3298InputLogOnePlusV_eq }

private noncomputable def leaf3298Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi193InputQChi innerPair430Input
    leaf3298InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3298LowerChecked :
    lowerCheck 24 leaf3298Box leaf3298Inputs = true := by
  rfl'

private theorem leaf3298CoversExact : CoversExact 8
    leaf3298Box leaf3298Certificate leaf3298InnerLog leaf3298Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi193RoundedFacts
    innerPair430RoundedFacts leaf3298RoundedFacts (by rfl)

private theorem leaf3298FlatSound : Sound leaf3298Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3298CertificateValid
    leaf3298InnerLogValid leaf3298CoversExact leaf3298LowerChecked

private noncomputable def leaf3299Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3299Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486496768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1882504413/1073741824) }, upper := { exponent := 0, mantissa := (7255/4096) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973881139/54972993536) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf3299InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3299LocalValidity :
    LeafFacts leaf3299Box leaf3299Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3299Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486496768) }) = true
      norm_num [leaf3299Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3299CertificateValid :
    WideCertificateValid leaf3299Box leaf3299Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi194ValidityFacts
    leaf3299LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3299CoverageChecked :
    coverageCheck (innerAD leaf3299Box) leaf3299InnerLog = true := by
  rfl'

private theorem leaf3299InnerLogValid :
    leaf3299InnerLog.Valid 8 (innerAD leaf3299Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3299CoverageChecked

private noncomputable def leaf3299InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3299InputLogOnePlusV_eq :
    leaf3299InputLogOnePlusV = outerEnclosure 24
      (leaf3299Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3299RoundedFacts : LeafRoundedFacts 8
    leaf3299Certificate.logOnePlusV leaf3299InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3299InputLogOnePlusV_eq }

private noncomputable def leaf3299Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi194InputQChi innerPair78Input
    leaf3299InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3299LowerChecked :
    lowerCheck 24 leaf3299Box leaf3299Inputs = true := by
  rfl'

private theorem leaf3299CoversExact : CoversExact 8
    leaf3299Box leaf3299Certificate leaf3299InnerLog leaf3299Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi194RoundedFacts
    innerPair78RoundedFacts leaf3299RoundedFacts (by rfl)

private theorem leaf3299FlatSound : Sound leaf3299Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3299CertificateValid
    leaf3299InnerLogValid leaf3299CoversExact leaf3299LowerChecked

private noncomputable def leaf3300Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3300Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090091008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1885846543/1073741824) }, upper := { exponent := 0, mantissa := (1817/1024) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180347373/10180182016) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf3300InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3300LocalValidity :
    LeafFacts leaf3300Box leaf3300Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3300Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090091008) }) = true
      norm_num [leaf3300Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3300CertificateValid :
    WideCertificateValid leaf3300Box leaf3300Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi194ValidityFacts
    leaf3300LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3300CoverageChecked :
    coverageCheck (innerAD leaf3300Box) leaf3300InnerLog = true := by
  rfl'

private theorem leaf3300InnerLogValid :
    leaf3300InnerLog.Valid 8 (innerAD leaf3300Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3300CoverageChecked

private noncomputable def leaf3300InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629353/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3300InputLogOnePlusV_eq :
    leaf3300InputLogOnePlusV = outerEnclosure 24
      (leaf3300Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3300RoundedFacts : LeafRoundedFacts 8
    leaf3300Certificate.logOnePlusV leaf3300InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3300InputLogOnePlusV_eq }

private noncomputable def leaf3300Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi194InputQChi innerPair78Input
    leaf3300InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3300LowerChecked :
    lowerCheck 24 leaf3300Box leaf3300Inputs = true := by
  rfl'

private theorem leaf3300CoversExact : CoversExact 8
    leaf3300Box leaf3300Certificate leaf3300InnerLog leaf3300Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi194RoundedFacts
    innerPair78RoundedFacts leaf3300RoundedFacts (by rfl)

private theorem leaf3300FlatSound : Sound leaf3300Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3300CertificateValid
    leaf3300InnerLogValid leaf3300CoversExact leaf3300LowerChecked

private noncomputable def leaf3301Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3301Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432806912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1841219255/1073741824) }, upper := { exponent := 0, mantissa := (28389/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869728767/274865613824) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf3301InnerLog : WideLogData :=
  innerPair90Data

set_option maxRecDepth 1000000 in
private theorem leaf3301LocalValidity :
    LeafFacts leaf3301Box leaf3301Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3301Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432806912) }) = true
      norm_num [leaf3301Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3301CertificateValid :
    WideCertificateValid leaf3301Box leaf3301Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi187ValidityFacts
    leaf3301LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3301CoverageChecked :
    coverageCheck (innerAD leaf3301Box) leaf3301InnerLog = true := by
  rfl'

private theorem leaf3301InnerLogValid :
    leaf3301InnerLog.Valid 8 (innerAD leaf3301Box) :=
  wideLogDataValid_of_cachedCheck endpoint20PositiveFacts
    endpoint139PositiveFacts.valid leaf3301CoverageChecked

private noncomputable def leaf3301InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907333/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3301InputLogOnePlusV_eq :
    leaf3301InputLogOnePlusV = outerEnclosure 24
      (leaf3301Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3301RoundedFacts : LeafRoundedFacts 8
    leaf3301Certificate.logOnePlusV leaf3301InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3301InputLogOnePlusV_eq }

private noncomputable def leaf3301Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi187InputQChi innerPair90Input
    leaf3301InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3301LowerChecked :
    lowerCheck 24 leaf3301Box leaf3301Inputs = true := by
  rfl'

private theorem leaf3301CoversExact : CoversExact 8
    leaf3301Box leaf3301Certificate leaf3301InnerLog leaf3301Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi187RoundedFacts
    innerPair90RoundedFacts leaf3301RoundedFacts (by rfl)

private theorem leaf3301FlatSound : Sound leaf3301Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3301CertificateValid
    leaf3301InnerLogValid leaf3301CoversExact leaf3301LowerChecked

private noncomputable def leaf3302Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3302Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432781824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1844364789/1073741824) }, upper := { exponent := 0, mantissa := (14219/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869703679/274865563648) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf3302InnerLog : WideLogData :=
  innerPair487Data

set_option maxRecDepth 1000000 in
private theorem leaf3302LocalValidity :
    LeafFacts leaf3302Box leaf3302Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3302Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432781824) }) = true
      norm_num [leaf3302Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3302CertificateValid :
    WideCertificateValid leaf3302Box leaf3302Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi187ValidityFacts
    leaf3302LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3302CoverageChecked :
    coverageCheck (innerAD leaf3302Box) leaf3302InnerLog = true := by
  rfl'

private theorem leaf3302InnerLogValid :
    leaf3302InnerLog.Valid 8 (innerAD leaf3302Box) :=
  wideLogDataValid_of_cachedCheck endpoint212PositiveFacts
    endpoint213PositiveFacts.valid leaf3302CoverageChecked

private noncomputable def leaf3302InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629333/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3302InputLogOnePlusV_eq :
    leaf3302InputLogOnePlusV = outerEnclosure 24
      (leaf3302Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3302RoundedFacts : LeafRoundedFacts 8
    leaf3302Certificate.logOnePlusV leaf3302InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3302InputLogOnePlusV_eq }

private noncomputable def leaf3302Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi187InputQChi innerPair487Input
    leaf3302InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3302LowerChecked :
    lowerCheck 24 leaf3302Box leaf3302Inputs = true := by
  rfl'

private theorem leaf3302CoversExact : CoversExact 8
    leaf3302Box leaf3302Certificate leaf3302InnerLog leaf3302Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi187RoundedFacts
    innerPair487RoundedFacts leaf3302RoundedFacts (by rfl)

private theorem leaf3302FlatSound : Sound leaf3302Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3302CertificateValid
    leaf3302InnerLogValid leaf3302CoversExact leaf3302LowerChecked

private noncomputable def leaf3303Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3303Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810893824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1857209061/1073741824) }, upper := { exponent := 0, mantissa := (14317/8192) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623201109/91621787648) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf3303InnerLog : WideLogData :=
  innerPair64Data

set_option maxRecDepth 1000000 in
private theorem leaf3303LocalValidity :
    LeafFacts leaf3303Box leaf3303Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3303Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810893824) }) = true
      norm_num [leaf3303Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3303CertificateValid :
    WideCertificateValid leaf3303Box leaf3303Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi188ValidityFacts
    leaf3303LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3303CoverageChecked :
    coverageCheck (innerAD leaf3303Box) leaf3303InnerLog = true := by
  rfl'

private theorem leaf3303InnerLogValid :
    leaf3303InnerLog.Valid 8 (innerAD leaf3303Box) :=
  wideLogDataValid_of_cachedCheck endpoint15PositiveFacts
    endpoint16PositiveFacts.valid leaf3303CoverageChecked

private noncomputable def leaf3303InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907335/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3303InputLogOnePlusV_eq :
    leaf3303InputLogOnePlusV = outerEnclosure 24
      (leaf3303Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3303RoundedFacts : LeafRoundedFacts 8
    leaf3303Certificate.logOnePlusV leaf3303InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3303InputLogOnePlusV_eq }

private noncomputable def leaf3303Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi188InputQChi innerPair64Input
    leaf3303InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3303LowerChecked :
    lowerCheck 24 leaf3303Box leaf3303Inputs = true := by
  rfl'

private theorem leaf3303CoversExact : CoversExact 8
    leaf3303Box leaf3303Certificate leaf3303InnerLog leaf3303Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi188RoundedFacts
    innerPair64RoundedFacts leaf3303RoundedFacts (by rfl)

private theorem leaf3303FlatSound : Sound leaf3303Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3303CertificateValid
    leaf3303InnerLogValid leaf3303CoversExact leaf3303LowerChecked

private noncomputable def leaf3304Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3304Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432655872) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1860420127/1073741824) }, upper := { exponent := 0, mantissa := (7171/4096) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869577727/274865311744) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf3304InnerLog : WideLogData :=
  innerPair463Data

set_option maxRecDepth 1000000 in
private theorem leaf3304LocalValidity :
    LeafFacts leaf3304Box leaf3304Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3304Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432655872) }) = true
      norm_num [leaf3304Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3304CertificateValid :
    WideCertificateValid leaf3304Box leaf3304Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi188ValidityFacts
    leaf3304LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3304CoverageChecked :
    coverageCheck (innerAD leaf3304Box) leaf3304InnerLog = true := by
  rfl'

private theorem leaf3304InnerLogValid :
    leaf3304InnerLog.Valid 8 (innerAD leaf3304Box) :=
  wideLogDataValid_of_cachedCheck endpoint180PositiveFacts
    endpoint178PositiveFacts.valid leaf3304CoverageChecked

private noncomputable def leaf3304InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629341/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3304InputLogOnePlusV_eq :
    leaf3304InputLogOnePlusV = outerEnclosure 24
      (leaf3304Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3304RoundedFacts : LeafRoundedFacts 8
    leaf3304Certificate.logOnePlusV leaf3304InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3304InputLogOnePlusV_eq }

private noncomputable def leaf3304Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi188InputQChi innerPair463Input
    leaf3304InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3304LowerChecked :
    lowerCheck 24 leaf3304Box leaf3304Inputs = true := by
  rfl'

private theorem leaf3304CoversExact : CoversExact 8
    leaf3304Box leaf3304Certificate leaf3304InnerLog leaf3304Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi188RoundedFacts
    innerPair463RoundedFacts leaf3304RoundedFacts (by rfl)

private theorem leaf3304FlatSound : Sound leaf3304Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3304CertificateValid
    leaf3304InnerLogValid leaf3304CoversExact leaf3304LowerChecked

private noncomputable def leaf3305Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3305Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (898280535/898253312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1847510323/1073741824) }, upper := { exponent := 0, mantissa := (28487/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1796533847/1796506624) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf3305InnerLog : WideLogData :=
  innerPair207Data

set_option maxRecDepth 1000000 in
private theorem leaf3305LocalValidity :
    LeafFacts leaf3305Box leaf3305Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3305Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (898280535/898253312) }) = true
      norm_num [leaf3305Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3305CertificateValid :
    WideCertificateValid leaf3305Box leaf3305Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi187ValidityFacts
    leaf3305LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3305CoverageChecked :
    coverageCheck (innerAD leaf3305Box) leaf3305InnerLog = true := by
  rfl'

private theorem leaf3305InnerLogValid :
    leaf3305InnerLog.Valid 8 (innerAD leaf3305Box) :=
  wideLogDataValid_of_cachedCheck endpoint62PositiveFacts
    endpoint214PositiveFacts.valid leaf3305CoverageChecked

private noncomputable def leaf3305InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629335/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3305InputLogOnePlusV_eq :
    leaf3305InputLogOnePlusV = outerEnclosure 24
      (leaf3305Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3305RoundedFacts : LeafRoundedFacts 8
    leaf3305Certificate.logOnePlusV leaf3305InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3305InputLogOnePlusV_eq }

private noncomputable def leaf3305Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi187InputQChi innerPair207Input
    leaf3305InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3305LowerChecked :
    lowerCheck 24 leaf3305Box leaf3305Inputs = true := by
  rfl'

private theorem leaf3305CoversExact : CoversExact 8
    leaf3305Box leaf3305Certificate leaf3305InnerLog leaf3305Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi187RoundedFacts
    innerPair207RoundedFacts leaf3305RoundedFacts (by rfl)

private theorem leaf3305FlatSound : Sound leaf3305Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3305CertificateValid
    leaf3305InnerLogValid leaf3305CoversExact leaf3305LowerChecked

private noncomputable def leaf3306Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (3/16), chiHi := (49/256) }

private noncomputable def leaf3306Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432731648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1850655857/1073741824) }, upper := { exponent := 0, mantissa := (3567/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi187LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869653503/274865463296) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf3306InnerLog : WideLogData :=
  innerPair460Data

set_option maxRecDepth 1000000 in
private theorem leaf3306LocalValidity :
    LeafFacts leaf3306Box leaf3306Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3306Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432731648) }) = true
      norm_num [leaf3306Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3306CertificateValid :
    WideCertificateValid leaf3306Box leaf3306Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi187ValidityFacts
    leaf3306LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3306CoverageChecked :
    coverageCheck (innerAD leaf3306Box) leaf3306InnerLog = true := by
  rfl'

private theorem leaf3306InnerLogValid :
    leaf3306InnerLog.Valid 8 (innerAD leaf3306Box) :=
  wideLogDataValid_of_cachedCheck endpoint179PositiveFacts
    endpoint214PositiveFacts.valid leaf3306CoverageChecked

private noncomputable def leaf3306InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629337/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3306InputLogOnePlusV_eq :
    leaf3306InputLogOnePlusV = outerEnclosure 24
      (leaf3306Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3306RoundedFacts : LeafRoundedFacts 8
    leaf3306Certificate.logOnePlusV leaf3306InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3306InputLogOnePlusV_eq }

private noncomputable def leaf3306Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi187InputQChi innerPair460Input
    leaf3306InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3306LowerChecked :
    lowerCheck 24 leaf3306Box leaf3306Inputs = true := by
  rfl'

private theorem leaf3306CoversExact : CoversExact 8
    leaf3306Box leaf3306Certificate leaf3306InnerLog leaf3306Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi187RoundedFacts
    innerPair460RoundedFacts leaf3306RoundedFacts (by rfl)

private theorem leaf3306FlatSound : Sound leaf3306Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3306CertificateValid
    leaf3306InnerLogValid leaf3306CoversExact leaf3306LowerChecked

private noncomputable def leaf3307Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3307Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432630272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1863631193/1073741824) }, upper := { exponent := 0, mantissa := (14367/8192) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869552127/274865260544) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf3307InnerLog : WideLogData :=
  innerPair432Data

set_option maxRecDepth 1000000 in
private theorem leaf3307LocalValidity :
    LeafFacts leaf3307Box leaf3307Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3307Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432630272) }) = true
      norm_num [leaf3307Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3307CertificateValid :
    WideCertificateValid leaf3307Box leaf3307Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi188ValidityFacts
    leaf3307LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3307CoverageChecked :
    coverageCheck (innerAD leaf3307Box) leaf3307InnerLog = true := by
  rfl'

private theorem leaf3307InnerLogValid :
    leaf3307InnerLog.Valid 8 (innerAD leaf3307Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint178PositiveFacts.valid leaf3307CoverageChecked

private noncomputable def leaf3307InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629343/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3307InputLogOnePlusV_eq :
    leaf3307InputLogOnePlusV = outerEnclosure 24
      (leaf3307Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3307RoundedFacts : LeafRoundedFacts 8
    leaf3307Certificate.logOnePlusV leaf3307InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3307InputLogOnePlusV_eq }

private noncomputable def leaf3307Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi188InputQChi innerPair432Input
    leaf3307InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3307LowerChecked :
    lowerCheck 24 leaf3307Box leaf3307Inputs = true := by
  rfl'

private theorem leaf3307CoversExact : CoversExact 8
    leaf3307Box leaf3307Certificate leaf3307InnerLog leaf3307Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi188RoundedFacts
    innerPair432RoundedFacts leaf3307RoundedFacts (by rfl)

private theorem leaf3307FlatSound : Sound leaf3307Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3307CertificateValid
    leaf3307InnerLogValid leaf3307CoversExact leaf3307LowerChecked

private noncomputable def leaf3308Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (49/256), chiHi := (25/128) }

private noncomputable def leaf3308Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (15270769095/15270289408) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1866842259/1073741824) }, upper := { exponent := 0, mantissa := (1799/1024) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi188LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (30541058503/30540578816) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf3308InnerLog : WideLogData :=
  innerPair489Data

set_option maxRecDepth 1000000 in
private theorem leaf3308LocalValidity :
    LeafFacts leaf3308Box leaf3308Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3308Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (15270769095/15270289408) }) = true
      norm_num [leaf3308Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3308CertificateValid :
    WideCertificateValid leaf3308Box leaf3308Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi188ValidityFacts
    leaf3308LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3308CoverageChecked :
    coverageCheck (innerAD leaf3308Box) leaf3308InnerLog = true := by
  rfl'

private theorem leaf3308InnerLogValid :
    leaf3308InnerLog.Valid 8 (innerAD leaf3308Box) :=
  wideLogDataValid_of_cachedCheck endpoint213PositiveFacts
    endpoint66PositiveFacts.valid leaf3308CoverageChecked

private noncomputable def leaf3308InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363417/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf3308InputLogOnePlusV_eq :
    leaf3308InputLogOnePlusV = outerEnclosure 24
      (leaf3308Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3308RoundedFacts : LeafRoundedFacts 8
    leaf3308Certificate.logOnePlusV leaf3308InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3308InputLogOnePlusV_eq }

private noncomputable def leaf3308Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi188InputQChi innerPair489Input
    leaf3308InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3308LowerChecked :
    lowerCheck 24 leaf3308Box leaf3308Inputs = true := by
  rfl'

private theorem leaf3308CoversExact : CoversExact 8
    leaf3308Box leaf3308Certificate leaf3308InnerLog leaf3308Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi188RoundedFacts
    innerPair489RoundedFacts leaf3308RoundedFacts (by rfl)

private theorem leaf3308FlatSound : Sound leaf3308Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3308CertificateValid
    leaf3308InnerLogValid leaf3308CoversExact leaf3308LowerChecked

private noncomputable def leaf3309Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3309Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432556032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1873198867/1073741824) }, upper := { exponent := 0, mantissa := (28879/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869477887/274865112064) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf3309InnerLog : WideLogData :=
  innerPair430Data

set_option maxRecDepth 1000000 in
private theorem leaf3309LocalValidity :
    LeafFacts leaf3309Box leaf3309Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3309Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432556032) }) = true
      norm_num [leaf3309Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3309CertificateValid :
    WideCertificateValid leaf3309Box leaf3309Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi193ValidityFacts
    leaf3309LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3309CoverageChecked :
    coverageCheck (innerAD leaf3309Box) leaf3309InnerLog = true := by
  rfl'

private theorem leaf3309InnerLogValid :
    leaf3309InnerLog.Valid 8 (innerAD leaf3309Box) :=
  wideLogDataValid_of_cachedCheck endpoint139PositiveFacts
    endpoint63PositiveFacts.valid leaf3309CoverageChecked

private noncomputable def leaf3309InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629347/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3309InputLogOnePlusV_eq :
    leaf3309InputLogOnePlusV = outerEnclosure 24
      (leaf3309Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3309RoundedFacts : LeafRoundedFacts 8
    leaf3309Certificate.logOnePlusV leaf3309InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3309InputLogOnePlusV_eq }

private noncomputable def leaf3309Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi193InputQChi innerPair430Input
    leaf3309InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3309LowerChecked :
    lowerCheck 24 leaf3309Box leaf3309Inputs = true := by
  rfl'

private theorem leaf3309CoversExact : CoversExact 8
    leaf3309Box leaf3309Certificate leaf3309InnerLog leaf3309Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi193RoundedFacts
    innerPair430RoundedFacts leaf3309RoundedFacts (by rfl)

private theorem leaf3309FlatSound : Sound leaf3309Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3309CertificateValid
    leaf3309InnerLogValid leaf3309CoversExact leaf3309LowerChecked

private noncomputable def leaf3310Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3310Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486505984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1876475465/1073741824) }, upper := { exponent := 0, mantissa := (14465/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973890355/54973011968) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf3310InnerLog : WideLogData :=
  innerPair490Data

set_option maxRecDepth 1000000 in
private theorem leaf3310LocalValidity :
    LeafFacts leaf3310Box leaf3310Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3310Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486505984) }) = true
      norm_num [leaf3310Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3310CertificateValid :
    WideCertificateValid leaf3310Box leaf3310Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi193ValidityFacts
    leaf3310LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3310CoverageChecked :
    coverageCheck (innerAD leaf3310Box) leaf3310InnerLog = true := by
  rfl'

private theorem leaf3310InnerLogValid :
    leaf3310InnerLog.Valid 8 (innerAD leaf3310Box) :=
  wideLogDataValid_of_cachedCheck endpoint215PositiveFacts
    endpoint216PositiveFacts.valid leaf3310CoverageChecked

private noncomputable def leaf3310InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629349/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3310InputLogOnePlusV_eq :
    leaf3310InputLogOnePlusV = outerEnclosure 24
      (leaf3310Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3310RoundedFacts : LeafRoundedFacts 8
    leaf3310Certificate.logOnePlusV leaf3310InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3310InputLogOnePlusV_eq }

private noncomputable def leaf3310Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi193InputQChi innerPair490Input
    leaf3310InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3310LowerChecked :
    lowerCheck 24 leaf3310Box leaf3310Inputs = true := by
  rfl'

private theorem leaf3310CoversExact : CoversExact 8
    leaf3310Box leaf3310Certificate leaf3310InnerLog leaf3310Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi193RoundedFacts
    innerPair490RoundedFacts leaf3310RoundedFacts (by rfl)

private theorem leaf3310FlatSound : Sound leaf3310Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3310CertificateValid
    leaf3310InnerLogValid leaf3310CoversExact leaf3310LowerChecked

private noncomputable def leaf3311Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3311Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432430592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1889188673/1073741824) }, upper := { exponent := 0, mantissa := (7281/4096) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869352447/274864861184) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf3311InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3311LocalValidity :
    LeafFacts leaf3311Box leaf3311Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3311Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432430592) }) = true
      norm_num [leaf3311Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3311CertificateValid :
    WideCertificateValid leaf3311Box leaf3311Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi194ValidityFacts
    leaf3311LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3311CoverageChecked :
    coverageCheck (innerAD leaf3311Box) leaf3311InnerLog = true := by
  rfl'

private theorem leaf3311InnerLogValid :
    leaf3311InnerLog.Valid 8 (innerAD leaf3311Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3311CoverageChecked

private noncomputable def leaf3311InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629355/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3311InputLogOnePlusV_eq :
    leaf3311InputLogOnePlusV = outerEnclosure 24
      (leaf3311Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3311RoundedFacts : LeafRoundedFacts 8
    leaf3311Certificate.logOnePlusV leaf3311InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3311InputLogOnePlusV_eq }

private noncomputable def leaf3311Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi194InputQChi innerPair78Input
    leaf3311InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3311LowerChecked :
    lowerCheck 24 leaf3311Box leaf3311Inputs = true := by
  rfl'

private theorem leaf3311CoversExact : CoversExact 8
    leaf3311Box leaf3311Certificate leaf3311InnerLog leaf3311Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi194RoundedFacts
    innerPair78RoundedFacts leaf3311RoundedFacts (by rfl)

private theorem leaf3311FlatSound : Sound leaf3311Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3311CertificateValid
    leaf3311InnerLogValid leaf3311CoversExact leaf3311LowerChecked

private noncomputable def leaf3312Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3312Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432403968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1892530803/1073741824) }, upper := { exponent := 0, mantissa := (3647/2048) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869325823/274864807936) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf3312InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3312LocalValidity :
    LeafFacts leaf3312Box leaf3312Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3312Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432403968) }) = true
      norm_num [leaf3312Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3312CertificateValid :
    WideCertificateValid leaf3312Box leaf3312Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi194ValidityFacts
    leaf3312LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3312CoverageChecked :
    coverageCheck (innerAD leaf3312Box) leaf3312InnerLog = true := by
  rfl'

private theorem leaf3312InnerLogValid :
    leaf3312InnerLog.Valid 8 (innerAD leaf3312Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3312CoverageChecked

private noncomputable def leaf3312InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629357/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3312InputLogOnePlusV_eq :
    leaf3312InputLogOnePlusV = outerEnclosure 24
      (leaf3312Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3312RoundedFacts : LeafRoundedFacts 8
    leaf3312Certificate.logOnePlusV leaf3312InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3312InputLogOnePlusV_eq }

private noncomputable def leaf3312Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi194InputQChi innerPair78Input
    leaf3312InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3312LowerChecked :
    lowerCheck 24 leaf3312Box leaf3312Inputs = true := by
  rfl'

private theorem leaf3312CoversExact : CoversExact 8
    leaf3312Box leaf3312Certificate leaf3312InnerLog leaf3312Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi194RoundedFacts
    innerPair78RoundedFacts leaf3312RoundedFacts (by rfl)

private theorem leaf3312FlatSound : Sound leaf3312Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3312CertificateValid
    leaf3312InnerLogValid leaf3312CoversExact leaf3312LowerChecked

private noncomputable def leaf3313Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3313Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432503808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1879752063/1073741824) }, upper := { exponent := 0, mantissa := (28981/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869425663/274865007616) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf3313InnerLog : WideLogData :=
  innerPair80Data

set_option maxRecDepth 1000000 in
private theorem leaf3313LocalValidity :
    LeafFacts leaf3313Box leaf3313Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3313Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432503808) }) = true
      norm_num [leaf3313Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3313CertificateValid :
    WideCertificateValid leaf3313Box leaf3313Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi193ValidityFacts
    leaf3313LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3313CoverageChecked :
    coverageCheck (innerAD leaf3313Box) leaf3313InnerLog = true := by
  rfl'

private theorem leaf3313InnerLogValid :
    leaf3313InnerLog.Valid 8 (innerAD leaf3313Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint216PositiveFacts.valid leaf3313CoverageChecked

private noncomputable def leaf3313InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814675/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3313InputLogOnePlusV_eq :
    leaf3313InputLogOnePlusV = outerEnclosure 24
      (leaf3313Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3313RoundedFacts : LeafRoundedFacts 8
    leaf3313Certificate.logOnePlusV leaf3313InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3313InputLogOnePlusV_eq }

private noncomputable def leaf3313Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi193InputQChi innerPair80Input
    leaf3313InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3313LowerChecked :
    lowerCheck 24 leaf3313Box leaf3313Inputs = true := by
  rfl'

private theorem leaf3313CoversExact : CoversExact 8
    leaf3313Box leaf3313Certificate leaf3313InnerLog leaf3313Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi193RoundedFacts
    innerPair80RoundedFacts leaf3313RoundedFacts (by rfl)

private theorem leaf3313FlatSound : Sound leaf3313Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3313CertificateValid
    leaf3313InnerLogValid leaf3313CoversExact leaf3313LowerChecked

private noncomputable def leaf3314Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (25/128), chiHi := (51/256) }

private noncomputable def leaf3314Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432477696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1883028661/1073741824) }, upper := { exponent := 0, mantissa := (3629/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi193LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869399551/274864955392) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf3314InnerLog : WideLogData :=
  innerPair81Data

set_option maxRecDepth 1000000 in
private theorem leaf3314LocalValidity :
    LeafFacts leaf3314Box leaf3314Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3314Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432477696) }) = true
      norm_num [leaf3314Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3314CertificateValid :
    WideCertificateValid leaf3314Box leaf3314Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi193ValidityFacts
    leaf3314LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3314CoverageChecked :
    coverageCheck (innerAD leaf3314Box) leaf3314InnerLog = true := by
  rfl'

private theorem leaf3314InnerLogValid :
    leaf3314InnerLog.Valid 8 (innerAD leaf3314Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint217PositiveFacts.valid leaf3314CoverageChecked

private noncomputable def leaf3314InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453669/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3314InputLogOnePlusV_eq :
    leaf3314InputLogOnePlusV = outerEnclosure 24
      (leaf3314Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3314RoundedFacts : LeafRoundedFacts 8
    leaf3314Certificate.logOnePlusV leaf3314InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3314InputLogOnePlusV_eq }

private noncomputable def leaf3314Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi193InputQChi innerPair81Input
    leaf3314InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3314LowerChecked :
    lowerCheck 24 leaf3314Box leaf3314Inputs = true := by
  rfl'

private theorem leaf3314CoversExact : CoversExact 8
    leaf3314Box leaf3314Certificate leaf3314InnerLog leaf3314Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi193RoundedFacts
    innerPair81RoundedFacts leaf3314RoundedFacts (by rfl)

private theorem leaf3314FlatSound : Sound leaf3314Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3314CertificateValid
    leaf3314InnerLogValid leaf3314CoversExact leaf3314LowerChecked

private noncomputable def leaf3315Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3315Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810792448) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1895872933/1073741824) }, upper := { exponent := 0, mantissa := (7307/4096) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623099733/91621584896) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf3315InnerLog : WideLogData :=
  innerPair210Data

set_option maxRecDepth 1000000 in
private theorem leaf3315LocalValidity :
    LeafFacts leaf3315Box leaf3315Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3315Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810792448) }) = true
      norm_num [leaf3315Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3315CertificateValid :
    WideCertificateValid leaf3315Box leaf3315Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi194ValidityFacts
    leaf3315LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3315CoverageChecked :
    coverageCheck (innerAD leaf3315Box) leaf3315InnerLog = true := by
  rfl'

private theorem leaf3315InnerLogValid :
    leaf3315InnerLog.Valid 8 (innerAD leaf3315Box) :=
  wideLogDataValid_of_cachedCheck endpoint63PositiveFacts
    endpoint183PositiveFacts.valid leaf3315CoverageChecked

private noncomputable def leaf3315InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3315InputLogOnePlusV_eq :
    leaf3315InputLogOnePlusV = outerEnclosure 24
      (leaf3315Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3315RoundedFacts : LeafRoundedFacts 8
    leaf3315Certificate.logOnePlusV leaf3315InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3315InputLogOnePlusV_eq }

private noncomputable def leaf3315Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi194InputQChi innerPair210Input
    leaf3315InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3315LowerChecked :
    lowerCheck 24 leaf3315Box leaf3315Inputs = true := by
  rfl'

private theorem leaf3315CoversExact : CoversExact 8
    leaf3315Box leaf3315Certificate leaf3315InnerLog leaf3315Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi194RoundedFacts
    innerPair210RoundedFacts leaf3315RoundedFacts (by rfl)

private theorem leaf3315FlatSound : Sound leaf3315Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3315CertificateValid
    leaf3315InnerLogValid leaf3315CoversExact leaf3315LowerChecked

private noncomputable def leaf3316Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (51/256), chiHi := (13/64) }

private noncomputable def leaf3316Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486470144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1899215063/1073741824) }, upper := { exponent := 0, mantissa := (915/512) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi194LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973854515/54972940288) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf3316InnerLog : WideLogData :=
  innerPair212Data

set_option maxRecDepth 1000000 in
private theorem leaf3316LocalValidity :
    LeafFacts leaf3316Box leaf3316Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3316Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486470144) }) = true
      norm_num [leaf3316Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3316CertificateValid :
    WideCertificateValid leaf3316Box leaf3316Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi194ValidityFacts
    leaf3316LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3316CoverageChecked :
    coverageCheck (innerAD leaf3316Box) leaf3316InnerLog = true := by
  rfl'

private theorem leaf3316InnerLogValid :
    leaf3316InnerLog.Valid 8 (innerAD leaf3316Box) :=
  wideLogDataValid_of_cachedCheck endpoint63PositiveFacts
    endpoint218PositiveFacts.valid leaf3316CoverageChecked

private noncomputable def leaf3316InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726835/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3316InputLogOnePlusV_eq :
    leaf3316InputLogOnePlusV = outerEnclosure 24
      (leaf3316Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3316RoundedFacts : LeafRoundedFacts 8
    leaf3316Certificate.logOnePlusV leaf3316InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3316InputLogOnePlusV_eq }

private noncomputable def leaf3316Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi194InputQChi innerPair212Input
    leaf3316InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3316LowerChecked :
    lowerCheck 24 leaf3316Box leaf3316Inputs = true := by
  rfl'

private theorem leaf3316CoversExact : CoversExact 8
    leaf3316Box leaf3316Certificate leaf3316InnerLog leaf3316Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi194RoundedFacts
    innerPair212RoundedFacts leaf3316RoundedFacts (by rfl)

private theorem leaf3316FlatSound : Sound leaf3316Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3316CertificateValid
    leaf3316InnerLogValid leaf3316CoversExact leaf3316LowerChecked

private noncomputable def leaf3317Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3317Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432413696) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1891547831/1073741824) }, upper := { exponent := 0, mantissa := (29157/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869335551/274864827392) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf3317InnerLog : WideLogData :=
  innerPair78Data

set_option maxRecDepth 1000000 in
private theorem leaf3317LocalValidity :
    LeafFacts leaf3317Box leaf3317Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3317Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432413696) }) = true
      norm_num [leaf3317Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3317CertificateValid :
    WideCertificateValid leaf3317Box leaf3317Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi195ValidityFacts
    leaf3317LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3317CoverageChecked :
    coverageCheck (innerAD leaf3317Box) leaf3317InnerLog = true := by
  rfl'

private theorem leaf3317InnerLogValid :
    leaf3317InnerLog.Valid 8 (innerAD leaf3317Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint68PositiveFacts.valid leaf3317CoverageChecked

private noncomputable def leaf3317InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907339/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3317InputLogOnePlusV_eq :
    leaf3317InputLogOnePlusV = outerEnclosure 24
      (leaf3317Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3317RoundedFacts : LeafRoundedFacts 8
    leaf3317Certificate.logOnePlusV leaf3317InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3317InputLogOnePlusV_eq }

private noncomputable def leaf3317Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi195InputQChi innerPair78Input
    leaf3317InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3317LowerChecked :
    lowerCheck 24 leaf3317Box leaf3317Inputs = true := by
  rfl'

private theorem leaf3317CoversExact : CoversExact 8
    leaf3317Box leaf3317Certificate leaf3317InnerLog leaf3317Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi195RoundedFacts
    innerPair78RoundedFacts leaf3317RoundedFacts (by rfl)

private theorem leaf3317FlatSound : Sound leaf3317Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3317CertificateValid
    leaf3317InnerLogValid leaf3317CoversExact leaf3317LowerChecked

private noncomputable def leaf3318Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3318Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162159104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1894955493/1073741824) }, upper := { exponent := 0, mantissa := (14605/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324620561/18324318208) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf3318InnerLog : WideLogData :=
  innerPair77Data

set_option maxRecDepth 1000000 in
private theorem leaf3318LocalValidity :
    LeafFacts leaf3318Box leaf3318Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3318Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162159104) }) = true
      norm_num [leaf3318Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3318CertificateValid :
    WideCertificateValid leaf3318Box leaf3318Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi195ValidityFacts
    leaf3318LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3318CoverageChecked :
    coverageCheck (innerAD leaf3318Box) leaf3318InnerLog = true := by
  rfl'

private theorem leaf3318InnerLogValid :
    leaf3318InnerLog.Valid 8 (innerAD leaf3318Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint67PositiveFacts.valid leaf3318CoverageChecked

private noncomputable def leaf3318InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814679/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3318InputLogOnePlusV_eq :
    leaf3318InputLogOnePlusV = outerEnclosure 24
      (leaf3318Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3318RoundedFacts : LeafRoundedFacts 8
    leaf3318Certificate.logOnePlusV leaf3318InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3318InputLogOnePlusV_eq }

private noncomputable def leaf3318Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi195InputQChi innerPair77Input
    leaf3318InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3318LowerChecked :
    lowerCheck 24 leaf3318Box leaf3318Inputs = true := by
  rfl'

private theorem leaf3318CoversExact : CoversExact 8
    leaf3318Box leaf3318Certificate leaf3318InnerLog leaf3318Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi195RoundedFacts
    innerPair77RoundedFacts leaf3318RoundedFacts (by rfl)

private theorem leaf3318FlatSound : Sound leaf3318Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3318CertificateValid
    leaf3318InnerLogValid leaf3318CoversExact leaf3318LowerChecked

private noncomputable def leaf3319Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3319Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432290304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1907275509/1073741824) }, upper := { exponent := 0, mantissa := (14699/8192) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869212159/274864580608) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf3319InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3319LocalValidity :
    LeafFacts leaf3319Box leaf3319Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3319Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432290304) }) = true
      norm_num [leaf3319Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3319CertificateValid :
    WideCertificateValid leaf3319Box leaf3319Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi196ValidityFacts
    leaf3319LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3319CoverageChecked :
    coverageCheck (innerAD leaf3319Box) leaf3319InnerLog = true := by
  rfl'

private theorem leaf3319InnerLogValid :
    leaf3319InnerLog.Valid 8 (innerAD leaf3319Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3319CoverageChecked

private noncomputable def leaf3319InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3319InputLogOnePlusV_eq :
    leaf3319InputLogOnePlusV = outerEnclosure 24
      (leaf3319Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3319RoundedFacts : LeafRoundedFacts 8
    leaf3319Certificate.logOnePlusV leaf3319InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3319InputLogOnePlusV_eq }

private noncomputable def leaf3319Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi196InputQChi innerPair71Input
    leaf3319InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3319LowerChecked :
    lowerCheck 24 leaf3319Box leaf3319Inputs = true := by
  rfl'

private theorem leaf3319CoversExact : CoversExact 8
    leaf3319Box leaf3319Certificate leaf3319InnerLog leaf3319Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi196RoundedFacts
    innerPair71RoundedFacts leaf3319RoundedFacts (by rfl)

private theorem leaf3319FlatSound : Sound leaf3319Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3319CertificateValid
    leaf3319InnerLogValid leaf3319CoversExact leaf3319LowerChecked

private noncomputable def leaf3320Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3320Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432262656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1910748703/1073741824) }, upper := { exponent := 0, mantissa := (7363/4096) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869184511/274864525312) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf3320InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3320LocalValidity :
    LeafFacts leaf3320Box leaf3320Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3320Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432262656) }) = true
      norm_num [leaf3320Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3320CertificateValid :
    WideCertificateValid leaf3320Box leaf3320Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi196ValidityFacts
    leaf3320LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3320CoverageChecked :
    coverageCheck (innerAD leaf3320Box) leaf3320InnerLog = true := by
  rfl'

private theorem leaf3320InnerLogValid :
    leaf3320InnerLog.Valid 8 (innerAD leaf3320Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3320CoverageChecked

private noncomputable def leaf3320InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629365/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3320InputLogOnePlusV_eq :
    leaf3320InputLogOnePlusV = outerEnclosure 24
      (leaf3320Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3320RoundedFacts : LeafRoundedFacts 8
    leaf3320Certificate.logOnePlusV leaf3320InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3320InputLogOnePlusV_eq }

private noncomputable def leaf3320Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi196InputQChi innerPair71Input
    leaf3320InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3320LowerChecked :
    lowerCheck 24 leaf3320Box leaf3320Inputs = true := by
  rfl'

private theorem leaf3320CoversExact : CoversExact 8
    leaf3320Box leaf3320Certificate leaf3320InnerLog leaf3320Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi196RoundedFacts
    innerPair71RoundedFacts leaf3320RoundedFacts (by rfl)

private theorem leaf3320FlatSound : Sound leaf3320Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3320CertificateValid
    leaf3320InnerLogValid leaf3320CoversExact leaf3320LowerChecked

private noncomputable def leaf3321Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3321Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432359424) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1898363155/1073741824) }, upper := { exponent := 0, mantissa := (29263/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869281279/274864718848) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf3321InnerLog : WideLogData :=
  innerPair209Data

set_option maxRecDepth 1000000 in
private theorem leaf3321LocalValidity :
    LeafFacts leaf3321Box leaf3321Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3321Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432359424) }) = true
      norm_num [leaf3321Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3321CertificateValid :
    WideCertificateValid leaf3321Box leaf3321Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi195ValidityFacts
    leaf3321LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3321CoverageChecked :
    coverageCheck (innerAD leaf3321Box) leaf3321InnerLog = true := by
  rfl'

private theorem leaf3321InnerLogValid :
    leaf3321InnerLog.Valid 8 (innerAD leaf3321Box) :=
  wideLogDataValid_of_cachedCheck endpoint63PositiveFacts
    endpoint67PositiveFacts.valid leaf3321CoverageChecked

private noncomputable def leaf3321InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629359/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3321InputLogOnePlusV_eq :
    leaf3321InputLogOnePlusV = outerEnclosure 24
      (leaf3321Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3321RoundedFacts : LeafRoundedFacts 8
    leaf3321Certificate.logOnePlusV leaf3321InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3321InputLogOnePlusV_eq }

private noncomputable def leaf3321Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi195InputQChi innerPair209Input
    leaf3321InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3321LowerChecked :
    lowerCheck 24 leaf3321Box leaf3321Inputs = true := by
  rfl'

private theorem leaf3321CoversExact : CoversExact 8
    leaf3321Box leaf3321Certificate leaf3321InnerLog leaf3321Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi195RoundedFacts
    innerPair209RoundedFacts leaf3321RoundedFacts (by rfl)

private theorem leaf3321FlatSound : Sound leaf3321Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3321CertificateValid
    leaf3321InnerLogValid leaf3321CoversExact leaf3321LowerChecked

private noncomputable def leaf3322Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3322Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432332288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1901770817/1073741824) }, upper := { exponent := 0, mantissa := (7329/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869254143/274864664576) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf3322InnerLog : WideLogData :=
  innerPair209Data

set_option maxRecDepth 1000000 in
private theorem leaf3322LocalValidity :
    LeafFacts leaf3322Box leaf3322Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3322Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432332288) }) = true
      norm_num [leaf3322Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3322CertificateValid :
    WideCertificateValid leaf3322Box leaf3322Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi195ValidityFacts
    leaf3322LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3322CoverageChecked :
    coverageCheck (innerAD leaf3322Box) leaf3322InnerLog = true := by
  rfl'

private theorem leaf3322InnerLogValid :
    leaf3322InnerLog.Valid 8 (innerAD leaf3322Box) :=
  wideLogDataValid_of_cachedCheck endpoint63PositiveFacts
    endpoint67PositiveFacts.valid leaf3322CoverageChecked

private noncomputable def leaf3322InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629361/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3322InputLogOnePlusV_eq :
    leaf3322InputLogOnePlusV = outerEnclosure 24
      (leaf3322Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3322RoundedFacts : LeafRoundedFacts 8
    leaf3322Certificate.logOnePlusV leaf3322InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3322InputLogOnePlusV_eq }

private noncomputable def leaf3322Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi195InputQChi innerPair209Input
    leaf3322InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3322LowerChecked :
    lowerCheck 24 leaf3322Box leaf3322Inputs = true := by
  rfl'

private theorem leaf3322CoversExact : CoversExact 8
    leaf3322Box leaf3322Certificate leaf3322InnerLog leaf3322Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi195RoundedFacts
    innerPair209RoundedFacts leaf3322RoundedFacts (by rfl)

private theorem leaf3322FlatSound : Sound leaf3322Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3322CertificateValid
    leaf3322InnerLogValid leaf3322CoversExact leaf3322LowerChecked

private noncomputable def leaf3323Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3323Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432235008) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1914221897/1073741824) }, upper := { exponent := 0, mantissa := (14753/8192) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869156863/274864470016) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf3323InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3323LocalValidity :
    LeafFacts leaf3323Box leaf3323Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3323Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432235008) }) = true
      norm_num [leaf3323Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3323CertificateValid :
    WideCertificateValid leaf3323Box leaf3323Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi196ValidityFacts
    leaf3323LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3323CoverageChecked :
    coverageCheck (innerAD leaf3323Box) leaf3323InnerLog = true := by
  rfl'

private theorem leaf3323InnerLogValid :
    leaf3323InnerLog.Valid 8 (innerAD leaf3323Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3323CoverageChecked

private noncomputable def leaf3323InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629367/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3323InputLogOnePlusV_eq :
    leaf3323InputLogOnePlusV = outerEnclosure 24
      (leaf3323Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3323RoundedFacts : LeafRoundedFacts 8
    leaf3323Certificate.logOnePlusV leaf3323InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3323InputLogOnePlusV_eq }

private noncomputable def leaf3323Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi196InputQChi innerPair71Input
    leaf3323InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3323LowerChecked :
    lowerCheck 24 leaf3323Box leaf3323Inputs = true := by
  rfl'

private theorem leaf3323CoversExact : CoversExact 8
    leaf3323Box leaf3323Certificate leaf3323InnerLog leaf3323Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi196RoundedFacts
    innerPair71RoundedFacts leaf3323RoundedFacts (by rfl)

private theorem leaf3323FlatSound : Sound leaf3323Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3323CertificateValid
    leaf3323InnerLogValid leaf3323CoversExact leaf3323LowerChecked

private noncomputable def leaf3324Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3324Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486441472) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1917695091/1073741824) }, upper := { exponent := 0, mantissa := (3695/2048) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973825843/54972882944) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf3324InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3324LocalValidity :
    LeafFacts leaf3324Box leaf3324Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3324Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486441472) }) = true
      norm_num [leaf3324Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3324CertificateValid :
    WideCertificateValid leaf3324Box leaf3324Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi196ValidityFacts
    leaf3324LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3324CoverageChecked :
    coverageCheck (innerAD leaf3324Box) leaf3324InnerLog = true := by
  rfl'

private theorem leaf3324InnerLogValid :
    leaf3324InnerLog.Valid 8 (innerAD leaf3324Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3324CoverageChecked

private noncomputable def leaf3324InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629369/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3324InputLogOnePlusV_eq :
    leaf3324InputLogOnePlusV = outerEnclosure 24
      (leaf3324Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3324RoundedFacts : LeafRoundedFacts 8
    leaf3324Certificate.logOnePlusV leaf3324InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3324InputLogOnePlusV_eq }

private noncomputable def leaf3324Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi196InputQChi innerPair71Input
    leaf3324InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3324LowerChecked :
    lowerCheck 24 leaf3324Box leaf3324Inputs = true := by
  rfl'

private theorem leaf3324CoversExact : CoversExact 8
    leaf3324Box leaf3324Certificate leaf3324InnerLog leaf3324Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi196RoundedFacts
    innerPair71RoundedFacts leaf3324RoundedFacts (by rfl)

private theorem leaf3324FlatSound : Sound leaf3324Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3324CertificateValid
    leaf3324InnerLogValid leaf3324CoversExact leaf3324LowerChecked

private noncomputable def leaf3325Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3325Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090080256) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1923003187/1073741824) }, upper := { exponent := 0, mantissa := (29639/16384) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180336621/10180160512) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf3325InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3325LocalValidity :
    LeafFacts leaf3325Box leaf3325Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3325Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090080256) }) = true
      norm_num [leaf3325Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3325CertificateValid :
    WideCertificateValid leaf3325Box leaf3325Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi197ValidityFacts
    leaf3325LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3325CoverageChecked :
    coverageCheck (innerAD leaf3325Box) leaf3325InnerLog = true := by
  rfl'

private theorem leaf3325InnerLogValid :
    leaf3325InnerLog.Valid 8 (innerAD leaf3325Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3325CoverageChecked

private noncomputable def leaf3325InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629371/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3325InputLogOnePlusV_eq :
    leaf3325InputLogOnePlusV = outerEnclosure 24
      (leaf3325Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3325RoundedFacts : LeafRoundedFacts 8
    leaf3325Certificate.logOnePlusV leaf3325InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3325InputLogOnePlusV_eq }

private noncomputable def leaf3325Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi197InputQChi innerPair71Input
    leaf3325InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3325LowerChecked :
    lowerCheck 24 leaf3325Box leaf3325Inputs = true := by
  rfl'

private theorem leaf3325CoversExact : CoversExact 8
    leaf3325Box leaf3325Certificate leaf3325InnerLog leaf3325Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi197RoundedFacts
    innerPair71RoundedFacts leaf3325RoundedFacts (by rfl)

private theorem leaf3325FlatSound : Sound leaf3325Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3325CertificateValid
    leaf3325InnerLogValid leaf3325CoversExact leaf3325LowerChecked

private noncomputable def leaf3326Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3326Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084243456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1926541913/1073741824) }, upper := { exponent := 0, mantissa := (14847/8192) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168768271/16168486912) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf3326InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3326LocalValidity :
    LeafFacts leaf3326Box leaf3326Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3326Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084243456) }) = true
      norm_num [leaf3326Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3326CertificateValid :
    WideCertificateValid leaf3326Box leaf3326Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi197ValidityFacts
    leaf3326LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3326CoverageChecked :
    coverageCheck (innerAD leaf3326Box) leaf3326InnerLog = true := by
  rfl'

private theorem leaf3326InnerLogValid :
    leaf3326InnerLog.Valid 8 (innerAD leaf3326Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3326CoverageChecked

private noncomputable def leaf3326InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629373/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3326InputLogOnePlusV_eq :
    leaf3326InputLogOnePlusV = outerEnclosure 24
      (leaf3326Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3326RoundedFacts : LeafRoundedFacts 8
    leaf3326Certificate.logOnePlusV leaf3326InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3326InputLogOnePlusV_eq }

private noncomputable def leaf3326Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi197InputQChi innerPair71Input
    leaf3326InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3326LowerChecked :
    lowerCheck 24 leaf3326Box leaf3326Inputs = true := by
  rfl'

private theorem leaf3326CoversExact : CoversExact 8
    leaf3326Box leaf3326Certificate leaf3326InnerLog leaf3326Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi197RoundedFacts
    innerPair71RoundedFacts leaf3326RoundedFacts (by rfl)

private theorem leaf3326FlatSound : Sound leaf3326Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3326CertificateValid
    leaf3326InnerLogValid leaf3326CoversExact leaf3326LowerChecked

private noncomputable def leaf3327Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (241/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3327Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486408704) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1938730865/1073741824) }, upper := { exponent := 0, mantissa := (3735/2048) } }, logOuter := sk225LogOuterCertificate, logK := sk225LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973793075/54972817408) } }, logDArg := sk225LogDArgCertificate }

private noncomputable def leaf3327InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3327LocalValidity :
    LeafFacts leaf3327Box leaf3327Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3327Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486408704) }) = true
      norm_num [leaf3327Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3327CertificateValid :
    WideCertificateValid leaf3327Box leaf3327Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk225ValidityFacts chi198ValidityFacts
    leaf3327LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3327CoverageChecked :
    coverageCheck (innerAD leaf3327Box) leaf3327InnerLog = true := by
  rfl'

private theorem leaf3327InnerLogValid :
    leaf3327InnerLog.Valid 8 (innerAD leaf3327Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3327CoverageChecked

private noncomputable def leaf3327InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3327InputLogOnePlusV_eq :
    leaf3327InputLogOnePlusV = outerEnclosure 24
      (leaf3327Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3327RoundedFacts : LeafRoundedFacts 8
    leaf3327Certificate.logOnePlusV leaf3327InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3327InputLogOnePlusV_eq }

private noncomputable def leaf3327Inputs : Inputs :=
  inputsOfCaches globalInput sk225RoundedInputs
    chi198InputQChi innerPair221Input
    leaf3327InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3327LowerChecked :
    lowerCheck 24 leaf3327Box leaf3327Inputs = true := by
  rfl'

private theorem leaf3327CoversExact : CoversExact 8
    leaf3327Box leaf3327Certificate leaf3327InnerLog leaf3327Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk225RoundedFacts chi198RoundedFacts
    innerPair221RoundedFacts leaf3327RoundedFacts (by rfl)

private theorem leaf3327FlatSound : Sound leaf3327Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3327CertificateValid
    leaf3327InnerLogValid leaf3327CoversExact leaf3327LowerChecked

private noncomputable def leaf3328Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (241/64), kHi := (121/32), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3328Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090074624) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1942335123/1073741824) }, upper := { exponent := 0, mantissa := (1871/1024) } }, logOuter := sk226LogOuterCertificate, logK := sk226LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180330989/10180149248) } }, logDArg := sk226LogDArgCertificate }

private noncomputable def leaf3328InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3328LocalValidity :
    LeafFacts leaf3328Box leaf3328Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3328Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090074624) }) = true
      norm_num [leaf3328Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3328CertificateValid :
    WideCertificateValid leaf3328Box leaf3328Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk226ValidityFacts chi198ValidityFacts
    leaf3328LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3328CoverageChecked :
    coverageCheck (innerAD leaf3328Box) leaf3328InnerLog = true := by
  rfl'

private theorem leaf3328InnerLogValid :
    leaf3328InnerLog.Valid 8 (innerAD leaf3328Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3328CoverageChecked

private noncomputable def leaf3328InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3328InputLogOnePlusV_eq :
    leaf3328InputLogOnePlusV = outerEnclosure 24
      (leaf3328Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3328RoundedFacts : LeafRoundedFacts 8
    leaf3328Certificate.logOnePlusV leaf3328InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3328InputLogOnePlusV_eq }

private noncomputable def leaf3328Inputs : Inputs :=
  inputsOfCaches globalInput sk226RoundedInputs
    chi198InputQChi innerPair221Input
    leaf3328InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3328LowerChecked :
    lowerCheck 24 leaf3328Box leaf3328Inputs = true := by
  rfl'

private theorem leaf3328CoversExact : CoversExact 8
    leaf3328Box leaf3328Certificate leaf3328InnerLog leaf3328Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk226RoundedFacts chi198RoundedFacts
    innerPair221RoundedFacts leaf3328RoundedFacts (by rfl)

private theorem leaf3328FlatSound : Sound leaf3328Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3328CertificateValid
    leaf3328InnerLogValid leaf3328CoversExact leaf3328LowerChecked

private noncomputable def leaf3329Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3329Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432110592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1930080639/1073741824) }, upper := { exponent := 0, mantissa := (29749/16384) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869032447/274864221184) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf3329InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3329LocalValidity :
    LeafFacts leaf3329Box leaf3329Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3329Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432110592) }) = true
      norm_num [leaf3329Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3329CertificateValid :
    WideCertificateValid leaf3329Box leaf3329Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi197ValidityFacts
    leaf3329LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3329CoverageChecked :
    coverageCheck (innerAD leaf3329Box) leaf3329InnerLog = true := by
  rfl'

private theorem leaf3329InnerLogValid :
    leaf3329InnerLog.Valid 8 (innerAD leaf3329Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3329CoverageChecked

private noncomputable def leaf3329InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814687/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3329InputLogOnePlusV_eq :
    leaf3329InputLogOnePlusV = outerEnclosure 24
      (leaf3329Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3329RoundedFacts : LeafRoundedFacts 8
    leaf3329Certificate.logOnePlusV leaf3329InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3329InputLogOnePlusV_eq }

private noncomputable def leaf3329Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi197InputQChi innerPair221Input
    leaf3329InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3329LowerChecked :
    lowerCheck 24 leaf3329Box leaf3329Inputs = true := by
  rfl'

private theorem leaf3329CoversExact : CoversExact 8
    leaf3329Box leaf3329Certificate leaf3329InnerLog leaf3329Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi197RoundedFacts
    innerPair221RoundedFacts leaf3329RoundedFacts (by rfl)

private theorem leaf3329FlatSound : Sound leaf3329Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3329CertificateValid
    leaf3329InnerLogValid leaf3329CoversExact leaf3329LowerChecked

private noncomputable def leaf3330Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3330Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810694144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1933619365/1073741824) }, upper := { exponent := 0, mantissa := (7451/4096) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623001429/91621388288) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf3330InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3330LocalValidity :
    LeafFacts leaf3330Box leaf3330Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3330Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810694144) }) = true
      norm_num [leaf3330Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3330CertificateValid :
    WideCertificateValid leaf3330Box leaf3330Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi197ValidityFacts
    leaf3330LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3330CoverageChecked :
    coverageCheck (innerAD leaf3330Box) leaf3330InnerLog = true := by
  rfl'

private theorem leaf3330InnerLogValid :
    leaf3330InnerLog.Valid 8 (innerAD leaf3330Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3330CoverageChecked

private noncomputable def leaf3330InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (181709/262144) }

set_option maxRecDepth 1000000 in
private theorem leaf3330InputLogOnePlusV_eq :
    leaf3330InputLogOnePlusV = outerEnclosure 24
      (leaf3330Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3330RoundedFacts : LeafRoundedFacts 8
    leaf3330Certificate.logOnePlusV leaf3330InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3330InputLogOnePlusV_eq }

private noncomputable def leaf3330Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi197InputQChi innerPair221Input
    leaf3330InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3330LowerChecked :
    lowerCheck 24 leaf3330Box leaf3330Inputs = true := by
  rfl'

private theorem leaf3330CoversExact : CoversExact 8
    leaf3330Box leaf3330Certificate leaf3330InnerLog leaf3330Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi197RoundedFacts
    innerPair221RoundedFacts leaf3330RoundedFacts (by rfl)

private theorem leaf3330FlatSound : Sound leaf3330Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3330CertificateValid
    leaf3330InnerLogValid leaf3330CoversExact leaf3330LowerChecked

private noncomputable def leaf3331Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (243/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3331Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431986176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1945939381/1073741824) }, upper := { exponent := 0, mantissa := (3749/2048) } }, logOuter := sk227LogOuterCertificate, logK := sk227LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868908031/274863972352) } }, logDArg := sk227LogDArgCertificate }

private noncomputable def leaf3331InnerLog : WideLogData :=
  innerPair220Data

set_option maxRecDepth 1000000 in
private theorem leaf3331LocalValidity :
    LeafFacts leaf3331Box leaf3331Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3331Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431986176) }) = true
      norm_num [leaf3331Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3331CertificateValid :
    WideCertificateValid leaf3331Box leaf3331Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk227ValidityFacts chi198ValidityFacts
    leaf3331LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3331CoverageChecked :
    coverageCheck (innerAD leaf3331Box) leaf3331InnerLog = true := by
  rfl'

private theorem leaf3331InnerLogValid :
    leaf3331InnerLog.Valid 8 (innerAD leaf3331Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint61PositiveFacts.valid leaf3331CoverageChecked

private noncomputable def leaf3331InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814691/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3331InputLogOnePlusV_eq :
    leaf3331InputLogOnePlusV = outerEnclosure 24
      (leaf3331Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3331RoundedFacts : LeafRoundedFacts 8
    leaf3331Certificate.logOnePlusV leaf3331InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3331InputLogOnePlusV_eq }

private noncomputable def leaf3331Inputs : Inputs :=
  inputsOfCaches globalInput sk227RoundedInputs
    chi198InputQChi innerPair220Input
    leaf3331InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3331LowerChecked :
    lowerCheck 24 leaf3331Box leaf3331Inputs = true := by
  rfl'

private theorem leaf3331CoversExact : CoversExact 8
    leaf3331Box leaf3331Certificate leaf3331InnerLog leaf3331Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk227RoundedFacts chi198RoundedFacts
    innerPair220RoundedFacts leaf3331RoundedFacts (by rfl)

private theorem leaf3331FlatSound : Sound leaf3331Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3331CertificateValid
    leaf3331InnerLogValid leaf3331CoversExact leaf3331LowerChecked

private noncomputable def leaf3332Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (243/64), kHi := (61/16), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3332Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431957504) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1949543639/1073741824) }, upper := { exponent := 0, mantissa := (939/512) } }, logOuter := sk228LogOuterCertificate, logK := sk228LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868879359/274863915008) } }, logDArg := sk228LogDArgCertificate }

private noncomputable def leaf3332InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf3332LocalValidity :
    LeafFacts leaf3332Box leaf3332Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3332Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431957504) }) = true
      norm_num [leaf3332Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3332CertificateValid :
    WideCertificateValid leaf3332Box leaf3332Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk228ValidityFacts chi198ValidityFacts
    leaf3332LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3332CoverageChecked :
    coverageCheck (innerAD leaf3332Box) leaf3332InnerLog = true := by
  rfl'

private theorem leaf3332InnerLogValid :
    leaf3332InnerLog.Valid 8 (innerAD leaf3332Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf3332CoverageChecked

private noncomputable def leaf3332InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3332InputLogOnePlusV_eq :
    leaf3332InputLogOnePlusV = outerEnclosure 24
      (leaf3332Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3332RoundedFacts : LeafRoundedFacts 8
    leaf3332Certificate.logOnePlusV leaf3332InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3332InputLogOnePlusV_eq }

private noncomputable def leaf3332Inputs : Inputs :=
  inputsOfCaches globalInput sk228RoundedInputs
    chi198InputQChi innerPair94Input
    leaf3332InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3332LowerChecked :
    lowerCheck 24 leaf3332Box leaf3332Inputs = true := by
  rfl'

private theorem leaf3332CoversExact : CoversExact 8
    leaf3332Box leaf3332Certificate leaf3332InnerLog leaf3332Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk228RoundedFacts chi198RoundedFacts
    innerPair94RoundedFacts leaf3332RoundedFacts (by rfl)

private theorem leaf3332FlatSound : Sound leaf3332Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3332CertificateValid
    leaf3332InnerLogValid leaf3332CoversExact leaf3332LowerChecked

private noncomputable def leaf3333Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3333Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090085376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1905178479/1073741824) }, upper := { exponent := 0, mantissa := (29369/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180341741/10180170752) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf3333InnerLog : WideLogData :=
  innerPair209Data

set_option maxRecDepth 1000000 in
private theorem leaf3333LocalValidity :
    LeafFacts leaf3333Box leaf3333Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3333Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090085376) }) = true
      norm_num [leaf3333Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3333CertificateValid :
    WideCertificateValid leaf3333Box leaf3333Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi195ValidityFacts
    leaf3333LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3333CoverageChecked :
    coverageCheck (innerAD leaf3333Box) leaf3333InnerLog = true := by
  rfl'

private theorem leaf3333InnerLogValid :
    leaf3333InnerLog.Valid 8 (innerAD leaf3333Box) :=
  wideLogDataValid_of_cachedCheck endpoint63PositiveFacts
    endpoint67PositiveFacts.valid leaf3333CoverageChecked

private noncomputable def leaf3333InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629363/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3333InputLogOnePlusV_eq :
    leaf3333InputLogOnePlusV = outerEnclosure 24
      (leaf3333Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3333RoundedFacts : LeafRoundedFacts 8
    leaf3333Certificate.logOnePlusV leaf3333InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3333InputLogOnePlusV_eq }

private noncomputable def leaf3333Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi195InputQChi innerPair209Input
    leaf3333InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3333LowerChecked :
    lowerCheck 24 leaf3333Box leaf3333Inputs = true := by
  rfl'

private theorem leaf3333CoversExact : CoversExact 8
    leaf3333Box leaf3333Certificate leaf3333InnerLog leaf3333Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi195RoundedFacts
    innerPair209RoundedFacts leaf3333RoundedFacts (by rfl)

private theorem leaf3333FlatSound : Sound leaf3333Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3333CertificateValid
    leaf3333InnerLogValid leaf3333CoversExact leaf3333LowerChecked

private noncomputable def leaf3334Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3334Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084251648) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1908586141/1073741824) }, upper := { exponent := 0, mantissa := (14711/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168776463/16168503296) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf3334InnerLog : WideLogData :=
  innerPair209Data

set_option maxRecDepth 1000000 in
private theorem leaf3334LocalValidity :
    LeafFacts leaf3334Box leaf3334Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3334Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084251648) }) = true
      norm_num [leaf3334Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3334CertificateValid :
    WideCertificateValid leaf3334Box leaf3334Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi195ValidityFacts
    leaf3334LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3334CoverageChecked :
    coverageCheck (innerAD leaf3334Box) leaf3334InnerLog = true := by
  rfl'

private theorem leaf3334InnerLogValid :
    leaf3334InnerLog.Valid 8 (innerAD leaf3334Box) :=
  wideLogDataValid_of_cachedCheck endpoint63PositiveFacts
    endpoint67PositiveFacts.valid leaf3334CoverageChecked

private noncomputable def leaf3334InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907341/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3334InputLogOnePlusV_eq :
    leaf3334InputLogOnePlusV = outerEnclosure 24
      (leaf3334Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3334RoundedFacts : LeafRoundedFacts 8
    leaf3334Certificate.logOnePlusV leaf3334InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3334InputLogOnePlusV_eq }

private noncomputable def leaf3334Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi195InputQChi innerPair209Input
    leaf3334InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3334LowerChecked :
    lowerCheck 24 leaf3334Box leaf3334Inputs = true := by
  rfl'

private theorem leaf3334CoversExact : CoversExact 8
    leaf3334Box leaf3334Certificate leaf3334InnerLog leaf3334Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi195RoundedFacts
    innerPair209RoundedFacts leaf3334RoundedFacts (by rfl)

private theorem leaf3334FlatSound : Sound leaf3334Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3334CertificateValid
    leaf3334InnerLogValid leaf3334CoversExact leaf3334LowerChecked

private noncomputable def leaf3335Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3335Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432179712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1921168285/1073741824) }, upper := { exponent := 0, mantissa := (14807/8192) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869101567/274864359424) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf3335InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3335LocalValidity :
    LeafFacts leaf3335Box leaf3335Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3335Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432179712) }) = true
      norm_num [leaf3335Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3335CertificateValid :
    WideCertificateValid leaf3335Box leaf3335Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi196ValidityFacts
    leaf3335LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3335CoverageChecked :
    coverageCheck (innerAD leaf3335Box) leaf3335InnerLog = true := by
  rfl'

private theorem leaf3335InnerLogValid :
    leaf3335InnerLog.Valid 8 (innerAD leaf3335Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3335CoverageChecked

private noncomputable def leaf3335InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814685/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3335InputLogOnePlusV_eq :
    leaf3335InputLogOnePlusV = outerEnclosure 24
      (leaf3335Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3335RoundedFacts : LeafRoundedFacts 8
    leaf3335Certificate.logOnePlusV leaf3335InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3335InputLogOnePlusV_eq }

private noncomputable def leaf3335Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi196InputQChi innerPair71Input
    leaf3335InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3335LowerChecked :
    lowerCheck 24 leaf3335Box leaf3335Inputs = true := by
  rfl'

private theorem leaf3335CoversExact : CoversExact 8
    leaf3335Box leaf3335Certificate leaf3335InnerLog leaf3335Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi196RoundedFacts
    innerPair71RoundedFacts leaf3335RoundedFacts (by rfl)

private theorem leaf3335FlatSound : Sound leaf3335Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3335CertificateValid
    leaf3335InnerLogValid leaf3335CoversExact leaf3335LowerChecked

private noncomputable def leaf3336Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3336Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432152064) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1924641479/1073741824) }, upper := { exponent := 0, mantissa := (7417/4096) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869073919/274864304128) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf3336InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3336LocalValidity :
    LeafFacts leaf3336Box leaf3336Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3336Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432152064) }) = true
      norm_num [leaf3336Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3336CertificateValid :
    WideCertificateValid leaf3336Box leaf3336Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi196ValidityFacts
    leaf3336LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3336CoverageChecked :
    coverageCheck (innerAD leaf3336Box) leaf3336InnerLog = true := by
  rfl'

private theorem leaf3336InnerLogValid :
    leaf3336InnerLog.Valid 8 (innerAD leaf3336Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3336CoverageChecked

private noncomputable def leaf3336InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3336InputLogOnePlusV_eq :
    leaf3336InputLogOnePlusV = outerEnclosure 24
      (leaf3336Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3336RoundedFacts : LeafRoundedFacts 8
    leaf3336Certificate.logOnePlusV leaf3336InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3336InputLogOnePlusV_eq }

private noncomputable def leaf3336Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi196InputQChi innerPair71Input
    leaf3336InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3336LowerChecked :
    lowerCheck 24 leaf3336Box leaf3336Inputs = true := by
  rfl'

private theorem leaf3336CoversExact : CoversExact 8
    leaf3336Box leaf3336Certificate leaf3336InnerLog leaf3336Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi196RoundedFacts
    innerPair71RoundedFacts leaf3336RoundedFacts (by rfl)

private theorem leaf3336FlatSound : Sound leaf3336Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3336CertificateValid
    leaf3336InnerLogValid leaf3336CoversExact leaf3336LowerChecked

private noncomputable def leaf3337Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3337Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (106954803/106951168) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1911993803/1073741824) }, upper := { exponent := 0, mantissa := (29475/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (213905971/213902336) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf3337InnerLog : WideLogData :=
  innerPair494Data

set_option maxRecDepth 1000000 in
private theorem leaf3337LocalValidity :
    LeafFacts leaf3337Box leaf3337Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3337Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (106954803/106951168) }) = true
      norm_num [leaf3337Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3337CertificateValid :
    WideCertificateValid leaf3337Box leaf3337Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi195ValidityFacts
    leaf3337LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3337CoverageChecked :
    coverageCheck (innerAD leaf3337Box) leaf3337InnerLog = true := by
  rfl'

private theorem leaf3337InnerLogValid :
    leaf3337InnerLog.Valid 8 (innerAD leaf3337Box) :=
  wideLogDataValid_of_cachedCheck endpoint219PositiveFacts
    endpoint187PositiveFacts.valid leaf3337CoverageChecked

private noncomputable def leaf3337InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814683/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3337InputLogOnePlusV_eq :
    leaf3337InputLogOnePlusV = outerEnclosure 24
      (leaf3337Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3337RoundedFacts : LeafRoundedFacts 8
    leaf3337Certificate.logOnePlusV leaf3337InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3337InputLogOnePlusV_eq }

private noncomputable def leaf3337Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi195InputQChi innerPair494Input
    leaf3337InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3337LowerChecked :
    lowerCheck 24 leaf3337Box leaf3337Inputs = true := by
  rfl'

private theorem leaf3337CoversExact : CoversExact 8
    leaf3337Box leaf3337Certificate leaf3337InnerLog leaf3337Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi195RoundedFacts
    innerPair494RoundedFacts leaf3337RoundedFacts (by rfl)

private theorem leaf3337FlatSound : Sound leaf3337Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3337CertificateValid
    leaf3337InnerLogValid leaf3337CoversExact leaf3337LowerChecked

private noncomputable def leaf3338Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (13/64), chiHi := (53/256) }

private noncomputable def leaf3338Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810741248) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1915401465/1073741824) }, upper := { exponent := 0, mantissa := (3691/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi195LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91623048533/91621482496) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf3338InnerLog : WideLogData :=
  innerPair227Data

set_option maxRecDepth 1000000 in
private theorem leaf3338LocalValidity :
    LeafFacts leaf3338Box leaf3338Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3338Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810741248) }) = true
      norm_num [leaf3338Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3338CertificateValid :
    WideCertificateValid leaf3338Box leaf3338Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi195ValidityFacts
    leaf3338LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3338CoverageChecked :
    coverageCheck (innerAD leaf3338Box) leaf3338InnerLog = true := by
  rfl'

private theorem leaf3338InnerLogValid :
    leaf3338InnerLog.Valid 8 (innerAD leaf3338Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint185PositiveFacts.valid leaf3338CoverageChecked

private noncomputable def leaf3338InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453671/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3338InputLogOnePlusV_eq :
    leaf3338InputLogOnePlusV = outerEnclosure 24
      (leaf3338Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3338RoundedFacts : LeafRoundedFacts 8
    leaf3338Certificate.logOnePlusV leaf3338InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3338InputLogOnePlusV_eq }

private noncomputable def leaf3338Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi195InputQChi innerPair227Input
    leaf3338InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3338LowerChecked :
    lowerCheck 24 leaf3338Box leaf3338Inputs = true := by
  rfl'

private theorem leaf3338CoversExact : CoversExact 8
    leaf3338Box leaf3338Certificate leaf3338InnerLog leaf3338Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi195RoundedFacts
    innerPair227RoundedFacts leaf3338RoundedFacts (by rfl)

private theorem leaf3338FlatSound : Sound leaf3338Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3338CertificateValid
    leaf3338InnerLogValid leaf3338CoversExact leaf3338LowerChecked

private noncomputable def leaf3339Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3339Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432124416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1928114673/1073741824) }, upper := { exponent := 0, mantissa := (14861/8192) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869046271/274864248832) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf3339InnerLog : WideLogData :=
  innerPair465Data

set_option maxRecDepth 1000000 in
private theorem leaf3339LocalValidity :
    LeafFacts leaf3339Box leaf3339Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3339Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432124416) }) = true
      norm_num [leaf3339Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3339CertificateValid :
    WideCertificateValid leaf3339Box leaf3339Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi196ValidityFacts
    leaf3339LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3339CoverageChecked :
    coverageCheck (innerAD leaf3339Box) leaf3339InnerLog = true := by
  rfl'

private theorem leaf3339InnerLogValid :
    leaf3339InnerLog.Valid 8 (innerAD leaf3339Box) :=
  wideLogDataValid_of_cachedCheck endpoint184PositiveFacts
    endpoint186PositiveFacts.valid leaf3339CoverageChecked

private noncomputable def leaf3339InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814687/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3339InputLogOnePlusV_eq :
    leaf3339InputLogOnePlusV = outerEnclosure 24
      (leaf3339Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3339RoundedFacts : LeafRoundedFacts 8
    leaf3339Certificate.logOnePlusV leaf3339InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3339InputLogOnePlusV_eq }

private noncomputable def leaf3339Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi196InputQChi innerPair465Input
    leaf3339InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3339LowerChecked :
    lowerCheck 24 leaf3339Box leaf3339Inputs = true := by
  rfl'

private theorem leaf3339CoversExact : CoversExact 8
    leaf3339Box leaf3339Certificate leaf3339InnerLog leaf3339Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi196RoundedFacts
    innerPair465RoundedFacts leaf3339RoundedFacts (by rfl)

private theorem leaf3339FlatSound : Sound leaf3339Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3339CertificateValid
    leaf3339InnerLogValid leaf3339CoversExact leaf3339LowerChecked

private noncomputable def leaf3340Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (53/256), chiHi := (27/128) }

private noncomputable def leaf3340Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432096768) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1931587867/1073741824) }, upper := { exponent := 0, mantissa := (1861/1024) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi196LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869018623/274864193536) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf3340InnerLog : WideLogData :=
  innerPair224Data

set_option maxRecDepth 1000000 in
private theorem leaf3340LocalValidity :
    LeafFacts leaf3340Box leaf3340Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3340Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432096768) }) = true
      norm_num [leaf3340Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3340CertificateValid :
    WideCertificateValid leaf3340Box leaf3340Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi196ValidityFacts
    leaf3340LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3340CoverageChecked :
    coverageCheck (innerAD leaf3340Box) leaf3340InnerLog = true := by
  rfl'

private theorem leaf3340InnerLogValid :
    leaf3340InnerLog.Valid 8 (innerAD leaf3340Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint220PositiveFacts.valid leaf3340CoverageChecked

private noncomputable def leaf3340InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3340InputLogOnePlusV_eq :
    leaf3340InputLogOnePlusV = outerEnclosure 24
      (leaf3340Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3340RoundedFacts : LeafRoundedFacts 8
    leaf3340Certificate.logOnePlusV leaf3340InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3340InputLogOnePlusV_eq }

private noncomputable def leaf3340Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi196InputQChi innerPair224Input
    leaf3340InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3340LowerChecked :
    lowerCheck 24 leaf3340Box leaf3340Inputs = true := by
  rfl'

private theorem leaf3340CoversExact : CoversExact 8
    leaf3340Box leaf3340Certificate leaf3340InnerLog leaf3340Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi196RoundedFacts
    innerPair224RoundedFacts leaf3340RoundedFacts (by rfl)

private theorem leaf3340FlatSound : Sound leaf3340Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3340CertificateValid
    leaf3340InnerLogValid leaf3340CoversExact leaf3340LowerChecked

private noncomputable def leaf3341Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3341Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432054272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1937158091/1073741824) }, upper := { exponent := 0, mantissa := (29859/16384) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868976127/274864108544) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf3341InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3341LocalValidity :
    LeafFacts leaf3341Box leaf3341Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3341Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432054272) }) = true
      norm_num [leaf3341Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3341CertificateValid :
    WideCertificateValid leaf3341Box leaf3341Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi197ValidityFacts
    leaf3341LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3341CoverageChecked :
    coverageCheck (innerAD leaf3341Box) leaf3341InnerLog = true := by
  rfl'

private theorem leaf3341InnerLogValid :
    leaf3341InnerLog.Valid 8 (innerAD leaf3341Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3341CoverageChecked

private noncomputable def leaf3341InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814689/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3341InputLogOnePlusV_eq :
    leaf3341InputLogOnePlusV = outerEnclosure 24
      (leaf3341Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3341RoundedFacts : LeafRoundedFacts 8
    leaf3341Certificate.logOnePlusV leaf3341InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3341InputLogOnePlusV_eq }

private noncomputable def leaf3341Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi197InputQChi innerPair221Input
    leaf3341InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3341LowerChecked :
    lowerCheck 24 leaf3341Box leaf3341Inputs = true := by
  rfl'

private theorem leaf3341CoversExact : CoversExact 8
    leaf3341Box leaf3341Certificate leaf3341InnerLog leaf3341Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi197RoundedFacts
    innerPair221RoundedFacts leaf3341RoundedFacts (by rfl)

private theorem leaf3341FlatSound : Sound leaf3341Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3341CertificateValid
    leaf3341InnerLogValid leaf3341CoversExact leaf3341LowerChecked

private noncomputable def leaf3342Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3342Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432026112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1940696817/1073741824) }, upper := { exponent := 0, mantissa := (14957/8192) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868947967/274864052224) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf3342InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3342LocalValidity :
    LeafFacts leaf3342Box leaf3342Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3342Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432026112) }) = true
      norm_num [leaf3342Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3342CertificateValid :
    WideCertificateValid leaf3342Box leaf3342Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi197ValidityFacts
    leaf3342LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3342CoverageChecked :
    coverageCheck (innerAD leaf3342Box) leaf3342InnerLog = true := by
  rfl'

private theorem leaf3342InnerLogValid :
    leaf3342InnerLog.Valid 8 (innerAD leaf3342Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3342CoverageChecked

private noncomputable def leaf3342InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907345/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3342InputLogOnePlusV_eq :
    leaf3342InputLogOnePlusV = outerEnclosure 24
      (leaf3342Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3342RoundedFacts : LeafRoundedFacts 8
    leaf3342Certificate.logOnePlusV leaf3342InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3342InputLogOnePlusV_eq }

private noncomputable def leaf3342Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi197InputQChi innerPair221Input
    leaf3342InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3342LowerChecked :
    lowerCheck 24 leaf3342Box leaf3342Inputs = true := by
  rfl'

private theorem leaf3342CoversExact : CoversExact 8
    leaf3342Box leaf3342Certificate leaf3342InnerLog leaf3342Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi197RoundedFacts
    innerPair221RoundedFacts leaf3342RoundedFacts (by rfl)

private theorem leaf3342FlatSound : Sound leaf3342Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3342CertificateValid
    leaf3342InnerLogValid leaf3342CoversExact leaf3342LowerChecked

private noncomputable def leaf3343Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (245/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3343Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810642944) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1953147897/1073741824) }, upper := { exponent := 0, mantissa := (3763/2048) } }, logOuter := sk229LogOuterCertificate, logK := sk229LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622950229/91621285888) } }, logDArg := sk229LogDArgCertificate }

private noncomputable def leaf3343InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf3343LocalValidity :
    LeafFacts leaf3343Box leaf3343Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3343Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810642944) }) = true
      norm_num [leaf3343Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3343CertificateValid :
    WideCertificateValid leaf3343Box leaf3343Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk229ValidityFacts chi198ValidityFacts
    leaf3343LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3343CoverageChecked :
    coverageCheck (innerAD leaf3343Box) leaf3343InnerLog = true := by
  rfl'

private theorem leaf3343InnerLogValid :
    leaf3343InnerLog.Valid 8 (innerAD leaf3343Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf3343CoverageChecked

private noncomputable def leaf3343InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3343InputLogOnePlusV_eq :
    leaf3343InputLogOnePlusV = outerEnclosure 24
      (leaf3343Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3343RoundedFacts : LeafRoundedFacts 8
    leaf3343Certificate.logOnePlusV leaf3343InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3343InputLogOnePlusV_eq }

private noncomputable def leaf3343Inputs : Inputs :=
  inputsOfCaches globalInput sk229RoundedInputs
    chi198InputQChi innerPair94Input
    leaf3343InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3343LowerChecked :
    lowerCheck 24 leaf3343Box leaf3343Inputs = true := by
  rfl'

private theorem leaf3343CoversExact : CoversExact 8
    leaf3343Box leaf3343Certificate leaf3343InnerLog leaf3343Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk229RoundedFacts chi198RoundedFacts
    innerPair94RoundedFacts leaf3343RoundedFacts (by rfl)

private theorem leaf3343FlatSound : Sound leaf3343Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3343CertificateValid
    leaf3343InnerLogValid leaf3343CoversExact leaf3343LowerChecked

private noncomputable def leaf3344Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (245/64), kHi := (123/32), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3344Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486380032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1956752155/1073741824) }, upper := { exponent := 0, mantissa := (1885/1024) } }, logOuter := sk230LogOuterCertificate, logK := sk230LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973764403/54972760064) } }, logDArg := sk230LogDArgCertificate }

private noncomputable def leaf3344InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf3344LocalValidity :
    LeafFacts leaf3344Box leaf3344Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3344Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486380032) }) = true
      norm_num [leaf3344Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3344CertificateValid :
    WideCertificateValid leaf3344Box leaf3344Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk230ValidityFacts chi198ValidityFacts
    leaf3344LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3344CoverageChecked :
    coverageCheck (innerAD leaf3344Box) leaf3344InnerLog = true := by
  rfl'

private theorem leaf3344InnerLogValid :
    leaf3344InnerLog.Valid 8 (innerAD leaf3344Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf3344CoverageChecked

private noncomputable def leaf3344InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629387/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3344InputLogOnePlusV_eq :
    leaf3344InputLogOnePlusV = outerEnclosure 24
      (leaf3344Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3344RoundedFacts : LeafRoundedFacts 8
    leaf3344Certificate.logOnePlusV leaf3344InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3344InputLogOnePlusV_eq }

private noncomputable def leaf3344Inputs : Inputs :=
  inputsOfCaches globalInput sk230RoundedInputs
    chi198InputQChi innerPair94Input
    leaf3344InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3344LowerChecked :
    lowerCheck 24 leaf3344Box leaf3344Inputs = true := by
  rfl'

private theorem leaf3344CoversExact : CoversExact 8
    leaf3344Box leaf3344Certificate leaf3344InnerLog leaf3344Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk230RoundedFacts chi198RoundedFacts
    innerPair94RoundedFacts leaf3344RoundedFacts (by rfl)

private theorem leaf3344FlatSound : Sound leaf3344Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3344CertificateValid
    leaf3344InnerLogValid leaf3344CoversExact leaf3344LowerChecked

private noncomputable def leaf3345Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3345Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810665984) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1944235543/1073741824) }, upper := { exponent := 0, mantissa := (29969/16384) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622973269/91621331968) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf3345InnerLog : WideLogData :=
  innerPair496Data

set_option maxRecDepth 1000000 in
private theorem leaf3345LocalValidity :
    LeafFacts leaf3345Box leaf3345Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3345Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810665984) }) = true
      norm_num [leaf3345Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3345CertificateValid :
    WideCertificateValid leaf3345Box leaf3345Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi197ValidityFacts
    leaf3345LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3345CoverageChecked :
    coverageCheck (innerAD leaf3345Box) leaf3345InnerLog = true := by
  rfl'

private theorem leaf3345InnerLogValid :
    leaf3345InnerLog.Valid 8 (innerAD leaf3345Box) :=
  wideLogDataValid_of_cachedCheck endpoint221PositiveFacts
    endpoint222PositiveFacts.valid leaf3345CoverageChecked

private noncomputable def leaf3345InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3345InputLogOnePlusV_eq :
    leaf3345InputLogOnePlusV = outerEnclosure 24
      (leaf3345Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3345RoundedFacts : LeafRoundedFacts 8
    leaf3345Certificate.logOnePlusV leaf3345InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3345InputLogOnePlusV_eq }

private noncomputable def leaf3345Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi197InputQChi innerPair496Input
    leaf3345InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3345LowerChecked :
    lowerCheck 24 leaf3345Box leaf3345Inputs = true := by
  rfl'

private theorem leaf3345CoversExact : CoversExact 8
    leaf3345Box leaf3345Certificate leaf3345InnerLog leaf3345Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi197RoundedFacts
    innerPair496RoundedFacts leaf3345RoundedFacts (by rfl)

private theorem leaf3345FlatSound : Sound leaf3345Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3345CertificateValid
    leaf3345InnerLogValid leaf3345CoversExact leaf3345LowerChecked

private noncomputable def leaf3346Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (27/128), chiHi := (55/256) }

private noncomputable def leaf3346Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431969792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1947774269/1073741824) }, upper := { exponent := 0, mantissa := (3753/2048) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi197LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868891647/274863939584) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf3346InnerLog : WideLogData :=
  innerPair98Data

set_option maxRecDepth 1000000 in
private theorem leaf3346LocalValidity :
    LeafFacts leaf3346Box leaf3346Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3346Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431969792) }) = true
      norm_num [leaf3346Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3346CertificateValid :
    WideCertificateValid leaf3346Box leaf3346Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi197ValidityFacts
    leaf3346LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3346CoverageChecked :
    coverageCheck (innerAD leaf3346Box) leaf3346InnerLog = true := by
  rfl'

private theorem leaf3346InnerLogValid :
    leaf3346InnerLog.Valid 8 (innerAD leaf3346Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint189PositiveFacts.valid leaf3346CoverageChecked

private noncomputable def leaf3346InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629383/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3346InputLogOnePlusV_eq :
    leaf3346InputLogOnePlusV = outerEnclosure 24
      (leaf3346Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3346RoundedFacts : LeafRoundedFacts 8
    leaf3346Certificate.logOnePlusV leaf3346InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3346InputLogOnePlusV_eq }

private noncomputable def leaf3346Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi197InputQChi innerPair98Input
    leaf3346InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3346LowerChecked :
    lowerCheck 24 leaf3346Box leaf3346Inputs = true := by
  rfl'

private theorem leaf3346CoversExact : CoversExact 8
    leaf3346Box leaf3346Certificate leaf3346InnerLog leaf3346Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi197RoundedFacts
    innerPair98RoundedFacts leaf3346RoundedFacts (by rfl)

private theorem leaf3346FlatSound : Sound leaf3346Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3346CertificateValid
    leaf3346InnerLogValid leaf3346CoversExact leaf3346LowerChecked

private noncomputable def leaf3347Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (247/64), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3347Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431871488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1960356413/1073741824) }, upper := { exponent := 0, mantissa := (3777/2048) } }, logOuter := sk231LogOuterCertificate, logK := sk231LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868793343/274863742976) } }, logDArg := sk231LogDArgCertificate }

private noncomputable def leaf3347InnerLog : WideLogData :=
  innerPair470Data

set_option maxRecDepth 1000000 in
private theorem leaf3347LocalValidity :
    LeafFacts leaf3347Box leaf3347Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3347Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431871488) }) = true
      norm_num [leaf3347Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3347CertificateValid :
    WideCertificateValid leaf3347Box leaf3347Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk231ValidityFacts chi198ValidityFacts
    leaf3347LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3347CoverageChecked :
    coverageCheck (innerAD leaf3347Box) leaf3347InnerLog = true := by
  rfl'

private theorem leaf3347InnerLogValid :
    leaf3347InnerLog.Valid 8 (innerAD leaf3347Box) :=
  wideLogDataValid_of_cachedCheck endpoint188PositiveFacts
    endpoint223PositiveFacts.valid leaf3347CoverageChecked

private noncomputable def leaf3347InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629389/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3347InputLogOnePlusV_eq :
    leaf3347InputLogOnePlusV = outerEnclosure 24
      (leaf3347Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3347RoundedFacts : LeafRoundedFacts 8
    leaf3347Certificate.logOnePlusV leaf3347InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3347InputLogOnePlusV_eq }

private noncomputable def leaf3347Inputs : Inputs :=
  inputsOfCaches globalInput sk231RoundedInputs
    chi198InputQChi innerPair470Input
    leaf3347InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3347LowerChecked :
    lowerCheck 24 leaf3347Box leaf3347Inputs = true := by
  rfl'

private theorem leaf3347CoversExact : CoversExact 8
    leaf3347Box leaf3347Certificate leaf3347InnerLog leaf3347Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk231RoundedFacts chi198RoundedFacts
    innerPair470RoundedFacts leaf3347RoundedFacts (by rfl)

private theorem leaf3347FlatSound : Sound leaf3347Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3347CertificateValid
    leaf3347InnerLogValid leaf3347CoversExact leaf3347LowerChecked

private noncomputable def leaf3348Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (247/64), kHi := (31/8), chiLo := (55/256), chiHi := (7/32) }

private noncomputable def leaf3348Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (2694841605/2694742016) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1963960671/1073741824) }, upper := { exponent := 0, mantissa := (473/256) } }, logOuter := sk232LogOuterCertificate, logK := sk232LogKCertificate, logChi := chi198LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (5389583621/5389484032) } }, logDArg := sk232LogDArgCertificate }

private noncomputable def leaf3348InnerLog : WideLogData :=
  innerPair215Data

set_option maxRecDepth 1000000 in
private theorem leaf3348LocalValidity :
    LeafFacts leaf3348Box leaf3348Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3348Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (2694841605/2694742016) }) = true
      norm_num [leaf3348Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3348CertificateValid :
    WideCertificateValid leaf3348Box leaf3348Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk232ValidityFacts chi198ValidityFacts
    leaf3348LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3348CoverageChecked :
    coverageCheck (innerAD leaf3348Box) leaf3348InnerLog = true := by
  rfl'

private theorem leaf3348InnerLogValid :
    leaf3348InnerLog.Valid 8 (innerAD leaf3348Box) :=
  wideLogDataValid_of_cachedCheck endpoint64PositiveFacts
    endpoint223PositiveFacts.valid leaf3348CoverageChecked

private noncomputable def leaf3348InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629391/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3348InputLogOnePlusV_eq :
    leaf3348InputLogOnePlusV = outerEnclosure 24
      (leaf3348Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3348RoundedFacts : LeafRoundedFacts 8
    leaf3348Certificate.logOnePlusV leaf3348InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3348InputLogOnePlusV_eq }

private noncomputable def leaf3348Inputs : Inputs :=
  inputsOfCaches globalInput sk232RoundedInputs
    chi198InputQChi innerPair215Input
    leaf3348InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3348LowerChecked :
    lowerCheck 24 leaf3348Box leaf3348Inputs = true := by
  rfl'

private theorem leaf3348CoversExact : CoversExact 8
    leaf3348Box leaf3348Certificate leaf3348InnerLog leaf3348Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk232RoundedFacts chi198RoundedFacts
    innerPair215RoundedFacts leaf3348RoundedFacts (by rfl)

private theorem leaf3348FlatSound : Sound leaf3348Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3348CertificateValid
    leaf3348InnerLogValid leaf3348CoversExact leaf3348LowerChecked

private noncomputable def component68Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component68Node0_sound : Sound component68Node0Box :=
  sound_of_literal_split component68Node0Box leaf3285Box leaf3286Box
    .k (241/64) (by rfl) (by rfl)
    leaf3285FlatSound leaf3286FlatSound

private noncomputable def component68Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node1_sound : Sound component68Node1Box :=
  sound_of_literal_split component68Node1Box leaf3287Box leaf3288Box
    .k (241/64) (by rfl) (by rfl)
    leaf3287FlatSound leaf3288FlatSound

private noncomputable def component68Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node2_sound : Sound component68Node2Box :=
  sound_of_literal_split component68Node2Box component68Node0Box component68Node1Box
    .chi (49/256) (by rfl) (by rfl)
    component68Node0_sound component68Node1_sound

private noncomputable def component68Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component68Node3_sound : Sound component68Node3Box :=
  sound_of_literal_split component68Node3Box leaf3289Box leaf3290Box
    .k (243/64) (by rfl) (by rfl)
    leaf3289FlatSound leaf3290FlatSound

private noncomputable def component68Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node4_sound : Sound component68Node4Box :=
  sound_of_literal_split component68Node4Box leaf3291Box leaf3292Box
    .k (243/64) (by rfl) (by rfl)
    leaf3291FlatSound leaf3292FlatSound

private noncomputable def component68Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node5_sound : Sound component68Node5Box :=
  sound_of_literal_split component68Node5Box component68Node3Box component68Node4Box
    .chi (49/256) (by rfl) (by rfl)
    component68Node3_sound component68Node4_sound

private noncomputable def component68Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node6_sound : Sound component68Node6Box :=
  sound_of_literal_split component68Node6Box component68Node2Box component68Node5Box
    .k (121/32) (by rfl) (by rfl)
    component68Node2_sound component68Node5_sound

private noncomputable def component68Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component68Node7_sound : Sound component68Node7Box :=
  sound_of_literal_split component68Node7Box leaf3293Box leaf3294Box
    .k (241/64) (by rfl) (by rfl)
    leaf3293FlatSound leaf3294FlatSound

private noncomputable def component68Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component68Node8_sound : Sound component68Node8Box :=
  sound_of_literal_split component68Node8Box leaf3295Box leaf3296Box
    .k (241/64) (by rfl) (by rfl)
    leaf3295FlatSound leaf3296FlatSound

private noncomputable def component68Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component68Node9_sound : Sound component68Node9Box :=
  sound_of_literal_split component68Node9Box component68Node7Box component68Node8Box
    .chi (51/256) (by rfl) (by rfl)
    component68Node7_sound component68Node8_sound

private noncomputable def component68Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component68Node10_sound : Sound component68Node10Box :=
  sound_of_literal_split component68Node10Box leaf3297Box leaf3298Box
    .k (243/64) (by rfl) (by rfl)
    leaf3297FlatSound leaf3298FlatSound

private noncomputable def component68Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component68Node11_sound : Sound component68Node11Box :=
  sound_of_literal_split component68Node11Box leaf3299Box leaf3300Box
    .k (243/64) (by rfl) (by rfl)
    leaf3299FlatSound leaf3300FlatSound

private noncomputable def component68Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component68Node12_sound : Sound component68Node12Box :=
  sound_of_literal_split component68Node12Box component68Node10Box component68Node11Box
    .chi (51/256) (by rfl) (by rfl)
    component68Node10_sound component68Node11_sound

private noncomputable def component68Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component68Node13_sound : Sound component68Node13Box :=
  sound_of_literal_split component68Node13Box component68Node9Box component68Node12Box
    .k (121/32) (by rfl) (by rfl)
    component68Node9_sound component68Node12_sound

private noncomputable def component68Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component68Node14_sound : Sound component68Node14Box :=
  sound_of_literal_split component68Node14Box component68Node6Box component68Node13Box
    .chi (25/128) (by rfl) (by rfl)
    component68Node6_sound component68Node13_sound

private noncomputable def component68Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component68Node15_sound : Sound component68Node15Box :=
  sound_of_literal_split component68Node15Box leaf3301Box leaf3302Box
    .k (245/64) (by rfl) (by rfl)
    leaf3301FlatSound leaf3302FlatSound

private noncomputable def component68Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node16_sound : Sound component68Node16Box :=
  sound_of_literal_split component68Node16Box leaf3303Box leaf3304Box
    .k (245/64) (by rfl) (by rfl)
    leaf3303FlatSound leaf3304FlatSound

private noncomputable def component68Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node17_sound : Sound component68Node17Box :=
  sound_of_literal_split component68Node17Box component68Node15Box component68Node16Box
    .chi (49/256) (by rfl) (by rfl)
    component68Node15_sound component68Node16_sound

private noncomputable def component68Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (3/16), chiHi := (49/256) }

set_option maxRecDepth 1000000 in
private theorem component68Node18_sound : Sound component68Node18Box :=
  sound_of_literal_split component68Node18Box leaf3305Box leaf3306Box
    .k (247/64) (by rfl) (by rfl)
    leaf3305FlatSound leaf3306FlatSound

private noncomputable def component68Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (49/256), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node19_sound : Sound component68Node19Box :=
  sound_of_literal_split component68Node19Box leaf3307Box leaf3308Box
    .k (247/64) (by rfl) (by rfl)
    leaf3307FlatSound leaf3308FlatSound

private noncomputable def component68Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node20_sound : Sound component68Node20Box :=
  sound_of_literal_split component68Node20Box component68Node18Box component68Node19Box
    .chi (49/256) (by rfl) (by rfl)
    component68Node18_sound component68Node19_sound

private noncomputable def component68Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (3/16), chiHi := (25/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node21_sound : Sound component68Node21Box :=
  sound_of_literal_split component68Node21Box component68Node17Box component68Node20Box
    .k (123/32) (by rfl) (by rfl)
    component68Node17_sound component68Node20_sound

private noncomputable def component68Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component68Node22_sound : Sound component68Node22Box :=
  sound_of_literal_split component68Node22Box leaf3309Box leaf3310Box
    .k (245/64) (by rfl) (by rfl)
    leaf3309FlatSound leaf3310FlatSound

private noncomputable def component68Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component68Node23_sound : Sound component68Node23Box :=
  sound_of_literal_split component68Node23Box leaf3311Box leaf3312Box
    .k (245/64) (by rfl) (by rfl)
    leaf3311FlatSound leaf3312FlatSound

private noncomputable def component68Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component68Node24_sound : Sound component68Node24Box :=
  sound_of_literal_split component68Node24Box component68Node22Box component68Node23Box
    .chi (51/256) (by rfl) (by rfl)
    component68Node22_sound component68Node23_sound

private noncomputable def component68Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (25/128), chiHi := (51/256) }

set_option maxRecDepth 1000000 in
private theorem component68Node25_sound : Sound component68Node25Box :=
  sound_of_literal_split component68Node25Box leaf3313Box leaf3314Box
    .k (247/64) (by rfl) (by rfl)
    leaf3313FlatSound leaf3314FlatSound

private noncomputable def component68Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (51/256), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component68Node26_sound : Sound component68Node26Box :=
  sound_of_literal_split component68Node26Box leaf3315Box leaf3316Box
    .k (247/64) (by rfl) (by rfl)
    leaf3315FlatSound leaf3316FlatSound

private noncomputable def component68Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component68Node27_sound : Sound component68Node27Box :=
  sound_of_literal_split component68Node27Box component68Node25Box component68Node26Box
    .chi (51/256) (by rfl) (by rfl)
    component68Node25_sound component68Node26_sound

private noncomputable def component68Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (25/128), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component68Node28_sound : Sound component68Node28Box :=
  sound_of_literal_split component68Node28Box component68Node24Box component68Node27Box
    .k (123/32) (by rfl) (by rfl)
    component68Node24_sound component68Node27_sound

private noncomputable def component68Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component68Node29_sound : Sound component68Node29Box :=
  sound_of_literal_split component68Node29Box component68Node21Box component68Node28Box
    .chi (25/128) (by rfl) (by rfl)
    component68Node21_sound component68Node28_sound

private noncomputable def component68Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (3/16), chiHi := (13/64) }

set_option maxRecDepth 1000000 in
private theorem component68Node30_sound : Sound component68Node30Box :=
  sound_of_literal_split component68Node30Box component68Node14Box component68Node29Box
    .k (61/16) (by rfl) (by rfl)
    component68Node14_sound component68Node29_sound

private noncomputable def component68Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component68Node31_sound : Sound component68Node31Box :=
  sound_of_literal_split component68Node31Box leaf3317Box leaf3318Box
    .k (241/64) (by rfl) (by rfl)
    leaf3317FlatSound leaf3318FlatSound

private noncomputable def component68Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node32_sound : Sound component68Node32Box :=
  sound_of_literal_split component68Node32Box leaf3319Box leaf3320Box
    .k (241/64) (by rfl) (by rfl)
    leaf3319FlatSound leaf3320FlatSound

private noncomputable def component68Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node33_sound : Sound component68Node33Box :=
  sound_of_literal_split component68Node33Box component68Node31Box component68Node32Box
    .chi (53/256) (by rfl) (by rfl)
    component68Node31_sound component68Node32_sound

private noncomputable def component68Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component68Node34_sound : Sound component68Node34Box :=
  sound_of_literal_split component68Node34Box leaf3321Box leaf3322Box
    .k (243/64) (by rfl) (by rfl)
    leaf3321FlatSound leaf3322FlatSound

private noncomputable def component68Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node35_sound : Sound component68Node35Box :=
  sound_of_literal_split component68Node35Box leaf3323Box leaf3324Box
    .k (243/64) (by rfl) (by rfl)
    leaf3323FlatSound leaf3324FlatSound

private noncomputable def component68Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node36_sound : Sound component68Node36Box :=
  sound_of_literal_split component68Node36Box component68Node34Box component68Node35Box
    .chi (53/256) (by rfl) (by rfl)
    component68Node34_sound component68Node35_sound

private noncomputable def component68Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node37_sound : Sound component68Node37Box :=
  sound_of_literal_split component68Node37Box component68Node33Box component68Node36Box
    .k (121/32) (by rfl) (by rfl)
    component68Node33_sound component68Node36_sound

private noncomputable def component68Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component68Node38_sound : Sound component68Node38Box :=
  sound_of_literal_split component68Node38Box leaf3325Box leaf3326Box
    .k (241/64) (by rfl) (by rfl)
    leaf3325FlatSound leaf3326FlatSound

private noncomputable def component68Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component68Node39_sound : Sound component68Node39Box :=
  sound_of_literal_split component68Node39Box leaf3327Box leaf3328Box
    .k (241/64) (by rfl) (by rfl)
    leaf3327FlatSound leaf3328FlatSound

private noncomputable def component68Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (121/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component68Node40_sound : Sound component68Node40Box :=
  sound_of_literal_split component68Node40Box component68Node38Box component68Node39Box
    .chi (55/256) (by rfl) (by rfl)
    component68Node38_sound component68Node39_sound

private noncomputable def component68Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component68Node41_sound : Sound component68Node41Box :=
  sound_of_literal_split component68Node41Box leaf3329Box leaf3330Box
    .k (243/64) (by rfl) (by rfl)
    leaf3329FlatSound leaf3330FlatSound

private noncomputable def component68Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component68Node42_sound : Sound component68Node42Box :=
  sound_of_literal_split component68Node42Box leaf3331Box leaf3332Box
    .k (243/64) (by rfl) (by rfl)
    leaf3331FlatSound leaf3332FlatSound

private noncomputable def component68Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (121/32), kHi := (61/16), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component68Node43_sound : Sound component68Node43Box :=
  sound_of_literal_split component68Node43Box component68Node41Box component68Node42Box
    .chi (55/256) (by rfl) (by rfl)
    component68Node41_sound component68Node42_sound

private noncomputable def component68Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component68Node44_sound : Sound component68Node44Box :=
  sound_of_literal_split component68Node44Box component68Node40Box component68Node43Box
    .k (121/32) (by rfl) (by rfl)
    component68Node40_sound component68Node43_sound

private noncomputable def component68Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (61/16), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component68Node45_sound : Sound component68Node45Box :=
  sound_of_literal_split component68Node45Box component68Node37Box component68Node44Box
    .chi (27/128) (by rfl) (by rfl)
    component68Node37_sound component68Node44_sound

private noncomputable def component68Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component68Node46_sound : Sound component68Node46Box :=
  sound_of_literal_split component68Node46Box leaf3333Box leaf3334Box
    .k (245/64) (by rfl) (by rfl)
    leaf3333FlatSound leaf3334FlatSound

private noncomputable def component68Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node47_sound : Sound component68Node47Box :=
  sound_of_literal_split component68Node47Box leaf3335Box leaf3336Box
    .k (245/64) (by rfl) (by rfl)
    leaf3335FlatSound leaf3336FlatSound

private noncomputable def component68Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node48_sound : Sound component68Node48Box :=
  sound_of_literal_split component68Node48Box component68Node46Box component68Node47Box
    .chi (53/256) (by rfl) (by rfl)
    component68Node46_sound component68Node47_sound

private noncomputable def component68Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (13/64), chiHi := (53/256) }

set_option maxRecDepth 1000000 in
private theorem component68Node49_sound : Sound component68Node49Box :=
  sound_of_literal_split component68Node49Box leaf3337Box leaf3338Box
    .k (247/64) (by rfl) (by rfl)
    leaf3337FlatSound leaf3338FlatSound

private noncomputable def component68Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (53/256), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node50_sound : Sound component68Node50Box :=
  sound_of_literal_split component68Node50Box leaf3339Box leaf3340Box
    .k (247/64) (by rfl) (by rfl)
    leaf3339FlatSound leaf3340FlatSound

private noncomputable def component68Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node51_sound : Sound component68Node51Box :=
  sound_of_literal_split component68Node51Box component68Node49Box component68Node50Box
    .chi (53/256) (by rfl) (by rfl)
    component68Node49_sound component68Node50_sound

private noncomputable def component68Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (13/64), chiHi := (27/128) }

set_option maxRecDepth 1000000 in
private theorem component68Node52_sound : Sound component68Node52Box :=
  sound_of_literal_split component68Node52Box component68Node48Box component68Node51Box
    .k (123/32) (by rfl) (by rfl)
    component68Node48_sound component68Node51_sound

private noncomputable def component68Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component68Node53_sound : Sound component68Node53Box :=
  sound_of_literal_split component68Node53Box leaf3341Box leaf3342Box
    .k (245/64) (by rfl) (by rfl)
    leaf3341FlatSound leaf3342FlatSound

private noncomputable def component68Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component68Node54_sound : Sound component68Node54Box :=
  sound_of_literal_split component68Node54Box leaf3343Box leaf3344Box
    .k (245/64) (by rfl) (by rfl)
    leaf3343FlatSound leaf3344FlatSound

private noncomputable def component68Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (123/32), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component68Node55_sound : Sound component68Node55Box :=
  sound_of_literal_split component68Node55Box component68Node53Box component68Node54Box
    .chi (55/256) (by rfl) (by rfl)
    component68Node53_sound component68Node54_sound

private noncomputable def component68Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (27/128), chiHi := (55/256) }

set_option maxRecDepth 1000000 in
private theorem component68Node56_sound : Sound component68Node56Box :=
  sound_of_literal_split component68Node56Box leaf3345Box leaf3346Box
    .k (247/64) (by rfl) (by rfl)
    leaf3345FlatSound leaf3346FlatSound

private noncomputable def component68Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (55/256), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component68Node57_sound : Sound component68Node57Box :=
  sound_of_literal_split component68Node57Box leaf3347Box leaf3348Box
    .k (247/64) (by rfl) (by rfl)
    leaf3347FlatSound leaf3348FlatSound

private noncomputable def component68Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (123/32), kHi := (31/8), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component68Node58_sound : Sound component68Node58Box :=
  sound_of_literal_split component68Node58Box component68Node56Box component68Node57Box
    .chi (55/256) (by rfl) (by rfl)
    component68Node56_sound component68Node57_sound

private noncomputable def component68Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (27/128), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component68Node59_sound : Sound component68Node59Box :=
  sound_of_literal_split component68Node59Box component68Node55Box component68Node58Box
    .k (123/32) (by rfl) (by rfl)
    component68Node55_sound component68Node58_sound

private noncomputable def component68Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (61/16), kHi := (31/8), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component68Node60_sound : Sound component68Node60Box :=
  sound_of_literal_split component68Node60Box component68Node52Box component68Node59Box
    .chi (27/128) (by rfl) (by rfl)
    component68Node52_sound component68Node59_sound

private noncomputable def component68Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (13/64), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
private theorem component68Node61_sound : Sound component68Node61Box :=
  sound_of_literal_split component68Node61Box component68Node45Box component68Node60Box
    .k (61/16) (by rfl) (by rfl)
    component68Node45_sound component68Node60_sound

noncomputable def component68Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (15/4), kHi := (31/8), chiLo := (3/16), chiHi := (7/32) }

set_option maxRecDepth 1000000 in
theorem component68_sound : Sound component68Box :=
  sound_of_literal_split component68Box component68Node30Box component68Node61Box
    .chi (13/64) (by rfl) (by rfl)
    component68Node30_sound component68Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
