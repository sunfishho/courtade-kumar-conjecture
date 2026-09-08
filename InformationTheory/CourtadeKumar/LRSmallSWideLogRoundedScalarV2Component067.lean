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

private noncomputable def leaf3221Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3221Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742403/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486430720) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1925100223/1073741824) }, upper := { exponent := 0, mantissa := (29665/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973815091/54972861440) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf3221InnerLog : WideLogData :=
  innerPair71Data

set_option maxRecDepth 1000000 in
private theorem leaf3221LocalValidity :
    LeafFacts leaf3221Box leaf3221Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3221Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486430720) }) = true
      norm_num [leaf3221Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3221CertificateValid :
    WideCertificateValid leaf3221Box leaf3221Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi201ValidityFacts
    leaf3221LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3221CoverageChecked :
    coverageCheck (innerAD leaf3221Box) leaf3221InnerLog = true := by
  rfl'

private theorem leaf3221InnerLogValid :
    leaf3221InnerLog.Valid 8 (innerAD leaf3221Box) :=
  wideLogDataValid_of_cachedCheck endpoint16PositiveFacts
    endpoint21PositiveFacts.valid leaf3221CoverageChecked

private noncomputable def leaf3221InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907343/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3221InputLogOnePlusV_eq :
    leaf3221InputLogOnePlusV = outerEnclosure 24
      (leaf3221Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3221RoundedFacts : LeafRoundedFacts 8
    leaf3221Certificate.logOnePlusV leaf3221InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3221InputLogOnePlusV_eq }

private noncomputable def leaf3221Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi201InputQChi innerPair71Input
    leaf3221InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3221LowerChecked :
    lowerCheck 24 leaf3221Box leaf3221Inputs = true := by
  rfl'

private theorem leaf3221CoversExact : CoversExact 8
    leaf3221Box leaf3221Certificate leaf3221InnerLog leaf3221Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi201RoundedFacts
    innerPair71RoundedFacts leaf3221RoundedFacts (by rfl)

private theorem leaf3221FlatSound : Sound leaf3221Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3221CertificateValid
    leaf3221InnerLogValid leaf3221CoversExact leaf3221LowerChecked

private noncomputable def leaf3222Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3222Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432124416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1928770013/1073741824) }, upper := { exponent := 0, mantissa := (14861/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274869046271/274864248832) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf3222InnerLog : WideLogData :=
  innerPair226Data

set_option maxRecDepth 1000000 in
private theorem leaf3222LocalValidity :
    LeafFacts leaf3222Box leaf3222Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3222Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432124416) }) = true
      norm_num [leaf3222Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3222CertificateValid :
    WideCertificateValid leaf3222Box leaf3222Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi201ValidityFacts
    leaf3222LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3222CoverageChecked :
    coverageCheck (innerAD leaf3222Box) leaf3222InnerLog = true := by
  rfl'

private theorem leaf3222InnerLogValid :
    leaf3222InnerLog.Valid 8 (innerAD leaf3222Box) :=
  wideLogDataValid_of_cachedCheck endpoint68PositiveFacts
    endpoint64PositiveFacts.valid leaf3222CoverageChecked

private noncomputable def leaf3222InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814687/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3222InputLogOnePlusV_eq :
    leaf3222InputLogOnePlusV = outerEnclosure 24
      (leaf3222Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3222RoundedFacts : LeafRoundedFacts 8
    leaf3222Certificate.logOnePlusV leaf3222InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3222InputLogOnePlusV_eq }

private noncomputable def leaf3222Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi201InputQChi innerPair226Input
    leaf3222InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3222LowerChecked :
    lowerCheck 24 leaf3222Box leaf3222Inputs = true := by
  rfl'

private theorem leaf3222CoversExact : CoversExact 8
    leaf3222Box leaf3222Certificate leaf3222InnerLog leaf3222Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi201RoundedFacts
    innerPair226RoundedFacts leaf3222RoundedFacts (by rfl)

private theorem leaf3222FlatSound : Sound leaf3222Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3222CertificateValid
    leaf3222InnerLogValid leaf3222CoversExact leaf3222LowerChecked

private noncomputable def leaf3223Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3223Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742405/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084237312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1940303645/1073741824) }, upper := { exponent := 0, mantissa := (14949/8192) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168762127/16168474624) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf3223InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3223LocalValidity :
    LeafFacts leaf3223Box leaf3223Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3223Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084237312) }) = true
      norm_num [leaf3223Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3223CertificateValid :
    WideCertificateValid leaf3223Box leaf3223Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi202ValidityFacts
    leaf3223LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3223CoverageChecked :
    coverageCheck (innerAD leaf3223Box) leaf3223InnerLog = true := by
  rfl'

private theorem leaf3223InnerLogValid :
    leaf3223InnerLog.Valid 8 (innerAD leaf3223Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3223CoverageChecked

private noncomputable def leaf3223InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3223InputLogOnePlusV_eq :
    leaf3223InputLogOnePlusV = outerEnclosure 24
      (leaf3223Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3223RoundedFacts : LeafRoundedFacts 8
    leaf3223Certificate.logOnePlusV leaf3223InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3223InputLogOnePlusV_eq }

private noncomputable def leaf3223Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi202InputQChi innerPair221Input
    leaf3223InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3223LowerChecked :
    lowerCheck 24 leaf3223Box leaf3223Inputs = true := by
  rfl'

private theorem leaf3223CoversExact : CoversExact 8
    leaf3223Box leaf3223Certificate leaf3223InnerLog leaf3223Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi202RoundedFacts
    innerPair221RoundedFacts leaf3223RoundedFacts (by rfl)

private theorem leaf3223FlatSound : Sound leaf3223Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3223CertificateValid
    leaf3223InnerLogValid leaf3223CoversExact leaf3223LowerChecked

private noncomputable def leaf3224Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3224Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432004608) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1944038967/1073741824) }, upper := { exponent := 0, mantissa := (7489/4096) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868926463/274864009216) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf3224InnerLog : WideLogData :=
  innerPair220Data

set_option maxRecDepth 1000000 in
private theorem leaf3224LocalValidity :
    LeafFacts leaf3224Box leaf3224Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3224Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432004608) }) = true
      norm_num [leaf3224Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3224CertificateValid :
    WideCertificateValid leaf3224Box leaf3224Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi202ValidityFacts
    leaf3224LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3224CoverageChecked :
    coverageCheck (innerAD leaf3224Box) leaf3224InnerLog = true := by
  rfl'

private theorem leaf3224InnerLogValid :
    leaf3224InnerLog.Valid 8 (innerAD leaf3224Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint61PositiveFacts.valid leaf3224CoverageChecked

private noncomputable def leaf3224InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3224InputLogOnePlusV_eq :
    leaf3224InputLogOnePlusV = outerEnclosure 24
      (leaf3224Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3224RoundedFacts : LeafRoundedFacts 8
    leaf3224Certificate.logOnePlusV leaf3224InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3224InputLogOnePlusV_eq }

private noncomputable def leaf3224Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi202InputQChi innerPair220Input
    leaf3224InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3224LowerChecked :
    lowerCheck 24 leaf3224Box leaf3224Inputs = true := by
  rfl'

private theorem leaf3224CoversExact : CoversExact 8
    leaf3224Box leaf3224Certificate leaf3224InnerLog leaf3224Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi202RoundedFacts
    innerPair220RoundedFacts leaf3224RoundedFacts (by rfl)

private theorem leaf3224FlatSound : Sound leaf3224Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3224CertificateValid
    leaf3224InnerLogValid leaf3224CoversExact leaf3224LowerChecked

private noncomputable def leaf3225Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3225Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084240896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1932439803/1073741824) }, upper := { exponent := 0, mantissa := (29779/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168765711/16168481792) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf3225InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3225LocalValidity :
    LeafFacts leaf3225Box leaf3225Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3225Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084240896) }) = true
      norm_num [leaf3225Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3225CertificateValid :
    WideCertificateValid leaf3225Box leaf3225Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi201ValidityFacts
    leaf3225LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3225CoverageChecked :
    coverageCheck (innerAD leaf3225Box) leaf3225InnerLog = true := by
  rfl'

private theorem leaf3225InnerLogValid :
    leaf3225InnerLog.Valid 8 (innerAD leaf3225Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3225CoverageChecked

private noncomputable def leaf3225InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629375/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3225InputLogOnePlusV_eq :
    leaf3225InputLogOnePlusV = outerEnclosure 24
      (leaf3225Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3225RoundedFacts : LeafRoundedFacts 8
    leaf3225Certificate.logOnePlusV leaf3225InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3225InputLogOnePlusV_eq }

private noncomputable def leaf3225Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi201InputQChi innerPair221Input
    leaf3225InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3225LowerChecked :
    lowerCheck 24 leaf3225Box leaf3225Inputs = true := by
  rfl'

private theorem leaf3225CoversExact : CoversExact 8
    leaf3225Box leaf3225Certificate leaf3225InnerLog leaf3225Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi201RoundedFacts
    innerPair221RoundedFacts leaf3225RoundedFacts (by rfl)

private theorem leaf3225FlatSound : Sound leaf3225Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3225CertificateValid
    leaf3225InnerLogValid leaf3225CoversExact leaf3225LowerChecked

private noncomputable def leaf3226Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3226Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432066048) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1936109593/1073741824) }, upper := { exponent := 0, mantissa := (7459/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868987903/274864132096) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf3226InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3226LocalValidity :
    LeafFacts leaf3226Box leaf3226Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3226Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432066048) }) = true
      norm_num [leaf3226Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3226CertificateValid :
    WideCertificateValid leaf3226Box leaf3226Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi201ValidityFacts
    leaf3226LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3226CoverageChecked :
    coverageCheck (innerAD leaf3226Box) leaf3226InnerLog = true := by
  rfl'

private theorem leaf3226InnerLogValid :
    leaf3226InnerLog.Valid 8 (innerAD leaf3226Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3226CoverageChecked

private noncomputable def leaf3226InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629377/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3226InputLogOnePlusV_eq :
    leaf3226InputLogOnePlusV = outerEnclosure 24
      (leaf3226Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3226RoundedFacts : LeafRoundedFacts 8
    leaf3226Certificate.logOnePlusV leaf3226InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3226InputLogOnePlusV_eq }

private noncomputable def leaf3226Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi201InputQChi innerPair221Input
    leaf3226InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3226LowerChecked :
    lowerCheck 24 leaf3226Box leaf3226Inputs = true := by
  rfl'

private theorem leaf3226CoversExact : CoversExact 8
    leaf3226Box leaf3226Certificate leaf3226InnerLog leaf3226Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi201RoundedFacts
    innerPair221RoundedFacts leaf3226RoundedFacts (by rfl)

private theorem leaf3226FlatSound : Sound leaf3226Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3226CertificateValid
    leaf3226InnerLogValid leaf3226CoversExact leaf3226LowerChecked

private noncomputable def leaf3227Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3227Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810658304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1947774289/1073741824) }, upper := { exponent := 0, mantissa := (15007/8192) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622965589/91621316608) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf3227InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf3227LocalValidity :
    LeafFacts leaf3227Box leaf3227Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3227Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810658304) }) = true
      norm_num [leaf3227Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3227CertificateValid :
    WideCertificateValid leaf3227Box leaf3227Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi202ValidityFacts
    leaf3227LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3227CoverageChecked :
    coverageCheck (innerAD leaf3227Box) leaf3227InnerLog = true := by
  rfl'

private theorem leaf3227InnerLogValid :
    leaf3227InnerLog.Valid 8 (innerAD leaf3227Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf3227CoverageChecked

private noncomputable def leaf3227InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629383/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3227InputLogOnePlusV_eq :
    leaf3227InputLogOnePlusV = outerEnclosure 24
      (leaf3227Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3227RoundedFacts : LeafRoundedFacts 8
    leaf3227Certificate.logOnePlusV leaf3227InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3227InputLogOnePlusV_eq }

private noncomputable def leaf3227Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi202InputQChi innerPair94Input
    leaf3227InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3227LowerChecked :
    lowerCheck 24 leaf3227Box leaf3227Inputs = true := by
  rfl'

private theorem leaf3227CoversExact : CoversExact 8
    leaf3227Box leaf3227Certificate leaf3227InnerLog leaf3227Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi202RoundedFacts
    innerPair94RoundedFacts leaf3227RoundedFacts (by rfl)

private theorem leaf3227FlatSound : Sound leaf3227Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3227CertificateValid
    leaf3227InnerLogValid leaf3227CoversExact leaf3227LowerChecked

private noncomputable def leaf3228Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3228Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431945216) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1951509611/1073741824) }, upper := { exponent := 0, mantissa := (3759/2048) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868867071/274863890432) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf3228InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf3228LocalValidity :
    LeafFacts leaf3228Box leaf3228Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3228Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431945216) }) = true
      norm_num [leaf3228Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3228CertificateValid :
    WideCertificateValid leaf3228Box leaf3228Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi202ValidityFacts
    leaf3228LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3228CoverageChecked :
    coverageCheck (innerAD leaf3228Box) leaf3228InnerLog = true := by
  rfl'

private theorem leaf3228InnerLogValid :
    leaf3228InnerLog.Valid 8 (innerAD leaf3228Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf3228CoverageChecked

private noncomputable def leaf3228InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629385/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3228InputLogOnePlusV_eq :
    leaf3228InputLogOnePlusV = outerEnclosure 24
      (leaf3228Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3228RoundedFacts : LeafRoundedFacts 8
    leaf3228Certificate.logOnePlusV leaf3228InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3228InputLogOnePlusV_eq }

private noncomputable def leaf3228Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi202InputQChi innerPair94Input
    leaf3228InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3228LowerChecked :
    lowerCheck 24 leaf3228Box leaf3228Inputs = true := by
  rfl'

private theorem leaf3228CoversExact : CoversExact 8
    leaf3228Box leaf3228Certificate leaf3228InnerLog leaf3228Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi202RoundedFacts
    innerPair94RoundedFacts leaf3228RoundedFacts (by rfl)

private theorem leaf3228FlatSound : Sound leaf3228Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3228CertificateValid
    leaf3228InnerLogValid leaf3228CoversExact leaf3228LowerChecked

private noncomputable def leaf3229Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3229Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742407/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810638336) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1955507067/1073741824) }, upper := { exponent := 0, mantissa := (30131/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622945621/91621276672) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf3229InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3229LocalValidity :
    LeafFacts leaf3229Box leaf3229Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3229Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810638336) }) = true
      norm_num [leaf3229Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3229CertificateValid :
    WideCertificateValid leaf3229Box leaf3229Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi199ValidityFacts
    leaf3229LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3229CoverageChecked :
    coverageCheck (innerAD leaf3229Box) leaf3229InnerLog = true := by
  rfl'

private theorem leaf3229InnerLogValid :
    leaf3229InnerLog.Valid 8 (innerAD leaf3229Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3229CoverageChecked

private noncomputable def leaf3229InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3229InputLogOnePlusV_eq :
    leaf3229InputLogOnePlusV = outerEnclosure 24
      (leaf3229Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3229RoundedFacts : LeafRoundedFacts 8
    leaf3229Certificate.logOnePlusV leaf3229InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3229InputLogOnePlusV_eq }

private noncomputable def leaf3229Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi199InputQChi innerPair91Input
    leaf3229InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3229LowerChecked :
    lowerCheck 24 leaf3229Box leaf3229Inputs = true := by
  rfl'

private theorem leaf3229CoversExact : CoversExact 8
    leaf3229Box leaf3229Certificate leaf3229InnerLog leaf3229Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi199RoundedFacts
    innerPair91RoundedFacts leaf3229RoundedFacts (by rfl)

private theorem leaf3229FlatSound : Sound leaf3229Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3229CertificateValid
    leaf3229InnerLogValid leaf3229CoversExact leaf3229LowerChecked

private noncomputable def leaf3230Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3230Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486376960) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1959307921/1073741824) }, upper := { exponent := 0, mantissa := (15095/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973761331/54972753920) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf3230InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3230LocalValidity :
    LeafFacts leaf3230Box leaf3230Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3230Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486376960) }) = true
      norm_num [leaf3230Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3230CertificateValid :
    WideCertificateValid leaf3230Box leaf3230Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi199ValidityFacts
    leaf3230LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3230CoverageChecked :
    coverageCheck (innerAD leaf3230Box) leaf3230InnerLog = true := by
  rfl'

private theorem leaf3230InnerLogValid :
    leaf3230InnerLog.Valid 8 (innerAD leaf3230Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3230CoverageChecked

private noncomputable def leaf3230InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3230InputLogOnePlusV_eq :
    leaf3230InputLogOnePlusV = outerEnclosure 24
      (leaf3230Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3230RoundedFacts : LeafRoundedFacts 8
    leaf3230Certificate.logOnePlusV leaf3230InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3230InputLogOnePlusV_eq }

private noncomputable def leaf3230Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi199InputQChi innerPair91Input
    leaf3230InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3230LowerChecked :
    lowerCheck 24 leaf3230Box leaf3230Inputs = true := by
  rfl'

private theorem leaf3230CoversExact : CoversExact 8
    leaf3230Box leaf3230Certificate leaf3230InnerLog leaf3230Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi199RoundedFacts
    innerPair91RoundedFacts leaf3230RoundedFacts (by rfl)

private theorem leaf3230FlatSound : Sound leaf3230Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3230CertificateValid
    leaf3230InnerLogValid leaf3230CoversExact leaf3230LowerChecked

private noncomputable def leaf3231Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3231Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742409/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431795712) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1970710489/1073741824) }, upper := { exponent := 0, mantissa := (7591/4096) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868717567/274863591424) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf3231InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3231LocalValidity :
    LeafFacts leaf3231Box leaf3231Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3231Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431795712) }) = true
      norm_num [leaf3231Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3231CertificateValid :
    WideCertificateValid leaf3231Box leaf3231Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi200ValidityFacts
    leaf3231LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3231CoverageChecked :
    coverageCheck (innerAD leaf3231Box) leaf3231InnerLog = true := by
  rfl'

private theorem leaf3231InnerLogValid :
    leaf3231InnerLog.Valid 8 (innerAD leaf3231Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3231CoverageChecked

private noncomputable def leaf3231InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814697/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3231InputLogOnePlusV_eq :
    leaf3231InputLogOnePlusV = outerEnclosure 24
      (leaf3231Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3231RoundedFacts : LeafRoundedFacts 8
    leaf3231Certificate.logOnePlusV leaf3231InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3231InputLogOnePlusV_eq }

private noncomputable def leaf3231Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi200InputQChi innerPair91Input
    leaf3231InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3231LowerChecked :
    lowerCheck 24 leaf3231Box leaf3231Inputs = true := by
  rfl'

private theorem leaf3231CoversExact : CoversExact 8
    leaf3231Box leaf3231Certificate leaf3231InnerLog leaf3231Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi200RoundedFacts
    innerPair91RoundedFacts leaf3231RoundedFacts (by rfl)

private theorem leaf3231FlatSound : Sound leaf3231Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3231CertificateValid
    leaf3231InnerLogValid leaf3231CoversExact leaf3231LowerChecked

private noncomputable def leaf3232Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3232Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431764992) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1974576875/1073741824) }, upper := { exponent := 0, mantissa := (3803/2048) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868686847/274863529984) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf3232InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3232LocalValidity :
    LeafFacts leaf3232Box leaf3232Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3232Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431764992) }) = true
      norm_num [leaf3232Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3232CertificateValid :
    WideCertificateValid leaf3232Box leaf3232Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi200ValidityFacts
    leaf3232LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3232CoverageChecked :
    coverageCheck (innerAD leaf3232Box) leaf3232InnerLog = true := by
  rfl'

private theorem leaf3232InnerLogValid :
    leaf3232InnerLog.Valid 8 (innerAD leaf3232Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3232CoverageChecked

private noncomputable def leaf3232InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3232InputLogOnePlusV_eq :
    leaf3232InputLogOnePlusV = outerEnclosure 24
      (leaf3232Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3232RoundedFacts : LeafRoundedFacts 8
    leaf3232Certificate.logOnePlusV leaf3232InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3232InputLogOnePlusV_eq }

private noncomputable def leaf3232Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi200InputQChi innerPair91Input
    leaf3232InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3232LowerChecked :
    lowerCheck 24 leaf3232Box leaf3232Inputs = true := by
  rfl'

private theorem leaf3232CoversExact : CoversExact 8
    leaf3232Box leaf3232Certificate leaf3232InnerLog leaf3232Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi200RoundedFacts
    innerPair91RoundedFacts leaf3232RoundedFacts (by rfl)

private theorem leaf3232FlatSound : Sound leaf3232Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3232CertificateValid
    leaf3232InnerLogValid leaf3232CoversExact leaf3232LowerChecked

private noncomputable def leaf3233Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3233Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431854592) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1963108775/1073741824) }, upper := { exponent := 0, mantissa := (30249/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868776447/274863709184) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf3233InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3233LocalValidity :
    LeafFacts leaf3233Box leaf3233Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3233Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431854592) }) = true
      norm_num [leaf3233Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3233CertificateValid :
    WideCertificateValid leaf3233Box leaf3233Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi199ValidityFacts
    leaf3233LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3233CoverageChecked :
    coverageCheck (innerAD leaf3233Box) leaf3233InnerLog = true := by
  rfl'

private theorem leaf3233InnerLogValid :
    leaf3233InnerLog.Valid 8 (innerAD leaf3233Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3233CoverageChecked

private noncomputable def leaf3233InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814695/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3233InputLogOnePlusV_eq :
    leaf3233InputLogOnePlusV = outerEnclosure 24
      (leaf3233Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3233RoundedFacts : LeafRoundedFacts 8
    leaf3233Certificate.logOnePlusV leaf3233InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3233InputLogOnePlusV_eq }

private noncomputable def leaf3233Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi199InputQChi innerPair91Input
    leaf3233InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3233LowerChecked :
    lowerCheck 24 leaf3233Box leaf3233Inputs = true := by
  rfl'

private theorem leaf3233CoversExact : CoversExact 8
    leaf3233Box leaf3233Certificate leaf3233InnerLog leaf3233Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi199RoundedFacts
    innerPair91RoundedFacts leaf3233RoundedFacts (by rfl)

private theorem leaf3233FlatSound : Sound leaf3233Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3233CertificateValid
    leaf3233InnerLogValid leaf3233CoversExact leaf3233LowerChecked

private noncomputable def leaf3234Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3234Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810608128) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1966909629/1073741824) }, upper := { exponent := 0, mantissa := (7577/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622915413/91621216256) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf3234InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3234LocalValidity :
    LeafFacts leaf3234Box leaf3234Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3234Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810608128) }) = true
      norm_num [leaf3234Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3234CertificateValid :
    WideCertificateValid leaf3234Box leaf3234Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi199ValidityFacts
    leaf3234LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3234CoverageChecked :
    coverageCheck (innerAD leaf3234Box) leaf3234InnerLog = true := by
  rfl'

private theorem leaf3234InnerLogValid :
    leaf3234InnerLog.Valid 8 (innerAD leaf3234Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3234CoverageChecked

private noncomputable def leaf3234InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726837/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3234InputLogOnePlusV_eq :
    leaf3234InputLogOnePlusV = outerEnclosure 24
      (leaf3234Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3234RoundedFacts : LeafRoundedFacts 8
    leaf3234Certificate.logOnePlusV leaf3234InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3234InputLogOnePlusV_eq }

private noncomputable def leaf3234Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi199InputQChi innerPair91Input
    leaf3234InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3234LowerChecked :
    lowerCheck 24 leaf3234Box leaf3234Inputs = true := by
  rfl'

private theorem leaf3234CoversExact : CoversExact 8
    leaf3234Box leaf3234Certificate leaf3234InnerLog leaf3234Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi199RoundedFacts
    innerPair91RoundedFacts leaf3234RoundedFacts (by rfl)

private theorem leaf3234FlatSound : Sound leaf3234Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3234CertificateValid
    leaf3234InnerLogValid leaf3234CoversExact leaf3234LowerChecked

private noncomputable def leaf3235Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3235Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431734272) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1978443261/1073741824) }, upper := { exponent := 0, mantissa := (7621/4096) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868656127/274863468544) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf3235InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3235LocalValidity :
    LeafFacts leaf3235Box leaf3235Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3235Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431734272) }) = true
      norm_num [leaf3235Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3235CertificateValid :
    WideCertificateValid leaf3235Box leaf3235Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi200ValidityFacts
    leaf3235LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3235CoverageChecked :
    coverageCheck (innerAD leaf3235Box) leaf3235InnerLog = true := by
  rfl'

private theorem leaf3235InnerLogValid :
    leaf3235InnerLog.Valid 8 (innerAD leaf3235Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3235CoverageChecked

private noncomputable def leaf3235InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3235InputLogOnePlusV_eq :
    leaf3235InputLogOnePlusV = outerEnclosure 24
      (leaf3235Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3235RoundedFacts : LeafRoundedFacts 8
    leaf3235Certificate.logOnePlusV leaf3235InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3235InputLogOnePlusV_eq }

private noncomputable def leaf3235Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi200InputQChi innerPair91Input
    leaf3235InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3235LowerChecked :
    lowerCheck 24 leaf3235Box leaf3235Inputs = true := by
  rfl'

private theorem leaf3235CoversExact : CoversExact 8
    leaf3235Box leaf3235Certificate leaf3235InnerLog leaf3235Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi200RoundedFacts
    innerPair91RoundedFacts leaf3235RoundedFacts (by rfl)

private theorem leaf3235FlatSound : Sound leaf3235Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3235CertificateValid
    leaf3235InnerLogValid leaf3235CoversExact leaf3235LowerChecked

private noncomputable def leaf3236Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3236Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084217856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1982309647/1073741824) }, upper := { exponent := 0, mantissa := (1909/1024) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168742671/16168435712) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf3236InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3236LocalValidity :
    LeafFacts leaf3236Box leaf3236Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3236Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084217856) }) = true
      norm_num [leaf3236Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3236CertificateValid :
    WideCertificateValid leaf3236Box leaf3236Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi200ValidityFacts
    leaf3236LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3236CoverageChecked :
    coverageCheck (innerAD leaf3236Box) leaf3236InnerLog = true := by
  rfl'

private theorem leaf3236InnerLogValid :
    leaf3236InnerLog.Valid 8 (innerAD leaf3236Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3236CoverageChecked

private noncomputable def leaf3236InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3236InputLogOnePlusV_eq :
    leaf3236InputLogOnePlusV = outerEnclosure 24
      (leaf3236Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3236RoundedFacts : LeafRoundedFacts 8
    leaf3236Certificate.logOnePlusV leaf3236InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3236InputLogOnePlusV_eq }

private noncomputable def leaf3236Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi200InputQChi innerPair91Input
    leaf3236InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3236LowerChecked :
    lowerCheck 24 leaf3236Box leaf3236Inputs = true := by
  rfl'

private theorem leaf3236CoversExact : CoversExact 8
    leaf3236Box leaf3236Certificate leaf3236InnerLog leaf3236Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi200RoundedFacts
    innerPair91RoundedFacts leaf3236RoundedFacts (by rfl)

private theorem leaf3236FlatSound : Sound leaf3236Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3236CertificateValid
    leaf3236InnerLogValid leaf3236CoversExact leaf3236LowerChecked

private noncomputable def leaf3237Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3237Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137432036864) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1939779383/1073741824) }, upper := { exponent := 0, mantissa := (29893/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868958719/274864073728) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf3237InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3237LocalValidity :
    LeafFacts leaf3237Box leaf3237Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3237Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137432036864) }) = true
      norm_num [leaf3237Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3237CertificateValid :
    WideCertificateValid leaf3237Box leaf3237Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi201ValidityFacts
    leaf3237LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3237CoverageChecked :
    coverageCheck (innerAD leaf3237Box) leaf3237InnerLog = true := by
  rfl'

private theorem leaf3237InnerLogValid :
    leaf3237InnerLog.Valid 8 (innerAD leaf3237Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3237CoverageChecked

private noncomputable def leaf3237InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629379/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3237InputLogOnePlusV_eq :
    leaf3237InputLogOnePlusV = outerEnclosure 24
      (leaf3237Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3237RoundedFacts : LeafRoundedFacts 8
    leaf3237Certificate.logOnePlusV leaf3237InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3237InputLogOnePlusV_eq }

private noncomputable def leaf3237Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi201InputQChi innerPair221Input
    leaf3237InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3237LowerChecked :
    lowerCheck 24 leaf3237Box leaf3237Inputs = true := by
  rfl'

private theorem leaf3237CoversExact : CoversExact 8
    leaf3237Box leaf3237Certificate leaf3237InnerLog leaf3237Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi201RoundedFacts
    innerPair221RoundedFacts leaf3237RoundedFacts (by rfl)

private theorem leaf3237FlatSound : Sound leaf3237Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3237CertificateValid
    leaf3237InnerLogValid leaf3237CoversExact leaf3237LowerChecked

private noncomputable def leaf3238Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3238Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486401536) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1943449173/1073741824) }, upper := { exponent := 0, mantissa := (14975/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973785907/54972803072) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf3238InnerLog : WideLogData :=
  innerPair221Data

set_option maxRecDepth 1000000 in
private theorem leaf3238LocalValidity :
    LeafFacts leaf3238Box leaf3238Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3238Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486401536) }) = true
      norm_num [leaf3238Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3238CertificateValid :
    WideCertificateValid leaf3238Box leaf3238Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi201ValidityFacts
    leaf3238LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3238CoverageChecked :
    coverageCheck (innerAD leaf3238Box) leaf3238InnerLog = true := by
  rfl'

private theorem leaf3238InnerLogValid :
    leaf3238InnerLog.Valid 8 (innerAD leaf3238Box) :=
  wideLogDataValid_of_cachedCheck endpoint67PositiveFacts
    endpoint64PositiveFacts.valid leaf3238CoverageChecked

private noncomputable def leaf3238InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629381/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3238InputLogOnePlusV_eq :
    leaf3238InputLogOnePlusV = outerEnclosure 24
      (leaf3238Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3238RoundedFacts : LeafRoundedFacts 8
    leaf3238Certificate.logOnePlusV leaf3238InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3238InputLogOnePlusV_eq }

private noncomputable def leaf3238Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi201InputQChi innerPair221Input
    leaf3238InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3238LowerChecked :
    lowerCheck 24 leaf3238Box leaf3238Inputs = true := by
  rfl'

private theorem leaf3238CoversExact : CoversExact 8
    leaf3238Box leaf3238Certificate leaf3238InnerLog leaf3238Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi201RoundedFacts
    innerPair221RoundedFacts leaf3238RoundedFacts (by rfl)

private theorem leaf3238FlatSound : Sound leaf3238Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3238CertificateValid
    leaf3238InnerLogValid leaf3238CoversExact leaf3238LowerChecked

private noncomputable def leaf3239Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3239Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486383104) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1955244933/1073741824) }, upper := { exponent := 0, mantissa := (15065/8192) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973767475/54972766208) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf3239InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf3239LocalValidity :
    LeafFacts leaf3239Box leaf3239Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3239Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486383104) }) = true
      norm_num [leaf3239Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3239CertificateValid :
    WideCertificateValid leaf3239Box leaf3239Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi202ValidityFacts
    leaf3239LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3239CoverageChecked :
    coverageCheck (innerAD leaf3239Box) leaf3239InnerLog = true := by
  rfl'

private theorem leaf3239InnerLogValid :
    leaf3239InnerLog.Valid 8 (innerAD leaf3239Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf3239CoverageChecked

private noncomputable def leaf3239InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814693/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3239InputLogOnePlusV_eq :
    leaf3239InputLogOnePlusV = outerEnclosure 24
      (leaf3239Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3239RoundedFacts : LeafRoundedFacts 8
    leaf3239Certificate.logOnePlusV leaf3239InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3239InputLogOnePlusV_eq }

private noncomputable def leaf3239Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi202InputQChi innerPair94Input
    leaf3239InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3239LowerChecked :
    lowerCheck 24 leaf3239Box leaf3239Inputs = true := by
  rfl'

private theorem leaf3239CoversExact : CoversExact 8
    leaf3239Box leaf3239Certificate leaf3239InnerLog leaf3239Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi202RoundedFacts
    innerPair94RoundedFacts leaf3239RoundedFacts (by rfl)

private theorem leaf3239FlatSound : Sound leaf3239Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3239CertificateValid
    leaf3239InnerLogValid leaf3239CoversExact leaf3239LowerChecked

private noncomputable def leaf3240Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3240Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (355134165/355121152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1958980255/1073741824) }, upper := { exponent := 0, mantissa := (7547/4096) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (710255317/710242304) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf3240InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf3240LocalValidity :
    LeafFacts leaf3240Box leaf3240Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3240Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (355134165/355121152) }) = true
      norm_num [leaf3240Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3240CertificateValid :
    WideCertificateValid leaf3240Box leaf3240Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi202ValidityFacts
    leaf3240LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3240CoverageChecked :
    coverageCheck (innerAD leaf3240Box) leaf3240InnerLog = true := by
  rfl'

private theorem leaf3240InnerLogValid :
    leaf3240InnerLog.Valid 8 (innerAD leaf3240Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf3240CoverageChecked

private noncomputable def leaf3240InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907347/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3240InputLogOnePlusV_eq :
    leaf3240InputLogOnePlusV = outerEnclosure 24
      (leaf3240Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3240RoundedFacts : LeafRoundedFacts 8
    leaf3240Certificate.logOnePlusV leaf3240InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3240InputLogOnePlusV_eq }

private noncomputable def leaf3240Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi202InputQChi innerPair94Input
    leaf3240InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3240LowerChecked :
    lowerCheck 24 leaf3240Box leaf3240Inputs = true := by
  rfl'

private theorem leaf3240CoversExact : CoversExact 8
    leaf3240Box leaf3240Certificate leaf3240InnerLog leaf3240Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi202RoundedFacts
    innerPair94RoundedFacts leaf3240RoundedFacts (by rfl)

private theorem leaf3240FlatSound : Sound leaf3240Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3240CertificateValid
    leaf3240InnerLogValid leaf3240CoversExact leaf3240LowerChecked

private noncomputable def leaf3241Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3241Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431978496) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1947118963/1073741824) }, upper := { exponent := 0, mantissa := (30007/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868900351/274863956992) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf3241InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf3241LocalValidity :
    LeafFacts leaf3241Box leaf3241Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3241Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431978496) }) = true
      norm_num [leaf3241Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3241CertificateValid :
    WideCertificateValid leaf3241Box leaf3241Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi201ValidityFacts
    leaf3241LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3241CoverageChecked :
    coverageCheck (innerAD leaf3241Box) leaf3241InnerLog = true := by
  rfl'

private theorem leaf3241InnerLogValid :
    leaf3241InnerLog.Valid 8 (innerAD leaf3241Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf3241CoverageChecked

private noncomputable def leaf3241InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814691/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3241InputLogOnePlusV_eq :
    leaf3241InputLogOnePlusV = outerEnclosure 24
      (leaf3241Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3241RoundedFacts : LeafRoundedFacts 8
    leaf3241Certificate.logOnePlusV leaf3241InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3241InputLogOnePlusV_eq }

private noncomputable def leaf3241Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi201InputQChi innerPair94Input
    leaf3241InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3241LowerChecked :
    lowerCheck 24 leaf3241Box leaf3241Inputs = true := by
  rfl'

private theorem leaf3241CoversExact : CoversExact 8
    leaf3241Box leaf3241Certificate leaf3241InnerLog leaf3241Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi201RoundedFacts
    innerPair94RoundedFacts leaf3241RoundedFacts (by rfl)

private theorem leaf3241FlatSound : Sound leaf3241Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3241CertificateValid
    leaf3241InnerLogValid leaf3241CoversExact leaf3241LowerChecked

private noncomputable def leaf3242Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (7/32), chiHi := (57/256) }

private noncomputable def leaf3242Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431949312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1950788753/1073741824) }, upper := { exponent := 0, mantissa := (1879/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi201LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868871167/274863898624) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf3242InnerLog : WideLogData :=
  innerPair94Data

set_option maxRecDepth 1000000 in
private theorem leaf3242LocalValidity :
    LeafFacts leaf3242Box leaf3242Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3242Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431949312) }) = true
      norm_num [leaf3242Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3242CertificateValid :
    WideCertificateValid leaf3242Box leaf3242Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi201ValidityFacts
    leaf3242LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3242CoverageChecked :
    coverageCheck (innerAD leaf3242Box) leaf3242InnerLog = true := by
  rfl'

private theorem leaf3242InnerLogValid :
    leaf3242InnerLog.Valid 8 (innerAD leaf3242Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint61PositiveFacts.valid leaf3242CoverageChecked

private noncomputable def leaf3242InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453673/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3242InputLogOnePlusV_eq :
    leaf3242InputLogOnePlusV = outerEnclosure 24
      (leaf3242Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3242RoundedFacts : LeafRoundedFacts 8
    leaf3242Certificate.logOnePlusV leaf3242InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3242InputLogOnePlusV_eq }

private noncomputable def leaf3242Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi201InputQChi innerPair94Input
    leaf3242InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3242LowerChecked :
    lowerCheck 24 leaf3242Box leaf3242Inputs = true := by
  rfl'

private theorem leaf3242CoversExact : CoversExact 8
    leaf3242Box leaf3242Certificate leaf3242InnerLog leaf3242Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi201RoundedFacts
    innerPair94RoundedFacts leaf3242RoundedFacts (by rfl)

private theorem leaf3242FlatSound : Sound leaf3242Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3242CertificateValid
    leaf3242InnerLogValid leaf3242CoversExact leaf3242LowerChecked

private noncomputable def leaf3243Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3243Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (534774015/534754304) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1962715577/1073741824) }, upper := { exponent := 0, mantissa := (15123/8192) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (1069528319/1069508608) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf3243InnerLog : WideLogData :=
  innerPair99Data

set_option maxRecDepth 1000000 in
private theorem leaf3243LocalValidity :
    LeafFacts leaf3243Box leaf3243Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3243Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (534774015/534754304) }) = true
      norm_num [leaf3243Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3243CertificateValid :
    WideCertificateValid leaf3243Box leaf3243Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi202ValidityFacts
    leaf3243LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3243CoverageChecked :
    coverageCheck (innerAD leaf3243Box) leaf3243InnerLog = true := by
  rfl'

private theorem leaf3243InnerLogValid :
    leaf3243InnerLog.Valid 8 (innerAD leaf3243Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint211PositiveFacts.valid leaf3243CoverageChecked

private noncomputable def leaf3243InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814695/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3243InputLogOnePlusV_eq :
    leaf3243InputLogOnePlusV = outerEnclosure 24
      (leaf3243Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3243RoundedFacts : LeafRoundedFacts 8
    leaf3243Certificate.logOnePlusV leaf3243InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3243InputLogOnePlusV_eq }

private noncomputable def leaf3243Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi202InputQChi innerPair99Input
    leaf3243InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3243LowerChecked :
    lowerCheck 24 leaf3243Box leaf3243Inputs = true := by
  rfl'

private theorem leaf3243CoversExact : CoversExact 8
    leaf3243Box leaf3243Certificate leaf3243InnerLog leaf3243Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi202RoundedFacts
    innerPair99RoundedFacts leaf3243RoundedFacts (by rfl)

private theorem leaf3243FlatSound : Sound leaf3243Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3243CertificateValid
    leaf3243InnerLogValid leaf3243CoversExact leaf3243LowerChecked

private noncomputable def leaf3244Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (57/256), chiHi := (29/128) }

private noncomputable def leaf3244Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431826432) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1966450899/1073741824) }, upper := { exponent := 0, mantissa := (947/512) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi202LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868748287/274863652864) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf3244InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3244LocalValidity :
    LeafFacts leaf3244Box leaf3244Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3244Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431826432) }) = true
      norm_num [leaf3244Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3244CertificateValid :
    WideCertificateValid leaf3244Box leaf3244Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi202ValidityFacts
    leaf3244LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3244CoverageChecked :
    coverageCheck (innerAD leaf3244Box) leaf3244InnerLog = true := by
  rfl'

private theorem leaf3244InnerLogValid :
    leaf3244InnerLog.Valid 8 (innerAD leaf3244Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3244CoverageChecked

private noncomputable def leaf3244InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (726837/1048576) }

set_option maxRecDepth 1000000 in
private theorem leaf3244InputLogOnePlusV_eq :
    leaf3244InputLogOnePlusV = outerEnclosure 24
      (leaf3244Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3244RoundedFacts : LeafRoundedFacts 8
    leaf3244Certificate.logOnePlusV leaf3244InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3244InputLogOnePlusV_eq }

private noncomputable def leaf3244Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi202InputQChi innerPair91Input
    leaf3244InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3244LowerChecked :
    lowerCheck 24 leaf3244Box leaf3244Inputs = true := by
  rfl'

private theorem leaf3244CoversExact : CoversExact 8
    leaf3244Box leaf3244Certificate leaf3244InnerLog leaf3244Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi202RoundedFacts
    innerPair91RoundedFacts leaf3244RoundedFacts (by rfl)

private theorem leaf3244FlatSound : Sound leaf3244Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3244CertificateValid
    leaf3244InnerLogValid leaf3244CoversExact leaf3244LowerChecked

private noncomputable def leaf3245Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3245Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431794176) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1970710483/1073741824) }, upper := { exponent := 0, mantissa := (30367/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868716031/274863588352) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf3245InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3245LocalValidity :
    LeafFacts leaf3245Box leaf3245Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3245Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431794176) }) = true
      norm_num [leaf3245Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3245CertificateValid :
    WideCertificateValid leaf3245Box leaf3245Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi199ValidityFacts
    leaf3245LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3245CoverageChecked :
    coverageCheck (innerAD leaf3245Box) leaf3245InnerLog = true := by
  rfl'

private theorem leaf3245InnerLogValid :
    leaf3245InnerLog.Valid 8 (innerAD leaf3245Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3245CoverageChecked

private noncomputable def leaf3245InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814697/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3245InputLogOnePlusV_eq :
    leaf3245InputLogOnePlusV = outerEnclosure 24
      (leaf3245Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3245RoundedFacts : LeafRoundedFacts 8
    leaf3245Certificate.logOnePlusV leaf3245InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3245InputLogOnePlusV_eq }

private noncomputable def leaf3245Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi199InputQChi innerPair91Input
    leaf3245InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3245LowerChecked :
    lowerCheck 24 leaf3245Box leaf3245Inputs = true := by
  rfl'

private theorem leaf3245CoversExact : CoversExact 8
    leaf3245Box leaf3245Certificate leaf3245InnerLog leaf3245Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi199RoundedFacts
    innerPair91RoundedFacts leaf3245RoundedFacts (by rfl)

private theorem leaf3245FlatSound : Sound leaf3245Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3245CertificateValid
    leaf3245InnerLogValid leaf3245CoversExact leaf3245LowerChecked

private noncomputable def leaf3246Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3246Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431763968) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1974511337/1073741824) }, upper := { exponent := 0, mantissa := (15213/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868685823/274863527936) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf3246InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3246LocalValidity :
    LeafFacts leaf3246Box leaf3246Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3246Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431763968) }) = true
      norm_num [leaf3246Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3246CertificateValid :
    WideCertificateValid leaf3246Box leaf3246Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi199ValidityFacts
    leaf3246LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3246CoverageChecked :
    coverageCheck (innerAD leaf3246Box) leaf3246InnerLog = true := by
  rfl'

private theorem leaf3246InnerLogValid :
    leaf3246InnerLog.Valid 8 (innerAD leaf3246Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3246CoverageChecked

private noncomputable def leaf3246InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907349/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3246InputLogOnePlusV_eq :
    leaf3246InputLogOnePlusV = outerEnclosure 24
      (leaf3246Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3246RoundedFacts : LeafRoundedFacts 8
    leaf3246Certificate.logOnePlusV leaf3246InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3246InputLogOnePlusV_eq }

private noncomputable def leaf3246Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi199InputQChi innerPair91Input
    leaf3246InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3246LowerChecked :
    lowerCheck 24 leaf3246Box leaf3246Inputs = true := by
  rfl'

private theorem leaf3246CoversExact : CoversExact 8
    leaf3246Box leaf3246Certificate leaf3246InnerLog leaf3246Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi199RoundedFacts
    innerPair91RoundedFacts leaf3246RoundedFacts (by rfl)

private theorem leaf3246FlatSound : Sound leaf3246Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3246CertificateValid
    leaf3246InnerLogValid leaf3246CoversExact leaf3246LowerChecked

private noncomputable def leaf3247Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3247Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431672832) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1986176033/1073741824) }, upper := { exponent := 0, mantissa := (7651/4096) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868594687/274863345664) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf3247InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3247LocalValidity :
    LeafFacts leaf3247Box leaf3247Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3247Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431672832) }) = true
      norm_num [leaf3247Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3247CertificateValid :
    WideCertificateValid leaf3247Box leaf3247Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi200ValidityFacts
    leaf3247LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3247CoverageChecked :
    coverageCheck (innerAD leaf3247Box) leaf3247InnerLog = true := by
  rfl'

private theorem leaf3247InnerLogValid :
    leaf3247InnerLog.Valid 8 (innerAD leaf3247Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3247CoverageChecked

private noncomputable def leaf3247InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3247InputLogOnePlusV_eq :
    leaf3247InputLogOnePlusV = outerEnclosure 24
      (leaf3247Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3247RoundedFacts : LeafRoundedFacts 8
    leaf3247Certificate.logOnePlusV leaf3247InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3247InputLogOnePlusV_eq }

private noncomputable def leaf3247Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi200InputQChi innerPair91Input
    leaf3247InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3247LowerChecked :
    lowerCheck 24 leaf3247Box leaf3247Inputs = true := by
  rfl'

private theorem leaf3247CoversExact : CoversExact 8
    leaf3247Box leaf3247Certificate leaf3247InnerLog leaf3247Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi200RoundedFacts
    innerPair91RoundedFacts leaf3247RoundedFacts (by rfl)

private theorem leaf3247FlatSound : Sound leaf3247Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3247CertificateValid
    leaf3247InnerLogValid leaf3247CoversExact leaf3247LowerChecked

private noncomputable def leaf3248Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3248Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431642112) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1990042419/1073741824) }, upper := { exponent := 0, mantissa := (3833/2048) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868563967/274863284224) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf3248InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3248LocalValidity :
    LeafFacts leaf3248Box leaf3248Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3248Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431642112) }) = true
      norm_num [leaf3248Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3248CertificateValid :
    WideCertificateValid leaf3248Box leaf3248Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi200ValidityFacts
    leaf3248LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3248CoverageChecked :
    coverageCheck (innerAD leaf3248Box) leaf3248InnerLog = true := by
  rfl'

private theorem leaf3248InnerLogValid :
    leaf3248InnerLog.Valid 8 (innerAD leaf3248Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3248CoverageChecked

private noncomputable def leaf3248InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3248InputLogOnePlusV_eq :
    leaf3248InputLogOnePlusV = outerEnclosure 24
      (leaf3248Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3248RoundedFacts : LeafRoundedFacts 8
    leaf3248Certificate.logOnePlusV leaf3248InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3248InputLogOnePlusV_eq }

private noncomputable def leaf3248Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi200InputQChi innerPair91Input
    leaf3248InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3248LowerChecked :
    lowerCheck 24 leaf3248Box leaf3248Inputs = true := by
  rfl'

private theorem leaf3248CoversExact : CoversExact 8
    leaf3248Box leaf3248Certificate leaf3248InnerLog leaf3248Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi200RoundedFacts
    innerPair91RoundedFacts leaf3248RoundedFacts (by rfl)

private theorem leaf3248FlatSound : Sound leaf3248Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3248CertificateValid
    leaf3248InnerLogValid leaf3248CoversExact leaf3248LowerChecked

private noncomputable def leaf3249Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3249Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (3054153819/3054038528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1978312191/1073741824) }, upper := { exponent := 0, mantissa := (30485/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (6108192347/6108077056) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf3249InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3249LocalValidity :
    LeafFacts leaf3249Box leaf3249Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3249Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (3054153819/3054038528) }) = true
      norm_num [leaf3249Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3249CertificateValid :
    WideCertificateValid leaf3249Box leaf3249Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi199ValidityFacts
    leaf3249LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3249CoverageChecked :
    coverageCheck (innerAD leaf3249Box) leaf3249InnerLog = true := by
  rfl'

private theorem leaf3249InnerLogValid :
    leaf3249InnerLog.Valid 8 (innerAD leaf3249Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3249CoverageChecked

private noncomputable def leaf3249InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629397/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3249InputLogOnePlusV_eq :
    leaf3249InputLogOnePlusV = outerEnclosure 24
      (leaf3249Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3249RoundedFacts : LeafRoundedFacts 8
    leaf3249Certificate.logOnePlusV leaf3249InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3249InputLogOnePlusV_eq }

private noncomputable def leaf3249Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi199InputQChi innerPair91Input
    leaf3249InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3249LowerChecked :
    lowerCheck 24 leaf3249Box leaf3249Inputs = true := by
  rfl'

private theorem leaf3249CoversExact : CoversExact 8
    leaf3249Box leaf3249Certificate leaf3249InnerLog leaf3249Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi199RoundedFacts
    innerPair91RoundedFacts leaf3249RoundedFacts (by rfl)

private theorem leaf3249FlatSound : Sound leaf3249Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3249CertificateValid
    leaf3249InnerLogValid leaf3249CoversExact leaf3249LowerChecked

private noncomputable def leaf3250Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (29/128), chiHi := (59/256) }

private noncomputable def leaf3250Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (8084524815/8084217856) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1982113045/1073741824) }, upper := { exponent := 0, mantissa := (1909/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi199LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (16168742671/16168435712) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf3250InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3250LocalValidity :
    LeafFacts leaf3250Box leaf3250Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3250Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (8084524815/8084217856) }) = true
      norm_num [leaf3250Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3250CertificateValid :
    WideCertificateValid leaf3250Box leaf3250Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi199ValidityFacts
    leaf3250LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3250CoverageChecked :
    coverageCheck (innerAD leaf3250Box) leaf3250InnerLog = true := by
  rfl'

private theorem leaf3250InnerLogValid :
    leaf3250InnerLog.Valid 8 (innerAD leaf3250Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3250CoverageChecked

private noncomputable def leaf3250InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629399/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3250InputLogOnePlusV_eq :
    leaf3250InputLogOnePlusV = outerEnclosure 24
      (leaf3250Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3250RoundedFacts : LeafRoundedFacts 8
    leaf3250Certificate.logOnePlusV leaf3250InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3250InputLogOnePlusV_eq }

private noncomputable def leaf3250Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi199InputQChi innerPair91Input
    leaf3250InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3250LowerChecked :
    lowerCheck 24 leaf3250Box leaf3250Inputs = true := by
  rfl'

private theorem leaf3250CoversExact : CoversExact 8
    leaf3250Box leaf3250Certificate leaf3250InnerLog leaf3250Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi199RoundedFacts
    innerPair91RoundedFacts leaf3250RoundedFacts (by rfl)

private theorem leaf3250FlatSound : Sound leaf3250Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3250CertificateValid
    leaf3250InnerLogValid leaf3250CoversExact leaf3250LowerChecked

private noncomputable def leaf3251Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3251Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431611392) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1993908805/1073741824) }, upper := { exponent := 0, mantissa := (7681/4096) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868533247/274863222784) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf3251InnerLog : WideLogData :=
  innerPair199Data

set_option maxRecDepth 1000000 in
private theorem leaf3251LocalValidity :
    LeafFacts leaf3251Box leaf3251Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3251Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431611392) }) = true
      norm_num [leaf3251Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3251CertificateValid :
    WideCertificateValid leaf3251Box leaf3251Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi200ValidityFacts
    leaf3251LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3251CoverageChecked :
    coverageCheck (innerAD leaf3251Box) leaf3251InnerLog = true := by
  rfl'

private theorem leaf3251InnerLogValid :
    leaf3251InnerLog.Valid 8 (innerAD leaf3251Box) :=
  wideLogDataValid_of_cachedCheck endpoint61PositiveFacts
    endpoint69PositiveFacts.valid leaf3251CoverageChecked

private noncomputable def leaf3251InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3251InputLogOnePlusV_eq :
    leaf3251InputLogOnePlusV = outerEnclosure 24
      (leaf3251Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3251RoundedFacts : LeafRoundedFacts 8
    leaf3251Certificate.logOnePlusV leaf3251InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3251InputLogOnePlusV_eq }

private noncomputable def leaf3251Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi200InputQChi innerPair199Input
    leaf3251InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3251LowerChecked :
    lowerCheck 24 leaf3251Box leaf3251Inputs = true := by
  rfl'

private theorem leaf3251CoversExact : CoversExact 8
    leaf3251Box leaf3251Certificate leaf3251InnerLog leaf3251Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi200RoundedFacts
    innerPair199RoundedFacts leaf3251RoundedFacts (by rfl)

private theorem leaf3251FlatSound : Sound leaf3251Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3251CertificateValid
    leaf3251InnerLogValid leaf3251CoversExact leaf3251LowerChecked

private noncomputable def leaf3252Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (59/256), chiHi := (15/64) }

private noncomputable def leaf3252Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431580672) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1997775191/1073741824) }, upper := { exponent := 0, mantissa := (481/256) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi200LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868502527/274863161344) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf3252InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3252LocalValidity :
    LeafFacts leaf3252Box leaf3252Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3252Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431580672) }) = true
      norm_num [leaf3252Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3252CertificateValid :
    WideCertificateValid leaf3252Box leaf3252Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi200ValidityFacts
    leaf3252LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3252CoverageChecked :
    coverageCheck (innerAD leaf3252Box) leaf3252InnerLog = true := by
  rfl'

private theorem leaf3252InnerLogValid :
    leaf3252InnerLog.Valid 8 (innerAD leaf3252Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3252CoverageChecked

private noncomputable def leaf3252InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3252InputLogOnePlusV_eq :
    leaf3252InputLogOnePlusV = outerEnclosure 24
      (leaf3252Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3252RoundedFacts : LeafRoundedFacts 8
    leaf3252Certificate.logOnePlusV leaf3252InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3252InputLogOnePlusV_eq }

private noncomputable def leaf3252Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi200InputQChi innerPair482Input
    leaf3252InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3252LowerChecked :
    lowerCheck 24 leaf3252Box leaf3252Inputs = true := by
  rfl'

private theorem leaf3252CoversExact : CoversExact 8
    leaf3252Box leaf3252Certificate leaf3252InnerLog leaf3252Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi200RoundedFacts
    innerPair482RoundedFacts leaf3252RoundedFacts (by rfl)

private theorem leaf3252FlatSound : Sound leaf3252Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3252CertificateValid
    leaf3252InnerLogValid leaf3252CoversExact leaf3252LowerChecked

private noncomputable def leaf3253Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3253Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742411/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431676416) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1985913911/1073741824) }, upper := { exponent := 0, mantissa := (30597/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868598271/274863352832) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf3253InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3253LocalValidity :
    LeafFacts leaf3253Box leaf3253Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3253Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431676416) }) = true
      norm_num [leaf3253Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3253CertificateValid :
    WideCertificateValid leaf3253Box leaf3253Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi191ValidityFacts
    leaf3253LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3253CoverageChecked :
    coverageCheck (innerAD leaf3253Box) leaf3253InnerLog = true := by
  rfl'

private theorem leaf3253InnerLogValid :
    leaf3253InnerLog.Valid 8 (innerAD leaf3253Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3253CoverageChecked

private noncomputable def leaf3253InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629401/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3253InputLogOnePlusV_eq :
    leaf3253InputLogOnePlusV = outerEnclosure 24
      (leaf3253Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3253RoundedFacts : LeafRoundedFacts 8
    leaf3253Certificate.logOnePlusV leaf3253InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3253InputLogOnePlusV_eq }

private noncomputable def leaf3253Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi191InputQChi innerPair91Input
    leaf3253InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3253LowerChecked :
    lowerCheck 24 leaf3253Box leaf3253Inputs = true := by
  rfl'

private theorem leaf3253CoversExact : CoversExact 8
    leaf3253Box leaf3253Certificate leaf3253InnerLog leaf3253Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi191RoundedFacts
    innerPair91RoundedFacts leaf3253RoundedFacts (by rfl)

private theorem leaf3253FlatSound : Sound leaf3253Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3253CertificateValid
    leaf3253InnerLogValid leaf3253CoversExact leaf3253LowerChecked

private noncomputable def leaf3254Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3254Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431645184) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1989845829/1073741824) }, upper := { exponent := 0, mantissa := (15329/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868567039/274863290368) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf3254InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3254LocalValidity :
    LeafFacts leaf3254Box leaf3254Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3254Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431645184) }) = true
      norm_num [leaf3254Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3254CertificateValid :
    WideCertificateValid leaf3254Box leaf3254Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi191ValidityFacts
    leaf3254LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3254CoverageChecked :
    coverageCheck (innerAD leaf3254Box) leaf3254InnerLog = true := by
  rfl'

private theorem leaf3254InnerLogValid :
    leaf3254InnerLog.Valid 8 (innerAD leaf3254Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3254CoverageChecked

private noncomputable def leaf3254InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629403/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3254InputLogOnePlusV_eq :
    leaf3254InputLogOnePlusV = outerEnclosure 24
      (leaf3254Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3254RoundedFacts : LeafRoundedFacts 8
    leaf3254Certificate.logOnePlusV leaf3254InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3254InputLogOnePlusV_eq }

private noncomputable def leaf3254Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi191InputQChi innerPair91Input
    leaf3254InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3254LowerChecked :
    lowerCheck 24 leaf3254Box leaf3254Inputs = true := by
  rfl'

private theorem leaf3254CoversExact : CoversExact 8
    leaf3254Box leaf3254Certificate leaf3254InnerLog leaf3254Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi191RoundedFacts
    innerPair91RoundedFacts leaf3254RoundedFacts (by rfl)

private theorem leaf3254FlatSound : Sound leaf3254Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3254CertificateValid
    leaf3254InnerLogValid leaf3254CoversExact leaf3254LowerChecked

private noncomputable def leaf3255Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3255Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742413/1073741824) }, vSqrt := { lower := (8191/8192), upper := (9162461457/9162103808) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2001117333/1073741824) }, upper := { exponent := 0, mantissa := (15415/8192) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (18324565265/18324207616) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf3255InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3255LocalValidity :
    LeafFacts leaf3255Box leaf3255Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3255Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (9162461457/9162103808) }) = true
      norm_num [leaf3255Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3255CertificateValid :
    WideCertificateValid leaf3255Box leaf3255Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi192ValidityFacts
    leaf3255LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3255CoverageChecked :
    coverageCheck (innerAD leaf3255Box) leaf3255InnerLog = true := by
  rfl'

private theorem leaf3255InnerLogValid :
    leaf3255InnerLog.Valid 8 (innerAD leaf3255Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3255CoverageChecked

private noncomputable def leaf3255InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (363419/524288) }

set_option maxRecDepth 1000000 in
private theorem leaf3255InputLogOnePlusV_eq :
    leaf3255InputLogOnePlusV = outerEnclosure 24
      (leaf3255Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3255RoundedFacts : LeafRoundedFacts 8
    leaf3255Certificate.logOnePlusV leaf3255InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3255InputLogOnePlusV_eq }

private noncomputable def leaf3255Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi192InputQChi innerPair482Input
    leaf3255InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3255LowerChecked :
    lowerCheck 24 leaf3255Box leaf3255Inputs = true := by
  rfl'

private theorem leaf3255CoversExact : CoversExact 8
    leaf3255Box leaf3255Certificate leaf3255InnerLog leaf3255Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi192RoundedFacts
    innerPair482RoundedFacts leaf3255RoundedFacts (by rfl)

private theorem leaf3255FlatSound : Sound leaf3255Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3255CertificateValid
    leaf3255InnerLogValid leaf3255CoversExact leaf3255LowerChecked

private noncomputable def leaf3256Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3256Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431525376) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2005114783/1073741824) }, upper := { exponent := 0, mantissa := (7723/4096) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868447231/274863050752) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf3256InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3256LocalValidity :
    LeafFacts leaf3256Box leaf3256Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3256Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431525376) }) = true
      norm_num [leaf3256Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3256CertificateValid :
    WideCertificateValid leaf3256Box leaf3256Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi192ValidityFacts
    leaf3256LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3256CoverageChecked :
    coverageCheck (innerAD leaf3256Box) leaf3256InnerLog = true := by
  rfl'

private theorem leaf3256InnerLogValid :
    leaf3256InnerLog.Valid 8 (innerAD leaf3256Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3256CoverageChecked

private noncomputable def leaf3256InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814705/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3256InputLogOnePlusV_eq :
    leaf3256InputLogOnePlusV = outerEnclosure 24
      (leaf3256Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3256RoundedFacts : LeafRoundedFacts 8
    leaf3256Certificate.logOnePlusV leaf3256InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3256InputLogOnePlusV_eq }

private noncomputable def leaf3256Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi192InputQChi innerPair482Input
    leaf3256InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3256LowerChecked :
    lowerCheck 24 leaf3256Box leaf3256Inputs = true := by
  rfl'

private theorem leaf3256CoversExact : CoversExact 8
    leaf3256Box leaf3256Certificate leaf3256InnerLog leaf3256Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi192RoundedFacts
    innerPair482RoundedFacts leaf3256RoundedFacts (by rfl)

private theorem leaf3256FlatSound : Sound leaf3256Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3256CertificateValid
    leaf3256InnerLogValid leaf3256CoversExact leaf3256LowerChecked

private noncomputable def leaf3257Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3257Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090059776) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1993777747/1073741824) }, upper := { exponent := 0, mantissa := (30719/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180316141/10180119552) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf3257InnerLog : WideLogData :=
  innerPair91Data

set_option maxRecDepth 1000000 in
private theorem leaf3257LocalValidity :
    LeafFacts leaf3257Box leaf3257Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3257Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090059776) }) = true
      norm_num [leaf3257Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3257CertificateValid :
    WideCertificateValid leaf3257Box leaf3257Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi191ValidityFacts
    leaf3257LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3257CoverageChecked :
    coverageCheck (innerAD leaf3257Box) leaf3257InnerLog = true := by
  rfl'

private theorem leaf3257InnerLogValid :
    leaf3257InnerLog.Valid 8 (innerAD leaf3257Box) :=
  wideLogDataValid_of_cachedCheck endpoint21PositiveFacts
    endpoint22PositiveFacts.valid leaf3257CoverageChecked

private noncomputable def leaf3257InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629405/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3257InputLogOnePlusV_eq :
    leaf3257InputLogOnePlusV = outerEnclosure 24
      (leaf3257Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3257RoundedFacts : LeafRoundedFacts 8
    leaf3257Certificate.logOnePlusV leaf3257InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3257InputLogOnePlusV_eq }

private noncomputable def leaf3257Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi191InputQChi innerPair91Input
    leaf3257InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3257LowerChecked :
    lowerCheck 24 leaf3257Box leaf3257Inputs = true := by
  rfl'

private theorem leaf3257CoversExact : CoversExact 8
    leaf3257Box leaf3257Certificate leaf3257InnerLog leaf3257Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi191RoundedFacts
    innerPair91RoundedFacts leaf3257RoundedFacts (by rfl)

private theorem leaf3257FlatSound : Sound leaf3257Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3257CertificateValid
    leaf3257InnerLogValid leaf3257CoversExact leaf3257LowerChecked

private noncomputable def leaf3258Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3258Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486316544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (1997709665/1073741824) }, upper := { exponent := 0, mantissa := (7695/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973700915/54972633088) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf3258InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3258LocalValidity :
    LeafFacts leaf3258Box leaf3258Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3258Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486316544) }) = true
      norm_num [leaf3258Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3258CertificateValid :
    WideCertificateValid leaf3258Box leaf3258Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi191ValidityFacts
    leaf3258LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3258CoverageChecked :
    coverageCheck (innerAD leaf3258Box) leaf3258InnerLog = true := by
  rfl'

private theorem leaf3258InnerLogValid :
    leaf3258InnerLog.Valid 8 (innerAD leaf3258Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3258CoverageChecked

private noncomputable def leaf3258InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629407/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3258InputLogOnePlusV_eq :
    leaf3258InputLogOnePlusV = outerEnclosure 24
      (leaf3258Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3258RoundedFacts : LeafRoundedFacts 8
    leaf3258Certificate.logOnePlusV leaf3258InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3258InputLogOnePlusV_eq }

private noncomputable def leaf3258Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi191InputQChi innerPair482Input
    leaf3258InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3258LowerChecked :
    lowerCheck 24 leaf3258Box leaf3258Inputs = true := by
  rfl'

private theorem leaf3258CoversExact : CoversExact 8
    leaf3258Box leaf3258Certificate leaf3258InnerLog leaf3258Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi191RoundedFacts
    innerPair482RoundedFacts leaf3258RoundedFacts (by rfl)

private theorem leaf3258FlatSound : Sound leaf3258Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3258CertificateValid
    leaf3258InnerLogValid leaf3258CoversExact leaf3258LowerChecked

private noncomputable def leaf3259Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3259Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431493632) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2009112233/1073741824) }, upper := { exponent := 0, mantissa := (15477/8192) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868415487/274862987264) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf3259InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3259LocalValidity :
    LeafFacts leaf3259Box leaf3259Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3259Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431493632) }) = true
      norm_num [leaf3259Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3259CertificateValid :
    WideCertificateValid leaf3259Box leaf3259Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi192ValidityFacts
    leaf3259LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3259CoverageChecked :
    coverageCheck (innerAD leaf3259Box) leaf3259InnerLog = true := by
  rfl'

private theorem leaf3259InnerLogValid :
    leaf3259InnerLog.Valid 8 (innerAD leaf3259Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3259CoverageChecked

private noncomputable def leaf3259InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3259InputLogOnePlusV_eq :
    leaf3259InputLogOnePlusV = outerEnclosure 24
      (leaf3259Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3259RoundedFacts : LeafRoundedFacts 8
    leaf3259Certificate.logOnePlusV leaf3259InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3259InputLogOnePlusV_eq }

private noncomputable def leaf3259Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi192InputQChi innerPair482Input
    leaf3259InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3259LowerChecked :
    lowerCheck 24 leaf3259Box leaf3259Inputs = true := by
  rfl'

private theorem leaf3259CoversExact : CoversExact 8
    leaf3259Box leaf3259Certificate leaf3259InnerLog leaf3259Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi192RoundedFacts
    innerPair482RoundedFacts leaf3259RoundedFacts (by rfl)

private theorem leaf3259FlatSound : Sound leaf3259Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3259CertificateValid
    leaf3259InnerLogValid leaf3259CoversExact leaf3259LowerChecked

private noncomputable def leaf3260Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3260Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (5090256365/5090054144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2013109683/1073741824) }, upper := { exponent := 0, mantissa := (3877/2048) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (10180310509/10180108288) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf3260InnerLog : WideLogData :=
  innerPair483Data

set_option maxRecDepth 1000000 in
private theorem leaf3260LocalValidity :
    LeafFacts leaf3260Box leaf3260Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3260Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (5090256365/5090054144) }) = true
      norm_num [leaf3260Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3260CertificateValid :
    WideCertificateValid leaf3260Box leaf3260Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi192ValidityFacts
    leaf3260LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3260CoverageChecked :
    coverageCheck (innerAD leaf3260Box) leaf3260InnerLog = true := by
  rfl'

private theorem leaf3260InnerLogValid :
    leaf3260InnerLog.Valid 8 (innerAD leaf3260Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint70PositiveFacts.valid leaf3260CoverageChecked

private noncomputable def leaf3260InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3260InputLogOnePlusV_eq :
    leaf3260InputLogOnePlusV = outerEnclosure 24
      (leaf3260Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3260RoundedFacts : LeafRoundedFacts 8
    leaf3260Certificate.logOnePlusV leaf3260InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3260InputLogOnePlusV_eq }

private noncomputable def leaf3260Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi192InputQChi innerPair483Input
    leaf3260InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3260LowerChecked :
    lowerCheck 24 leaf3260Box leaf3260Inputs = true := by
  rfl'

private theorem leaf3260CoversExact : CoversExact 8
    leaf3260Box leaf3260Certificate leaf3260InnerLog leaf3260Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi192RoundedFacts
    innerPair483RoundedFacts leaf3260RoundedFacts (by rfl)

private theorem leaf3260FlatSound : Sound leaf3260Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3260CertificateValid
    leaf3260InnerLogValid leaf3260CoversExact leaf3260LowerChecked

private noncomputable def leaf3261Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3261Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742415/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431437824) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2016320755/1073741824) }, upper := { exponent := 0, mantissa := (31063/16384) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868359679/274862875648) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf3261InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3261LocalValidity :
    LeafFacts leaf3261Box leaf3261Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3261Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431437824) }) = true
      norm_num [leaf3261Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3261CertificateValid :
    WideCertificateValid leaf3261Box leaf3261Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi189ValidityFacts
    leaf3261LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3261CoverageChecked :
    coverageCheck (innerAD leaf3261Box) leaf3261InnerLog = true := by
  rfl'

private theorem leaf3261InnerLogValid :
    leaf3261InnerLog.Valid 8 (innerAD leaf3261Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3261CoverageChecked

private noncomputable def leaf3261InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629415/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3261InputLogOnePlusV_eq :
    leaf3261InputLogOnePlusV = outerEnclosure 24
      (leaf3261Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3261RoundedFacts : LeafRoundedFacts 8
    leaf3261Certificate.logOnePlusV leaf3261InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3261InputLogOnePlusV_eq }

private noncomputable def leaf3261Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi189InputQChi innerPair100Input
    leaf3261InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3261LowerChecked :
    lowerCheck 24 leaf3261Box leaf3261Inputs = true := by
  rfl'

private theorem leaf3261CoversExact : CoversExact 8
    leaf3261Box leaf3261Certificate leaf3261InnerLog leaf3261Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi189RoundedFacts
    innerPair100RoundedFacts leaf3261RoundedFacts (by rfl)

private theorem leaf3261FlatSound : Sound leaf3261Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3261CertificateValid
    leaf3261InnerLogValid leaf3261CoversExact leaf3261LowerChecked

private noncomputable def leaf3262Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3262Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431405568) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2020383737/1073741824) }, upper := { exponent := 0, mantissa := (15563/8192) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868327423/274862811136) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf3262InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3262LocalValidity :
    LeafFacts leaf3262Box leaf3262Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3262Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431405568) }) = true
      norm_num [leaf3262Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3262CertificateValid :
    WideCertificateValid leaf3262Box leaf3262Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi189ValidityFacts
    leaf3262LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3262CoverageChecked :
    coverageCheck (innerAD leaf3262Box) leaf3262InnerLog = true := by
  rfl'

private theorem leaf3262InnerLogValid :
    leaf3262InnerLog.Valid 8 (innerAD leaf3262Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3262CoverageChecked

private noncomputable def leaf3262InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629417/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3262InputLogOnePlusV_eq :
    leaf3262InputLogOnePlusV = outerEnclosure 24
      (leaf3262Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3262RoundedFacts : LeafRoundedFacts 8
    leaf3262Certificate.logOnePlusV leaf3262InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3262InputLogOnePlusV_eq }

private noncomputable def leaf3262Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi189InputQChi innerPair100Input
    leaf3262InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3262LowerChecked :
    lowerCheck 24 leaf3262Box leaf3262Inputs = true := by
  rfl'

private theorem leaf3262CoversExact : CoversExact 8
    leaf3262Box leaf3262Certificate leaf3262InnerLog leaf3262Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi189RoundedFacts
    innerPair100RoundedFacts leaf3262RoundedFacts (by rfl)

private theorem leaf3262FlatSound : Sound leaf3262Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3262CertificateValid
    leaf3262InnerLogValid leaf3262CoversExact leaf3262LowerChecked

private noncomputable def leaf3263Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (233/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3263Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742417/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431318528) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2031524177/1073741824) }, upper := { exponent := 0, mantissa := (489/256) } }, logOuter := sk217LogOuterCertificate, logK := sk217LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868240383/274862637056) } }, logDArg := sk217LogDArgCertificate }

private noncomputable def leaf3263InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3263LocalValidity :
    LeafFacts leaf3263Box leaf3263Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3263Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431318528) }) = true
      norm_num [leaf3263Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3263CertificateValid :
    WideCertificateValid leaf3263Box leaf3263Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk217ValidityFacts chi190ValidityFacts
    leaf3263LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3263CoverageChecked :
    coverageCheck (innerAD leaf3263Box) leaf3263InnerLog = true := by
  rfl'

private theorem leaf3263InnerLogValid :
    leaf3263InnerLog.Valid 8 (innerAD leaf3263Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3263CoverageChecked

private noncomputable def leaf3263InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629423/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3263InputLogOnePlusV_eq :
    leaf3263InputLogOnePlusV = outerEnclosure 24
      (leaf3263Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3263RoundedFacts : LeafRoundedFacts 8
    leaf3263Certificate.logOnePlusV leaf3263InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3263InputLogOnePlusV_eq }

private noncomputable def leaf3263Inputs : Inputs :=
  inputsOfCaches globalInput sk217RoundedInputs
    chi190InputQChi innerPair100Input
    leaf3263InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3263LowerChecked :
    lowerCheck 24 leaf3263Box leaf3263Inputs = true := by
  rfl'

private theorem leaf3263CoversExact : CoversExact 8
    leaf3263Box leaf3263Certificate leaf3263InnerLog leaf3263Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk217RoundedFacts chi190RoundedFacts
    innerPair100RoundedFacts leaf3263RoundedFacts (by rfl)

private theorem leaf3263FlatSound : Sound leaf3263Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3263CertificateValid
    leaf3263InnerLogValid leaf3263CoversExact leaf3263LowerChecked

private noncomputable def leaf3264Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (233/64), kHi := (117/32), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3264Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (1616904963/1616838656) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2035652691/1073741824) }, upper := { exponent := 0, mantissa := (245/128) } }, logOuter := sk218LogOuterCertificate, logK := sk218LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (3233743619/3233677312) } }, logDArg := sk218LogDArgCertificate }

private noncomputable def leaf3264InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3264LocalValidity :
    LeafFacts leaf3264Box leaf3264Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3264Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (1616904963/1616838656) }) = true
      norm_num [leaf3264Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3264CertificateValid :
    WideCertificateValid leaf3264Box leaf3264Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk218ValidityFacts chi190ValidityFacts
    leaf3264LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3264CoverageChecked :
    coverageCheck (innerAD leaf3264Box) leaf3264InnerLog = true := by
  rfl'

private theorem leaf3264InnerLogValid :
    leaf3264InnerLog.Valid 8 (innerAD leaf3264Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3264CoverageChecked

private noncomputable def leaf3264InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629425/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3264InputLogOnePlusV_eq :
    leaf3264InputLogOnePlusV = outerEnclosure 24
      (leaf3264Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3264RoundedFacts : LeafRoundedFacts 8
    leaf3264Certificate.logOnePlusV leaf3264InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3264InputLogOnePlusV_eq }

private noncomputable def leaf3264Inputs : Inputs :=
  inputsOfCaches globalInput sk218RoundedInputs
    chi190InputQChi innerPair100Input
    leaf3264InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3264LowerChecked :
    lowerCheck 24 leaf3264Box leaf3264Inputs = true := by
  rfl'

private theorem leaf3264CoversExact : CoversExact 8
    leaf3264Box leaf3264Certificate leaf3264InnerLog leaf3264Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk218RoundedFacts chi190RoundedFacts
    innerPair100RoundedFacts leaf3264RoundedFacts (by rfl)

private theorem leaf3264FlatSound : Sound leaf3264Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3264CertificateValid
    leaf3264InnerLogValid leaf3264CoversExact leaf3264LowerChecked

private noncomputable def leaf3265Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3265Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431373312) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2024446719/1073741824) }, upper := { exponent := 0, mantissa := (31189/16384) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868295167/274862746624) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf3265InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3265LocalValidity :
    LeafFacts leaf3265Box leaf3265Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3265Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431373312) }) = true
      norm_num [leaf3265Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3265CertificateValid :
    WideCertificateValid leaf3265Box leaf3265Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi189ValidityFacts
    leaf3265LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3265CoverageChecked :
    coverageCheck (innerAD leaf3265Box) leaf3265InnerLog = true := by
  rfl'

private theorem leaf3265InnerLogValid :
    leaf3265InnerLog.Valid 8 (innerAD leaf3265Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3265CoverageChecked

private noncomputable def leaf3265InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629419/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3265InputLogOnePlusV_eq :
    leaf3265InputLogOnePlusV = outerEnclosure 24
      (leaf3265Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3265RoundedFacts : LeafRoundedFacts 8
    leaf3265Certificate.logOnePlusV leaf3265InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3265InputLogOnePlusV_eq }

private noncomputable def leaf3265Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi189InputQChi innerPair100Input
    leaf3265InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3265LowerChecked :
    lowerCheck 24 leaf3265Box leaf3265Inputs = true := by
  rfl'

private theorem leaf3265CoversExact : CoversExact 8
    leaf3265Box leaf3265Certificate leaf3265InnerLog leaf3265Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi189RoundedFacts
    innerPair100RoundedFacts leaf3265RoundedFacts (by rfl)

private theorem leaf3265FlatSound : Sound leaf3265Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3265CertificateValid
    leaf3265InnerLogValid leaf3265CoversExact leaf3265LowerChecked

private noncomputable def leaf3266Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3266Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431341056) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2028509701/1073741824) }, upper := { exponent := 0, mantissa := (7813/4096) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868262911/274862682112) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf3266InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3266LocalValidity :
    LeafFacts leaf3266Box leaf3266Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3266Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431341056) }) = true
      norm_num [leaf3266Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3266CertificateValid :
    WideCertificateValid leaf3266Box leaf3266Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi189ValidityFacts
    leaf3266LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3266CoverageChecked :
    coverageCheck (innerAD leaf3266Box) leaf3266InnerLog = true := by
  rfl'

private theorem leaf3266InnerLogValid :
    leaf3266InnerLog.Valid 8 (innerAD leaf3266Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3266CoverageChecked

private noncomputable def leaf3266InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629421/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3266InputLogOnePlusV_eq :
    leaf3266InputLogOnePlusV = outerEnclosure 24
      (leaf3266Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3266RoundedFacts : LeafRoundedFacts 8
    leaf3266Certificate.logOnePlusV leaf3266InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3266InputLogOnePlusV_eq }

private noncomputable def leaf3266Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi189InputQChi innerPair100Input
    leaf3266InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3266LowerChecked :
    lowerCheck 24 leaf3266Box leaf3266Inputs = true := by
  rfl'

private theorem leaf3266CoversExact : CoversExact 8
    leaf3266Box leaf3266Certificate leaf3266InnerLog leaf3266Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi189RoundedFacts
    innerPair100RoundedFacts leaf3266RoundedFacts (by rfl)

private theorem leaf3266FlatSound : Sound leaf3266Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3266CertificateValid
    leaf3266InnerLogValid leaf3266CoversExact leaf3266LowerChecked

private noncomputable def leaf3267Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (235/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3267Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810417664) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2039781205/1073741824) }, upper := { exponent := 0, mantissa := (491/256) } }, logOuter := sk219LogOuterCertificate, logK := sk219LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622724949/91620835328) } }, logDArg := sk219LogDArgCertificate }

private noncomputable def leaf3267InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3267LocalValidity :
    LeafFacts leaf3267Box leaf3267Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3267Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810417664) }) = true
      norm_num [leaf3267Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3267CertificateValid :
    WideCertificateValid leaf3267Box leaf3267Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk219ValidityFacts chi190ValidityFacts
    leaf3267LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3267CoverageChecked :
    coverageCheck (innerAD leaf3267Box) leaf3267InnerLog = true := by
  rfl'

private theorem leaf3267InnerLogValid :
    leaf3267InnerLog.Valid 8 (innerAD leaf3267Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3267CoverageChecked

private noncomputable def leaf3267InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3267InputLogOnePlusV_eq :
    leaf3267InputLogOnePlusV = outerEnclosure 24
      (leaf3267Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3267RoundedFacts : LeafRoundedFacts 8
    leaf3267Certificate.logOnePlusV leaf3267InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3267InputLogOnePlusV_eq }

private noncomputable def leaf3267Inputs : Inputs :=
  inputsOfCaches globalInput sk219RoundedInputs
    chi190InputQChi innerPair100Input
    leaf3267InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3267LowerChecked :
    lowerCheck 24 leaf3267Box leaf3267Inputs = true := by
  rfl'

private theorem leaf3267CoversExact : CoversExact 8
    leaf3267Box leaf3267Certificate leaf3267InnerLog leaf3267Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk219RoundedFacts chi190RoundedFacts
    innerPair100RoundedFacts leaf3267RoundedFacts (by rfl)

private theorem leaf3267FlatSound : Sound leaf3267Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3267CertificateValid
    leaf3267InnerLogValid leaf3267CoversExact leaf3267LowerChecked

private noncomputable def leaf3268Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (235/64), kHi := (59/16), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3268Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431220224) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2043909719/1073741824) }, upper := { exponent := 0, mantissa := (123/64) } }, logOuter := sk220LogOuterCertificate, logK := sk220LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868142079/274862440448) } }, logDArg := sk220LogDArgCertificate }

private noncomputable def leaf3268InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3268LocalValidity :
    LeafFacts leaf3268Box leaf3268Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3268Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431220224) }) = true
      norm_num [leaf3268Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3268CertificateValid :
    WideCertificateValid leaf3268Box leaf3268Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk220ValidityFacts chi190ValidityFacts
    leaf3268LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3268CoverageChecked :
    coverageCheck (innerAD leaf3268Box) leaf3268InnerLog = true := by
  rfl'

private theorem leaf3268InnerLogValid :
    leaf3268InnerLog.Valid 8 (innerAD leaf3268Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3268CoverageChecked

private noncomputable def leaf3268InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3268InputLogOnePlusV_eq :
    leaf3268InputLogOnePlusV = outerEnclosure 24
      (leaf3268Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3268RoundedFacts : LeafRoundedFacts 8
    leaf3268Certificate.logOnePlusV leaf3268InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3268InputLogOnePlusV_eq }

private noncomputable def leaf3268Inputs : Inputs :=
  inputsOfCaches globalInput sk220RoundedInputs
    chi190InputQChi innerPair100Input
    leaf3268InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3268LowerChecked :
    lowerCheck 24 leaf3268Box leaf3268Inputs = true := by
  rfl'

private theorem leaf3268CoversExact : CoversExact 8
    leaf3268Box leaf3268Certificate leaf3268InnerLog leaf3268Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk220RoundedFacts chi190RoundedFacts
    innerPair100RoundedFacts leaf3268RoundedFacts (by rfl)

private theorem leaf3268FlatSound : Sound leaf3268Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3268CertificateValid
    leaf3268InnerLogValid leaf3268CoversExact leaf3268LowerChecked

private noncomputable def leaf3269Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3269Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742419/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431551488) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2001641583/1073741824) }, upper := { exponent := 0, mantissa := (30841/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868473343/274863102976) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf3269InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3269LocalValidity :
    LeafFacts leaf3269Box leaf3269Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3269Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431551488) }) = true
      norm_num [leaf3269Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3269CertificateValid :
    WideCertificateValid leaf3269Box leaf3269Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi191ValidityFacts
    leaf3269LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3269CoverageChecked :
    coverageCheck (innerAD leaf3269Box) leaf3269InnerLog = true := by
  rfl'

private theorem leaf3269InnerLogValid :
    leaf3269InnerLog.Valid 8 (innerAD leaf3269Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3269CoverageChecked

private noncomputable def leaf3269InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629409/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3269InputLogOnePlusV_eq :
    leaf3269InputLogOnePlusV = outerEnclosure 24
      (leaf3269Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3269RoundedFacts : LeafRoundedFacts 8
    leaf3269Certificate.logOnePlusV leaf3269InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3269InputLogOnePlusV_eq }

private noncomputable def leaf3269Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi191InputQChi innerPair482Input
    leaf3269InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3269LowerChecked :
    lowerCheck 24 leaf3269Box leaf3269Inputs = true := by
  rfl'

private theorem leaf3269CoversExact : CoversExact 8
    leaf3269Box leaf3269Certificate leaf3269InnerLog leaf3269Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi191RoundedFacts
    innerPair482RoundedFacts leaf3269RoundedFacts (by rfl)

private theorem leaf3269FlatSound : Sound leaf3269Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3269CertificateValid
    leaf3269InnerLogValid leaf3269CoversExact leaf3269LowerChecked

private noncomputable def leaf3270Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3270Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810506752) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2005573501/1073741824) }, upper := { exponent := 0, mantissa := (15451/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622814037/91621013504) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf3270InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3270LocalValidity :
    LeafFacts leaf3270Box leaf3270Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3270Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810506752) }) = true
      norm_num [leaf3270Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3270CertificateValid :
    WideCertificateValid leaf3270Box leaf3270Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi191ValidityFacts
    leaf3270LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3270CoverageChecked :
    coverageCheck (innerAD leaf3270Box) leaf3270InnerLog = true := by
  rfl'

private theorem leaf3270InnerLogValid :
    leaf3270InnerLog.Valid 8 (innerAD leaf3270Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3270CoverageChecked

private noncomputable def leaf3270InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814705/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3270InputLogOnePlusV_eq :
    leaf3270InputLogOnePlusV = outerEnclosure 24
      (leaf3270Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3270RoundedFacts : LeafRoundedFacts 8
    leaf3270Certificate.logOnePlusV leaf3270InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3270InputLogOnePlusV_eq }

private noncomputable def leaf3270Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi191InputQChi innerPair482Input
    leaf3270InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3270LowerChecked :
    lowerCheck 24 leaf3270Box leaf3270Inputs = true := by
  rfl'

private theorem leaf3270CoversExact : CoversExact 8
    leaf3270Box leaf3270Certificate leaf3270InnerLog leaf3270Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi191RoundedFacts
    innerPair482RoundedFacts leaf3270RoundedFacts (by rfl)

private theorem leaf3270FlatSound : Sound leaf3270Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3270CertificateValid
    leaf3270InnerLogValid leaf3270CoversExact leaf3270LowerChecked

private noncomputable def leaf3271Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3271Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742421/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431430144) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2017107133/1073741824) }, upper := { exponent := 0, mantissa := (15539/8192) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868351999/274862860288) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf3271InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf3271LocalValidity :
    LeafFacts leaf3271Box leaf3271Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3271Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431430144) }) = true
      norm_num [leaf3271Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3271CertificateValid :
    WideCertificateValid leaf3271Box leaf3271Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi192ValidityFacts
    leaf3271LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3271CoverageChecked :
    coverageCheck (innerAD leaf3271Box) leaf3271InnerLog = true := by
  rfl'

private theorem leaf3271InnerLogValid :
    leaf3271InnerLog.Valid 8 (innerAD leaf3271Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf3271CoverageChecked

private noncomputable def leaf3271InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (1453677/2097152) }

set_option maxRecDepth 1000000 in
private theorem leaf3271InputLogOnePlusV_eq :
    leaf3271InputLogOnePlusV = outerEnclosure 24
      (leaf3271Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3271RoundedFacts : LeafRoundedFacts 8
    leaf3271Certificate.logOnePlusV leaf3271InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3271InputLogOnePlusV_eq }

private noncomputable def leaf3271Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi192InputQChi innerPair103Input
    leaf3271InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3271LowerChecked :
    lowerCheck 24 leaf3271Box leaf3271Inputs = true := by
  rfl'

private theorem leaf3271CoversExact : CoversExact 8
    leaf3271Box leaf3271Certificate leaf3271InnerLog leaf3271Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi192RoundedFacts
    innerPair103RoundedFacts leaf3271RoundedFacts (by rfl)

private theorem leaf3271FlatSound : Sound leaf3271Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3271CertificateValid
    leaf3271InnerLogValid leaf3271CoversExact leaf3271LowerChecked

private noncomputable def leaf3272Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3272Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486279680) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2021104583/1073741824) }, upper := { exponent := 0, mantissa := (7785/4096) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973664051/54972559360) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf3272InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf3272LocalValidity :
    LeafFacts leaf3272Box leaf3272Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3272Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486279680) }) = true
      norm_num [leaf3272Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3272CertificateValid :
    WideCertificateValid leaf3272Box leaf3272Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi192ValidityFacts
    leaf3272LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3272CoverageChecked :
    coverageCheck (innerAD leaf3272Box) leaf3272InnerLog = true := by
  rfl'

private theorem leaf3272InnerLogValid :
    leaf3272InnerLog.Valid 8 (innerAD leaf3272Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf3272CoverageChecked

private noncomputable def leaf3272InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814709/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3272InputLogOnePlusV_eq :
    leaf3272InputLogOnePlusV = outerEnclosure 24
      (leaf3272Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3272RoundedFacts : LeafRoundedFacts 8
    leaf3272Certificate.logOnePlusV leaf3272InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3272InputLogOnePlusV_eq }

private noncomputable def leaf3272Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi192InputQChi innerPair103Input
    leaf3272InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3272LowerChecked :
    lowerCheck 24 leaf3272Box leaf3272Inputs = true := by
  rfl'

private theorem leaf3272CoversExact : CoversExact 8
    leaf3272Box leaf3272Certificate leaf3272InnerLog leaf3272Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi192RoundedFacts
    innerPair103RoundedFacts leaf3272RoundedFacts (by rfl)

private theorem leaf3272FlatSound : Sound leaf3272Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3272CertificateValid
    leaf3272InnerLogValid leaf3272CoversExact leaf3272LowerChecked

private noncomputable def leaf3273Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3273Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431489024) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2009505419/1073741824) }, upper := { exponent := 0, mantissa := (30963/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868410879/274862978048) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf3273InnerLog : WideLogData :=
  innerPair482Data

set_option maxRecDepth 1000000 in
private theorem leaf3273LocalValidity :
    LeafFacts leaf3273Box leaf3273Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3273Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431489024) }) = true
      norm_num [leaf3273Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3273CertificateValid :
    WideCertificateValid leaf3273Box leaf3273Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi191ValidityFacts
    leaf3273LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3273CoverageChecked :
    coverageCheck (innerAD leaf3273Box) leaf3273InnerLog = true := by
  rfl'

private theorem leaf3273InnerLogValid :
    leaf3273InnerLog.Valid 8 (innerAD leaf3273Box) :=
  wideLogDataValid_of_cachedCheck endpoint211PositiveFacts
    endpoint69PositiveFacts.valid leaf3273CoverageChecked

private noncomputable def leaf3273InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907353/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3273InputLogOnePlusV_eq :
    leaf3273InputLogOnePlusV = outerEnclosure 24
      (leaf3273Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3273RoundedFacts : LeafRoundedFacts 8
    leaf3273Certificate.logOnePlusV leaf3273InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3273InputLogOnePlusV_eq }

private noncomputable def leaf3273Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi191InputQChi innerPair482Input
    leaf3273InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3273LowerChecked :
    lowerCheck 24 leaf3273Box leaf3273Inputs = true := by
  rfl'

private theorem leaf3273CoversExact : CoversExact 8
    leaf3273Box leaf3273Certificate leaf3273InnerLog leaf3273Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi191RoundedFacts
    innerPair482RoundedFacts leaf3273RoundedFacts (by rfl)

private theorem leaf3273FlatSound : Sound leaf3273Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3273CertificateValid
    leaf3273InnerLogValid leaf3273CoversExact leaf3273LowerChecked

private noncomputable def leaf3274Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (15/64), chiHi := (61/256) }

private noncomputable def leaf3274Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431457792) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2013437337/1073741824) }, upper := { exponent := 0, mantissa := (1939/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi191LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868379647/274862915584) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf3274InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf3274LocalValidity :
    LeafFacts leaf3274Box leaf3274Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3274Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431457792) }) = true
      norm_num [leaf3274Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3274CertificateValid :
    WideCertificateValid leaf3274Box leaf3274Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi191ValidityFacts
    leaf3274LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3274CoverageChecked :
    coverageCheck (innerAD leaf3274Box) leaf3274InnerLog = true := by
  rfl'

private theorem leaf3274InnerLogValid :
    leaf3274InnerLog.Valid 8 (innerAD leaf3274Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf3274CoverageChecked

private noncomputable def leaf3274InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814707/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3274InputLogOnePlusV_eq :
    leaf3274InputLogOnePlusV = outerEnclosure 24
      (leaf3274Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3274RoundedFacts : LeafRoundedFacts 8
    leaf3274Certificate.logOnePlusV leaf3274InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3274InputLogOnePlusV_eq }

private noncomputable def leaf3274Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi191InputQChi innerPair103Input
    leaf3274InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3274LowerChecked :
    lowerCheck 24 leaf3274Box leaf3274Inputs = true := by
  rfl'

private theorem leaf3274CoversExact : CoversExact 8
    leaf3274Box leaf3274Certificate leaf3274InnerLog leaf3274Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi191RoundedFacts
    innerPair103RoundedFacts leaf3274RoundedFacts (by rfl)

private theorem leaf3274FlatSound : Sound leaf3274Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3274CertificateValid
    leaf3274InnerLogValid leaf3274CoversExact leaf3274LowerChecked

private noncomputable def leaf3275Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3275Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810455552) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2025102033/1073741824) }, upper := { exponent := 0, mantissa := (15601/8192) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622762837/91620911104) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf3275InnerLog : WideLogData :=
  innerPair103Data

set_option maxRecDepth 1000000 in
private theorem leaf3275LocalValidity :
    LeafFacts leaf3275Box leaf3275Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3275Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810455552) }) = true
      norm_num [leaf3275Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3275CertificateValid :
    WideCertificateValid leaf3275Box leaf3275Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi192ValidityFacts
    leaf3275LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3275CoverageChecked :
    coverageCheck (innerAD leaf3275Box) leaf3275InnerLog = true := by
  rfl'

private theorem leaf3275InnerLogValid :
    leaf3275InnerLog.Valid 8 (innerAD leaf3275Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint70PositiveFacts.valid leaf3275CoverageChecked

private noncomputable def leaf3275InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (2907355/4194304) }

set_option maxRecDepth 1000000 in
private theorem leaf3275InputLogOnePlusV_eq :
    leaf3275InputLogOnePlusV = outerEnclosure 24
      (leaf3275Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3275RoundedFacts : LeafRoundedFacts 8
    leaf3275Certificate.logOnePlusV leaf3275InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3275InputLogOnePlusV_eq }

private noncomputable def leaf3275Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi192InputQChi innerPair103Input
    leaf3275InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3275LowerChecked :
    lowerCheck 24 leaf3275Box leaf3275Inputs = true := by
  rfl'

private theorem leaf3275CoversExact : CoversExact 8
    leaf3275Box leaf3275Certificate leaf3275InnerLog leaf3275Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi192RoundedFacts
    innerPair103RoundedFacts leaf3275RoundedFacts (by rfl)

private theorem leaf3275FlatSound : Sound leaf3275Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3275CertificateValid
    leaf3275InnerLogValid leaf3275CoversExact leaf3275LowerChecked

private noncomputable def leaf3276Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (61/256), chiHi := (31/128) }

private noncomputable def leaf3276Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431334912) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2029099483/1073741824) }, upper := { exponent := 0, mantissa := (977/512) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi192LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868256767/274862669824) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf3276InnerLog : WideLogData :=
  innerPair106Data

set_option maxRecDepth 1000000 in
private theorem leaf3276LocalValidity :
    LeafFacts leaf3276Box leaf3276Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3276Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431334912) }) = true
      norm_num [leaf3276Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3276CertificateValid :
    WideCertificateValid leaf3276Box leaf3276Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi192ValidityFacts
    leaf3276LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3276CoverageChecked :
    coverageCheck (innerAD leaf3276Box) leaf3276InnerLog = true := by
  rfl'

private theorem leaf3276InnerLogValid :
    leaf3276InnerLog.Valid 8 (innerAD leaf3276Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint81PositiveFacts.valid leaf3276CoverageChecked

private noncomputable def leaf3276InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (5814711/8388608) }

set_option maxRecDepth 1000000 in
private theorem leaf3276InputLogOnePlusV_eq :
    leaf3276InputLogOnePlusV = outerEnclosure 24
      (leaf3276Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3276RoundedFacts : LeafRoundedFacts 8
    leaf3276Certificate.logOnePlusV leaf3276InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3276InputLogOnePlusV_eq }

private noncomputable def leaf3276Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi192InputQChi innerPair106Input
    leaf3276InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3276LowerChecked :
    lowerCheck 24 leaf3276Box leaf3276Inputs = true := by
  rfl'

private theorem leaf3276CoversExact : CoversExact 8
    leaf3276Box leaf3276Certificate leaf3276InnerLog leaf3276Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi192RoundedFacts
    innerPair106RoundedFacts leaf3276RoundedFacts (by rfl)

private theorem leaf3276FlatSound : Sound leaf3276Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3276CertificateValid
    leaf3276InnerLogValid leaf3276CoversExact leaf3276LowerChecked

private noncomputable def leaf3277Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3277Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742423/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486261760) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2032572683/1073741824) }, upper := { exponent := 0, mantissa := (31315/16384) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973646131/54972523520) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf3277InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3277LocalValidity :
    LeafFacts leaf3277Box leaf3277Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3277Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486261760) }) = true
      norm_num [leaf3277Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3277CertificateValid :
    WideCertificateValid leaf3277Box leaf3277Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi189ValidityFacts
    leaf3277LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3277CoverageChecked :
    coverageCheck (innerAD leaf3277Box) leaf3277InnerLog = true := by
  rfl'

private theorem leaf3277InnerLogValid :
    leaf3277InnerLog.Valid 8 (innerAD leaf3277Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3277CoverageChecked

private noncomputable def leaf3277InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629423/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3277InputLogOnePlusV_eq :
    leaf3277InputLogOnePlusV = outerEnclosure 24
      (leaf3277Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3277RoundedFacts : LeafRoundedFacts 8
    leaf3277Certificate.logOnePlusV leaf3277InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3277InputLogOnePlusV_eq }

private noncomputable def leaf3277Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi189InputQChi innerPair100Input
    leaf3277InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3277LowerChecked :
    lowerCheck 24 leaf3277Box leaf3277Inputs = true := by
  rfl'

private theorem leaf3277CoversExact : CoversExact 8
    leaf3277Box leaf3277Certificate leaf3277InnerLog leaf3277Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi189RoundedFacts
    innerPair100RoundedFacts leaf3277RoundedFacts (by rfl)

private theorem leaf3277FlatSound : Sound leaf3277Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3277CertificateValid
    leaf3277InnerLogValid leaf3277CoversExact leaf3277LowerChecked

private noncomputable def leaf3278Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3278Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431276544) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2036635665/1073741824) }, upper := { exponent := 0, mantissa := (15689/8192) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868198399/274862553088) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf3278InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3278LocalValidity :
    LeafFacts leaf3278Box leaf3278Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3278Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431276544) }) = true
      norm_num [leaf3278Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3278CertificateValid :
    WideCertificateValid leaf3278Box leaf3278Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi189ValidityFacts
    leaf3278LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3278CoverageChecked :
    coverageCheck (innerAD leaf3278Box) leaf3278InnerLog = true := by
  rfl'

private theorem leaf3278InnerLogValid :
    leaf3278InnerLog.Valid 8 (innerAD leaf3278Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3278CoverageChecked

private noncomputable def leaf3278InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629425/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3278InputLogOnePlusV_eq :
    leaf3278InputLogOnePlusV = outerEnclosure 24
      (leaf3278Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3278RoundedFacts : LeafRoundedFacts 8
    leaf3278Certificate.logOnePlusV leaf3278InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3278InputLogOnePlusV_eq }

private noncomputable def leaf3278Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi189InputQChi innerPair100Input
    leaf3278InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3278LowerChecked :
    lowerCheck 24 leaf3278Box leaf3278Inputs = true := by
  rfl'

private theorem leaf3278CoversExact : CoversExact 8
    leaf3278Box leaf3278Certificate leaf3278InnerLog leaf3278Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi189RoundedFacts
    innerPair100RoundedFacts leaf3278RoundedFacts (by rfl)

private theorem leaf3278FlatSound : Sound leaf3278Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3278CertificateValid
    leaf3278InnerLogValid leaf3278CoversExact leaf3278LowerChecked

private noncomputable def leaf3279Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (237/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3279Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742425/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431187456) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2048038233/1073741824) }, upper := { exponent := 0, mantissa := (493/256) } }, logOuter := sk221LogOuterCertificate, logK := sk221LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868109311/274862374912) } }, logDArg := sk221LogDArgCertificate }

private noncomputable def leaf3279InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3279LocalValidity :
    LeafFacts leaf3279Box leaf3279Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3279Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431187456) }) = true
      norm_num [leaf3279Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3279CertificateValid :
    WideCertificateValid leaf3279Box leaf3279Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk221ValidityFacts chi190ValidityFacts
    leaf3279LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3279CoverageChecked :
    coverageCheck (innerAD leaf3279Box) leaf3279InnerLog = true := by
  rfl'

private theorem leaf3279InnerLogValid :
    leaf3279InnerLog.Valid 8 (innerAD leaf3279Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3279CoverageChecked

private noncomputable def leaf3279InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629431/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3279InputLogOnePlusV_eq :
    leaf3279InputLogOnePlusV = outerEnclosure 24
      (leaf3279Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3279RoundedFacts : LeafRoundedFacts 8
    leaf3279Certificate.logOnePlusV leaf3279InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3279InputLogOnePlusV_eq }

private noncomputable def leaf3279Inputs : Inputs :=
  inputsOfCaches globalInput sk221RoundedInputs
    chi190InputQChi innerPair100Input
    leaf3279InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3279LowerChecked :
    lowerCheck 24 leaf3279Box leaf3279Inputs = true := by
  rfl'

private theorem leaf3279CoversExact : CoversExact 8
    leaf3279Box leaf3279Certificate leaf3279InnerLog leaf3279Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk221RoundedFacts chi190RoundedFacts
    innerPair100RoundedFacts leaf3279RoundedFacts (by rfl)

private theorem leaf3279FlatSound : Sound leaf3279Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3279CertificateValid
    leaf3279InnerLogValid leaf3279CoversExact leaf3279LowerChecked

private noncomputable def leaf3280Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (237/64), kHi := (119/32), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3280Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (45812307285/45810384896) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2052166747/1073741824) }, upper := { exponent := 0, mantissa := (247/128) } }, logOuter := sk222LogOuterCertificate, logK := sk222LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (91622692181/91620769792) } }, logDArg := sk222LogDArgCertificate }

private noncomputable def leaf3280InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3280LocalValidity :
    LeafFacts leaf3280Box leaf3280Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3280Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (45812307285/45810384896) }) = true
      norm_num [leaf3280Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3280CertificateValid :
    WideCertificateValid leaf3280Box leaf3280Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk222ValidityFacts chi190ValidityFacts
    leaf3280LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3280CoverageChecked :
    coverageCheck (innerAD leaf3280Box) leaf3280InnerLog = true := by
  rfl'

private theorem leaf3280InnerLogValid :
    leaf3280InnerLog.Valid 8 (innerAD leaf3280Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3280CoverageChecked

private noncomputable def leaf3280InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629433/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3280InputLogOnePlusV_eq :
    leaf3280InputLogOnePlusV = outerEnclosure 24
      (leaf3280Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3280RoundedFacts : LeafRoundedFacts 8
    leaf3280Certificate.logOnePlusV leaf3280InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3280InputLogOnePlusV_eq }

private noncomputable def leaf3280Inputs : Inputs :=
  inputsOfCaches globalInput sk222RoundedInputs
    chi190InputQChi innerPair100Input
    leaf3280InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3280LowerChecked :
    lowerCheck 24 leaf3280Box leaf3280Inputs = true := by
  rfl'

private theorem leaf3280CoversExact : CoversExact 8
    leaf3280Box leaf3280Certificate leaf3280InnerLog leaf3280Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk222RoundedFacts chi190RoundedFacts
    innerPair100RoundedFacts leaf3280RoundedFacts (by rfl)

private theorem leaf3280FlatSound : Sound leaf3280Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3280CertificateValid
    leaf3280InnerLogValid leaf3280CoversExact leaf3280LowerChecked

private noncomputable def leaf3281Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3281Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742427/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431244288) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2040698647/1073741824) }, upper := { exponent := 0, mantissa := (31441/16384) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868166143/274862488576) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf3281InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3281LocalValidity :
    LeafFacts leaf3281Box leaf3281Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3281Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431244288) }) = true
      norm_num [leaf3281Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3281CertificateValid :
    WideCertificateValid leaf3281Box leaf3281Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi189ValidityFacts
    leaf3281LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3281CoverageChecked :
    coverageCheck (innerAD leaf3281Box) leaf3281InnerLog = true := by
  rfl'

private theorem leaf3281InnerLogValid :
    leaf3281InnerLog.Valid 8 (innerAD leaf3281Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3281CoverageChecked

private noncomputable def leaf3281InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629427/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3281InputLogOnePlusV_eq :
    leaf3281InputLogOnePlusV = outerEnclosure 24
      (leaf3281Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3281RoundedFacts : LeafRoundedFacts 8
    leaf3281Certificate.logOnePlusV leaf3281InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3281InputLogOnePlusV_eq }

private noncomputable def leaf3281Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi189InputQChi innerPair100Input
    leaf3281InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3281LowerChecked :
    lowerCheck 24 leaf3281Box leaf3281Inputs = true := by
  rfl'

private theorem leaf3281CoversExact : CoversExact 8
    leaf3281Box leaf3281Certificate leaf3281InnerLog leaf3281Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi189RoundedFacts
    innerPair100RoundedFacts leaf3281RoundedFacts (by rfl)

private theorem leaf3281FlatSound : Sound leaf3281Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3281CertificateValid
    leaf3281InnerLogValid leaf3281CoversExact leaf3281LowerChecked

private noncomputable def leaf3282Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (31/128), chiHi := (63/256) }

private noncomputable def leaf3282Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431212032) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2044761629/1073741824) }, upper := { exponent := 0, mantissa := (1969/1024) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi189LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868133887/274862424064) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf3282InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3282LocalValidity :
    LeafFacts leaf3282Box leaf3282Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3282Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431212032) }) = true
      norm_num [leaf3282Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3282CertificateValid :
    WideCertificateValid leaf3282Box leaf3282Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi189ValidityFacts
    leaf3282LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3282CoverageChecked :
    coverageCheck (innerAD leaf3282Box) leaf3282InnerLog = true := by
  rfl'

private theorem leaf3282InnerLogValid :
    leaf3282InnerLog.Valid 8 (innerAD leaf3282Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3282CoverageChecked

private noncomputable def leaf3282InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629429/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3282InputLogOnePlusV_eq :
    leaf3282InputLogOnePlusV = outerEnclosure 24
      (leaf3282Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3282RoundedFacts : LeafRoundedFacts 8
    leaf3282Certificate.logOnePlusV leaf3282InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3282InputLogOnePlusV_eq }

private noncomputable def leaf3282Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi189InputQChi innerPair100Input
    leaf3282InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3282LowerChecked :
    lowerCheck 24 leaf3282Box leaf3282Inputs = true := by
  rfl'

private theorem leaf3282CoversExact : CoversExact 8
    leaf3282Box leaf3282Certificate leaf3282InnerLog leaf3282Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi189RoundedFacts
    innerPair100RoundedFacts leaf3282RoundedFacts (by rfl)

private theorem leaf3282FlatSound : Sound leaf3282Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3282CertificateValid
    leaf3282InnerLogValid leaf3282CoversExact leaf3282LowerChecked

private noncomputable def leaf3283Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (239/64), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3283Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742429/1073741824) }, vSqrt := { lower := (8191/8192), upper := (27487384371/27486224384) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2056295261/1073741824) }, upper := { exponent := 0, mantissa := (495/256) } }, logOuter := sk223LogOuterCertificate, logK := sk223LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (54973608755/54972448768) } }, logDArg := sk223LogDArgCertificate }

private noncomputable def leaf3283InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3283LocalValidity :
    LeafFacts leaf3283Box leaf3283Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3283Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (27487384371/27486224384) }) = true
      norm_num [leaf3283Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3283CertificateValid :
    WideCertificateValid leaf3283Box leaf3283Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk223ValidityFacts chi190ValidityFacts
    leaf3283LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3283CoverageChecked :
    coverageCheck (innerAD leaf3283Box) leaf3283InnerLog = true := by
  rfl'

private theorem leaf3283InnerLogValid :
    leaf3283InnerLog.Valid 8 (innerAD leaf3283Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3283CoverageChecked

private noncomputable def leaf3283InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629435/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3283InputLogOnePlusV_eq :
    leaf3283InputLogOnePlusV = outerEnclosure 24
      (leaf3283Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3283RoundedFacts : LeafRoundedFacts 8
    leaf3283Certificate.logOnePlusV leaf3283InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3283InputLogOnePlusV_eq }

private noncomputable def leaf3283Inputs : Inputs :=
  inputsOfCaches globalInput sk223RoundedInputs
    chi190InputQChi innerPair100Input
    leaf3283InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3283LowerChecked :
    lowerCheck 24 leaf3283Box leaf3283Inputs = true := by
  rfl'

private theorem leaf3283CoversExact : CoversExact 8
    leaf3283Box leaf3283Certificate leaf3283InnerLog leaf3283Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk223RoundedFacts chi190RoundedFacts
    innerPair100RoundedFacts leaf3283RoundedFacts (by rfl)

private theorem leaf3283FlatSound : Sound leaf3283Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3283CertificateValid
    leaf3283InnerLogValid leaf3283CoversExact leaf3283LowerChecked

private noncomputable def leaf3284Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (239/64), kHi := (15/4), chiLo := (63/256), chiHi := (1/4) }

private noncomputable def leaf3284Certificate : LRSmallSBridgeCoreCertificate :=
  { coordinate := { tSqrt := { lower := (32767/32768), upper := (1073742431/1073741824) }, vSqrt := { lower := (8191/8192), upper := (137436921855/137431089152) } }, logTwo := globalLogTwoCertificate, logInner := { lower := { exponent := 0, mantissa := (2060423775/1073741824) }, upper := { exponent := 0, mantissa := (31/16) } }, logOuter := sk224LogOuterCertificate, logK := sk224LogKCertificate, logChi := chi190LogChiCertificate, logOnePlusV := { lower := { exponent := 0, mantissa := (16383/8192) }, upper := { exponent := 1, mantissa := (274868011007/274862178304) } }, logDArg := sk224LogDArgCertificate }

private noncomputable def leaf3284InnerLog : WideLogData :=
  innerPair100Data

set_option maxRecDepth 1000000 in
private theorem leaf3284LocalValidity :
    LeafFacts leaf3284Box leaf3284Certificate :=
  { coordinate := by rfl'
    logOnePlusV := by
      change leaf3284Certificate.logOnePlusV.check
        (RationalEnclosure.add (RationalEnclosure.point 1)
          { lower := (8191/8192), upper := (137436921855/137431089152) }) = true
      norm_num [leaf3284Certificate,
        RationalEnclosure.LogIntervalCertificate.check,
        RationalEnclosure.LogRangeCertificate.check,
        RationalEnclosure.point, RationalEnclosure.add] }

private theorem leaf3284CertificateValid :
    WideCertificateValid leaf3284Box leaf3284Certificate :=
  wideCertificateValid_of_cached globalValidityFacts
    sk224ValidityFacts chi190ValidityFacts
    leaf3284LocalValidity (by rfl)

set_option maxRecDepth 1000000 in
private theorem leaf3284CoverageChecked :
    coverageCheck (innerAD leaf3284Box) leaf3284InnerLog = true := by
  rfl'

private theorem leaf3284InnerLogValid :
    leaf3284InnerLog.Valid 8 (innerAD leaf3284Box) :=
  wideLogDataValid_of_cachedCheck endpoint22PositiveFacts
    endpoint23PositiveFacts.valid leaf3284CoverageChecked

private noncomputable def leaf3284InputLogOnePlusV : RationalEnclosure :=
  { lower := (11628055/16777216), upper := (11629437/16777216) }

set_option maxRecDepth 1000000 in
private theorem leaf3284InputLogOnePlusV_eq :
    leaf3284InputLogOnePlusV = outerEnclosure 24
      (leaf3284Certificate.logOnePlusV.enclosure 8) := by
  rfl'

private theorem leaf3284RoundedFacts : LeafRoundedFacts 8
    leaf3284Certificate.logOnePlusV leaf3284InputLogOnePlusV :=
  { coversLogOnePlusV :=
      covers_of_outerEnclosure_eq 24 leaf3284InputLogOnePlusV_eq }

private noncomputable def leaf3284Inputs : Inputs :=
  inputsOfCaches globalInput sk224RoundedInputs
    chi190InputQChi innerPair100Input
    leaf3284InputLogOnePlusV

set_option maxRecDepth 1000000 in
private theorem leaf3284LowerChecked :
    lowerCheck 24 leaf3284Box leaf3284Inputs = true := by
  rfl'

private theorem leaf3284CoversExact : CoversExact 8
    leaf3284Box leaf3284Certificate leaf3284InnerLog leaf3284Inputs := by
  exact coversExact_of_cached globalRoundedFacts
    sk224RoundedFacts chi190RoundedFacts
    innerPair100RoundedFacts leaf3284RoundedFacts (by rfl)

private theorem leaf3284FlatSound : Sound leaf3284Box := by
  intro point hpoint
  exact positive_of_lowerCheck 24 8 hpoint leaf3284CertificateValid
    leaf3284InnerLogValid leaf3284CoversExact leaf3284LowerChecked

private noncomputable def component67Node0Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component67Node0_sound : Sound component67Node0Box :=
  sound_of_literal_split component67Node0Box leaf3221Box leaf3222Box
    .k (233/64) (by rfl) (by rfl)
    leaf3221FlatSound leaf3222FlatSound

private noncomputable def component67Node1Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node1_sound : Sound component67Node1Box :=
  sound_of_literal_split component67Node1Box leaf3223Box leaf3224Box
    .k (233/64) (by rfl) (by rfl)
    leaf3223FlatSound leaf3224FlatSound

private noncomputable def component67Node2Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node2_sound : Sound component67Node2Box :=
  sound_of_literal_split component67Node2Box component67Node0Box component67Node1Box
    .chi (57/256) (by rfl) (by rfl)
    component67Node0_sound component67Node1_sound

private noncomputable def component67Node3Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component67Node3_sound : Sound component67Node3Box :=
  sound_of_literal_split component67Node3Box leaf3225Box leaf3226Box
    .k (235/64) (by rfl) (by rfl)
    leaf3225FlatSound leaf3226FlatSound

private noncomputable def component67Node4Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node4_sound : Sound component67Node4Box :=
  sound_of_literal_split component67Node4Box leaf3227Box leaf3228Box
    .k (235/64) (by rfl) (by rfl)
    leaf3227FlatSound leaf3228FlatSound

private noncomputable def component67Node5Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node5_sound : Sound component67Node5Box :=
  sound_of_literal_split component67Node5Box component67Node3Box component67Node4Box
    .chi (57/256) (by rfl) (by rfl)
    component67Node3_sound component67Node4_sound

private noncomputable def component67Node6Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node6_sound : Sound component67Node6Box :=
  sound_of_literal_split component67Node6Box component67Node2Box component67Node5Box
    .k (117/32) (by rfl) (by rfl)
    component67Node2_sound component67Node5_sound

private noncomputable def component67Node7Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component67Node7_sound : Sound component67Node7Box :=
  sound_of_literal_split component67Node7Box leaf3229Box leaf3230Box
    .k (233/64) (by rfl) (by rfl)
    leaf3229FlatSound leaf3230FlatSound

private noncomputable def component67Node8Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component67Node8_sound : Sound component67Node8Box :=
  sound_of_literal_split component67Node8Box leaf3231Box leaf3232Box
    .k (233/64) (by rfl) (by rfl)
    leaf3231FlatSound leaf3232FlatSound

private noncomputable def component67Node9Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component67Node9_sound : Sound component67Node9Box :=
  sound_of_literal_split component67Node9Box component67Node7Box component67Node8Box
    .chi (59/256) (by rfl) (by rfl)
    component67Node7_sound component67Node8_sound

private noncomputable def component67Node10Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component67Node10_sound : Sound component67Node10Box :=
  sound_of_literal_split component67Node10Box leaf3233Box leaf3234Box
    .k (235/64) (by rfl) (by rfl)
    leaf3233FlatSound leaf3234FlatSound

private noncomputable def component67Node11Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component67Node11_sound : Sound component67Node11Box :=
  sound_of_literal_split component67Node11Box leaf3235Box leaf3236Box
    .k (235/64) (by rfl) (by rfl)
    leaf3235FlatSound leaf3236FlatSound

private noncomputable def component67Node12Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component67Node12_sound : Sound component67Node12Box :=
  sound_of_literal_split component67Node12Box component67Node10Box component67Node11Box
    .chi (59/256) (by rfl) (by rfl)
    component67Node10_sound component67Node11_sound

private noncomputable def component67Node13Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component67Node13_sound : Sound component67Node13Box :=
  sound_of_literal_split component67Node13Box component67Node9Box component67Node12Box
    .k (117/32) (by rfl) (by rfl)
    component67Node9_sound component67Node12_sound

private noncomputable def component67Node14Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component67Node14_sound : Sound component67Node14Box :=
  sound_of_literal_split component67Node14Box component67Node6Box component67Node13Box
    .chi (29/128) (by rfl) (by rfl)
    component67Node6_sound component67Node13_sound

private noncomputable def component67Node15Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component67Node15_sound : Sound component67Node15Box :=
  sound_of_literal_split component67Node15Box leaf3237Box leaf3238Box
    .k (237/64) (by rfl) (by rfl)
    leaf3237FlatSound leaf3238FlatSound

private noncomputable def component67Node16Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node16_sound : Sound component67Node16Box :=
  sound_of_literal_split component67Node16Box leaf3239Box leaf3240Box
    .k (237/64) (by rfl) (by rfl)
    leaf3239FlatSound leaf3240FlatSound

private noncomputable def component67Node17Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node17_sound : Sound component67Node17Box :=
  sound_of_literal_split component67Node17Box component67Node15Box component67Node16Box
    .chi (57/256) (by rfl) (by rfl)
    component67Node15_sound component67Node16_sound

private noncomputable def component67Node18Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (7/32), chiHi := (57/256) }

set_option maxRecDepth 1000000 in
private theorem component67Node18_sound : Sound component67Node18Box :=
  sound_of_literal_split component67Node18Box leaf3241Box leaf3242Box
    .k (239/64) (by rfl) (by rfl)
    leaf3241FlatSound leaf3242FlatSound

private noncomputable def component67Node19Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (57/256), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node19_sound : Sound component67Node19Box :=
  sound_of_literal_split component67Node19Box leaf3243Box leaf3244Box
    .k (239/64) (by rfl) (by rfl)
    leaf3243FlatSound leaf3244FlatSound

private noncomputable def component67Node20Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node20_sound : Sound component67Node20Box :=
  sound_of_literal_split component67Node20Box component67Node18Box component67Node19Box
    .chi (57/256) (by rfl) (by rfl)
    component67Node18_sound component67Node19_sound

private noncomputable def component67Node21Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (7/32), chiHi := (29/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node21_sound : Sound component67Node21Box :=
  sound_of_literal_split component67Node21Box component67Node17Box component67Node20Box
    .k (119/32) (by rfl) (by rfl)
    component67Node17_sound component67Node20_sound

private noncomputable def component67Node22Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component67Node22_sound : Sound component67Node22Box :=
  sound_of_literal_split component67Node22Box leaf3245Box leaf3246Box
    .k (237/64) (by rfl) (by rfl)
    leaf3245FlatSound leaf3246FlatSound

private noncomputable def component67Node23Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component67Node23_sound : Sound component67Node23Box :=
  sound_of_literal_split component67Node23Box leaf3247Box leaf3248Box
    .k (237/64) (by rfl) (by rfl)
    leaf3247FlatSound leaf3248FlatSound

private noncomputable def component67Node24Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component67Node24_sound : Sound component67Node24Box :=
  sound_of_literal_split component67Node24Box component67Node22Box component67Node23Box
    .chi (59/256) (by rfl) (by rfl)
    component67Node22_sound component67Node23_sound

private noncomputable def component67Node25Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (29/128), chiHi := (59/256) }

set_option maxRecDepth 1000000 in
private theorem component67Node25_sound : Sound component67Node25Box :=
  sound_of_literal_split component67Node25Box leaf3249Box leaf3250Box
    .k (239/64) (by rfl) (by rfl)
    leaf3249FlatSound leaf3250FlatSound

private noncomputable def component67Node26Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (59/256), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component67Node26_sound : Sound component67Node26Box :=
  sound_of_literal_split component67Node26Box leaf3251Box leaf3252Box
    .k (239/64) (by rfl) (by rfl)
    leaf3251FlatSound leaf3252FlatSound

private noncomputable def component67Node27Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component67Node27_sound : Sound component67Node27Box :=
  sound_of_literal_split component67Node27Box component67Node25Box component67Node26Box
    .chi (59/256) (by rfl) (by rfl)
    component67Node25_sound component67Node26_sound

private noncomputable def component67Node28Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (29/128), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component67Node28_sound : Sound component67Node28Box :=
  sound_of_literal_split component67Node28Box component67Node24Box component67Node27Box
    .k (119/32) (by rfl) (by rfl)
    component67Node24_sound component67Node27_sound

private noncomputable def component67Node29Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component67Node29_sound : Sound component67Node29Box :=
  sound_of_literal_split component67Node29Box component67Node21Box component67Node28Box
    .chi (29/128) (by rfl) (by rfl)
    component67Node21_sound component67Node28_sound

private noncomputable def component67Node30Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (7/32), chiHi := (15/64) }

set_option maxRecDepth 1000000 in
private theorem component67Node30_sound : Sound component67Node30Box :=
  sound_of_literal_split component67Node30Box component67Node14Box component67Node29Box
    .k (59/16) (by rfl) (by rfl)
    component67Node14_sound component67Node29_sound

private noncomputable def component67Node31Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component67Node31_sound : Sound component67Node31Box :=
  sound_of_literal_split component67Node31Box leaf3253Box leaf3254Box
    .k (233/64) (by rfl) (by rfl)
    leaf3253FlatSound leaf3254FlatSound

private noncomputable def component67Node32Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node32_sound : Sound component67Node32Box :=
  sound_of_literal_split component67Node32Box leaf3255Box leaf3256Box
    .k (233/64) (by rfl) (by rfl)
    leaf3255FlatSound leaf3256FlatSound

private noncomputable def component67Node33Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node33_sound : Sound component67Node33Box :=
  sound_of_literal_split component67Node33Box component67Node31Box component67Node32Box
    .chi (61/256) (by rfl) (by rfl)
    component67Node31_sound component67Node32_sound

private noncomputable def component67Node34Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component67Node34_sound : Sound component67Node34Box :=
  sound_of_literal_split component67Node34Box leaf3257Box leaf3258Box
    .k (235/64) (by rfl) (by rfl)
    leaf3257FlatSound leaf3258FlatSound

private noncomputable def component67Node35Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node35_sound : Sound component67Node35Box :=
  sound_of_literal_split component67Node35Box leaf3259Box leaf3260Box
    .k (235/64) (by rfl) (by rfl)
    leaf3259FlatSound leaf3260FlatSound

private noncomputable def component67Node36Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node36_sound : Sound component67Node36Box :=
  sound_of_literal_split component67Node36Box component67Node34Box component67Node35Box
    .chi (61/256) (by rfl) (by rfl)
    component67Node34_sound component67Node35_sound

private noncomputable def component67Node37Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node37_sound : Sound component67Node37Box :=
  sound_of_literal_split component67Node37Box component67Node33Box component67Node36Box
    .k (117/32) (by rfl) (by rfl)
    component67Node33_sound component67Node36_sound

private noncomputable def component67Node38Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component67Node38_sound : Sound component67Node38Box :=
  sound_of_literal_split component67Node38Box leaf3261Box leaf3262Box
    .k (233/64) (by rfl) (by rfl)
    leaf3261FlatSound leaf3262FlatSound

private noncomputable def component67Node39Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component67Node39_sound : Sound component67Node39Box :=
  sound_of_literal_split component67Node39Box leaf3263Box leaf3264Box
    .k (233/64) (by rfl) (by rfl)
    leaf3263FlatSound leaf3264FlatSound

private noncomputable def component67Node40Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (117/32), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component67Node40_sound : Sound component67Node40Box :=
  sound_of_literal_split component67Node40Box component67Node38Box component67Node39Box
    .chi (63/256) (by rfl) (by rfl)
    component67Node38_sound component67Node39_sound

private noncomputable def component67Node41Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component67Node41_sound : Sound component67Node41Box :=
  sound_of_literal_split component67Node41Box leaf3265Box leaf3266Box
    .k (235/64) (by rfl) (by rfl)
    leaf3265FlatSound leaf3266FlatSound

private noncomputable def component67Node42Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component67Node42_sound : Sound component67Node42Box :=
  sound_of_literal_split component67Node42Box leaf3267Box leaf3268Box
    .k (235/64) (by rfl) (by rfl)
    leaf3267FlatSound leaf3268FlatSound

private noncomputable def component67Node43Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (117/32), kHi := (59/16), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component67Node43_sound : Sound component67Node43Box :=
  sound_of_literal_split component67Node43Box component67Node41Box component67Node42Box
    .chi (63/256) (by rfl) (by rfl)
    component67Node41_sound component67Node42_sound

private noncomputable def component67Node44Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component67Node44_sound : Sound component67Node44Box :=
  sound_of_literal_split component67Node44Box component67Node40Box component67Node43Box
    .k (117/32) (by rfl) (by rfl)
    component67Node40_sound component67Node43_sound

private noncomputable def component67Node45Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (59/16), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component67Node45_sound : Sound component67Node45Box :=
  sound_of_literal_split component67Node45Box component67Node37Box component67Node44Box
    .chi (31/128) (by rfl) (by rfl)
    component67Node37_sound component67Node44_sound

private noncomputable def component67Node46Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component67Node46_sound : Sound component67Node46Box :=
  sound_of_literal_split component67Node46Box leaf3269Box leaf3270Box
    .k (237/64) (by rfl) (by rfl)
    leaf3269FlatSound leaf3270FlatSound

private noncomputable def component67Node47Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node47_sound : Sound component67Node47Box :=
  sound_of_literal_split component67Node47Box leaf3271Box leaf3272Box
    .k (237/64) (by rfl) (by rfl)
    leaf3271FlatSound leaf3272FlatSound

private noncomputable def component67Node48Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node48_sound : Sound component67Node48Box :=
  sound_of_literal_split component67Node48Box component67Node46Box component67Node47Box
    .chi (61/256) (by rfl) (by rfl)
    component67Node46_sound component67Node47_sound

private noncomputable def component67Node49Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (15/64), chiHi := (61/256) }

set_option maxRecDepth 1000000 in
private theorem component67Node49_sound : Sound component67Node49Box :=
  sound_of_literal_split component67Node49Box leaf3273Box leaf3274Box
    .k (239/64) (by rfl) (by rfl)
    leaf3273FlatSound leaf3274FlatSound

private noncomputable def component67Node50Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (61/256), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node50_sound : Sound component67Node50Box :=
  sound_of_literal_split component67Node50Box leaf3275Box leaf3276Box
    .k (239/64) (by rfl) (by rfl)
    leaf3275FlatSound leaf3276FlatSound

private noncomputable def component67Node51Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node51_sound : Sound component67Node51Box :=
  sound_of_literal_split component67Node51Box component67Node49Box component67Node50Box
    .chi (61/256) (by rfl) (by rfl)
    component67Node49_sound component67Node50_sound

private noncomputable def component67Node52Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (15/64), chiHi := (31/128) }

set_option maxRecDepth 1000000 in
private theorem component67Node52_sound : Sound component67Node52Box :=
  sound_of_literal_split component67Node52Box component67Node48Box component67Node51Box
    .k (119/32) (by rfl) (by rfl)
    component67Node48_sound component67Node51_sound

private noncomputable def component67Node53Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component67Node53_sound : Sound component67Node53Box :=
  sound_of_literal_split component67Node53Box leaf3277Box leaf3278Box
    .k (237/64) (by rfl) (by rfl)
    leaf3277FlatSound leaf3278FlatSound

private noncomputable def component67Node54Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component67Node54_sound : Sound component67Node54Box :=
  sound_of_literal_split component67Node54Box leaf3279Box leaf3280Box
    .k (237/64) (by rfl) (by rfl)
    leaf3279FlatSound leaf3280FlatSound

private noncomputable def component67Node55Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (119/32), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component67Node55_sound : Sound component67Node55Box :=
  sound_of_literal_split component67Node55Box component67Node53Box component67Node54Box
    .chi (63/256) (by rfl) (by rfl)
    component67Node53_sound component67Node54_sound

private noncomputable def component67Node56Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (31/128), chiHi := (63/256) }

set_option maxRecDepth 1000000 in
private theorem component67Node56_sound : Sound component67Node56Box :=
  sound_of_literal_split component67Node56Box leaf3281Box leaf3282Box
    .k (239/64) (by rfl) (by rfl)
    leaf3281FlatSound leaf3282FlatSound

private noncomputable def component67Node57Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (63/256), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component67Node57_sound : Sound component67Node57Box :=
  sound_of_literal_split component67Node57Box leaf3283Box leaf3284Box
    .k (239/64) (by rfl) (by rfl)
    leaf3283FlatSound leaf3284FlatSound

private noncomputable def component67Node58Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (119/32), kHi := (15/4), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component67Node58_sound : Sound component67Node58Box :=
  sound_of_literal_split component67Node58Box component67Node56Box component67Node57Box
    .chi (63/256) (by rfl) (by rfl)
    component67Node56_sound component67Node57_sound

private noncomputable def component67Node59Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (31/128), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component67Node59_sound : Sound component67Node59Box :=
  sound_of_literal_split component67Node59Box component67Node55Box component67Node58Box
    .k (119/32) (by rfl) (by rfl)
    component67Node55_sound component67Node58_sound

private noncomputable def component67Node60Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (59/16), kHi := (15/4), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component67Node60_sound : Sound component67Node60Box :=
  sound_of_literal_split component67Node60Box component67Node52Box component67Node59Box
    .chi (31/128) (by rfl) (by rfl)
    component67Node52_sound component67Node59_sound

private noncomputable def component67Node61Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (15/64), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
private theorem component67Node61_sound : Sound component67Node61Box :=
  sound_of_literal_split component67Node61Box component67Node45Box component67Node60Box
    .k (59/16) (by rfl) (by rfl)
    component67Node45_sound component67Node60_sound

noncomputable def component67Box : CertificateBox :=
  { sLo := (0), sHi := (1/16384), kLo := (29/8), kHi := (15/4), chiLo := (7/32), chiHi := (1/4) }

set_option maxRecDepth 1000000 in
theorem component67_sound : Sound component67Box :=
  sound_of_literal_split component67Box component67Node30Box component67Node61Box
    .chi (15/64) (by rfl) (by rfl)
    component67Node30_sound component67Node61_sound

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
